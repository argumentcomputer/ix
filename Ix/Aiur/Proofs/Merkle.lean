/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Merkle
import Ix.Aiur.Proofs.Blake3
import Ix.Aiur.Proofs.MerkleCap

/-! Fixed-width row packing and binary path authentication. Hash security
is reduced to a collision among the explicitly retained query inputs. -/

namespace Aiur.NativeAIR.Merkle

theorem fieldsBytes_injective {left right : List G}
    (same : Transcript.fieldsBytes left = Transcript.fieldsBytes right) : left = right := by
  have lengths := congrArg List.length same
  rw [Transcript.fieldsBytes_length, Transcript.fieldsBytes_length] at lengths
  have count : left.length = right.length := by omega
  have l := KeyCodec.readMany_reads ProofCodec.encodeField left
    (fun value _ => ProofCodec.readField_reads value) []
  have r := KeyCodec.readMany_reads ProofCodec.encodeField right
    (fun value _ => ProofCodec.readField_reads value) []
  change KeyCodec.readMany ProofCodec.readField left.length
    (Transcript.fieldsBytes left ++ []) = some (left, []) at l
  change KeyCodec.readMany ProofCodec.readField right.length
    (Transcript.fieldsBytes right ++ []) = some (right, []) at r
  rw [same, count, r] at l
  exact (congrArg Prod.fst (Option.some.inj l)).symm

theorem pairBytes_length (left right : Digest) : (pairBytes left right).length = 64 := by
  simp [pairBytes]

theorem pairBytes_injective {left right otherLeft otherRight : Digest}
    (same : pairBytes left right = pairBytes otherLeft otherRight) :
    left = otherLeft ∧ right = otherRight := by
  have heads := congrArg (List.take 32) same
  have tails := congrArg (List.drop 32) same
  simp [pairBytes] at heads tails
  exact ⟨Vector.toList_inj.mp heads, Vector.toList_inj.mp tails⟩

theorem branchBytes_injective {index : Nat} {left right leftSibling rightSibling : Digest}
    (same : branchBytes index left leftSibling = branchBytes index right rightSibling) :
    left = right ∧ leftSibling = rightSibling := by
  unfold branchBytes at same
  split at same
  · exact pairBytes_injective same
  · exact (pairBytes_injective same).symm

theorem shape_length {dimensions : List Dimensions} {rows : List (List G)}
    (fits : shape dimensions rows = true) : rows.length = dimensions.length := by
  induction dimensions generalizing rows with
  | nil => cases rows <;> simp_all [shape]
  | cons dimension dimensions ih =>
    cases rows with
    | nil => simp [shape] at fits
    | cons row rows =>
      simp only [shape, Bool.and_eq_true, beq_iff_eq] at fits
      simp only [List.length_cons, ih fits.2]

theorem rowsAt_absent {dimensions : List Dimensions} {rows : List (List G)} {height : Nat}
    (absent : hasHeight dimensions height = false) : rowsAt dimensions rows height = [] := by
  induction dimensions generalizing rows with
  | nil => rfl
  | cons dimension dimensions ih =>
    simp only [hasHeight, List.any_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at absent
    cases rows with
    | nil => rfl
    | cons row rows => simp only [rowsAt, if_neg absent.1, ih absent.2]

theorem rowsAt_injective {dimensions : List Dimensions} {left right : List (List G)}
    (lf : shape dimensions left = true) (rf : shape dimensions right = true)
    (same : ∀ height, (rowsAt dimensions left height).flatten = (rowsAt dimensions right height).flatten) :
    left = right := by
  induction dimensions generalizing left right with
  | nil => cases left <;> cases right <;> simp_all [shape]
  | cons dimension dimensions ih =>
    cases left with
    | nil => simp [shape] at lf
    | cons l left =>
      cases right with
      | nil => simp [shape] at rf
      | cons r right =>
        simp only [shape, Bool.and_eq_true, beq_iff_eq] at lf rf
        have first := same dimension.logHeight
        simp only [rowsAt] at first
        have pieces := List.append_inj first (lf.1.trans rf.1.symm)
        obtain rfl := pieces.1
        congr 1
        apply ih lf.2 rf.2
        intro height
        have next := same height
        by_cases equal : dimension.logHeight = height
        · simp only [rowsAt, if_pos equal, List.flatten_cons] at next
          exact List.append_cancel_left next
        · simpa only [rowsAt, if_neg equal] using next

theorem rowBytes_injective {dimensions : List Dimensions} {left right : List (List G)}
    (lf : shape dimensions left = true) (rf : shape dimensions right = true)
    (same : ∀ height, rowBytes dimensions left height = rowBytes dimensions right height) :
    left = right :=
  rowsAt_injective lf rf fun height => fieldsBytes_injective (same height)

theorem CollisionOn.mono {hash : Hash} {smaller larger : List (List UInt8)}
    (subset : ∀ input ∈ smaller, input ∈ larger) (collision : CollisionOn hash smaller) :
    CollisionOn hash larger := by
  obtain ⟨left, hl, right, hr, different, same⟩ := collision
  exact ⟨left, subset left hl, right, subset right hr, different, same⟩

theorem equal_of_no_collision {hash : Hash} {inputs : List (List UInt8)}
    (free : ¬CollisionOn hash inputs) {left right : List UInt8}
    (hl : left ∈ inputs) (hr : right ∈ inputs) (same : hash left = hash right) : left = right := by
  by_cases equal : left = right
  · exact equal
  · exact False.elim (free ⟨left, hl, right, hr, equal, same⟩)

theorem step_calls (hash : Hash) (dimensions : List Dimensions) (rows : List (List G))
    (height index : Nat) (current sibling : Digest) :
    (step hash dimensions rows height index current sibling).inputs.length ≤ 3 := by
  unfold step
  split <;> simp only [List.length_cons, List.length_nil] <;> omega

theorem walk_calls (hash : Hash) (dimensions : List Dimensions) (rows : List (List G))
    (height index : Nat) (current : Digest) (proof : List Digest) :
    (walk hash dimensions rows height index current proof).inputs.length ≤ 3 * proof.length := by
  induction proof generalizing height index current with
  | nil => simp [walk]
  | cons sibling proof ih =>
    simp only [walk, List.length_append, List.length_cons]
    have := step_calls hash dimensions rows (height - 1) index current sibling
    have := ih (height - 1) (index / 2) (step hash dimensions rows (height - 1) index current sibling).digest
    omega

theorem step_binding {hash : Hash} {dimensions : List Dimensions} {leftRows rightRows : List (List G)}
    {height index : Nat} {left right leftSibling rightSibling : Digest}
    (free : ¬CollisionOn hash
      ((step hash dimensions leftRows height index left leftSibling).inputs ++
       (step hash dimensions rightRows height index right rightSibling).inputs))
    (same : (step hash dimensions leftRows height index left leftSibling).digest =
      (step hash dimensions rightRows height index right rightSibling).digest) :
    left = right ∧ (hasHeight dimensions height = true →
      rowBytes dimensions leftRows height = rowBytes dimensions rightRows height) := by
  by_cases inject : hasHeight dimensions height = true
  · simp only [step, inject, ↓reduceIte] at same
    have outer := equal_of_no_collision free (same := same)
      (by simp [step, inject]) (by simp [step, inject])
    have parts := pairBytes_injective outer
    have branch := equal_of_no_collision free
      (by simp [step, inject]) (by simp [step, inject]) parts.1
    have leaf := equal_of_no_collision free
      (by simp [step, inject]) (by simp [step, inject]) parts.2
    exact ⟨(branchBytes_injective branch).1, fun _ => leaf⟩
  · simp only [step, if_neg inject] at same
    have branch := equal_of_no_collision free (same := same)
      (by simp [step, inject]) (by simp [step, inject])
    exact ⟨(branchBytes_injective branch).1, fun impossible => False.elim (inject impossible)⟩

/-- Equal final nodes bind the starting digest and every injected height,
unless the two walks have queried a concrete hash collision. -/
theorem walk_binding {hash : Hash} {dimensions : List Dimensions} {leftRows rightRows : List (List G)}
    {height index : Nat} {left right : Digest} {leftProof rightProof : List Digest}
    (count : leftProof.length = rightProof.length)
    (free : ¬CollisionOn hash
      ((walk hash dimensions leftRows height index left leftProof).inputs ++
       (walk hash dimensions rightRows height index right rightProof).inputs))
    (same : (walk hash dimensions leftRows height index left leftProof).digest =
      (walk hash dimensions rightRows height index right rightProof).digest) :
    left = right ∧ ∀ depth < leftProof.length,
      hasHeight dimensions (height - (depth + 1)) = true →
      rowBytes dimensions leftRows (height - (depth + 1)) =
        rowBytes dimensions rightRows (height - (depth + 1)) := by
  induction leftProof generalizing rightProof height index left right with
  | nil =>
    have empty : rightProof = [] := List.eq_nil_of_length_eq_zero count.symm
    subst rightProof
    exact ⟨same, fun depth bound => by simp at bound⟩
  | cons leftSibling leftProof ih =>
    cases rightProof with
    | nil => simp at count
    | cons rightSibling rightProof =>
      have tailCount : leftProof.length = rightProof.length := Nat.succ.inj count
      have freeTail : ¬CollisionOn hash
          ((walk hash dimensions leftRows (height - 1) (index / 2)
              (step hash dimensions leftRows (height - 1) index left leftSibling).digest leftProof).inputs ++
           (walk hash dimensions rightRows (height - 1) (index / 2)
              (step hash dimensions rightRows (height - 1) index right rightSibling).digest rightProof).inputs) := by
        intro collision
        apply free (collision.mono ?_)
        intro input member
        simp only [List.mem_append] at member
        simp only [walk, List.mem_append]
        exact member.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))
      have tail := ih tailCount freeTail same
      have freeStep : ¬CollisionOn hash
          ((step hash dimensions leftRows (height - 1) index left leftSibling).inputs ++
           (step hash dimensions rightRows (height - 1) index right rightSibling).inputs) := by
        intro collision
        apply free (collision.mono ?_)
        intro input member
        simp only [List.mem_append] at member
        simp only [walk, List.mem_append]
        exact member.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h))
      have first := step_binding freeStep tail.1
      refine ⟨first.1, ?_⟩
      intro depth bound inject
      cases depth with
      | zero => exact first.2 inject
      | succ depth =>
        have shorter : depth < leftProof.length := by simpa using bound
        have heightEq : height - (depth + 1 + 1) = (height - 1) - (depth + 1) := by omega
        rw [heightEq] at inject ⊢
        exact tail.2 depth shorter inject

theorem replay_success {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {rows : List (List G)} {proof : List Digest} {result : Replay}
    (success : replay hash dimensions capHeight index rows proof = some result) :
    dimensions ≠ [] ∧ shape dimensions rows = true ∧ proof.length = maxHeight dimensions - capHeight ∧
      index < 2^maxHeight dimensions ∧
      result = ⟨maxHeight dimensions - proof.length, index / 2^proof.length,
        ⟨(walk hash dimensions rows (maxHeight dimensions) index
            (hash (rowBytes dimensions rows (maxHeight dimensions))) proof).digest,
         rowBytes dimensions rows (maxHeight dimensions) ::
           (walk hash dimensions rows (maxHeight dimensions) index
             (hash (rowBytes dimensions rows (maxHeight dimensions))) proof).inputs⟩⟩ := by
  unfold replay at success
  dsimp only at success
  split at success
  · cases success
  next valid =>
    simp only [Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_true',
      bne_iff_ne, Bool.not_eq_false, decide_eq_true_eq, not_or] at valid
    exact ⟨valid.1.1.1, by simpa using valid.1.1.2,
      Decidable.not_not.mp valid.1.2, valid.2, (Option.some.inj success).symm⟩

theorem replay_complete {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {rows : List (List G)} {proof : List Digest}
    (nonempty : dimensions ≠ []) (fits : shape dimensions rows = true)
    (count : proof.length = maxHeight dimensions - capHeight) (bounded : index < 2^maxHeight dimensions) :
    replay hash dimensions capHeight index rows proof =
      some ⟨maxHeight dimensions - proof.length, index / 2^proof.length,
        ⟨(walk hash dimensions rows (maxHeight dimensions) index
            (hash (rowBytes dimensions rows (maxHeight dimensions))) proof).digest,
         rowBytes dimensions rows (maxHeight dimensions) ::
           (walk hash dimensions rows (maxHeight dimensions) index
             (hash (rowBytes dimensions rows (maxHeight dimensions))) proof).inputs⟩⟩ := by
  simp only [replay, List.isEmpty_eq_false_iff.mpr nonempty, fits, Bool.not_true, Bool.or_self,
    count, bne_self_eq_false, bounded, decide_true, Bool.false_eq_true, ↓reduceIte]

theorem replay_calls {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {rows : List (List G)} {proof : List Digest} {result : Replay}
    (success : replay hash dimensions capHeight index rows proof = some result) :
    result.hashing.inputs.length ≤ 1 + 3 * proof.length := by
  obtain ⟨_, _, _, _, rfl⟩ := replay_success success
  have := walk_calls hash dimensions rows (maxHeight dimensions) index
    (hash (rowBytes dimensions rows (maxHeight dimensions))) proof
  simp only [List.length_cons]
  omega

theorem replay_position {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {rows : List (List G)} {proof : List Digest} {result : Replay}
    (success : replay hash dimensions capHeight index rows proof = some result) :
    result.logHeight = min capHeight (maxHeight dimensions) ∧
      result.index = index / 2^(maxHeight dimensions - capHeight) := by
  obtain ⟨_, _, count, _, rfl⟩ := replay_success success
  simp only [count]
  constructor
  · omega
  · trivial

theorem replay_index_bound {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {rows : List (List G)} {proof : List Digest} {result : Replay}
    (success : replay hash dimensions capHeight index rows proof = some result) :
    result.index < 2^result.logHeight := by
  obtain ⟨_, _, count, bounded, rfl⟩ := replay_success success
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
  have lengthBound : proof.length ≤ maxHeight dimensions := by omega
  simpa only [← Nat.pow_add, Nat.sub_add_cancel lengthBound] using bounded

theorem hasHeight_iff {dimensions : List Dimensions} {height : Nat} :
    hasHeight dimensions height = true ↔ ∃ dimension ∈ dimensions, dimension.logHeight = height := by
  simp only [hasHeight, List.any_eq_true, beq_iff_eq]

theorem height_le_max {dimensions : List Dimensions} {dimension : Dimensions}
    (member : dimension ∈ dimensions) : dimension.logHeight ≤ maxHeight dimensions :=
  MerkleCap.degree_le_max (List.mem_map.mpr ⟨dimension, member, rfl⟩)

theorem covered_iff {dimensions : List Dimensions} {capHeight : Nat} :
    covered dimensions capHeight = true ↔
      ∀ dimension ∈ dimensions, min capHeight (maxHeight dimensions) ≤ dimension.logHeight := by
  simp only [covered, MerkleCap.coverage_iff, Nat.sub_zero, List.forall_mem_map, maxHeight]

/-- Coverage makes every matrix row recoverable from the authenticated
height groups. Both paths may supply different sibling digests. -/
theorem replay_binding {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {leftRows rightRows : List (List G)} {leftProof rightProof : List Digest} {left right : Replay}
    (coverage : covered dimensions capHeight = true)
    (ls : replay hash dimensions capHeight index leftRows leftProof = some left)
    (rs : replay hash dimensions capHeight index rightRows rightProof = some right)
    (free : ¬CollisionOn hash (left.hashing.inputs ++ right.hashing.inputs))
    (same : left.hashing.digest = right.hashing.digest) : leftRows = rightRows := by
  obtain ⟨_, lf, lc, _, rfl⟩ := replay_success ls
  obtain ⟨_, rf, rc, _, rfl⟩ := replay_success rs
  have freeWalk : ¬CollisionOn hash
      ((walk hash dimensions leftRows (maxHeight dimensions) index
          (hash (rowBytes dimensions leftRows (maxHeight dimensions))) leftProof).inputs ++
       (walk hash dimensions rightRows (maxHeight dimensions) index
          (hash (rowBytes dimensions rightRows (maxHeight dimensions))) rightProof).inputs) := by
    intro collision
    apply free (collision.mono ?_)
    intro input member
    simp only [List.mem_append] at member
    simp only [List.mem_append, List.mem_cons]
    exact member.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))
  have path := walk_binding (lc.trans rc.symm) freeWalk same
  have leaf := equal_of_no_collision free
    (by simp) (by simp) path.1
  apply rowBytes_injective lf rf
  intro height
  by_cases present : hasHeight dimensions height = true
  · obtain ⟨dimension, member, atHeight⟩ := hasHeight_iff.mp present
    have upper := height_le_max member
    have lower := covered_iff.mp coverage dimension member
    rw [atHeight] at upper lower
    by_cases atTop : height = maxHeight dimensions
    · simpa only [atTop] using leaf
    · have depthBound : maxHeight dimensions - height - 1 < leftProof.length := by omega
      have heightEq : maxHeight dimensions - (maxHeight dimensions - height - 1 + 1) = height := by omega
      have inject : hasHeight dimensions (maxHeight dimensions - (maxHeight dimensions - height - 1 + 1)) = true := by
        simpa only [heightEq] using present
      simpa only [heightEq] using path.2 _ depthBound inject
  · have absent : hasHeight dimensions height = false := by simpa using present
    simp only [rowBytes, rowsAt_absent absent]

theorem verify_success {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {cap : List Digest} {rows : List (List G)} {proof : List Digest}
    (accepted : verify hash dimensions capHeight index cap rows proof = true) :
    ∃ result, replay hash dimensions capHeight index rows proof = some result ∧
      cap[result.index]? = some result.hashing.digest := by
  cases running : replay hash dimensions capHeight index rows proof with
  | none => simp [verify, running] at accepted
  | some result =>
    exact ⟨result, rfl, by simpa only [verify, running, accepts, beq_iff_eq] using accepted⟩

/-- Two different accepted rows at the same public dimensions, cap and
index exhibit a collision within at most two path transcripts. -/
theorem verify_collision {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {cap : List Digest} {leftRows rightRows : List (List G)} {leftProof rightProof : List Digest}
    (coverage : covered dimensions capHeight = true)
    (la : verify hash dimensions capHeight index cap leftRows leftProof = true)
    (ra : verify hash dimensions capHeight index cap rightRows rightProof = true)
    (different : leftRows ≠ rightRows) :
    ∃ left right, replay hash dimensions capHeight index leftRows leftProof = some left ∧
      replay hash dimensions capHeight index rightRows rightProof = some right ∧
      CollisionOn hash (left.hashing.inputs ++ right.hashing.inputs) ∧
      (left.hashing.inputs ++ right.hashing.inputs).length ≤ 2 + 6 * (maxHeight dimensions - capHeight) := by
  classical
  obtain ⟨left, ls, lc⟩ := verify_success la
  obtain ⟨right, rs, rc⟩ := verify_success ra
  have li := (replay_position ls).2
  have ri := (replay_position rs).2
  have sameIndex := li.trans ri.symm
  rw [sameIndex, rc] at lc
  have same := (Option.some.inj lc).symm
  have collision : CollisionOn hash (left.hashing.inputs ++ right.hashing.inputs) := by
    by_cases collides : CollisionOn hash (left.hashing.inputs ++ right.hashing.inputs)
    · exact collides
    · exact False.elim (different (replay_binding coverage ls rs collides same))
  refine ⟨left, right, ls, rs, collision, ?_⟩
  have leftBound := replay_calls ls
  have rightBound := replay_calls rs
  have leftCount := (replay_success ls).2.2.1
  have rightCount := (replay_success rs).2.2.1
  simp only [List.length_append]
  omega

theorem verifyCovered_collision {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {cap : List Digest} {leftRows rightRows : List (List G)} {leftProof rightProof : List Digest}
    (la : verifyCovered hash dimensions capHeight index cap leftRows leftProof = true)
    (ra : verifyCovered hash dimensions capHeight index cap rightRows rightProof = true)
    (different : leftRows ≠ rightRows) :
    ∃ left right, replay hash dimensions capHeight index leftRows leftProof = some left ∧
      replay hash dimensions capHeight index rightRows rightProof = some right ∧
      CollisionOn hash (left.hashing.inputs ++ right.hashing.inputs) ∧
      (left.hashing.inputs ++ right.hashing.inputs).length ≤ 2 + 6 * (maxHeight dimensions - capHeight) := by
  simp only [verifyCovered, Bool.and_eq_true] at la ra
  exact verify_collision la.1 la.2 ra.2 different

theorem blake3_collision {dimensions : List Dimensions} {capHeight index : Nat}
    {cap : List Digest} {leftRows rightRows : List (List G)} {leftProof rightProof : List Digest}
    (la : verifyCovered Blake3.digest dimensions capHeight index cap leftRows leftProof = true)
    (ra : verifyCovered Blake3.digest dimensions capHeight index cap rightRows rightProof = true)
    (different : leftRows ≠ rightRows) :
    ∃ left right, replay Blake3.digest dimensions capHeight index leftRows leftProof = some left ∧
      replay Blake3.digest dimensions capHeight index rightRows rightProof = some right ∧
      CollisionOn Blake3.digest (left.hashing.inputs ++ right.hashing.inputs) ∧
      (left.hashing.inputs ++ right.hashing.inputs).length ≤ 2 + 6 * (maxHeight dimensions - capHeight) :=
  verifyCovered_collision la ra different

theorem branchBytes_length (index : Nat) (current sibling : Digest) :
    (branchBytes index current sibling).length = 64 := by
  unfold branchBytes
  split <;> exact pairBytes_length _ _

theorem rowsAt_fields_le (dimensions : List Dimensions) (rows : List (List G)) (height : Nat) :
    (rowsAt dimensions rows height).flatten.length ≤ rows.flatten.length := by
  induction dimensions generalizing rows with
  | nil => simp [rowsAt]
  | cons dimension dimensions ih =>
    cases rows with
    | nil => simp [rowsAt]
    | cons row rows =>
      have rest := ih rows
      unfold rowsAt
      split <;> simp only [List.flatten_cons, List.length_append] <;> omega

theorem rowBytes_length_le (dimensions : List Dimensions) (rows : List (List G)) (height : Nat) :
    (rowBytes dimensions rows height).length ≤ 8 * rows.flatten.length := by
  rw [rowBytes, Transcript.fieldsBytes_length]
  exact Nat.mul_le_mul_left 8 (rowsAt_fields_le dimensions rows height)

theorem step_input_length {hash : Hash} {dimensions : List Dimensions} {rows : List (List G)}
    {height index : Nat} {current sibling : Digest} {input : List UInt8}
    (member : input ∈ (step hash dimensions rows height index current sibling).inputs) :
    input.length ≤ max 64 (8 * rows.flatten.length) := by
  unfold step at member
  split at member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rw [branchBytes_length]; exact Nat.le_max_left _ _
    · exact Nat.le_trans (rowBytes_length_le dimensions rows height) (Nat.le_max_right _ _)
    · rw [pairBytes_length]; exact Nat.le_max_left _ _
  · simp only [List.mem_singleton] at member
    subst input
    rw [branchBytes_length]
    exact Nat.le_max_left _ _

theorem walk_input_length {hash : Hash} {dimensions : List Dimensions} {rows : List (List G)}
    {height index : Nat} {current : Digest} {proof : List Digest} {input : List UInt8}
    (member : input ∈ (walk hash dimensions rows height index current proof).inputs) :
    input.length ≤ max 64 (8 * rows.flatten.length) := by
  induction proof generalizing height index current with
  | nil => cases member
  | cons sibling proof ih =>
    simp only [walk, List.mem_append] at member
    exact member.elim step_input_length ih

theorem replay_input_length {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {rows : List (List G)} {proof : List Digest} {result : Replay}
    (success : replay hash dimensions capHeight index rows proof = some result)
    {input : List UInt8} (member : input ∈ result.hashing.inputs) :
    input.length ≤ max 64 (8 * rows.flatten.length) := by
  obtain ⟨_, _, _, _, rfl⟩ := replay_success success
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact Nat.le_trans (rowBytes_length_le dimensions rows (maxHeight dimensions)) (Nat.le_max_right _ _)
  · exact walk_input_length member

theorem replay_native_input {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {rows : List (List G)} {proof : List Digest} {result : Replay}
    (success : replay hash dimensions capHeight index rows proof = some result)
    (bounded : rows.flatten.length < 2^61) {input : List UInt8} (member : input ∈ result.hashing.inputs) :
    Blake3.NativeInput input := by
  have bound := replay_input_length success member
  unfold Blake3.NativeInput
  omega

end Aiur.NativeAIR.Merkle
