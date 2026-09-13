/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Challenger
import Ix.Aiur.Proofs.KeyCodec

namespace Aiur.NativeAIR.Challenger

/-- Pending bytes are a suffix of the reversed digest still held in the
input buffer. Observations may leave any input and no pending output. -/
def State.Valid (state : State) : Prop :=
  state.pending = [] ∨ ∃ consumed, state.input.length = 32 ∧ state.pending = state.input.reverse.drop consumed

theorem initial_valid (seed : List UInt8) : (initial seed).Valid := Or.inl rfl

theorem State.Valid.bound {state : State} (valid : state.Valid) : state.pending.length ≤ 32 := by
  rcases valid with empty | ⟨consumed, length, pending⟩
  · simp only [empty, List.length_nil]; omega
  · simp only [pending, List.length_drop, List.length_reverse, length]; omega

theorem observeBytes_nil (state : State) : observeBytes state [] = state := rfl

theorem observeBytes_append (state : State) (left right : List UInt8) :
    observeBytes state (left ++ right) = observeBytes (observeBytes state left) right := by
  cases left <;> cases right <;> simp [observeBytes, List.append_assoc]

theorem observeBytes_value (state : State) (bytes : List UInt8) :
    observeBytes state bytes = if bytes.isEmpty then state else ⟨state.input ++ bytes, []⟩ := rfl

theorem observeBytes_fold (state : State) (bytes : List UInt8) :
    observeBytes state bytes = bytes.foldl observeByte state := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    rw [List.foldl_cons, ← ih]
    cases bytes <;> simp [observeBytes, observeByte, List.append_assoc]

theorem observeBytes_valid {state : State} (valid : state.Valid) (bytes : List UInt8) :
    (observeBytes state bytes).Valid := by
  rw [observeBytes_value]
  split
  · exact valid
  · exact Or.inl rfl

theorem observeField_value (state : State) (value : G) :
    observeField state value = ⟨state.input ++ ProofCodec.encodeField value, []⟩ := by
  rw [observeField, observeBytes_value]
  rfl

theorem observeField_valid {state : State} (valid : state.Valid) (value : G) :
    (observeField state value).Valid := observeBytes_valid valid _

theorem observeExtension_bytes (state : State) (value : ProofCodec.Extension) :
    observeExtension state value = observeBytes state (ProofCodec.encodeExtension value) := by
  rw [observeExtension, ProofCodec.encodeExtension, observeBytes_append]
  rfl

theorem observeExtension_valid {state : State} (valid : state.Valid) (value : ProofCodec.Extension) :
    (observeExtension state value).Valid := observeField_valid (observeField_valid valid value.c0) value.c1

theorem observeExtensions_valid {state : State} (valid : state.Valid) (values : List ProofCodec.Extension) :
    (values.foldl observeExtension state).Valid := by
  induction values generalizing state with
  | nil => exact valid
  | cons value values ih => exact ih (observeExtension_valid valid value)

theorem observeCap_empty (state : State) : observeCap state [] = state := rfl

theorem observeCap_valid {state : State} (valid : state.Valid) (cap : KeyCodec.MerkleCap) :
    (observeCap state cap).Valid := observeBytes_valid valid _

theorem sampleByte_buffered (hash : Hash32) (input : List UInt8) (byte : UInt8) (rest : List UInt8) :
    sampleByte hash ⟨input, byte :: rest⟩ = (byte, ⟨input, rest⟩) := rfl

theorem sampleByte_refill (hash : Hash32) (input : List UInt8) :
    sampleByte hash ⟨input, []⟩ =
      (hash input 31, ⟨List.ofFn (hash input), (List.ofFn (hash input)).reverse.drop 1⟩) := rfl

theorem sampleByte_valid (hash : Hash32) {state : State} (valid : state.Valid) :
    (sampleByte hash state).2.Valid := by
  cases pending : state.pending with
  | nil =>
    simp only [sampleByte, pending]
    exact Or.inr ⟨1, List.length_ofFn, rfl⟩
  | cons byte rest =>
    rcases valid with empty | ⟨consumed, length, remaining⟩
    · rw [empty] at pending; cases pending
    · change (sampleByte hash state).2.pending = [] ∨ _
      right
      refine ⟨consumed + 1, ?_, ?_⟩
      · simpa only [sampleByte, pending] using length
      · simp only [sampleByte, pending]
        rw [← List.tail_drop, ← remaining, pending]
        rfl

theorem digest_reverse (digest : Fin 32 → UInt8) :
    (List.ofFn digest).reverse = digest 31 :: (List.ofFn digest).reverse.drop 1 := by
  conv => lhs; rw [List.ofFn_succ_last]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [List.ofFn_succ_last]
  simp

theorem sampleByte_pending_bound (hash : Hash32) (state : State) (bounded : state.pending.length ≤ 32) :
    (sampleByte hash state).2.pending.length ≤ 32 := by
  cases pending : state.pending with
  | nil => simp [sampleByte, pending]
  | cons byte rest => simp only [sampleByte, pending]; simp_all; omega

theorem sampleBytes_length (hash : Hash32) (count : Nat) (state : State) :
    (sampleBytes hash count state).1.length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp only [sampleBytes, List.length_cons, ih]

theorem sampleBytes_pending_bound (hash : Hash32) (count : Nat) (state : State)
    (bounded : state.pending.length ≤ 32) : (sampleBytes hash count state).2.pending.length ≤ 32 := by
  induction count generalizing state with
  | zero => exact bounded
  | succ count ih => exact ih _ (sampleByte_pending_bound hash state bounded)

theorem sampleBytes_valid (hash : Hash32) (count : Nat) {state : State} (valid : state.Valid) :
    (sampleBytes hash count state).2.Valid := by
  induction count generalizing state with
  | zero => exact valid
  | succ count ih => exact ih (sampleByte_valid hash valid)

theorem sampleBytes_buffered (hash : Hash32) (input bytes rest : List UInt8) :
    sampleBytes hash bytes.length ⟨input, bytes ++ rest⟩ = (bytes, ⟨input, rest⟩) := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih => simp only [List.length_cons, List.cons_append, sampleBytes, sampleByte, ih]

theorem sampleBytes_refill (hash : Hash32) (input : List UInt8) :
    sampleBytes hash 32 ⟨input, []⟩ =
      ((List.ofFn (hash input)).reverse, ⟨List.ofFn (hash input), []⟩) := by
  have tail := sampleBytes_buffered hash (List.ofFn (hash input))
    ((List.ofFn (hash input)).reverse.drop 1) []
  simp only [List.length_drop, List.length_reverse, List.length_ofFn, List.append_nil] at tail
  rw [sampleBytes]
  simp only [sampleByte]
  rw [tail, ← digest_reverse]

theorem littleEndian_bound (bytes : List UInt8) : littleEndian bytes < 256^bytes.length := by
  induction bytes with
  | nil => decide
  | cons byte bytes ih =>
    have bounded := byte.toNat_lt
    simp only [littleEndian, List.foldr_cons, List.length_cons, Nat.pow_succ] at *
    omega

theorem littleEndian_encode (count value : Nat) (bounded : value < 256^count) :
    littleEndian (KeyCodec.encodeNat count value) = value := by
  induction count generalizing value with
  | zero =>
    have zero : value = 0 := by simpa using bounded
    subst value
    rfl
  | succ count ih =>
    have small : value / 256 < 256^count := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr
      simpa only [Nat.pow_succ] using bounded
    simp only [KeyCodec.encodeNat, littleEndian, List.foldr_cons]
    change value.toUInt8.toNat + 256 * littleEndian (KeyCodec.encodeNat count (value / 256)) = value
    rw [ih _ small]
    exact Nat.mod_add_div _ _

theorem littleEndian_reads (bytes : List UInt8) :
    KeyCodec.Reads (KeyCodec.readNat bytes.length) bytes (littleEndian bytes) := by
  induction bytes with
  | nil => exact KeyCodec.Reads.pure 0
  | cons byte bytes ih =>
    exact KeyCodec.Reads.byte (ih.result (fun value => byte.toNat + 256 * value))

theorem sampleWord_bound (hash : Hash32) (state : State) : (sampleWord hash state).1 < 2^64 := by
  have bound := littleEndian_bound (sampleBytes hash 8 state).1
  rw [sampleBytes_length] at bound
  exact bound

theorem sampleWord_full_mask (hash : Hash32) (state : State) :
    (sampleWord hash state).1 &&& (2^64 - 1) = (sampleWord hash state).1 :=
  Nat.and_two_pow_sub_one_of_lt_two_pow (sampleWord_bound hash state)

theorem sampleWord_reads (hash : Hash32) (state : State) :
    KeyCodec.Reads (KeyCodec.readNat 8) (sampleBytes hash 8 state).1 (sampleWord hash state).1 := by
  have read := littleEndian_reads (sampleBytes hash 8 state).1
  rw [sampleBytes_length] at read
  exact read

/-- A finite native execution: each rejected word advances to its returned
state, and the first canonical word is the returned field representative. -/
inductive FieldSample (hash : Hash32) : State → Nat → G → State → Prop where
  | accept {state : State} (canonical : (sampleWord hash state).1 < gSize.toNat) :
      FieldSample hash state 1 (G.ofNat (sampleWord hash state).1) (sampleWord hash state).2
  | reject {state final : State} {count : Nat} {value : G}
      (noncanonical : ¬(sampleWord hash state).1 < gSize.toNat)
      (rest : FieldSample hash (sampleWord hash state).2 count value final) :
      FieldSample hash state (count + 1) value final

theorem FieldSample.positive {hash : Hash32} {state final : State} {count : Nat} {value : G}
    (trace : FieldSample hash state count value final) : 0 < count := by
  cases trace <;> omega

theorem sampleField_success {hash : Hash32} {fuel : Nat} {state final : State} {value : G}
    (accepted : sampleField hash fuel state = some (value, final)) :
    ∃ count, count ≤ fuel ∧ FieldSample hash state count value final := by
  induction fuel generalizing state with
  | zero => cases accepted
  | succ fuel ih =>
    change (if (sampleWord hash state).1 < gSize.toNat then
      some (G.ofNat (sampleWord hash state).1, (sampleWord hash state).2)
      else sampleField hash fuel (sampleWord hash state).2) = some (value, final) at accepted
    split at accepted
    · obtain ⟨sameValue, sameState⟩ := Prod.mk.inj (Option.some.inj accepted)
      rw [← sameValue, ← sameState]
      exact ⟨1, by omega, .accept (by assumption)⟩
    · obtain ⟨count, bound, trace⟩ := ih accepted
      exact ⟨count + 1, by omega, .reject (by assumption) trace⟩

theorem FieldSample.complete {hash : Hash32} {state final : State} {count : Nat} {value : G}
    (trace : FieldSample hash state count value final) (fuel : Nat) (bound : count ≤ fuel) :
    sampleField hash fuel state = some (value, final) := by
  induction trace generalizing fuel with
  | accept canonical =>
    cases fuel with
    | zero => omega
    | succ fuel => simp only [sampleField, canonical, ↓reduceIte]
  | reject noncanonical trace ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [sampleField, noncanonical, ↓reduceIte]
      exact ih fuel (by omega)

theorem sampleField_iff (hash : Hash32) (fuel : Nat) (state final : State) (value : G) :
    sampleField hash fuel state = some (value, final) ↔
      ∃ count, count ≤ fuel ∧ FieldSample hash state count value final :=
  ⟨sampleField_success, fun ⟨_, bound, trace⟩ => trace.complete fuel bound⟩

theorem sampleField_mono {hash : Hash32} {fuel more : Nat} {state final : State} {value : G}
    (accepted : sampleField hash fuel state = some (value, final)) (bound : fuel ≤ more) :
    sampleField hash more state = some (value, final) := by
  obtain ⟨count, small, trace⟩ := sampleField_success accepted
  exact trace.complete more (Nat.le_trans small bound)

theorem sampleField_unique {hash : Hash32} {fuel other : Nat} {state left right : State} {a b : G}
    (first : sampleField hash fuel state = some (a, left))
    (second : sampleField hash other state = some (b, right)) : a = b ∧ left = right := by
  have one := sampleField_mono first (Nat.le_max_left fuel other)
  have two := sampleField_mono second (Nat.le_max_right fuel other)
  exact Prod.mk.inj (Option.some.inj (one.symm.trans two))

theorem FieldSample.valid {hash : Hash32} {state final : State} {count : Nat} {value : G}
    (trace : FieldSample hash state count value final) (valid : state.Valid) : final.Valid := by
  induction trace with
  | accept _ => exact sampleBytes_valid hash 8 valid
  | @reject before _ _ _ _ _ ih =>
    apply ih
    change (sampleBytes hash 8 before).2.Valid
    exact sampleBytes_valid hash 8 valid

theorem sampleField_valid {hash : Hash32} {fuel : Nat} {state final : State} {value : G}
    (accepted : sampleField hash fuel state = some (value, final)) (valid : state.Valid) : final.Valid := by
  obtain ⟨_, _, trace⟩ := sampleField_success accepted
  exact trace.valid valid

theorem sampleField_canonical {hash : Hash32} {fuel : Nat} {state final : State} {value : G}
    (accepted : sampleField hash fuel state = some (value, final)) :
    ∃ before, sampleWord hash before = (value.n, final) ∧ value.n < gSize.toNat := by
  obtain ⟨_, _, trace⟩ := sampleField_success accepted
  clear accepted
  rename_i count bound
  clear bound
  induction trace with
  | @accept before canonical =>
    refine ⟨before, ?_, ?_⟩
    · simp only [G.n_ofNat, Nat.mod_eq_of_lt canonical]
    · simpa only [G.n_ofNat, Nat.mod_eq_of_lt canonical] using canonical
  | reject _ _ ih => exact ih

theorem sampleExtension_success {hash : Hash32} {fuel : Nat} {state final : State}
    {value : ProofCodec.Extension} (accepted : sampleExtension hash fuel state = some (value, final)) :
    ∃ next, sampleField hash fuel state = some (value.c0, next) ∧
      sampleField hash fuel next = some (value.c1, final) := by
  simp only [sampleExtension, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.exists, Prod.mk.injEq] at accepted
  obtain ⟨c0, next, first, c1, final', second, ⟨rfl, rfl⟩, rfl⟩ := accepted
  exact ⟨next, first, second⟩

theorem sampleExtension_mono {hash : Hash32} {fuel more : Nat} {state final : State}
    {value : ProofCodec.Extension} (accepted : sampleExtension hash fuel state = some (value, final))
    (bound : fuel ≤ more) : sampleExtension hash more state = some (value, final) := by
  obtain ⟨next, first, second⟩ := sampleExtension_success accepted
  simp only [sampleExtension, sampleField_mono first bound, sampleField_mono second bound,
    bind, pure, Option.bind_some]

theorem sampleExtension_valid {hash : Hash32} {fuel : Nat} {state final : State}
    {value : ProofCodec.Extension} (accepted : sampleExtension hash fuel state = some (value, final))
    (valid : state.Valid) : final.Valid := by
  obtain ⟨next, first, second⟩ := sampleExtension_success accepted
  exact sampleField_valid second (sampleField_valid first valid)

theorem sampleBits_success {hash : Hash32} {bits value : Nat} {state final : State}
    (accepted : sampleBits hash bits state = some (value, final)) :
    bits < 64 ∧ 2^bits < gSize.toNat ∧ value = (sampleWord hash state).1 % 2^bits ∧
      final = (sampleWord hash state).2 ∧ value < 2^bits := by
  change (if bits < 64 ∧ 2^bits < gSize.toNat then
    some ((sampleWord hash state).1 % 2^bits, (sampleWord hash state).2)
    else none) = some (value, final) at accepted
  split at accepted
  · rename_i valid
    obtain ⟨sameValue, sameState⟩ := Prod.mk.inj (Option.some.inj accepted)
    refine ⟨valid.1, valid.2, sameValue.symm, sameState.symm, ?_⟩
    rw [← sameValue]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · cases accepted

theorem sampleBits_zero (hash : Hash32) (state : State) :
    sampleBits hash 0 state = some (0, (sampleWord hash state).2) := by
  have bound : 1 < gSize.toNat := by decide
  change (if 0 < 64 ∧ 2^0 < gSize.toNat then
    some ((sampleWord hash state).1 % 2^0, (sampleWord hash state).2) else none) = _
  simp only [Nat.pow_zero, bound, Nat.mod_one, Nat.zero_lt_succ, and_self, ↓reduceIte]

theorem sampleBits_mask {hash : Hash32} {bits value : Nat} {state final : State}
    (accepted : sampleBits hash bits state = some (value, final)) :
    value = (sampleWord hash state).1 &&& (2^bits - 1) := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact (sampleBits_success accepted).2.2.1

theorem sampleBits_valid {hash : Hash32} {bits value : Nat} {state final : State}
    (accepted : sampleBits hash bits state = some (value, final)) (valid : state.Valid) : final.Valid := by
  rw [(sampleBits_success accepted).2.2.2.1]
  exact sampleBytes_valid hash 8 valid

theorem checkWitness_zero (hash : Hash32) (witness : G) (state : State) :
    checkWitness hash 0 witness state = some (true, state) := rfl

theorem checkWitness_positive (hash : Hash32) {bits : Nat} (positive : bits ≠ 0)
    (witness : G) (state : State) : checkWitness hash bits witness state = do
      let (value, next) ← sampleBits hash bits (observeField state witness)
      return (value == 0, next) := by
  simp only [checkWitness, positive, ↓reduceIte]

theorem checkWitness_true_iff (hash : Hash32) (bits : Nat) (witness : G) (state final : State) :
    checkWitness hash bits witness state = some (true, final) ↔
      (bits = 0 ∧ final = state) ∨
        (bits ≠ 0 ∧ sampleBits hash bits (observeField state witness) = some (0, final)) := by
  by_cases zero : bits = 0
  · subst bits
    simp only [checkWitness_zero, Option.some.injEq, Prod.mk.injEq, true_and,
      ne_eq, not_true_eq_false, false_and, or_false]
    exact eq_comm
  · rw [checkWitness_positive hash zero witness state]
    simp only [bind, pure, Option.bind_eq_some_iff, Prod.exists, Option.some.injEq, Prod.mk.injEq,
      beq_iff_eq, ne_eq, zero, false_and, not_false_eq_true, true_and, false_or]
    constructor
    · rintro ⟨value, next, read, rfl, rfl⟩; exact read
    · intro read; exact ⟨0, final, read, rfl, rfl⟩

theorem checkWitness_valid {hash : Hash32} {bits : Nat} {witness : G} {state final : State}
    {accepted : Bool} (read : checkWitness hash bits witness state = some (accepted, final))
    (valid : state.Valid) : final.Valid := by
  by_cases zero : bits = 0
  · subst bits
    obtain ⟨_, same⟩ := Prod.mk.inj (Option.some.inj read)
    exact same ▸ valid
  · rw [checkWitness_positive hash zero witness state] at read
    simp only [bind, pure, Option.bind_eq_some_iff, Prod.exists, Option.some.injEq, Prod.mk.injEq] at read
    obtain ⟨value, next, sampled, _, rfl⟩ := read
    exact sampleBits_valid sampled (observeField_valid valid witness)

end Aiur.NativeAIR.Challenger
