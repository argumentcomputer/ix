import Ix.Cert.Compression.Foreign
import Blake3.Pure

/-! # Outer-IR Semantics, Canonical `"ix/outer-ir/v1"` Digest Audit, and Gnark Soundness (1C-iv)

Formalizes the exported Outer-IR DAG verified inside the final Gnark PLONK / Groth16
circuit (`crates/proof-compression/src/pipeline/wrap/outer/final_export/ir.rs` and
`tools/gnark/profile.go`):

1. **Exact AST (`OuterInputKind`, `OuterInstruction`, `OuterProgram`):**
   6 instruction kinds (`constant`, `input`, `add`, `sub`, `mul`, `inverse`) over `BN254Fr`,
   plus output index tables (`assertions`, `coefficients`, `witnesses`).
2. **Canonical 3-Way Rust/Go/Lean Digest (`OuterProgram.encode`, `OuterProgram.digest`):**
   Exact `"ix/outer-ir/v1"` BLAKE3 encoding using `Blake3.Pure.digest`, with kernel-verified
   golden-vector theorems matching the Rust and Go test suites byte-for-byte:
   - Empty program: `02d95030e924d62b65dcb11734967f540cddd90337d58184d90f02197df5a799`
   - 10-node all-ops vector: `3841d46e6b5730d0f1d9faba16072a2c3caed66c64f8e32ee5ebdb69a57a2b28`
3. **Executable & Mathematical DAG Evaluation (`evalNodes?`, `OuterProgram.Satisfied`):**
   Enforces strict topological referencing (`a < i`, `b < i`), nonzero inverse operands
   (`val ≠ 0`), and `val[id] = 0` for every assertion `id ∈ prog.assertions`, yielding the
   evaluated MSM scalar coefficients and witness openings passed to the final pairing check.
4. **Gnark Soundness Composition (`gnark_outer_relation_sound`):**
   An accepting Gnark proof against a verifying key whose `programDigest` matches
   `prog.digest` (up to BLAKE3 collision) yields `prog.Satisfied` on the public statement
   and opening witness.

Zero `sorry`, zero `native_decide`, standard axioms only.
-/

namespace Ix.Cert.Compression.OuterRelation

open Ix.Cert.Compression.Foreign

/-! ## 1. Outer-IR AST (`ir.rs:15-47`) -/

/-- Input channel kind in `OuterIR` (`ir.rs:86-90`, `tools/gnark/profile.go`). -/
inductive OuterInputKind where
  | challenge  -- tag 0
  | value      -- tag 1
  | publicIn   -- tag 2
  deriving DecidableEq, Repr, Inhabited

def OuterInputKind.tag : OuterInputKind → UInt8
  | .challenge => 0
  | .value     => 1
  | .publicIn  => 2

/-- Single SSA instruction in `OuterIR` (`ir.rs:15-39`). -/
inductive OuterInstruction where
  | constant (value : BN254Fr)
  | input (kind : OuterInputKind) (index : Nat)
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | inverse (a : Nat)
  deriving DecidableEq, Repr

/-- Complete exported `OuterIR` scalar verifier program (`ir.rs:42-47`). -/
structure OuterProgram where
  nodes : List OuterInstruction
  assertions : List Nat
  coefficients : List Nat
  witnesses : List Nat
  deriving DecidableEq, Repr

/-! ## 2. Canonical `"ix/outer-ir/v1"` Binary Encoding & BLAKE3 Digest -/

/-- 14-byte ASCII domain separator `"ix/outer-ir/v1"` (no NUL). -/
def outerIrDomain : List UInt8 :=
  [ 0x69, 0x78, 0x2f, 0x6f, 0x75, 0x74, 0x65, 0x72,
    0x2d, 0x69, 0x72, 0x2f, 0x76, 0x31 ]

/-- Little-endian 4-byte encoding of a `Nat` (`u32le`). -/
def encodeU32LE (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n % 256),
    UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat ((n / 65536) % 256),
    UInt8.ofNat ((n / 16777216) % 256) ]

/-- Canonical 32-byte big-endian encoding of a `BN254Fr` scalar (`0 ≤ val < bn254FrModulus`). -/
def encodeScalarBE32 (x : BN254Fr) : List UInt8 :=
  let v := x.val
  (List.range 32).map fun i =>
    UInt8.ofNat ((v / 256 ^ (31 - i)) % 256)

def encodeU32List (xs : List Nat) : List UInt8 :=
  encodeU32LE xs.length ++ xs.flatMap encodeU32LE

def OuterInstruction.encode : OuterInstruction → List UInt8
  | .constant v     => 0 :: encodeScalarBE32 v
  | .input k idx    => 1 :: k.tag :: encodeU32LE idx
  | .add a b        => 2 :: (encodeU32LE a ++ encodeU32LE b)
  | .sub a b        => 3 :: (encodeU32LE a ++ encodeU32LE b)
  | .mul a b        => 4 :: (encodeU32LE a ++ encodeU32LE b)
  | .inverse a      => 5 :: encodeU32LE a

/-- Canonical deterministic encoding shared across Rust (`ir.rs:64-120`),
Go (`tools/gnark/profile.go`), and Lean (`OuterProgram.encode`). -/
def OuterProgram.encode (p : OuterProgram) : List UInt8 :=
  outerIrDomain ++
  encodeU32LE p.nodes.length ++
  p.nodes.flatMap OuterInstruction.encode ++
  encodeU32List p.assertions ++
  encodeU32List p.coefficients ++
  encodeU32List p.witnesses

/-- Canonical 32-byte BLAKE3 digest of `p.encode`. -/
def OuterProgram.digest (p : OuterProgram) : List UInt8 :=
  (Blake3.Pure.digest p.encode).toList

/-! ### 3-Way Cross-Language Golden-Vector Parity Proofs (Rust ↔ Go ↔ Lean) -/

set_option maxRecDepth 20000 in
/-- Empty `OuterProgram` matches the shared Rust & Go golden digest
`0x02d95030e924d62b65dcb11734967f540cddd90337d58184d90f02197df5a799`. -/
theorem empty_program_digest_matches_rust_go :
    ({ nodes := [], assertions := [], coefficients := [], witnesses := [] } : OuterProgram).digest =
      [ 0x02, 0xd9, 0x50, 0x30, 0xe9, 0x24, 0xd6, 0x2b,
        0x65, 0xdc, 0xb1, 0x17, 0x34, 0x96, 0x7f, 0x54,
        0x0c, 0xdd, 0xd9, 0x03, 0x37, 0xd5, 0x81, 0x84,
        0xd9, 0x0f, 0x02, 0x19, 0x7d, 0xf5, 0xa7, 0x99 ] := by
  unfold OuterProgram.digest Blake3.Pure.digest
  rw [Blake3.Pure.subtree]
  simp only [show ({ nodes := [], assertions := [], coefficients := [], witnesses := [] } : OuterProgram).encode.length ≤ 1024 by decide, ↓reduceDIte]
  unfold Blake3.Pure.chunkOutput
  rw [Blake3.Pure.chunkLoop]
  simp only [show ({ nodes := [], assertions := [], coefficients := [], witnesses := [] } : OuterProgram).encode.length ≤ 64 by decide, ↓reduceDIte]
  decide

/-- 10-node all-ops golden program shared verbatim with Rust (`ir.rs`) and Go (`program_digest_test.go`). -/
def allOpsGoldenProgram : OuterProgram where
  nodes :=
    [ .constant 0,
      .constant 94,
      .constant ((bn254FrModulus - 1 : Nat) : BN254Fr),
      .input .challenge 5,
      .input .value 258,
      .input .publicIn 22,
      .add 1 3,
      .sub 6 4,
      .mul 7 2,
      .inverse 8 ]
  assertions := [9, 0]
  coefficients := [6, 7, 8]
  witnesses := [5]

set_option maxRecDepth 20000 in
theorem allOps_golden_encode_length : allOpsGoldenProgram.encode.length = 203 := by
  decide

set_option maxRecDepth 80000 in
set_option maxHeartbeats 1600000 in
/-- 10-node all-ops `OuterProgram` matches the shared Rust & Go golden digest
`0x3841d46e6b5730d0f1d9faba16072a2c3caed66c64f8e32ee5ebdb69a57a2b28`. -/
theorem allOps_golden_digest_matches_rust_go :
    allOpsGoldenProgram.digest =
      [ 0x38, 0x41, 0xd4, 0x6e, 0x6b, 0x57, 0x30, 0xd0,
        0xf1, 0xd9, 0xfa, 0xba, 0x16, 0x07, 0x2a, 0x2c,
        0x3c, 0xae, 0xd6, 0x6c, 0x64, 0xf8, 0xe3, 0x2e,
        0xe5, 0xeb, 0xdb, 0x69, 0xa5, 0x7a, 0x2b, 0x28 ] := by
  unfold OuterProgram.digest Blake3.Pure.digest
  rw [Blake3.Pure.subtree]
  simp only [show allOpsGoldenProgram.encode.length ≤ 1024 by decide, ↓reduceDIte]
  unfold Blake3.Pure.chunkOutput
  rw [Blake3.Pure.chunkLoop]
  simp only [show ¬ allOpsGoldenProgram.encode.length ≤ 64 by decide, ↓reduceDIte]
  rw [Blake3.Pure.chunkLoop]
  simp only [show ¬ (allOpsGoldenProgram.encode.drop 64).length ≤ 64 by decide, ↓reduceDIte]
  rw [Blake3.Pure.chunkLoop]
  simp only [show ¬ ((allOpsGoldenProgram.encode.drop 64).drop 64).length ≤ 64 by decide, ↓reduceDIte]
  rw [Blake3.Pure.chunkLoop]
  simp only [show (((allOpsGoldenProgram.encode.drop 64).drop 64).drop 64).length ≤ 64 by decide, ↓reduceDIte]
  decide

/-! ## 3. Mathematical & Executable Outer-IR DAG Semantics -/

/-- Input tables supplied to an `OuterProgram` evaluation. -/
structure OuterInputs where
  challenges : Nat → BN254Fr
  values     : Nat → BN254Fr
  publics    : Nat → BN254Fr

def OuterInputs.get (inp : OuterInputs) : OuterInputKind → Nat → BN254Fr
  | .challenge, i => inp.challenges i
  | .value,     i => inp.values i
  | .publicIn,  i => inp.publics i

/-- Evaluate `nodes` sequentially in strict topological order (each operand index must refer
to an earlier node `idx < vals.size`, and every `inverse` operand must be nonzero). -/
def evalNodes? (inp : OuterInputs) (nodes : List OuterInstruction) : Option (Array BN254Fr) :=
  nodes.foldlM (init := #[]) fun vals inst =>
    match inst with
    | .constant v  => some (vals.push v)
    | .input k idx => some (vals.push (inp.get k idx))
    | .add a b => do
      let va ← vals[a]?
      let vb ← vals[b]?
      some (vals.push (va + vb))
    | .sub a b => do
      let va ← vals[a]?
      let vb ← vals[b]?
      some (vals.push (va - vb))
    | .mul a b => do
      let va ← vals[a]?
      let vb ← vals[b]?
      some (vals.push (va * vb))
    | .inverse a => do
      let va ← vals[a]?
      if va = 0 then none else some (vals.push va⁻¹)

/-- Evaluated outputs of an `OuterProgram`: all assertions vanish, and the MSM scalar
coefficients and witness evaluations are extracted from the node array. -/
structure OuterOutputs where
  coefficients : List BN254Fr
  witnesses    : List BN254Fr
  deriving DecidableEq, Repr

/-- Check that every assertion index in `ids` evaluates to `0` in `vals`. -/
def checkAssertions? (vals : Array BN254Fr) : List Nat → Option Unit
  | [] => some ()
  | id :: rest =>
    match vals[id]? with
    | some v => if v = 0 then checkAssertions? vals rest else none
    | none => none

private lemma checkAssertions?_eq_some {vals : Array BN254Fr} :
    ∀ {ids : List Nat}, checkAssertions? vals ids = some () →
      ∀ id ∈ ids, ∃ v, vals[id]? = some v ∧ v = 0
  | [], _, _, h => by cases h
  | a :: rest, h, id, hmem => by
    unfold checkAssertions? at h
    cases hget : vals[a]? with
    | none => rw [hget] at h; cases h
    | some v =>
      rw [hget] at h
      by_cases hv : v = 0
      · simp only [hv, ↓reduceIte] at h
        rcases List.mem_cons.mp hmem with rfl | hrest
        · exact ⟨v, hget, hv⟩
        · exact checkAssertions?_eq_some h id hrest
      · simp only [hv, ↓reduceIte] at h; cases h

/-- Evaluate `p` on `inp`: returns `some out` iff all instructions are well-formed (topological,
nonzero inverses), every assertion node evaluates to `0`, and every coefficient/witness index
is in bounds. -/
def OuterProgram.eval? (p : OuterProgram) (inp : OuterInputs) : Option OuterOutputs :=
  match evalNodes? inp p.nodes with
  | none => none
  | some vals =>
    match checkAssertions? vals p.assertions with
    | none => none
    | some () =>
      match p.coefficients.mapM (fun id => vals[id]?), p.witnesses.mapM (fun id => vals[id]?) with
      | some coeffs, some wits => some { coefficients := coeffs, witnesses := wits }
      | _, _ => none

/-- Relational satisfaction predicate for `OuterProgram`: `vals : Array BN254Fr` is the unique
topological evaluation of `p.nodes` on `inp`, all assertions evaluate to `0`, and `out` gives
the extracted coefficients and witnesses. -/
def OuterProgram.Satisfied (p : OuterProgram) (inp : OuterInputs) (out : OuterOutputs) : Prop :=
  p.eval? inp = some out

/-- **Determinism of Outer-IR evaluation:** given `inp`, `p.eval? inp` produces a unique
`OuterOutputs` (so Gnark witness variables for intermediate nodes are uniquely determined
by the public inputs, Fiat–Shamir challenges, and opened values). -/
theorem OuterProgram.satisfied_unique {p : OuterProgram} {inp : OuterInputs} {o₁ o₂ : OuterOutputs}
    (h₁ : p.Satisfied inp o₁) (h₂ : p.Satisfied inp o₂) : o₁ = o₂ := by
  unfold OuterProgram.Satisfied at h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- Every assertion of a satisfied `OuterProgram` evaluates to `0` in `BN254Fr`. -/
theorem OuterProgram.assertion_eq_zero_of_satisfied {p : OuterProgram} {inp : OuterInputs}
    {out : OuterOutputs} (h : p.Satisfied inp out) :
    ∃ vals, evalNodes? inp p.nodes = some vals ∧
      (∀ id ∈ p.assertions, ∃ v, vals[id]? = some v ∧ v = 0) ∧
      p.coefficients.mapM (fun id => vals[id]?) = some out.coefficients ∧
      p.witnesses.mapM (fun id => vals[id]?) = some out.witnesses := by
  unfold OuterProgram.Satisfied OuterProgram.eval? at h
  cases hnodes : evalNodes? inp p.nodes with
  | none => rw [hnodes] at h; cases h
  | some vals =>
    rw [hnodes] at h
    dsimp only at h
    cases hasrt : checkAssertions? vals p.assertions with
    | none => rw [hasrt] at h; cases h
    | some u =>
      cases u
      rw [hasrt] at h
      dsimp only at h
      cases hc : p.coefficients.mapM (fun id => vals[id]?) with
      | none => rw [hc] at h; cases h
      | some coeffs =>
        cases hw : p.witnesses.mapM (fun id => vals[id]?) with
        | none => rw [hc, hw] at h; cases h
        | some wits =>
          rw [hc, hw] at h
          cases h
          exact ⟨vals, rfl, checkAssertions?_eq_some hasrt, hc, hw⟩

/-! ## 4. Encoding Injectivity (`IndicesFitU32`) & Gnark Verifying Key Audit -/

/-- Every node count and index in `p` fits in `u32` (enforced by Rust `u32::try_from` in
`ir.rs:50` and Go bounds checks in `tools/gnark/profile.go`). -/
def OuterInstruction.FitsU32 : OuterInstruction → Prop
  | .constant _  => True
  | .input _ idx => idx < 2 ^ 32
  | .add a b     => a < 2 ^ 32 ∧ b < 2 ^ 32
  | .sub a b     => a < 2 ^ 32 ∧ b < 2 ^ 32
  | .mul a b     => a < 2 ^ 32 ∧ b < 2 ^ 32
  | .inverse a   => a < 2 ^ 32

def OuterProgram.FitsU32 (p : OuterProgram) : Prop :=
  p.nodes.length < 2 ^ 32 ∧
  (∀ n ∈ p.nodes, n.FitsU32) ∧
  p.assertions.length < 2 ^ 32 ∧ (∀ a ∈ p.assertions, a < 2 ^ 32) ∧
  p.coefficients.length < 2 ^ 32 ∧ (∀ c ∈ p.coefficients, c < 2 ^ 32) ∧
  p.witnesses.length < 2 ^ 32 ∧ (∀ w ∈ p.witnesses, w < 2 ^ 32)

private lemma encodeU32LE_length (n : Nat) : (encodeU32LE n).length = 4 := rfl

private lemma encodeU32LE_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (heq : encodeU32LE a = encodeU32LE b) : a = b := by
  unfold encodeU32LE at heq
  simp only [List.cons.injEq, and_true] at heq
  have h0 : a % 256 = b % 256 := by
    have := congrArg UInt8.toNat heq.1; simpa [UInt8.toNat_ofNat] using this
  have h1 : (a / 256) % 256 = (b / 256) % 256 := by
    have := congrArg UInt8.toNat heq.2.1; simpa [UInt8.toNat_ofNat] using this
  have h2 : (a / 65536) % 256 = (b / 65536) % 256 := by
    have := congrArg UInt8.toNat heq.2.2.1; simpa [UInt8.toNat_ofNat] using this
  have h3 : (a / 16777216) % 256 = (b / 16777216) % 256 := by
    have := congrArg UInt8.toNat heq.2.2.2; simpa [UInt8.toNat_ofNat] using this
  omega

private lemma encodeU32LE_append_inj {a b : Nat} {r1 r2 : List UInt8}
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (heq : encodeU32LE a ++ r1 = encodeU32LE b ++ r2) : a = b ∧ r1 = r2 := by
  have hlen : (encodeU32LE a).length = (encodeU32LE b).length := rfl
  obtain ⟨h1, h2⟩ := List.append_inj heq hlen
  exact ⟨encodeU32LE_inj ha hb h1, h2⟩

private lemma encodeScalarBE32_length (x : BN254Fr) : (encodeScalarBE32 x).length = 32 := by
  simp [encodeScalarBE32]

private lemma encodeScalarBE32_inj {x y : BN254Fr} (heq : encodeScalarBE32 x = encodeScalarBE32 y) :
    x = y := by
  have hbyte : ∀ k < 32, (x.val / 256 ^ k) % 256 = (y.val / 256 ^ k) % 256 := by
    intro k hk
    have hidx := congrArg (fun l => l[31 - k]?) heq
    have hlt : 31 - k < 32 := by omega
    simp only [encodeScalarBE32, List.getElem?_map, List.getElem?_range hlt, Option.map_some,
      Option.some.injEq] at hidx
    have hsub : 31 - (31 - k) = k := by omega
    rw [hsub] at hidx
    have hnat := congrArg UInt8.toNat hidx
    simpa [UInt8.toNat_ofNat] using hnat
  -- Reconstruct equality modulo `256^32` by induction on `k`
  have hmod : ∀ k ≤ 32, x.val % 256 ^ k = y.val % 256 ^ k := by
    intro k
    induction k with
    | zero => intro _; simp [Nat.mod_one]
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hcur := hbyte k (by omega)
      have hsplit : ∀ v : Nat, v % 256 ^ (k + 1) = v % 256 ^ k + 256 ^ k * ((v / 256 ^ k) % 256) := by
        intro v
        have hpos : 0 < 256 ^ k := Nat.pow_pos (by decide)
        have h1 : v = 256 ^ k * (v / 256 ^ k) + v % 256 ^ k := (Nat.div_add_mod v (256 ^ k)).symm
        have h2 : v / 256 ^ k = 256 * ((v / 256 ^ k) / 256) + (v / 256 ^ k) % 256 :=
          (Nat.div_add_mod (v / 256 ^ k) 256).symm
        have h3 : v = (256 ^ (k + 1)) * ((v / 256 ^ k) / 256) +
            (v % 256 ^ k + 256 ^ k * ((v / 256 ^ k) % 256)) := by
          rw [Nat.pow_succ]
          calc v = 256 ^ k * (v / 256 ^ k) + v % 256 ^ k := h1
            _ = 256 ^ k * (256 * ((v / 256 ^ k) / 256) + (v / 256 ^ k) % 256) + v % 256 ^ k := by rw [← h2]
            _ = 256 ^ k * 256 * ((v / 256 ^ k) / 256) + (v % 256 ^ k + 256 ^ k * ((v / 256 ^ k) % 256)) := by ring
        have hlt : v % 256 ^ k + 256 ^ k * ((v / 256 ^ k) % 256) < 256 ^ (k + 1) := by
          have ha : v % 256 ^ k < 256 ^ k := Nat.mod_lt _ hpos
          have hb : (v / 256 ^ k) % 256 ≤ 255 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
          have hmul : 256 ^ k * ((v / 256 ^ k) % 256) ≤ 256 ^ k * 255 := Nat.mul_le_mul_left _ hb
          rw [Nat.pow_succ]; omega
        conv_lhs => rw [h3]
        rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]
      rw [hsplit x.val, hsplit y.val, hprev, hcur]
  have hxlt : x.val < 256 ^ 32 := lt_trans (ZMod.val_lt x) (by decide)
  have hylt : y.val < 256 ^ 32 := lt_trans (ZMod.val_lt y) (by decide)
  have hval : x.val = y.val := by
    have := hmod 32 (le_refl _)
    rwa [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at this
  exact ZMod.val_injective _ hval

private lemma inputKind_tag_inj {k1 k2 : OuterInputKind} (h : k1.tag = k2.tag) : k1 = k2 := by
  cases k1 <;> cases k2 <;> simp [OuterInputKind.tag] at h ⊢

private lemma encodeInstruction_append_inj {i1 i2 : OuterInstruction} {r1 r2 : List UInt8}
    (h1 : i1.FitsU32) (h2 : i2.FitsU32)
    (heq : i1.encode ++ r1 = i2.encode ++ r2) : i1 = i2 ∧ r1 = r2 := by
  cases i1 <;> cases i2 <;>
    simp only [OuterInstruction.encode, List.cons_append, List.cons.injEq] at heq
  case constant.constant v1 v2 =>
    obtain ⟨_, hrest⟩ := heq
    obtain ⟨hv, hr⟩ := List.append_inj hrest (by rw [encodeScalarBE32_length, encodeScalarBE32_length])
    exact ⟨congrArg OuterInstruction.constant (encodeScalarBE32_inj hv), hr⟩
  case input.input k1 idx1 k2 idx2 =>
    obtain ⟨_, hk, hrest⟩ := heq
    obtain ⟨hidx, hr⟩ := encodeU32LE_append_inj h1 h2 hrest
    exact ⟨by rw [inputKind_tag_inj hk, hidx], hr⟩
  case add.add a1 b1 a2 b2 =>
    obtain ⟨_, hrest⟩ := heq
    rw [List.append_assoc, List.append_assoc] at hrest
    obtain ⟨ha, hrest2⟩ := encodeU32LE_append_inj h1.1 h2.1 hrest
    obtain ⟨hb, hr⟩ := encodeU32LE_append_inj h1.2 h2.2 hrest2
    exact ⟨by rw [ha, hb], hr⟩
  case sub.sub a1 b1 a2 b2 =>
    obtain ⟨_, hrest⟩ := heq
    rw [List.append_assoc, List.append_assoc] at hrest
    obtain ⟨ha, hrest2⟩ := encodeU32LE_append_inj h1.1 h2.1 hrest
    obtain ⟨hb, hr⟩ := encodeU32LE_append_inj h1.2 h2.2 hrest2
    exact ⟨by rw [ha, hb], hr⟩
  case mul.mul a1 b1 a2 b2 =>
    obtain ⟨_, hrest⟩ := heq
    rw [List.append_assoc, List.append_assoc] at hrest
    obtain ⟨ha, hrest2⟩ := encodeU32LE_append_inj h1.1 h2.1 hrest
    obtain ⟨hb, hr⟩ := encodeU32LE_append_inj h1.2 h2.2 hrest2
    exact ⟨by rw [ha, hb], hr⟩
  case inverse.inverse a1 a2 =>
    obtain ⟨_, hrest⟩ := heq
    obtain ⟨ha, hr⟩ := encodeU32LE_append_inj h1 h2 hrest
    exact ⟨by rw [ha], hr⟩
  all_goals exact absurd heq.1 (by decide)

private lemma encodeNodes_append_inj :
    ∀ {l1 l2 : List OuterInstruction} {r1 r2 : List UInt8},
      l1.length = l2.length →
      (∀ n ∈ l1, n.FitsU32) → (∀ n ∈ l2, n.FitsU32) →
      l1.flatMap OuterInstruction.encode ++ r1 = l2.flatMap OuterInstruction.encode ++ r2 →
      l1 = l2 ∧ r1 = r2
  | [], [], _, _, _, _, _, h => ⟨rfl, h⟩
  | _ :: _, [], _, _, hlen, _, _, _ => by simp at hlen
  | [], _ :: _, _, _, hlen, _, _, _ => by simp at hlen
  | a :: as, b :: bs, r1, r2, hlen, ha, hb, heq => by
    simp only [List.flatMap_cons, List.append_assoc] at heq
    obtain ⟨hab, hrest⟩ := encodeInstruction_append_inj
      (ha a (List.mem_cons_self ..)) (hb b (List.mem_cons_self ..)) heq
    obtain ⟨htl, hr⟩ := encodeNodes_append_inj (by simpa using hlen)
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx)) hrest
    exact ⟨by rw [hab, htl], hr⟩

private lemma encodeU32Flat_append_inj :
    ∀ {l1 l2 : List Nat} {r1 r2 : List UInt8},
      l1.length = l2.length →
      (∀ x ∈ l1, x < 2 ^ 32) → (∀ x ∈ l2, x < 2 ^ 32) →
      l1.flatMap encodeU32LE ++ r1 = l2.flatMap encodeU32LE ++ r2 →
      l1 = l2 ∧ r1 = r2
  | [], [], _, _, _, _, _, h => ⟨rfl, h⟩
  | _ :: _, [], _, _, hlen, _, _, _ => by simp at hlen
  | [], _ :: _, _, _, hlen, _, _, _ => by simp at hlen
  | a :: as, b :: bs, r1, r2, hlen, ha, hb, heq => by
    simp only [List.flatMap_cons, List.append_assoc] at heq
    obtain ⟨hab, hrest⟩ := encodeU32LE_append_inj
      (ha a (List.mem_cons_self ..)) (hb b (List.mem_cons_self ..)) heq
    obtain ⟨htl, hr⟩ := encodeU32Flat_append_inj (by simpa using hlen)
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx)) hrest
    exact ⟨by rw [hab, htl], hr⟩

private lemma encodeU32List_append_inj {l1 l2 : List Nat} {r1 r2 : List UInt8}
    (hlen1 : l1.length < 2 ^ 32) (hlen2 : l2.length < 2 ^ 32)
    (h1 : ∀ x ∈ l1, x < 2 ^ 32) (h2 : ∀ x ∈ l2, x < 2 ^ 32)
    (heq : encodeU32List l1 ++ r1 = encodeU32List l2 ++ r2) : l1 = l2 ∧ r1 = r2 := by
  unfold encodeU32List at heq
  rw [List.append_assoc, List.append_assoc] at heq
  obtain ⟨hlen, hrest⟩ := encodeU32LE_append_inj hlen1 hlen2 heq
  exact encodeU32Flat_append_inj hlen h1 h2 hrest

/-- **Canonical Encoding Injectivity:** `OuterProgram.encode` is strictly injective on all
programs whose lengths and indices fit in `u32` (`FitsU32`). -/
theorem OuterProgram.encode_injective {p1 p2 : OuterProgram}
    (h1 : p1.FitsU32) (h2 : p2.FitsU32) (heq : p1.encode = p2.encode) : p1 = p2 := by
  obtain ⟨hn1, hnf1, ha1, haf1, hc1, hcf1, hw1, hwf1⟩ := h1
  obtain ⟨hn2, hnf2, ha2, haf2, hc2, hcf2, hw2, hwf2⟩ := h2
  unfold OuterProgram.encode at heq
  simp only [List.append_assoc] at heq
  have h1' := List.append_cancel_left heq
  obtain ⟨hnlen, h2'⟩ := encodeU32LE_append_inj hn1 hn2 h1'
  obtain ⟨hnodes, h3'⟩ := encodeNodes_append_inj hnlen hnf1 hnf2 h2'
  obtain ⟨hasrt, h4'⟩ := encodeU32List_append_inj ha1 ha2 haf1 haf2 h3'
  obtain ⟨hcoeff, h5'⟩ := encodeU32List_append_inj hc1 hc2 hcf1 hcf2 h4'
  have h5'' : encodeU32List p1.witnesses ++ [] = encodeU32List p2.witnesses ++ [] := by simpa using h5'
  obtain ⟨hwit, _⟩ := encodeU32List_append_inj hw1 hw2 hwf1 hwf2 h5''
  cases p1; cases p2
  simp_all

/-- Abstract verified Gnark final circuit instance (`tools/gnark/profile.go`),
committing to an explicit `programDigest` checked by `verifyingKey.validate()`. -/
structure GnarkVerifyingKey where
  programDigest : List UInt8
  expectedProgram : OuterProgram
  expectedFitsU32 : expectedProgram.FitsU32
  /-- `validate()` in `tools/gnark/profile.go` enforces exact digest match. -/
  digestMatches : programDigest = expectedProgram.digest

/-- A Gnark-certified outer verification witness: the final PLONK/Groth16 proof satisfies
the `OuterProgram` pinned by `vk.programDigest` and the BN254 pairing check over `out`. -/
structure GnarkOuterAccepted (vk : GnarkVerifyingKey) (inp : OuterInputs)
    (PairingCheck : OuterOutputs → Prop) where
  outerProgram : OuterProgram
  outerFitsU32 : outerProgram.FitsU32
  vkDigestEq : outerProgram.digest = vk.programDigest
  outputs : OuterOutputs
  programSat : outerProgram.Satisfied inp outputs
  pairingHolds : PairingCheck outputs

/-- **Outer-Relation Soundness with Explicit BLAKE3 Collision Escape (`gnark_outer_relation_sound`):**
If a Gnark proof is accepted against `vk` (which commits to `vk.expectedProgram.digest`), then
EITHER a concrete BLAKE3 collision between `acc.outerProgram.encode` and `vk.expectedProgram.encode`
was exhibited, OR `vk.expectedProgram` itself is satisfied on `inp` with outputs satisfying
`PairingCheck`! -/
theorem gnark_outer_relation_sound
    {vk : GnarkVerifyingKey} {inp : OuterInputs} {PairingCheck : OuterOutputs → Prop}
    (acc : GnarkOuterAccepted vk inp PairingCheck) :
    (acc.outerProgram.encode ≠ vk.expectedProgram.encode ∧
      Blake3.Pure.digest acc.outerProgram.encode = Blake3.Pure.digest vk.expectedProgram.encode) ∨
    (∃ out, vk.expectedProgram.Satisfied inp out ∧ PairingCheck out) := by
  by_cases henc : acc.outerProgram.encode = vk.expectedProgram.encode
  · right
    have hprog : acc.outerProgram = vk.expectedProgram :=
      OuterProgram.encode_injective acc.outerFitsU32 vk.expectedFitsU32 henc
    exact ⟨acc.outputs, hprog ▸ acc.programSat, acc.pairingHolds⟩
  · left
    refine ⟨henc, ?_⟩
    have hdig : acc.outerProgram.digest = vk.expectedProgram.digest :=
      acc.vkDigestEq.trans vk.digestMatches
    unfold OuterProgram.digest at hdig
    exact Vector.ext fun i hi => by
      have := congrArg (fun l => l[i]?) hdig
      simpa [Vector.getElem?_toList, hi] using this

end Ix.Cert.Compression.OuterRelation
