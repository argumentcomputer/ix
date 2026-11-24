import Ix.Cert.Compression.OuterRelation
import Ix.Cert.Compression.Bls12381.Field
import Blake3.Pure

/-! # BLS12-381 Outer-IR Semantics, `"ix/outer-ir/v1"` Digest Audit & Subgroup-Enforced Folded Pairing

Formalizes the exported BLS12-381 Outer-IR DAG verified inside the final Gnark PLONK / Groth16
circuit (`crates/proof-compression/src/pipeline/wrap/outer/final_export/ir.rs`,
`tools/gnark/profile.go`, and `tools/gnark/curve_bls.go`):

1. **Exact AST over `BLS12381Fr` (`Bls12381OuterInstruction`, `Bls12381OuterProgram`):**
   6 instruction kinds (`constant`, `input`, `add`, `sub`, `mul`, `inverse`) over the 255-bit
   prime scalar field `BLS12381Fr`, plus output index tables (`assertions`, `coefficients`,
   `witnesses`).
2. **Canonical `"ix/outer-ir/v1"` Binary Encoding & BLAKE3 Digest:**
   - 32-byte big-endian scalar encoding (`encodeBlsScalarBE32`, sound since
     `bls12381FrModulus < 256 ^ 32`),
   - Kernel-verified empty-program golden digest matching Rust & Go byte-for-byte
     (`bls12381_empty_program_digest_matches_rust_go`),
   - Canonical encoding injectivity on `FitsU32` programs
     (`Bls12381OuterProgram.encode_injective`).
3. **Executable & Mathematical DAG Evaluation (`evalBlsNodes?`, `Bls12381OuterProgram.Satisfied`):**
   - Determinism (`satisfied_unique`) and assertion vanishing (`assertion_eq_zero_of_satisfied`).
   - Gnark outer-relation soundness with explicit BLAKE3 collision escape
     (`bls12381_gnark_outer_relation_sound`).
4. **Subgroup-Enforced Folded BLS12-381 Pairing Check (`Bls12381BilinearPairing`,
   `Bls12381FoldedPairingCheck`, `bls12381_folded_pairing_bad_card`,
   `bls12381_gnark_folded_pairing_sound`):**
   - Explicitly enforces `bp.InPrimeSubgroupG1` on ALL FOUR $G_1$ pairing inputs
     `(left, right, d0, d1)` (modeling `curve_bls.go:71` `!result.IsInSubGroup()` and
     EIP-2537 BLS12-381 pairing precompile subgroup checks).
   - Proves deterministic rejection of any non-subgroup $G_1$ input
     (`bls12381_foldedPairingCheck_rejects_nonSubgroup`) and exact Schwartz–Zippel soundness
     error `≤ 1 / bls12381FrModulus` (`≤ 2^{-254}`) when all four points lie in $G_1$.

Zero `sorry`, zero `native_decide`, strictly `[propext, Classical.choice, Quot.sound]`.
-/

namespace Ix.Cert.Compression.Bls12381.OuterRelation

open Ix.Cert.Compression.OuterRelation
open Ix.Cert.Compression.Bls12381.Field

/-! ## 1. BLS12-381 Outer-IR AST -/

/-- Single SSA instruction in BLS12-381 `OuterIR`. -/
inductive Bls12381OuterInstruction where
  | constant (value : BLS12381Fr)
  | input (kind : OuterInputKind) (index : Nat)
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | inverse (a : Nat)
  deriving DecidableEq, Repr

/-- Complete exported BLS12-381 `OuterIR` scalar verifier program. -/
structure Bls12381OuterProgram where
  nodes : List Bls12381OuterInstruction
  assertions : List Nat
  coefficients : List Nat
  witnesses : List Nat
  deriving DecidableEq, Repr

/-! ## 2. Canonical `"ix/outer-ir/v1"` Binary Encoding & BLAKE3 Digest -/

/-- Canonical 32-byte big-endian encoding of a `BLS12381Fr` scalar
(`0 ≤ val < bls12381FrModulus < 256^32`). -/
def encodeBlsScalarBE32 (x : BLS12381Fr) : List UInt8 :=
  let v := x.val
  (List.range 32).map fun i =>
    UInt8.ofNat ((v / 256 ^ (31 - i)) % 256)

def Bls12381OuterInstruction.encode : Bls12381OuterInstruction → List UInt8
  | .constant v     => 0 :: encodeBlsScalarBE32 v
  | .input k idx    => 1 :: k.tag :: encodeU32LE idx
  | .add a b        => 2 :: (encodeU32LE a ++ encodeU32LE b)
  | .sub a b        => 3 :: (encodeU32LE a ++ encodeU32LE b)
  | .mul a b        => 4 :: (encodeU32LE a ++ encodeU32LE b)
  | .inverse a      => 5 :: encodeU32LE a

/-- Canonical deterministic `"ix/outer-ir/v1"` encoding for BLS12-381 programs. -/
def Bls12381OuterProgram.encode (p : Bls12381OuterProgram) : List UInt8 :=
  outerIrDomain ++
  encodeU32LE p.nodes.length ++
  p.nodes.flatMap Bls12381OuterInstruction.encode ++
  encodeU32List p.assertions ++
  encodeU32List p.coefficients ++
  encodeU32List p.witnesses

/-- Canonical 32-byte BLAKE3 digest of `p.encode`. -/
def Bls12381OuterProgram.digest (p : Bls12381OuterProgram) : List UInt8 :=
  (Blake3.Pure.digest p.encode).toList

set_option maxRecDepth 20000 in
/-- Empty BLS12-381 `OuterProgram` matches the shared Rust & Go golden digest
`0x02d95030e924d62b65dcb11734967f540cddd90337d58184d90f02197df5a799`. -/
theorem bls12381_empty_program_digest_matches_rust_go :
    ({ nodes := [], assertions := [], coefficients := [], witnesses := [] } :
        Bls12381OuterProgram).digest =
      [ 0x02, 0xd9, 0x50, 0x30, 0xe9, 0x24, 0xd6, 0x2b,
        0x65, 0xdc, 0xb1, 0x17, 0x34, 0x96, 0x7f, 0x54,
        0x0c, 0xdd, 0xd9, 0x03, 0x37, 0xd5, 0x81, 0x84,
        0xd9, 0x0f, 0x02, 0x19, 0x7d, 0xf5, 0xa7, 0x99 ] := by
  unfold Bls12381OuterProgram.digest Blake3.Pure.digest
  rw [Blake3.Pure.subtree]
  simp only [show ({ nodes := [], assertions := [], coefficients := [], witnesses := [] } :
      Bls12381OuterProgram).encode.length ≤ 1024 by decide, ↓reduceDIte]
  unfold Blake3.Pure.chunkOutput
  rw [Blake3.Pure.chunkLoop]
  simp only [show ({ nodes := [], assertions := [], coefficients := [], witnesses := [] } :
      Bls12381OuterProgram).encode.length ≤ 64 by decide, ↓reduceDIte]
  decide

/-! ## 3. Mathematical & Executable BLS12-381 Outer-IR DAG Semantics -/

/-- Input tables supplied to a `Bls12381OuterProgram` evaluation. -/
structure Bls12381OuterInputs where
  challenges : Nat → BLS12381Fr
  values     : Nat → BLS12381Fr
  publics    : Nat → BLS12381Fr

def Bls12381OuterInputs.get (inp : Bls12381OuterInputs) : OuterInputKind → Nat → BLS12381Fr
  | .challenge, i => inp.challenges i
  | .value,     i => inp.values i
  | .publicIn,  i => inp.publics i

/-- Evaluate `nodes` sequentially in strict topological order over `BLS12381Fr`. -/
def evalBlsNodes? (inp : Bls12381OuterInputs) (nodes : List Bls12381OuterInstruction) :
    Option (Array BLS12381Fr) :=
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

/-- Evaluated outputs of a `Bls12381OuterProgram`. -/
structure Bls12381OuterOutputs where
  coefficients : List BLS12381Fr
  witnesses    : List BLS12381Fr
  deriving DecidableEq, Repr

/-- Check that every assertion index in `ids` evaluates to `0` in `vals`. -/
def checkBlsAssertions? (vals : Array BLS12381Fr) : List Nat → Option Unit
  | [] => some ()
  | id :: rest =>
    match vals[id]? with
    | some v => if v = 0 then checkBlsAssertions? vals rest else none
    | none => none

private lemma checkBlsAssertions?_eq_some {vals : Array BLS12381Fr} :
    ∀ {ids : List Nat}, checkBlsAssertions? vals ids = some () →
      ∀ id ∈ ids, ∃ v, vals[id]? = some v ∧ v = 0
  | [], _, _, h => by cases h
  | a :: rest, h, id, hmem => by
    unfold checkBlsAssertions? at h
    cases hget : vals[a]? with
    | none => rw [hget] at h; cases h
    | some v =>
      rw [hget] at h
      by_cases hv : v = 0
      · simp only [hv, ↓reduceIte] at h
        rcases List.mem_cons.mp hmem with rfl | hrest
        · exact ⟨v, hget, hv⟩
        · exact checkBlsAssertions?_eq_some h id hrest
      · simp only [hv, ↓reduceIte] at h; cases h

/-- Evaluate `p` on `inp`. -/
def Bls12381OuterProgram.eval? (p : Bls12381OuterProgram) (inp : Bls12381OuterInputs) :
    Option Bls12381OuterOutputs :=
  match evalBlsNodes? inp p.nodes with
  | none => none
  | some vals =>
    match checkBlsAssertions? vals p.assertions with
    | none => none
    | some () =>
      match p.coefficients.mapM (fun id => vals[id]?), p.witnesses.mapM (fun id => vals[id]?) with
      | some coeffs, some wits => some { coefficients := coeffs, witnesses := wits }
      | _, _ => none

/-- Relational satisfaction predicate for `Bls12381OuterProgram`. -/
def Bls12381OuterProgram.Satisfied (p : Bls12381OuterProgram) (inp : Bls12381OuterInputs)
    (out : Bls12381OuterOutputs) : Prop :=
  p.eval? inp = some out

theorem Bls12381OuterProgram.satisfied_unique {p : Bls12381OuterProgram}
    {inp : Bls12381OuterInputs} {o₁ o₂ : Bls12381OuterOutputs}
    (h₁ : p.Satisfied inp o₁) (h₂ : p.Satisfied inp o₂) : o₁ = o₂ := by
  unfold Bls12381OuterProgram.Satisfied at h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem Bls12381OuterProgram.assertion_eq_zero_of_satisfied {p : Bls12381OuterProgram}
    {inp : Bls12381OuterInputs} {out : Bls12381OuterOutputs} (h : p.Satisfied inp out) :
    ∃ vals, evalBlsNodes? inp p.nodes = some vals ∧
      (∀ id ∈ p.assertions, ∃ v, vals[id]? = some v ∧ v = 0) ∧
      p.coefficients.mapM (fun id => vals[id]?) = some out.coefficients ∧
      p.witnesses.mapM (fun id => vals[id]?) = some out.witnesses := by
  unfold Bls12381OuterProgram.Satisfied Bls12381OuterProgram.eval? at h
  cases hnodes : evalBlsNodes? inp p.nodes with
  | none => rw [hnodes] at h; cases h
  | some vals =>
    rw [hnodes] at h
    dsimp only at h
    cases hasrt : checkBlsAssertions? vals p.assertions with
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
          exact ⟨vals, rfl, checkBlsAssertions?_eq_some hasrt, hc, hw⟩

/-! ## 4. Encoding Injectivity (`FitsU32`) & Gnark Verifying Key Soundness -/

def Bls12381OuterInstruction.FitsU32 : Bls12381OuterInstruction → Prop
  | .constant _  => True
  | .input _ idx => idx < 2 ^ 32
  | .add a b     => a < 2 ^ 32 ∧ b < 2 ^ 32
  | .sub a b     => a < 2 ^ 32 ∧ b < 2 ^ 32
  | .mul a b     => a < 2 ^ 32 ∧ b < 2 ^ 32
  | .inverse a   => a < 2 ^ 32

def Bls12381OuterProgram.FitsU32 (p : Bls12381OuterProgram) : Prop :=
  p.nodes.length < 2 ^ 32 ∧
  (∀ n ∈ p.nodes, n.FitsU32) ∧
  p.assertions.length < 2 ^ 32 ∧ (∀ a ∈ p.assertions, a < 2 ^ 32) ∧
  p.coefficients.length < 2 ^ 32 ∧ (∀ c ∈ p.coefficients, c < 2 ^ 32) ∧
  p.witnesses.length < 2 ^ 32 ∧ (∀ w ∈ p.witnesses, w < 2 ^ 32)

private lemma encodeU32LE_inj_bls {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
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

private lemma encodeU32LE_append_inj_bls {a b : Nat} {r1 r2 : List UInt8}
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (heq : encodeU32LE a ++ r1 = encodeU32LE b ++ r2) : a = b ∧ r1 = r2 := by
  have hlen : (encodeU32LE a).length = (encodeU32LE b).length := rfl
  obtain ⟨h1, h2⟩ := List.append_inj heq hlen
  exact ⟨encodeU32LE_inj_bls ha hb h1, h2⟩

private lemma encodeBlsScalarBE32_length (x : BLS12381Fr) :
    (encodeBlsScalarBE32 x).length = 32 := by
  simp [encodeBlsScalarBE32]

private lemma encodeBlsScalarBE32_inj {x y : BLS12381Fr}
    (heq : encodeBlsScalarBE32 x = encodeBlsScalarBE32 y) : x = y := by
  have hbyte : ∀ k < 32, (x.val / 256 ^ k) % 256 = (y.val / 256 ^ k) % 256 := by
    intro k hk
    have hidx := congrArg (fun l => l[31 - k]?) heq
    have hlt : 31 - k < 32 := by omega
    simp only [encodeBlsScalarBE32, List.getElem?_map, List.getElem?_range hlt, Option.map_some,
      Option.some.injEq] at hidx
    have hsub : 31 - (31 - k) = k := by omega
    rw [hsub] at hidx
    have hnat := congrArg UInt8.toNat hidx
    simpa [UInt8.toNat_ofNat] using hnat
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
  have hFrLt : bls12381FrModulus < 256 ^ 32 := by decide
  have hxlt : x.val < 256 ^ 32 := lt_trans (ZMod.val_lt x) hFrLt
  have hylt : y.val < 256 ^ 32 := lt_trans (ZMod.val_lt y) hFrLt
  have hval : x.val = y.val := by
    have := hmod 32 (le_refl _)
    rwa [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at this
  exact ZMod.val_injective _ hval

private lemma inputKind_tag_inj_bls {k1 k2 : OuterInputKind} (h : k1.tag = k2.tag) : k1 = k2 := by
  cases k1 <;> cases k2 <;> simp [OuterInputKind.tag] at h ⊢

private lemma encodeBlsInstruction_append_inj {i1 i2 : Bls12381OuterInstruction}
    {r1 r2 : List UInt8}
    (h1 : i1.FitsU32) (h2 : i2.FitsU32)
    (heq : i1.encode ++ r1 = i2.encode ++ r2) : i1 = i2 ∧ r1 = r2 := by
  cases i1 <;> cases i2 <;>
    simp only [Bls12381OuterInstruction.encode, List.cons_append, List.cons.injEq] at heq
  case constant.constant v1 v2 =>
    obtain ⟨_, hrest⟩ := heq
    obtain ⟨hv, hr⟩ := List.append_inj hrest
      (by rw [encodeBlsScalarBE32_length, encodeBlsScalarBE32_length])
    exact ⟨congrArg Bls12381OuterInstruction.constant (encodeBlsScalarBE32_inj hv), hr⟩
  case input.input k1 idx1 k2 idx2 =>
    obtain ⟨_, hk, hrest⟩ := heq
    obtain ⟨hidx, hr⟩ := encodeU32LE_append_inj_bls h1 h2 hrest
    exact ⟨by rw [inputKind_tag_inj_bls hk, hidx], hr⟩
  case add.add a1 b1 a2 b2 =>
    obtain ⟨_, hrest⟩ := heq
    rw [List.append_assoc, List.append_assoc] at hrest
    obtain ⟨ha, hrest2⟩ := encodeU32LE_append_inj_bls h1.1 h2.1 hrest
    obtain ⟨hb, hr⟩ := encodeU32LE_append_inj_bls h1.2 h2.2 hrest2
    exact ⟨by rw [ha, hb], hr⟩
  case sub.sub a1 b1 a2 b2 =>
    obtain ⟨_, hrest⟩ := heq
    rw [List.append_assoc, List.append_assoc] at hrest
    obtain ⟨ha, hrest2⟩ := encodeU32LE_append_inj_bls h1.1 h2.1 hrest
    obtain ⟨hb, hr⟩ := encodeU32LE_append_inj_bls h1.2 h2.2 hrest2
    exact ⟨by rw [ha, hb], hr⟩
  case mul.mul a1 b1 a2 b2 =>
    obtain ⟨_, hrest⟩ := heq
    rw [List.append_assoc, List.append_assoc] at hrest
    obtain ⟨ha, hrest2⟩ := encodeU32LE_append_inj_bls h1.1 h2.1 hrest
    obtain ⟨hb, hr⟩ := encodeU32LE_append_inj_bls h1.2 h2.2 hrest2
    exact ⟨by rw [ha, hb], hr⟩
  case inverse.inverse a1 a2 =>
    obtain ⟨_, hrest⟩ := heq
    obtain ⟨ha, hr⟩ := encodeU32LE_append_inj_bls h1 h2 hrest
    exact ⟨by rw [ha], hr⟩
  all_goals exact absurd heq.1 (by decide)

private lemma encodeBlsNodes_append_inj :
    ∀ {l1 l2 : List Bls12381OuterInstruction} {r1 r2 : List UInt8},
      l1.length = l2.length →
      (∀ n ∈ l1, n.FitsU32) → (∀ n ∈ l2, n.FitsU32) →
      l1.flatMap Bls12381OuterInstruction.encode ++ r1 =
        l2.flatMap Bls12381OuterInstruction.encode ++ r2 →
      l1 = l2 ∧ r1 = r2
  | [], [], _, _, _, _, _, h => ⟨rfl, h⟩
  | _ :: _, [], _, _, hlen, _, _, _ => by simp at hlen
  | [], _ :: _, _, _, hlen, _, _, _ => by simp at hlen
  | a :: as, b :: bs, r1, r2, hlen, ha, hb, heq => by
    simp only [List.flatMap_cons, List.append_assoc] at heq
    obtain ⟨hab, hrest⟩ := encodeBlsInstruction_append_inj
      (ha a (List.mem_cons_self ..)) (hb b (List.mem_cons_self ..)) heq
    obtain ⟨htl, hr⟩ := encodeBlsNodes_append_inj (by simpa using hlen)
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx)) hrest
    exact ⟨by rw [hab, htl], hr⟩

private lemma encodeU32Flat_append_inj_bls :
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
    obtain ⟨hab, hrest⟩ := encodeU32LE_append_inj_bls
      (ha a (List.mem_cons_self ..)) (hb b (List.mem_cons_self ..)) heq
    obtain ⟨htl, hr⟩ := encodeU32Flat_append_inj_bls (by simpa using hlen)
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx)) hrest
    exact ⟨by rw [hab, htl], hr⟩

private lemma encodeU32List_append_inj_bls {l1 l2 : List Nat} {r1 r2 : List UInt8}
    (hlen1 : l1.length < 2 ^ 32) (hlen2 : l2.length < 2 ^ 32)
    (h1 : ∀ x ∈ l1, x < 2 ^ 32) (h2 : ∀ x ∈ l2, x < 2 ^ 32)
    (heq : encodeU32List l1 ++ r1 = encodeU32List l2 ++ r2) : l1 = l2 ∧ r1 = r2 := by
  unfold encodeU32List at heq
  rw [List.append_assoc, List.append_assoc] at heq
  obtain ⟨hlen, hrest⟩ := encodeU32LE_append_inj_bls hlen1 hlen2 heq
  exact encodeU32Flat_append_inj_bls hlen h1 h2 hrest

/-- **Canonical Encoding Injectivity (`Bls12381OuterProgram.encode_injective`)**. -/
theorem Bls12381OuterProgram.encode_injective {p1 p2 : Bls12381OuterProgram}
    (h1 : p1.FitsU32) (h2 : p2.FitsU32) (heq : p1.encode = p2.encode) : p1 = p2 := by
  obtain ⟨hn1, hnf1, ha1, haf1, hc1, hcf1, hw1, hwf1⟩ := h1
  obtain ⟨hn2, hnf2, ha2, haf2, hc2, hcf2, hw2, hwf2⟩ := h2
  unfold Bls12381OuterProgram.encode at heq
  simp only [List.append_assoc] at heq
  have h1' := List.append_cancel_left heq
  obtain ⟨hnlen, h2'⟩ := encodeU32LE_append_inj_bls hn1 hn2 h1'
  obtain ⟨hnodes, h3'⟩ := encodeBlsNodes_append_inj hnlen hnf1 hnf2 h2'
  obtain ⟨hasrt, h4'⟩ := encodeU32List_append_inj_bls ha1 ha2 haf1 haf2 h3'
  obtain ⟨hcoeff, h5'⟩ := encodeU32List_append_inj_bls hc1 hc2 hcf1 hcf2 h4'
  have h5'' : encodeU32List p1.witnesses ++ [] = encodeU32List p2.witnesses ++ [] := by simpa using h5'
  obtain ⟨hwit, _⟩ := encodeU32List_append_inj_bls hw1 hw2 hwf1 hwf2 h5''
  cases p1; cases p2
  simp_all

/-- Abstract verified BLS12-381 Gnark final circuit verifying key (`tools/gnark/curve_bls.go`). -/
structure Bls12381GnarkVerifyingKey where
  programDigest : List UInt8
  expectedProgram : Bls12381OuterProgram
  expectedFitsU32 : expectedProgram.FitsU32
  digestMatches : programDigest = expectedProgram.digest

/-- A Gnark-certified BLS12-381 outer verification witness. -/
structure Bls12381GnarkOuterAccepted (vk : Bls12381GnarkVerifyingKey)
    (inp : Bls12381OuterInputs) (PairingCheck : Bls12381OuterOutputs → Prop) where
  outerProgram : Bls12381OuterProgram
  outerFitsU32 : outerProgram.FitsU32
  vkDigestEq : outerProgram.digest = vk.programDigest
  outputs : Bls12381OuterOutputs
  programSat : outerProgram.Satisfied inp outputs
  pairingHolds : PairingCheck outputs

/-- **BLS12-381 Outer-Relation Soundness (`bls12381_gnark_outer_relation_sound`)**. -/
theorem bls12381_gnark_outer_relation_sound
    {vk : Bls12381GnarkVerifyingKey} {inp : Bls12381OuterInputs}
    {PairingCheck : Bls12381OuterOutputs → Prop}
    (acc : Bls12381GnarkOuterAccepted vk inp PairingCheck) :
    (acc.outerProgram.encode ≠ vk.expectedProgram.encode ∧
      Blake3.Pure.digest acc.outerProgram.encode = Blake3.Pure.digest vk.expectedProgram.encode) ∨
    (∃ out, vk.expectedProgram.Satisfied inp out ∧ PairingCheck out) := by
  by_cases henc : acc.outerProgram.encode = vk.expectedProgram.encode
  · right
    have hprog : acc.outerProgram = vk.expectedProgram :=
      Bls12381OuterProgram.encode_injective acc.outerFitsU32 vk.expectedFitsU32 henc
    exact ⟨acc.outputs, hprog ▸ acc.programSat, acc.pairingHolds⟩
  · left
    refine ⟨henc, ?_⟩
    have hdig : acc.outerProgram.digest = vk.expectedProgram.digest :=
      acc.vkDigestEq.trans vk.digestMatches
    unfold Bls12381OuterProgram.digest at hdig
    exact Vector.ext fun i hi => by
      have := congrArg (fun l => l[i]?) hdig
      simpa [Vector.getElem?_toList, hi] using this

/-! ## 5. Subgroup-Enforced Folded BLS12-381 Pairing Check Soundness -/

/-- Abstract BLS12-381 optimal Ate bilinear pairing `(G1, G2, GT, e)` of prime subgroup order
`bls12381FrModulus`, with an **explicit prime-order $G_1$ subgroup predicate `InPrimeSubgroupG1`**
required for bilinearity (modeling EIP-2537 and `tools/gnark/curve_bls.go:71`). -/
structure Bls12381BilinearPairing where
  G1 : Type
  G2 : Type
  GT : Type
  [g1AddCommGroup : AddCommGroup G1]
  [gtCommGroup : CommGroup GT]
  [g2DecEq : DecidableEq G2]
  [gtDecEq : DecidableEq GT]
  InPrimeSubgroupG1 : G1 → Prop
  [inSubgroupDec : DecidablePred InPrimeSubgroupG1]
  inSubgroup_zero : InPrimeSubgroupG1 0
  inSubgroup_add : ∀ {P Q}, InPrimeSubgroupG1 P → InPrimeSubgroupG1 Q → InPrimeSubgroupG1 (P + Q)
  inSubgroup_neg : ∀ {P}, InPrimeSubgroupG1 P → InPrimeSubgroupG1 (-P)
  smul : BLS12381Fr → G1 → G1
  inSubgroup_smul : ∀ (ρ : BLS12381Fr) {P}, InPrimeSubgroupG1 P → InPrimeSubgroupG1 (smul ρ P)
  e : G1 → G2 → GT
  e_add : ∀ {P Q} (H : G2), InPrimeSubgroupG1 P → InPrimeSubgroupG1 Q →
    e (P + Q) H = e P H * e Q H
  e_smul : ∀ (ρ : BLS12381Fr) {P} (H : G2), InPrimeSubgroupG1 P →
    e (smul ρ P) H = (e P H) ^ ρ.val
  gt_pow_order : ∀ x : GT, x ^ bls12381FrModulus = 1

attribute [instance] Bls12381BilinearPairing.g1AddCommGroup Bls12381BilinearPairing.gtCommGroup
  Bls12381BilinearPairing.g2DecEq Bls12381BilinearPairing.gtDecEq
  Bls12381BilinearPairing.inSubgroupDec

/-- Outer BLS12-381 KZG opening pairing value `e(left, h) * e(-right, tauH)` in `GT`. -/
def Bls12381BilinearPairing.outerPairingVal (bp : Bls12381BilinearPairing)
    (outerKeys : bp.G2 × bp.G2) (left right : bp.G1) : bp.GT :=
  bp.e left outerKeys.1 * bp.e (-right) outerKeys.2

/-- Deferred inner BLS12-381 KZG opening pairing value `e(d0, ih) * e(d1, itauH)` in `GT`. -/
def Bls12381BilinearPairing.deferredPairingVal (bp : Bls12381BilinearPairing)
    (deferredKeys : bp.G2 × bp.G2) (d0 d1 : bp.G1) : bp.GT :=
  bp.e d0 deferredKeys.1 * bp.e d1 deferredKeys.2

/-- All four outer and deferred $G_1$ inputs lie in the prime-order subgroup $G_1$. -/
def Bls12381BilinearPairing.AllInPrimeSubgroupG1 (bp : Bls12381BilinearPairing)
    (left right d0 d1 : bp.G1) : Prop :=
  bp.InPrimeSubgroupG1 left ∧
  bp.InPrimeSubgroupG1 right ∧
  bp.InPrimeSubgroupG1 d0 ∧
  bp.InPrimeSubgroupG1 d1

instance (bp : Bls12381BilinearPairing) (left right d0 d1 : bp.G1) :
    Decidable (bp.AllInPrimeSubgroupG1 left right d0 d1) := by
  unfold Bls12381BilinearPairing.AllInPrimeSubgroupG1
  infer_instance

/-- **Subgroup-Enforced Folded BLS12-381 Pairing Check (`Bls12381FoldedPairingCheck`):**
Explicitly requires `bp.AllInPrimeSubgroupG1 left right d0 d1` BEFORE checking the folded
pairing equation (2-pair fast path when `outerKeys = deferredKeys`, 4-pair fallback otherwise). -/
def Bls12381FoldedPairingCheck (bp : Bls12381BilinearPairing)
    (outerKeys deferredKeys : bp.G2 × bp.G2)
    (left right d0 d1 : bp.G1) (ρ : BLS12381Fr) : Prop :=
  bp.AllInPrimeSubgroupG1 left right d0 d1 ∧
  (if outerKeys = deferredKeys then
    bp.e (left + bp.smul ρ d0) outerKeys.1 *
      bp.e (-right + bp.smul ρ d1) outerKeys.2 = 1
  else
    bp.e left outerKeys.1 * bp.e (-right) outerKeys.2 *
      bp.e (bp.smul ρ d0) deferredKeys.1 *
      bp.e (bp.smul ρ d1) deferredKeys.2 = 1)

instance (bp : Bls12381BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
    (left right d0 d1 : bp.G1) (ρ : BLS12381Fr) :
    Decidable (Bls12381FoldedPairingCheck bp outerKeys deferredKeys left right d0 d1 ρ) := by
  unfold Bls12381FoldedPairingCheck
  infer_instance

/-- Deterministic rejection of any non-subgroup $G_1$ input on `Bls12381FoldedPairingCheck`. -/
theorem bls12381_foldedPairingCheck_rejects_nonSubgroup (bp : Bls12381BilinearPairing)
    (outerKeys deferredKeys : bp.G2 × bp.G2)
    (left right d0 d1 : bp.G1) (ρ : BLS12381Fr)
    (hBad : ¬ bp.AllInPrimeSubgroupG1 left right d0 d1) :
    ¬ Bls12381FoldedPairingCheck bp outerKeys deferredKeys left right d0 d1 ρ :=
  fun h => hBad h.1

/-- Both branches of `Bls12381FoldedPairingCheck` reduce algebraically to
`AllInPrimeSubgroupG1 ∧ A * B ^ ρ.val = 1`. -/
theorem bls12381_foldedPairingCheck_iff (bp : Bls12381BilinearPairing)
    (outerKeys deferredKeys : bp.G2 × bp.G2)
    (left right d0 d1 : bp.G1) (ρ : BLS12381Fr) :
    Bls12381FoldedPairingCheck bp outerKeys deferredKeys left right d0 d1 ρ ↔
      bp.AllInPrimeSubgroupG1 left right d0 d1 ∧
      bp.outerPairingVal outerKeys left right *
        (bp.deferredPairingVal deferredKeys d0 d1) ^ ρ.val = 1 := by
  unfold Bls12381FoldedPairingCheck Bls12381BilinearPairing.outerPairingVal
    Bls12381BilinearPairing.deferredPairingVal
  constructor
  · rintro ⟨hSub, hEq⟩
    refine ⟨hSub, ?_⟩
    obtain ⟨hL, hR, hD0, hD1⟩ := hSub
    split_ifs at hEq with hkeys
    · subst hkeys
      rw [bp.e_add outerKeys.1 hL (bp.inSubgroup_smul ρ hD0),
        bp.e_add outerKeys.2 (bp.inSubgroup_neg hR) (bp.inSubgroup_smul ρ hD1),
        bp.e_smul ρ outerKeys.1 hD0,
        bp.e_smul ρ outerKeys.2 hD1] at hEq
      rw [mul_pow]
      have hrearr :
          (bp.e left outerKeys.1 * bp.e d0 outerKeys.1 ^ ρ.val) *
            (bp.e (-right) outerKeys.2 * bp.e d1 outerKeys.2 ^ ρ.val) =
          (bp.e left outerKeys.1 * bp.e (-right) outerKeys.2) *
            (bp.e d0 outerKeys.1 ^ ρ.val * bp.e d1 outerKeys.2 ^ ρ.val) := by ac_rfl
      rwa [hrearr] at hEq
    · rw [bp.e_smul ρ deferredKeys.1 hD0, bp.e_smul ρ deferredKeys.2 hD1] at hEq
      rw [mul_pow]
      have hrearr :
          bp.e left outerKeys.1 * bp.e (-right) outerKeys.2 *
            bp.e d0 deferredKeys.1 ^ ρ.val * bp.e d1 deferredKeys.2 ^ ρ.val =
          (bp.e left outerKeys.1 * bp.e (-right) outerKeys.2) *
            (bp.e d0 deferredKeys.1 ^ ρ.val * bp.e d1 deferredKeys.2 ^ ρ.val) := by ac_rfl
      rwa [hrearr] at hEq
  · rintro ⟨hSub, hEq⟩
    refine ⟨hSub, ?_⟩
    obtain ⟨hL, hR, hD0, hD1⟩ := hSub
    split_ifs with hkeys
    · subst hkeys
      rw [bp.e_add outerKeys.1 hL (bp.inSubgroup_smul ρ hD0),
        bp.e_add outerKeys.2 (bp.inSubgroup_neg hR) (bp.inSubgroup_smul ρ hD1),
        bp.e_smul ρ outerKeys.1 hD0,
        bp.e_smul ρ outerKeys.2 hD1]
      rw [mul_pow] at hEq
      have hrearr :
          (bp.e left outerKeys.1 * bp.e d0 outerKeys.1 ^ ρ.val) *
            (bp.e (-right) outerKeys.2 * bp.e d1 outerKeys.2 ^ ρ.val) =
          (bp.e left outerKeys.1 * bp.e (-right) outerKeys.2) *
            (bp.e d0 outerKeys.1 ^ ρ.val * bp.e d1 outerKeys.2 ^ ρ.val) := by ac_rfl
      rw [hrearr]
      exact hEq
    · rw [bp.e_smul ρ deferredKeys.1 hD0, bp.e_smul ρ deferredKeys.2 hD1]
      rw [mul_pow] at hEq
      have hrearr :
          bp.e left outerKeys.1 * bp.e (-right) outerKeys.2 *
            bp.e d0 deferredKeys.1 ^ ρ.val * bp.e d1 deferredKeys.2 ^ ρ.val =
          (bp.e left outerKeys.1 * bp.e (-right) outerKeys.2) *
            (bp.e d0 deferredKeys.1 ^ ρ.val * bp.e d1 deferredKeys.2 ^ ρ.val) := by ac_rfl
      rw [hrearr]
      exact hEq

/-- **Prime-Order Folded Pairing Soundness over `BLS12381Fr` (`bls12381_folded_pairing_bad_card`):**
In any commutative group `GT` of prime exponent `r = bls12381FrModulus`, if `¬ (A = 1 ∧ B = 1)`,
at most one challenge `ρ ∈ BLS12381Fr` satisfies `A * B ^ ρ.val = 1` (soundness error `≤ 1 / r`). -/
theorem bls12381_folded_pairing_bad_card {GT : Type} [CommGroup GT] [DecidableEq GT]
    (hExp : ∀ x : GT, x ^ bls12381FrModulus = 1)
    {A B : GT} (hfail : ¬ (A = 1 ∧ B = 1)) :
    (Finset.univ.filter fun ρ : BLS12381Fr => A * B ^ ρ.val = 1).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro ρ₁ hρ₁ ρ₂ hρ₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ₁ hρ₂
  by_cases hB : B = 1
  · subst hB
    simp only [one_pow, mul_one] at hρ₁
    exact absurd ⟨hρ₁, rfl⟩ hfail
  · have hpow_eq : B ^ ρ₁.val = B ^ ρ₂.val :=
      mul_left_cancel (hρ₁.trans hρ₂.symm)
    have hle_imp_eq : ∀ {x y : BLS12381Fr}, x.val ≤ y.val → B ^ x.val = B ^ y.val → x = y := by
      intro x y hle heq
      change ZMod.val x ≤ ZMod.val y at hle
      set d := ZMod.val y - ZMod.val x
      have hd_lt : d < bls12381FrModulus := by
        have hy := ZMod.val_lt y
        omega
      have hsum : ZMod.val x + d = ZMod.val y := Nat.add_sub_of_le hle
      have hBd : B ^ d = 1 := by
        have h1 : B ^ ZMod.val x * B ^ d = B ^ ZMod.val x * 1 := by
          rw [← pow_add, hsum, mul_one, heq]
        exact mul_left_cancel h1
      by_cases hd0 : d = 0
      · exact ZMod.val_injective bls12381FrModulus (by omega)
      · have hd_cast_ne : (d : BLS12381Fr) ≠ 0 := by
          intro hzero
          have hval : ZMod.val (d : BLS12381Fr) = 0 := by rw [hzero, ZMod.val_zero]
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt hd_lt] at hval
          exact hd0 hval
        set inv : BLS12381Fr := (d : BLS12381Fr)⁻¹
        have hmul1 : (d : BLS12381Fr) * inv = 1 := mul_inv_cancel₀ hd_cast_ne
        have hmod1 : (d * ZMod.val inv) % bls12381FrModulus = 1 := by
          have hcast : ((d * ZMod.val inv : Nat) : BLS12381Fr) = 1 := by
            push_cast
            rw [ZMod.natCast_zmod_val, hmul1]
          have hval := congrArg ZMod.val hcast
          rw [ZMod.val_natCast, ZMod.val_one] at hval
          exact hval
        have hdivmod :
            bls12381FrModulus * (d * ZMod.val inv / bls12381FrModulus) + 1 = d * ZMod.val inv := by
          have h := Nat.div_add_mod (d * ZMod.val inv) bls12381FrModulus
          rw [hmod1] at h
          exact h
        have hB1 : B = 1 := by
          calc B = B ^ 1 := (pow_one B).symm
            _ = (B ^ bls12381FrModulus) ^ (d * ZMod.val inv / bls12381FrModulus) * B ^ 1 := by
                rw [hExp B, one_pow, one_mul]
            _ = B ^ (bls12381FrModulus * (d * ZMod.val inv / bls12381FrModulus) + 1) := by
                rw [pow_add, pow_mul]
            _ = B ^ (d * ZMod.val inv) := by rw [hdivmod]
            _ = (B ^ d) ^ ZMod.val inv := by rw [pow_mul]
            _ = 1 := by rw [hBd, one_pow]
        exact absurd hB1 hB
    rcases le_total ρ₁.val ρ₂.val with hle | hle
    · exact hle_imp_eq hle hpow_eq
    · exact (hle_imp_eq hle hpow_eq.symm).symm

/-- **Folded Pairing Soundness for `Bls12381FoldedPairingCheck` (`bls12381_foldedPairingCheck_bad_card`):**
If ANY subgroup check fails OR either pairing equation fails, at most one challenge `ρ ∈ BLS12381Fr`
makes `Bls12381FoldedPairingCheck` accept (in fact `0` if any subgroup check fails!). -/
theorem bls12381_foldedPairingCheck_bad_card (bp : Bls12381BilinearPairing)
    (outerKeys deferredKeys : bp.G2 × bp.G2)
    (left right d0 d1 : bp.G1)
    (hfail : ¬ (bp.AllInPrimeSubgroupG1 left right d0 d1 ∧
      bp.outerPairingVal outerKeys left right = 1 ∧
      bp.deferredPairingVal deferredKeys d0 d1 = 1)) :
    (Finset.univ.filter fun ρ : BLS12381Fr =>
      Bls12381FoldedPairingCheck bp outerKeys deferredKeys left right d0 d1 ρ).card ≤ 1 := by
  by_cases hSub : bp.AllInPrimeSubgroupG1 left right d0 d1
  · have hpairFail : ¬ (bp.outerPairingVal outerKeys left right = 1 ∧
        bp.deferredPairingVal deferredKeys d0 d1 = 1) :=
      fun h => hfail ⟨hSub, h⟩
    have hfilt :
        (Finset.univ.filter fun ρ : BLS12381Fr =>
          Bls12381FoldedPairingCheck bp outerKeys deferredKeys left right d0 d1 ρ) =
        (Finset.univ.filter fun ρ : BLS12381Fr =>
          bp.outerPairingVal outerKeys left right *
            (bp.deferredPairingVal deferredKeys d0 d1) ^ ρ.val = 1) := by
      ext ρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        bls12381_foldedPairingCheck_iff, hSub]
    rw [hfilt]
    exact bls12381_folded_pairing_bad_card bp.gt_pow_order hpairFail
  · have hempty :
        (Finset.univ.filter fun ρ : BLS12381Fr =>
          Bls12381FoldedPairingCheck bp outerKeys deferredKeys left right d0 d1 ρ) = ∅ := by
      ext ρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact bls12381_foldedPairingCheck_rejects_nonSubgroup bp outerKeys deferredKeys
        left right d0 d1 ρ hSub
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le 1

/-- **Gnark BLS12-381 Outer-Relation + Subgroup-Enforced Folded Pairing Soundness
(`bls12381_gnark_folded_pairing_sound`):**
An accepting Gnark final proof implies EITHER a BLAKE3 collision on `"ix/outer-ir/v1"`,
OR `vk.expectedProgram` is satisfied on `inp` with outputs `out` such that ALL FOUR $G_1$
inputs satisfy `InPrimeSubgroupG1` AND EITHER both individual BLS12-381 pairing checks hold
(`outer = 1 ∧ deferred = 1`) OR `ρ` landed in a bad set of size `≤ 1` out of `bls12381FrModulus`. -/
theorem bls12381_gnark_folded_pairing_sound
    {vk : Bls12381GnarkVerifyingKey} {inp : Bls12381OuterInputs}
    (bp : Bls12381BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
    (leftOf rightOf : Bls12381OuterOutputs → bp.G1) (d0 d1 : bp.G1) (ρ : BLS12381Fr)
    (acc : Bls12381GnarkOuterAccepted vk inp
      (fun out => Bls12381FoldedPairingCheck bp outerKeys deferredKeys
        (leftOf out) (rightOf out) d0 d1 ρ)) :
    (acc.outerProgram.encode ≠ vk.expectedProgram.encode ∧
      Blake3.Pure.digest acc.outerProgram.encode = Blake3.Pure.digest vk.expectedProgram.encode) ∨
    (∃ out, vk.expectedProgram.Satisfied inp out ∧
      bp.AllInPrimeSubgroupG1 (leftOf out) (rightOf out) d0 d1 ∧
      ((bp.outerPairingVal outerKeys (leftOf out) (rightOf out) = 1 ∧
        bp.deferredPairingVal deferredKeys d0 d1 = 1) ∨
       (Bls12381FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ ∧
        (Finset.univ.filter fun ρ' : BLS12381Fr =>
          Bls12381FoldedPairingCheck bp outerKeys deferredKeys
            (leftOf out) (rightOf out) d0 d1 ρ').card ≤ 1))) := by
  rcases bls12381_gnark_outer_relation_sound acc with hCol | ⟨out, hsat, hfold⟩
  · exact Or.inl hCol
  · right
    have hSub : bp.AllInPrimeSubgroupG1 (leftOf out) (rightOf out) d0 d1 := hfold.1
    refine ⟨out, hsat, hSub, ?_⟩
    by_cases hboth : bp.outerPairingVal outerKeys (leftOf out) (rightOf out) = 1 ∧
        bp.deferredPairingVal deferredKeys d0 d1 = 1
    · exact Or.inl hboth
    · exact Or.inr ⟨hfold, bls12381_foldedPairingCheck_bad_card bp outerKeys deferredKeys
        (leftOf out) (rightOf out) d0 d1 (fun h => hboth h.2)⟩

end Ix.Cert.Compression.Bls12381.OuterRelation
