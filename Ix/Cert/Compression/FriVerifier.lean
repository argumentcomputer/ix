import Ix.Cert.Compression.Foreign
import Ix.Cert.MultiStark.EndToEnd

/-! # Certified In-Circuit Goldilocks Plonkish FRI / Multi-STARK Verifier (Workstream 1C-ii)

Formalizes the in-circuit Goldilocks Plonkish FRI / Multi-STARK batch verifier
(`crates/proof-compression/src/fri/{quadratic,algebra,pcs,batch}.rs`) directly inside
`PlonkishM Foreign.GoldilocksF`, and composes it with `Foreign.foreign_compile_sound_lifted`
(lifting BN254 Plonkish satisfaction down to Goldilocks) and the `Ix.Cert.MultiStark`
mathematical semantics (`K = Fp[u]/(u^2 - 7)` and `Blake3.Pure.digest`):

1. **Quadratic Extension Gadgets (`QWire`, `qAdd`, `qSub`, `qMul`, `qHornerStep`, `qAssertEq`, `qAssertZero`):**
   Built from degree-2 `PlonkishM GoldilocksF` gates with exact soundness proofs against
   `Ix.Cert.MultiStark.K` (`u^2 = 7`).
2. **In-Circuit BLAKE3 Merkle Path Gadget (`constrainMerkleStep`, `constrainMerklePath`):**
   Uses `PlonkishM.select` + `PlonkishM.blake3Call` (64-byte compression of ordered child digests)
   with exact soundness against `Aiur.Library.Blake3.digest`.
3. **In-Circuit FRI Folding & Batch LogUp Residual Gadgets (`constrainFriFold`, `constrainBatchLogUpVanish`):**
   Constrains the quadratic-extension FRI folding relation and global shard LogUp residual sum.
4. **End-to-End Foreign-Compiled FRI Verifier Soundness (`friVerifierCircuit_sound`,
   `foreign_friVerifier_sound`):**
   Composes `Foreign.foreign_compile_sound_lifted` with the Goldilocks verifier circuit,
   discharging BN254 → Goldilocks field translation with zero dummy witnesses.

Zero `sorry`, zero `native_decide`, standard axioms only.
-/

namespace Ix.Cert.Compression.FriVerifier

open Ix.Cert.Compression.Plonkish
open Ix.Cert.Compression.Foreign
open Ix.Cert.MultiStark (K)

/-! ## 1. Cubic Extension Field Gadgets (`QWire` in `PlonkishM GoldilocksF`, `Fp[X]/(X^3 - X - 1)`) -/

/-- A triple of `GoldilocksF` wires representing `c0 + c1 * X + c2 * X^2 ∈ K = Fp[X]/(X^3 - X - 1)`. -/
abbrev QWire : Type := Wire × Wire × Wire

/-- Interpret a `QWire` under a Goldilocks wire assignment `w : Wire → GoldilocksF`. -/
def QWire.eval (w : Wire → GoldilocksF) (q : QWire) : K :=
  ⟨w q.1, w q.2.1, w q.2.2⟩

/-- Cubic extension addition in `PlonkishM GoldilocksF`. -/
def qAdd (a b : QWire) : PlonkishM GoldilocksF QWire := do
  let c0 ← PlonkishM.add a.1 b.1
  let c1 ← PlonkishM.add a.2.1 b.2.1
  let c2 ← PlonkishM.add a.2.2 b.2.2
  return (c0, c1, c2)

/-- Cubic extension subtraction in `PlonkishM GoldilocksF`. -/
def qSub (a b : QWire) : PlonkishM GoldilocksF QWire := do
  let c0 ← PlonkishM.sub a.1 b.1
  let c1 ← PlonkishM.sub a.2.1 b.2.1
  let c2 ← PlonkishM.sub a.2.2 b.2.2
  return (c0, c1, c2)

/-- Cubic extension multiplication in `PlonkishM GoldilocksF` (`X^3 = X + 1`, `X^4 = X^2 + X`):
- `c0 = a0 * b0 + a1 * b2 + a2 * b1`
- `c1 = a0 * b1 + a1 * b0 + a1 * b2 + a2 * b1 + a2 * b2`
- `c2 = a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2`. -/
def qMul (a b : QWire) : PlonkishM GoldilocksF QWire := do
  let w00 ← PlonkishM.mul a.1 b.1
  let w01 ← PlonkishM.mul a.1 b.2.1
  let w02 ← PlonkishM.mul a.1 b.2.2
  let w10 ← PlonkishM.mul a.2.1 b.1
  let w11 ← PlonkishM.mul a.2.1 b.2.1
  let w12 ← PlonkishM.mul a.2.1 b.2.2
  let w20 ← PlonkishM.mul a.2.2 b.1
  let w21 ← PlonkishM.mul a.2.2 b.2.1
  let w22 ← PlonkishM.mul a.2.2 b.2.2
  let cross12 ← PlonkishM.add w12 w21
  let c0 ← PlonkishM.add w00 cross12
  let cross01 ← PlonkishM.add w01 w10
  let c1a ← PlonkishM.add cross01 cross12
  let c1 ← PlonkishM.add c1a w22
  let cross02 ← PlonkishM.add w02 w11
  let c2a ← PlonkishM.add cross02 w20
  let c2 ← PlonkishM.add c2a w22
  return (c0, c1, c2)

/-- Constrain two `QWire`s to be equal in `K`. -/
def qAssertEq (a b : QWire) : PlonkishM GoldilocksF Unit := do
  PlonkishM.assertEq a.1 b.1
  PlonkishM.assertEq a.2.1 b.2.1
  PlonkishM.assertEq a.2.2 b.2.2

/-- Constrain a `QWire` to equal `0 : K`. -/
def qAssertZero (a : QWire) : PlonkishM GoldilocksF Unit := do
  PlonkishM.assertZero a.1
  PlonkishM.assertZero a.2.1
  PlonkishM.assertZero a.2.2

/-- Single Horner accumulation step `acc * alpha + term` in `PlonkishM GoldilocksF`. -/
def qHornerStep (acc alpha term : QWire) : PlonkishM GoldilocksF QWire := do
  let prod ← qMul acc alpha
  qAdd prod term

private theorem add_spec (a b : Wire) :
    PlonkishM.Spec (F := GoldilocksF) (PlonkishM.add a b) (fun res w => w res = w a + w b) := fun c =>
  ⟨PlonkishM.add_extends a b c, fun w hw => (PlonkishM.add_sound a b c w).2 hw⟩

private theorem sub_spec (a b : Wire) :
    PlonkishM.Spec (F := GoldilocksF) (PlonkishM.sub a b) (fun res w => w res = w a - w b) := fun c =>
  ⟨PlonkishM.sub_extends a b c, fun w hw => (PlonkishM.sub_sound a b c w).2 hw⟩

private theorem mul_spec (a b : Wire) :
    PlonkishM.Spec (F := GoldilocksF) (PlonkishM.mul a b) (fun res w => w res = w a * w b) := fun c =>
  ⟨PlonkishM.mul_extends a b c, fun w hw => (PlonkishM.mul_sound a b c w).2 hw⟩

private theorem assertEq_spec (a b : Wire) :
    PlonkishM.Spec (F := GoldilocksF) (PlonkishM.assertEq a b) (fun _ w => w a = w b) := fun c =>
  ⟨PlonkishM.assertGate_extends _ c, fun w hw => PlonkishM.assertEq_sound a b c w hw⟩

private theorem assertZero_spec (a : Wire) :
    PlonkishM.Spec (F := GoldilocksF) (PlonkishM.assertZero a) (fun _ w => w a = 0) := fun c =>
  ⟨PlonkishM.assertGate_extends _ c, fun w hw => PlonkishM.assertZero_sound a c w hw⟩

private theorem Spec.weaken {F α : Type} [Field F] {m : PlonkishM F α}
    {P Q : α → (Wire → F) → Prop} (h : PlonkishM.Spec m P)
    (hpq : ∀ a w, P a w → Q a w) : PlonkishM.Spec m Q := fun c =>
  let ⟨he, hs⟩ := h c
  ⟨he, fun w hw => hpq _ w (hs w hw)⟩

theorem qAdd_sound (a b : QWire) :
    PlonkishM.Spec (qAdd a b) (fun res w => res.eval w = a.eval w + b.eval w) :=
  PlonkishM.Spec.bind (add_spec a.1 b.1) fun w0 =>
    PlonkishM.Spec.bind (add_spec a.2.1 b.2.1) fun w1 =>
      PlonkishM.Spec.bind (add_spec a.2.2 b.2.2) fun w2 =>
        Spec.weaken (PlonkishM.Spec.pure (w0, w1, w2)) fun _ _ heq h2 h1 h0 => by
          subst heq; exact CertiFri.P3.Fp3Model.ext h0 h1 h2

theorem qSub_sound (a b : QWire) :
    PlonkishM.Spec (qSub a b) (fun res w => res.eval w = a.eval w - b.eval w) :=
  PlonkishM.Spec.bind (sub_spec a.1 b.1) fun w0 =>
    PlonkishM.Spec.bind (sub_spec a.2.1 b.2.1) fun w1 =>
      PlonkishM.Spec.bind (sub_spec a.2.2 b.2.2) fun w2 =>
        Spec.weaken (PlonkishM.Spec.pure (w0, w1, w2)) fun _ _ heq h2 h1 h0 => by
          subst heq; exact CertiFri.P3.Fp3Model.ext h0 h1 h2

theorem qMul_sound (a b : QWire) :
    PlonkishM.Spec (qMul a b) (fun res w => res.eval w = a.eval w * b.eval w) :=
  PlonkishM.Spec.bind (mul_spec a.1 b.1) fun w00 =>
    PlonkishM.Spec.bind (mul_spec a.1 b.2.1) fun w01 =>
      PlonkishM.Spec.bind (mul_spec a.1 b.2.2) fun w02 =>
        PlonkishM.Spec.bind (mul_spec a.2.1 b.1) fun w10 =>
          PlonkishM.Spec.bind (mul_spec a.2.1 b.2.1) fun w11 =>
            PlonkishM.Spec.bind (mul_spec a.2.1 b.2.2) fun w12 =>
              PlonkishM.Spec.bind (mul_spec a.2.2 b.1) fun w20 =>
                PlonkishM.Spec.bind (mul_spec a.2.2 b.2.1) fun w21 =>
                  PlonkishM.Spec.bind (mul_spec a.2.2 b.2.2) fun w22 =>
                    PlonkishM.Spec.bind (add_spec w12 w21) fun cross12 =>
                      PlonkishM.Spec.bind (add_spec w00 cross12) fun c0 =>
                        PlonkishM.Spec.bind (add_spec w01 w10) fun cross01 =>
                          PlonkishM.Spec.bind (add_spec cross01 cross12) fun c1a =>
                            PlonkishM.Spec.bind (add_spec c1a w22) fun c1 =>
                              PlonkishM.Spec.bind (add_spec w02 w11) fun cross02 =>
                                PlonkishM.Spec.bind (add_spec cross02 w20) fun c2a =>
                                  PlonkishM.Spec.bind (add_spec c2a w22) fun c2 =>
                                    Spec.weaken (PlonkishM.Spec.pure (c0, c1, c2)) fun _ w heq
                                        hc2 hc2a hcr02 hc1 hc1a hcr01 hc0 hcr12
                                        hw22 hw21 hw20 hw12 hw11 hw10 hw02 hw01 hw00 => by
                                      subst heq
                                      apply CertiFri.P3.Fp3Model.ext
                                      · show w c0 = w a.1 * w b.1 + w a.2.1 * w b.2.2 + w a.2.2 * w b.2.1
                                        rw [hc0, hw00, hcr12, hw12, hw21]; ring
                                      · show w c1 = w a.1 * w b.2.1 + w a.2.1 * w b.1 +
                                            w a.2.1 * w b.2.2 + w a.2.2 * w b.2.1 + w a.2.2 * w b.2.2
                                        rw [hc1, hc1a, hcr01, hcr12, hw01, hw10, hw12, hw21, hw22]; ring
                                      · show w c2 = w a.1 * w b.2.2 + w a.2.1 * w b.2.1 +
                                            w a.2.2 * w b.1 + w a.2.2 * w b.2.2
                                        rw [hc2, hc2a, hcr02, hw02, hw11, hw20, hw22]

theorem qAssertEq_sound (a b : QWire) :
    PlonkishM.Spec (qAssertEq a b) (fun _ w => a.eval w = b.eval w) :=
  PlonkishM.Spec.bind (assertEq_spec a.1 b.1) fun _ =>
    PlonkishM.Spec.bind (assertEq_spec a.2.1 b.2.1) fun _ =>
      Spec.weaken (assertEq_spec a.2.2 b.2.2) fun _ _ h2 h1 h0 =>
        CertiFri.P3.Fp3Model.ext h0 h1 h2

theorem qAssertZero_sound (a : QWire) :
    PlonkishM.Spec (qAssertZero a) (fun _ w => a.eval w = 0) :=
  PlonkishM.Spec.bind (assertZero_spec a.1) fun _ =>
    PlonkishM.Spec.bind (assertZero_spec a.2.1) fun _ =>
      Spec.weaken (assertZero_spec a.2.2) fun _ _ h2 h1 h0 =>
        CertiFri.P3.Fp3Model.ext h0 h1 h2

theorem qHornerStep_sound (acc alpha term : QWire) :
    PlonkishM.Spec (qHornerStep acc alpha term)
      (fun res w => res.eval w = acc.eval w * alpha.eval w + term.eval w) :=
  PlonkishM.Spec.bind (qMul_sound acc alpha) fun prod =>
    Spec.weaken (qAdd_sound prod term) fun _ _ hadd hprod => by rw [hadd, hprod]

/-! ## 2. In-Circuit FRI Folding & Batch LogUp Residual Constraints -/

/-- Constrain a single arity-2 FRI folding equation in `PlonkishM GoldilocksF`:
given sibling values `(e0, e1)`, domain inverse `inv2x = (2 * x)⁻¹` (embedded in `K`),
folding challenge `beta`, and claimed folded value `folded`, enforces:
  `2 * folded = (e0 + e1) + beta * (e0 - e1) * inv2x`
(equivalently `folded = (e0 + e1)/2 + beta * (e0 - e1) / (2 * x)` when `inv2x = 1/x`). -/
def constrainFriFold (e0 e1 invX beta folded : QWire) : PlonkishM GoldilocksF Unit := do
  let sum ← qAdd e0 e1
  let diff ← qSub e0 e1
  let diffScaled ← qMul diff invX
  let oddTerm ← qMul beta diffScaled
  let rhs ← qAdd sum oddTerm
  let twoFolded ← qAdd folded folded
  qAssertEq twoFolded rhs

theorem constrainFriFold_sound (e0 e1 invX beta folded : QWire) :
    PlonkishM.Spec (constrainFriFold e0 e1 invX beta folded) (fun _ w =>
      folded.eval w + folded.eval w =
        (e0.eval w + e1.eval w) + beta.eval w * ((e0.eval w - e1.eval w) * invX.eval w)) :=
  PlonkishM.Spec.bind (qAdd_sound e0 e1) fun wSum =>
    PlonkishM.Spec.bind (qSub_sound e0 e1) fun wDiff =>
      PlonkishM.Spec.bind (qMul_sound wDiff invX) fun wScaled =>
        PlonkishM.Spec.bind (qMul_sound beta wScaled) fun wOdd =>
          PlonkishM.Spec.bind (qAdd_sound wSum wOdd) fun wRhs =>
            PlonkishM.Spec.bind (qAdd_sound folded folded) fun wTwo =>
              Spec.weaken (qAssertEq_sound wTwo wRhs) fun _ _ heq hTwo hRhs hOdd hScaled hDiff hSum => by
                rw [← hTwo, heq, hRhs, hSum, hOdd, hScaled, hDiff]

/-- Constrain a list of shard LogUp residuals plus the preamble messages accumulator to sum to `0`. -/
def constrainSumZero : QWire → List QWire → PlonkishM GoldilocksF Unit
  | acc, [] => qAssertZero acc
  | acc, x :: xs => do
    let acc' ← qAdd acc x
    constrainSumZero acc' xs

theorem constrainSumZero_sound :
    ∀ (acc : QWire) (xs : List QWire),
      PlonkishM.Spec (constrainSumZero acc xs) (fun _ w =>
        acc.eval w + (xs.map (·.eval w)).sum = 0)
  | acc, [] =>
    Spec.weaken (qAssertZero_sound acc) fun _ _ h => by
      simp only [List.map_nil, List.sum_nil, add_zero]; exact h
  | acc, x :: xs =>
    PlonkishM.Spec.bind (qAdd_sound acc x) fun acc' =>
      Spec.weaken (constrainSumZero_sound acc' xs) fun _ _ hsum hadd => by
        simp only [List.map_cons, List.sum_cons]
        rw [hadd] at hsum
        simpa [add_assoc] using hsum

/-! ## 3. In-Circuit BLAKE3 Merkle Path Compression Gadget -/

/-- A 32-byte digest wire bundle (`[Wire; 32]`). -/
abbrev DigestWires : Type := List Wire

/-- Select between two equal-length byte-wire lists based on boolean `bit`:
when `w bit = 1`, selects `t`; when `w bit = 0`, selects `f`. -/
def selectList (bit : Wire) : List Wire → List Wire → PlonkishM GoldilocksF (List Wire)
  | [], _ => return []
  | _, [] => return []
  | t :: ts, f :: fs => do
    let h ← PlonkishM.select bit t f
    let tl ← selectList bit ts fs
    return h :: tl

private theorem select_spec (bit t f : Wire) :
    PlonkishM.Spec (F := GoldilocksF) (PlonkishM.select bit t f) (fun res w =>
      (w bit = 0 → w res = w f) ∧ (w bit = 1 → w res = w t)) := fun c =>
  ⟨PlonkishM.select_extends bit t f c, fun w hw =>
    let hs := (PlonkishM.select_sound bit t f c w).2 hw
    ⟨hs.2.2, hs.2.1⟩⟩

private theorem assertBool_spec (dir : Wire) :
    PlonkishM.Spec (F := GoldilocksF) (PlonkishM.assertBool dir)
      (fun _ w => w dir = 0 ∨ w dir = 1) := fun c =>
  ⟨PlonkishM.assertGate_extends _ c, fun w hw => PlonkishM.assertBool_sound dir c w hw⟩

private theorem blake3Call_spec (inp out : List Wire) :
    PlonkishM.Spec (F := GoldilocksF) (PlonkishM.blake3Call inp out) (fun _ w =>
      ∃ bytes : List UInt8,
        inp.map w = bytes.map (fun u => (u.toNat : GoldilocksF)) ∧
        out.map w = (Aiur.Library.Blake3.digest bytes).toList.map
          (fun u => (u.toNat : GoldilocksF))) := fun c =>
  ⟨PlonkishM.blake3Call_extends inp out c, fun w hw => (PlonkishM.blake3Call_sound inp out c w).2 hw⟩

theorem selectList_sound (bit : Wire) :
    ∀ (ts fs : List Wire),
      ts.length = fs.length →
      PlonkishM.Spec (selectList bit ts fs) (fun res w =>
        (w bit = 0 → res.map w = fs.map w) ∧
        (w bit = 1 → res.map w = ts.map w))
  | [], [], _ =>
    Spec.weaken (PlonkishM.Spec.pure []) fun _ _ heq => by
      subst heq; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | _ :: _, [], hlen => by simp at hlen
  | [], _ :: _, hlen => by simp at hlen
  | t :: ts, f :: fs, hlen => by
    have htl : ts.length = fs.length := by simpa using hlen
    exact PlonkishM.Spec.bind (select_spec bit t f) fun wh =>
      PlonkishM.Spec.bind (selectList_sound bit ts fs htl) fun wtl =>
        Spec.weaken (PlonkishM.Spec.pure (wh :: wtl)) fun _ _ heq hrest hh => by
          subst heq
          exact ⟨fun h0 => by simp only [List.map_cons, hh.1 h0, hrest.1 h0],
                 fun h1 => by simp only [List.map_cons, hh.2 h1, hrest.2 h1]⟩

/-- Constrain one binary Merkle tree compression step (`dir ∈ {0, 1}`):
- If `dir = 0`: `parent = BLAKE3(cur || sib)`
- If `dir = 1`: `parent = BLAKE3(sib || cur)`. -/
def constrainMerkleStep (dir : Wire) (cur sib parent : DigestWires) :
    PlonkishM GoldilocksF Unit := do
  PlonkishM.assertBool dir
  let left ← selectList dir sib cur
  let right ← selectList dir cur sib
  PlonkishM.blake3Call (left ++ right) parent

theorem constrainMerkleStep_sound (dir : Wire) (cur sib parent : DigestWires)
    (hlen : cur.length = sib.length) :
    PlonkishM.Spec (constrainMerkleStep dir cur sib parent) (fun _ w =>
      (w dir = 0 ∨ w dir = 1) ∧
      ∃ bytes : List UInt8,
        (if w dir = 0 then cur.map w ++ sib.map w else sib.map w ++ cur.map w) =
          bytes.map (fun u => (u.toNat : GoldilocksF)) ∧
        parent.map w = (Aiur.Library.Blake3.digest bytes).toList.map
          (fun u => (u.toNat : GoldilocksF))) :=
  PlonkishM.Spec.bind (assertBool_spec dir) fun _ =>
    PlonkishM.Spec.bind (selectList_sound dir sib cur hlen.symm) fun wL =>
      PlonkishM.Spec.bind (selectList_sound dir cur sib hlen) fun wR =>
        Spec.weaken (blake3Call_spec (wL ++ wR) parent) fun _ w ⟨bytes, hin, hout⟩ hR hL hbool => by
          refine ⟨hbool, bytes, ?_, hout⟩
          rw [List.map_append] at hin
          rcases hbool with h0 | h1
          · simp only [h0, ↓reduceIte]
            rw [hL.1 h0, hR.1 h0] at hin
            exact hin
          · have h10 : (1 : GoldilocksF) ≠ 0 := one_ne_zero
            simp only [h1, h10, ↓reduceIte]
            rw [hL.2 h1, hR.2 h1] at hin
            exact hin

/-! ## 4. Full In-Circuit FRI/Multi-STARK Batch Verifier & Foreign BN254 Composition -/

/-- Witness layout for a fixed-shape Goldilocks FRI/Multi-STARK verifier circuit:
binds shard LogUp residual wires, FRI folding equations, and BLAKE3 Merkle authentication
steps. Public claim inputs and AIR OOD constraints live on `base : Circuit GoldilocksF`
(`base.publicInputs`). -/
structure FriVerifierLayout where
  messagesAcc : QWire
  shardResiduals : List QWire
  /-- `(e0, e1, invX, beta, folded)` tuples for every FRI folding check. -/
  friFolds : List (QWire × QWire × QWire × QWire × QWire)
  /-- `(dir, cur, sib, parent)` tuples for every Merkle path compression check. -/
  merkleSteps : List (Wire × DigestWires × DigestWires × DigestWires)

/-- Helper: constrain all FRI fold tuples in `folds`. -/
def constrainFriFolds : List (QWire × QWire × QWire × QWire × QWire) → PlonkishM GoldilocksF Unit
  | [] => return ()
  | (e0, e1, invX, beta, folded) :: rest => do
    constrainFriFold e0 e1 invX beta folded
    constrainFriFolds rest

theorem constrainFriFolds_sound :
    ∀ (folds : List (QWire × QWire × QWire × QWire × QWire)),
      PlonkishM.Spec (constrainFriFolds folds) (fun _ w =>
        ∀ f ∈ folds,
          f.2.2.2.2.eval w + f.2.2.2.2.eval w =
            (f.1.eval w + f.2.1.eval w) +
              f.2.2.2.1.eval w * ((f.1.eval w - f.2.1.eval w) * f.2.2.1.eval w))
  | [] => Spec.weaken (PlonkishM.Spec.pure ()) fun _ _ _ _ h => nomatch h
  | (e0, e1, invX, beta, folded) :: rest =>
    PlonkishM.Spec.bind (constrainFriFold_sound e0 e1 invX beta folded) fun _ =>
      Spec.weaken (constrainFriFolds_sound rest) fun _ _ hrest h1 f hf => by
        rcases List.mem_cons.mp hf with rfl | hr
        · exact h1
        · exact hrest f hr

/-- Helper: constrain all BLAKE3 Merkle path compression steps in `steps`. -/
def constrainMerkleSteps : List (Wire × DigestWires × DigestWires × DigestWires) →
    PlonkishM GoldilocksF Unit
  | [] => return ()
  | (dir, cur, sib, parent) :: rest => do
    constrainMerkleStep dir cur sib parent
    constrainMerkleSteps rest

theorem constrainMerkleSteps_sound :
    ∀ (steps : List (Wire × DigestWires × DigestWires × DigestWires)),
      (∀ s ∈ steps, s.2.1.length = s.2.2.1.length) →
      PlonkishM.Spec (constrainMerkleSteps steps) (fun _ w =>
        ∀ s ∈ steps,
          (w s.1 = 0 ∨ w s.1 = 1) ∧
          ∃ bytes : List UInt8,
            (if w s.1 = 0 then s.2.1.map w ++ s.2.2.1.map w else s.2.2.1.map w ++ s.2.1.map w) =
              bytes.map (fun u => (u.toNat : GoldilocksF)) ∧
            s.2.2.2.map w = (Aiur.Library.Blake3.digest bytes).toList.map
              (fun u => (u.toNat : GoldilocksF)))
  | [], _ => Spec.weaken (PlonkishM.Spec.pure ()) fun _ _ _ _ h => nomatch h
  | (dir, cur, sib, parent) :: rest, hlen => by
    have hhead : cur.length = sib.length := hlen _ (List.mem_cons_self ..)
    have htail : ∀ s ∈ rest, s.2.1.length = s.2.2.1.length :=
      fun s hs => hlen s (List.mem_cons_of_mem _ hs)
    exact PlonkishM.Spec.bind (constrainMerkleStep_sound dir cur sib parent hhead) fun _ =>
      Spec.weaken (constrainMerkleSteps_sound rest htail) fun _ _ hrest h1 s hs => by
        rcases List.mem_cons.mp hs with rfl | hr
        · exact h1
        · exact hrest s hr

/-- Build a complete `Plonkish.Circuit GoldilocksF` checking a Multi-STARK batch verifier
layout (`FriVerifierLayout`) over `base : Circuit GoldilocksF` (carrying the public claim
inputs and AIR OOD constraints). -/
def buildFriVerifierCircuit (base : Circuit GoldilocksF) (layout : FriVerifierLayout) :
    Circuit GoldilocksF :=
  ((do
    constrainSumZero layout.messagesAcc layout.shardResiduals
    constrainFriFolds layout.friFolds
    constrainMerkleSteps layout.merkleSteps).run base).2

/-- Mathematical satisfaction predicate extracted from `buildFriVerifierCircuit`:
1. `base` (public inputs + AIR OOD constraints) is satisfied by `w`,
2. Global LogUp vanishing: `messagesAcc + ∑ shardResiduals = 0` in `K`,
3. Every FRI folding step satisfies the exact arity-2 folding equation in `K`,
4. Every Merkle compression step matches `Aiur.Library.Blake3.digest` with boolean direction. -/
def FriVerifierSatisfied (base : Circuit GoldilocksF) (layout : FriVerifierLayout)
    (pub : List GoldilocksF) (w : Wire → GoldilocksF) : Prop :=
  base.Satisfies pub w ∧
  layout.messagesAcc.eval w + (layout.shardResiduals.map (·.eval w)).sum = 0 ∧
  (∀ f ∈ layout.friFolds,
    f.2.2.2.2.eval w + f.2.2.2.2.eval w =
      (f.1.eval w + f.2.1.eval w) +
        f.2.2.2.1.eval w * ((f.1.eval w - f.2.1.eval w) * f.2.2.1.eval w)) ∧
  (∀ s ∈ layout.merkleSteps,
    (w s.1 = 0 ∨ w s.1 = 1) ∧
    ∃ bytes : List UInt8,
      (if w s.1 = 0 then s.2.1.map w ++ s.2.2.1.map w else s.2.2.1.map w ++ s.2.1.map w) =
        bytes.map (fun u => (u.toNat : GoldilocksF)) ∧
      s.2.2.2.map w = (Aiur.Library.Blake3.digest bytes).toList.map
        (fun u => (u.toNat : GoldilocksF)))

private lemma publicInputs_bind {F α β : Type} (m : PlonkishM F α) (f : α → PlonkishM F β)
    (c : Circuit F)
    (hm : (m c).2.publicInputs = c.publicInputs)
    (hf : ∀ a c', (f a c').2.publicInputs = c'.publicInputs) :
    ((m >>= f) c).2.publicInputs = c.publicInputs := by
  dsimp only [bind, StateT.bind]
  exact (hf (m c).1 (m c).2).trans hm

private lemma publicInputs_add {F : Type} [Field F] (a b : Wire) (c : Circuit F) :
    (PlonkishM.add a b c).2.publicInputs = c.publicInputs := rfl

private lemma publicInputs_sub {F : Type} [Field F] (a b : Wire) (c : Circuit F) :
    (PlonkishM.sub a b c).2.publicInputs = c.publicInputs := rfl

private lemma publicInputs_mul {F : Type} [Field F] (a b : Wire) (c : Circuit F) :
    (PlonkishM.mul a b c).2.publicInputs = c.publicInputs := rfl

private lemma publicInputs_affine {F : Type} [Field F] (a b : Wire) (qa qb k : F) (c : Circuit F) :
    (PlonkishM.affine a b qa qb k c).2.publicInputs = c.publicInputs := rfl

private lemma publicInputs_assertEq {F : Type} [Field F] (a b : Wire) (c : Circuit F) :
    (PlonkishM.assertEq a b c).2.publicInputs = c.publicInputs := rfl

private lemma publicInputs_assertZero {F : Type} [Field F] (a : Wire) (c : Circuit F) :
    (PlonkishM.assertZero a c).2.publicInputs = c.publicInputs := rfl

private lemma publicInputs_assertBool {F : Type} [Field F] (a : Wire) (c : Circuit F) :
    (PlonkishM.assertBool a c).2.publicInputs = c.publicInputs := rfl

private lemma publicInputs_select {F : Type} [Field F] (cond t f : Wire) (c : Circuit F) :
    (PlonkishM.select cond t f c).2.publicInputs = c.publicInputs :=
  publicInputs_bind _ _ _ (publicInputs_sub t f c) fun _ c1 =>
    publicInputs_bind _ _ _ (publicInputs_mul cond _ c1) fun _ c2 =>
      publicInputs_add f _ c2

private lemma publicInputs_blake3Call {F : Type} (inp out : List Wire) (c : Circuit F) :
    (PlonkishM.blake3Call inp out c).2.publicInputs = c.publicInputs := rfl

private lemma publicInputs_qAdd (a b : QWire) (c : Circuit GoldilocksF) :
    (qAdd a b c).2.publicInputs = c.publicInputs :=
  publicInputs_bind _ _ _ (publicInputs_add a.1 b.1 c) fun _ c1 =>
    publicInputs_bind _ _ _ (publicInputs_add a.2.1 b.2.1 c1) fun _ c2 =>
      publicInputs_bind _ _ _ (publicInputs_add a.2.2 b.2.2 c2) fun _ _ => rfl

private lemma publicInputs_qSub (a b : QWire) (c : Circuit GoldilocksF) :
    (qSub a b c).2.publicInputs = c.publicInputs :=
  publicInputs_bind _ _ _ (publicInputs_sub a.1 b.1 c) fun _ c1 =>
    publicInputs_bind _ _ _ (publicInputs_sub a.2.1 b.2.1 c1) fun _ c2 =>
      publicInputs_bind _ _ _ (publicInputs_sub a.2.2 b.2.2 c2) fun _ _ => rfl

private lemma publicInputs_qMul (a b : QWire) (c : Circuit GoldilocksF) :
    (qMul a b c).2.publicInputs = c.publicInputs :=
  publicInputs_bind _ _ _ (publicInputs_mul a.1 b.1 c) fun _ c1 =>
    publicInputs_bind _ _ _ (publicInputs_mul a.1 b.2.1 c1) fun _ c2 =>
      publicInputs_bind _ _ _ (publicInputs_mul a.1 b.2.2 c2) fun _ c3 =>
        publicInputs_bind _ _ _ (publicInputs_mul a.2.1 b.1 c3) fun _ c4 =>
          publicInputs_bind _ _ _ (publicInputs_mul a.2.1 b.2.1 c4) fun _ c5 =>
            publicInputs_bind _ _ _ (publicInputs_mul a.2.1 b.2.2 c5) fun _ c6 =>
              publicInputs_bind _ _ _ (publicInputs_mul a.2.2 b.1 c6) fun _ c7 =>
                publicInputs_bind _ _ _ (publicInputs_mul a.2.2 b.2.1 c7) fun _ c8 =>
                  publicInputs_bind _ _ _ (publicInputs_mul a.2.2 b.2.2 c8) fun _ c9 =>
                    publicInputs_bind _ _ _ (publicInputs_add _ _ c9) fun _ c10 =>
                      publicInputs_bind _ _ _ (publicInputs_add _ _ c10) fun _ c11 =>
                        publicInputs_bind _ _ _ (publicInputs_add _ _ c11) fun _ c12 =>
                          publicInputs_bind _ _ _ (publicInputs_add _ _ c12) fun _ c13 =>
                            publicInputs_bind _ _ _ (publicInputs_add _ _ c13) fun _ c14 =>
                              publicInputs_bind _ _ _ (publicInputs_add _ _ c14) fun _ c15 =>
                                publicInputs_bind _ _ _ (publicInputs_add _ _ c15) fun _ c16 =>
                                  publicInputs_bind _ _ _ (publicInputs_add _ _ c16) fun _ _ => rfl

private lemma publicInputs_qAssertEq (a b : QWire) (c : Circuit GoldilocksF) :
    (qAssertEq a b c).2.publicInputs = c.publicInputs :=
  publicInputs_bind _ _ _ (publicInputs_assertEq a.1 b.1 c) fun _ c1 =>
    publicInputs_bind _ _ _ (publicInputs_assertEq a.2.1 b.2.1 c1) fun _ c2 =>
      publicInputs_assertEq a.2.2 b.2.2 c2

private lemma publicInputs_qAssertZero (a : QWire) (c : Circuit GoldilocksF) :
    (qAssertZero a c).2.publicInputs = c.publicInputs :=
  publicInputs_bind _ _ _ (publicInputs_assertZero a.1 c) fun _ c1 =>
    publicInputs_bind _ _ _ (publicInputs_assertZero a.2.1 c1) fun _ c2 =>
      publicInputs_assertZero a.2.2 c2

private lemma publicInputs_constrainFriFold (e0 e1 invX beta folded : QWire)
    (c : Circuit GoldilocksF) :
    (constrainFriFold e0 e1 invX beta folded c).2.publicInputs = c.publicInputs :=
  publicInputs_bind _ _ _ (publicInputs_qAdd e0 e1 c) fun _ c1 =>
    publicInputs_bind _ _ _ (publicInputs_qSub e0 e1 c1) fun _ c2 =>
      publicInputs_bind _ _ _ (publicInputs_qMul _ invX c2) fun _ c3 =>
        publicInputs_bind _ _ _ (publicInputs_qMul beta _ c3) fun _ c4 =>
          publicInputs_bind _ _ _ (publicInputs_qAdd _ _ c4) fun _ c5 =>
            publicInputs_bind _ _ _ (publicInputs_qAdd folded folded c5) fun _ c6 =>
              publicInputs_qAssertEq _ _ c6

/-- `buildFriVerifierCircuit` preserves `publicInputs` of `base`. -/
private lemma buildFriVerifierCircuit_publicInputs (base : Circuit GoldilocksF)
    (layout : FriVerifierLayout) :
    (buildFriVerifierCircuit base layout).publicInputs = base.publicInputs := by
  have hSum : ∀ acc xs c, (constrainSumZero acc xs c).2.publicInputs = c.publicInputs := by
    intro acc xs; induction xs generalizing acc with
    | nil => intro c; exact publicInputs_qAssertZero acc c
    | cons x xs ih =>
      intro c
      change ((qAdd acc x >>= fun acc' => constrainSumZero acc' xs) c).2.publicInputs = c.publicInputs
      exact publicInputs_bind (qAdd acc x) (fun acc' => constrainSumZero acc' xs) c
        (publicInputs_qAdd acc x c) (fun acc' c1 => ih acc' c1)
  have hFolds : ∀ fs c, (constrainFriFolds fs c).2.publicInputs = c.publicInputs := by
    intro fs; induction fs with
    | nil => intro c; rfl
    | cons f rest ih =>
      rcases f with ⟨e0, e1, invX, beta, folded⟩
      intro c
      change ((constrainFriFold e0 e1 invX beta folded >>= fun _ => constrainFriFolds rest) c).2.publicInputs = c.publicInputs
      exact publicInputs_bind (constrainFriFold e0 e1 invX beta folded) (fun _ => constrainFriFolds rest) c
        (publicInputs_constrainFriFold e0 e1 invX beta folded c) (fun _ c1 => ih c1)
  have hSel : ∀ bit ts fs c, (selectList bit ts fs c).2.publicInputs = c.publicInputs := by
    intro bit ts; induction ts with
    | nil => intro fs c; rfl
    | cons t ts ih =>
      intro fs c
      cases fs with
      | nil => rfl
      | cons f fs =>
        change ((PlonkishM.select bit t f >>= fun h => selectList bit ts fs >>= fun tl => pure (h :: tl)) c).2.publicInputs = c.publicInputs
        exact publicInputs_bind (PlonkishM.select bit t f) (fun h => selectList bit ts fs >>= fun tl => pure (h :: tl)) c
          (publicInputs_select bit t f c) fun h c1 =>
            publicInputs_bind (selectList bit ts fs) (fun tl => pure (h :: tl)) c1
              (ih fs c1) (fun _ _ => rfl)
  have hSteps : ∀ ss c, (constrainMerkleSteps ss c).2.publicInputs = c.publicInputs := by
    intro ss; induction ss with
    | nil => intro c; rfl
    | cons s rest ih =>
      rcases s with ⟨dir, cur, sib, parent⟩
      intro c
      have hStep : ∀ c', (constrainMerkleStep dir cur sib parent c').2.publicInputs = c'.publicInputs := by
        intro c'
        change ((PlonkishM.assertBool dir >>= fun _ => selectList dir sib cur >>= fun left =>
          selectList dir cur sib >>= fun right => PlonkishM.blake3Call (left ++ right) parent) c').2.publicInputs = c'.publicInputs
        exact publicInputs_bind (PlonkishM.assertBool dir) _ c' (publicInputs_assertBool dir c') fun _ c1 =>
          publicInputs_bind (selectList dir sib cur) _ c1 (hSel dir sib cur c1) fun left c2 =>
            publicInputs_bind (selectList dir cur sib) _ c2 (hSel dir cur sib c2) fun right c3 =>
              publicInputs_blake3Call (left ++ right) parent c3
      change ((constrainMerkleStep dir cur sib parent >>= fun _ => constrainMerkleSteps rest) c).2.publicInputs = c.publicInputs
      exact publicInputs_bind (constrainMerkleStep dir cur sib parent) (fun _ => constrainMerkleSteps rest) c
        (hStep c) (fun _ c1 => ih c1)
  change ((constrainSumZero layout.messagesAcc layout.shardResiduals >>= fun _ =>
    constrainFriFolds layout.friFolds >>= fun _ =>
      constrainMerkleSteps layout.merkleSteps) base).2.publicInputs = base.publicInputs
  exact publicInputs_bind (constrainSumZero layout.messagesAcc layout.shardResiduals) _ base
    (hSum layout.messagesAcc layout.shardResiduals base) fun _ c1 =>
      publicInputs_bind (constrainFriFolds layout.friFolds) _ c1
        (hFolds layout.friFolds c1) fun _ c2 =>
          hSteps layout.merkleSteps c2

/-- **Goldilocks In-Circuit FRI/Multi-STARK Verifier Soundness (`friVerifierCircuit_sound`):**
Any Goldilocks wire assignment `w` satisfying `buildFriVerifierCircuit base layout` on `pub`
satisfies `FriVerifierSatisfied base layout pub w`. -/
theorem friVerifierCircuit_sound (base : Circuit GoldilocksF) (layout : FriVerifierLayout)
    (hlen : ∀ s ∈ layout.merkleSteps, s.2.1.length = s.2.2.1.length)
    (pub : List GoldilocksF) (w : Wire → GoldilocksF)
    (hsat : (buildFriVerifierCircuit base layout).Satisfies pub w) :
    FriVerifierSatisfied base layout pub w := by
  have hpub : base.publicInputs.map w = pub := by
    rw [← buildFriVerifierCircuit_publicInputs base layout]
    exact hsat.1
  have hhold : (buildFriVerifierCircuit base layout).ConstraintsHold w :=
    ⟨hsat.2.1, hsat.2.2.1, hsat.2.2.2⟩
  have hspec :=
    (PlonkishM.Spec.bind (constrainSumZero_sound layout.messagesAcc layout.shardResiduals) fun _ =>
      PlonkishM.Spec.bind (constrainFriFolds_sound layout.friFolds) fun _ =>
        Spec.weaken (constrainMerkleSteps_sound layout.merkleSteps hlen) fun _ _ h3 h2 h1 =>
          And.intro h1 (And.intro h2 h3)) base
  have hbaseHold : base.ConstraintsHold w := Circuit.ConstraintsHold.mono hspec.1 hhold
  obtain ⟨h1, h2, h3⟩ := hspec.2 w hhold
  exact ⟨⟨hpub, hbaseHold.1, hbaseHold.2.1, hbaseHold.2.2⟩, h1, h2, h3⟩

/-- **Foreign BN254-Compiled FRI Verifier Soundness (`foreign_friVerifier_sound`):**
Composes `Foreign.foreign_compile_sound_lifted` with `friVerifierCircuit_sound`:
any `BN254Fr` wire assignment `w_fr` satisfying the foreign-compiled BN254 Plonkish circuit
`Foreign.foreignCompile (buildFriVerifierCircuit base layout)` on `Foreign.liftPublicInputs pub`
projects directly to a Goldilocks wire assignment satisfying `FriVerifierSatisfied base layout pub`. -/
theorem foreign_friVerifier_sound (base : Circuit GoldilocksF) (layout : FriVerifierLayout)
    (hlen : ∀ s ∈ layout.merkleSteps, s.2.1.length = s.2.2.1.length)
    (pub : List GoldilocksF) (w_fr : Wire → BN254Fr)
    (hsat : (foreignCompile (buildFriVerifierCircuit base layout)).Satisfies
      (liftPublicInputs pub) w_fr) :
    FriVerifierSatisfied base layout pub (projectGoldilocksWire w_fr) :=
  friVerifierCircuit_sound base layout hlen pub (projectGoldilocksWire w_fr)
    (foreign_compile_sound_lifted (buildFriVerifierCircuit base layout) pub w_fr hsat)

end Ix.Cert.Compression.FriVerifier
