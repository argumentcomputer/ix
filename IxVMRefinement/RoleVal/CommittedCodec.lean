import Ix.Cert.RoleClosure
import Ix.IxVM.Refinement.Claim
import IxC.Ixon.Verify.Canonical
import IxC.Ixon.Verify.ConstantTables
import IxC.Kernel.Ixon.RoleTableInj
import IxVMRefinement.Claim.HexDecode
import IxVMRefinement.L1.Hashed

/-! # Base evaluators and default table admission for `RoleData`

Provides:
* `committedDefaultRoleTable`, `defaultBinding_eq`, `admitBinding_committedDefault`,
  `committedDefaultRoleTable_literalSupportBound`;
* strict `Nat`-word BLAKE3 tree hashing (`checkHashChunks`, `row_hashed_of_checkHashChunks`);
* proof-free structural `wireWF` checker (`validConstantFast`) and fuel-indexed pure Ixon
  serializer (`encConstantFuel`), avoiding kernel unfolding of `WellFounded.fix` or dependent
  proof-carrying summaries (`Ixon.WireCheck.ExprSummary`). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.RoleVal

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

def mkAddr (bs : List UInt8) : _root_.Address := ⟨⟨bs.toArray⟩⟩


/-! ## Strict `Nat`-word BLAKE3 tree hashing for arbitrary chunk lists -/

private inductive CV8 where
  | mk : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → CV8
  deriving DecidableEq

private inductive W16 where
  | mk : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
         Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → W16
  deriving DecidableEq

private def letN {α : Type} (x : Nat) (k : Nat → α) : α :=
  Nat.casesOn (motive := fun _ => α) x (k 0) (fun n => k (Nat.succ n))

private theorem letN_eq {α : Type} (x : Nat) (k : Nat → α) : letN x k = k x := by
  cases x <;> rfl

private def bindW16 {α : Type} (s : W16) (k : W16 → α) : α :=
  W16.casesOn (motive := fun _ => α) s fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =>
    k (.mk w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)

private theorem bindW16_eq {α : Type} (s : W16) (k : W16 → α) : bindW16 s k = k s := by
  cases s; rfl

private def bindCV8 {α : Type} (c : CV8) (k : CV8 → α) : α :=
  CV8.casesOn (motive := fun _ => α) c fun c0 c1 c2 c3 c4 c5 c6 c7 =>
    k (.mk c0 c1 c2 c3 c4 c5 c6 c7)

private theorem bindCV8_eq {α : Type} (c : CV8) (k : CV8 → α) : bindCV8 c k = k c := by
  cases c; rfl

private def CV8.ofCV (cv : Blake3.Pure.CV) : CV8 :=
  .mk cv[0].toNat cv[1].toNat cv[2].toNat cv[3].toNat
      cv[4].toNat cv[5].toNat cv[6].toNat cv[7].toNat

private def CV8.toCV (c : CV8) : Blake3.Pure.CV :=
  CV8.casesOn (motive := fun _ => Blake3.Pure.CV) c fun c0 c1 c2 c3 c4 c5 c6 c7 =>
    #v[UInt32.ofNat c0, UInt32.ofNat c1, UInt32.ofNat c2, UInt32.ofNat c3,
       UInt32.ofNat c4, UInt32.ofNat c5, UInt32.ofNat c6, UInt32.ofNat c7]

private def W16.ofBlock (b : Blake3.Pure.Block) : W16 :=
  .mk b[0].toNat b[1].toNat b[2].toNat b[3].toNat
      b[4].toNat b[5].toNat b[6].toNat b[7].toNat
      b[8].toNat b[9].toNat b[10].toNat b[11].toNat
      b[12].toNat b[13].toNat b[14].toNat b[15].toNat

private theorem uint32_ofNat_toNat (x : UInt32) : UInt32.ofNat x.toNat = x := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt x.toNat_lt

private theorem toCV_ofCV (cv : Blake3.Pure.CV) : (CV8.ofCV cv).toCV = cv := by
  ext i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CV8.ofCV, CV8.toCV, uint32_ofNat_toNat]

private def add2Mod32 (a b : Nat) : Nat := (a + b) % 4294967296
private def add3Mod32 (a b c : Nat) : Nat := (a + b + c) % 4294967296
private def rotrN (w r : Nat) : Nat := (w >>> r) ||| ((w <<< (32 - r)) % 4294967296)

private theorem add2Mod32_toNat (a b : UInt32) :
    add2Mod32 a.toNat b.toNat = (a + b).toNat := by
  rw [UInt32.toNat_add]; rfl

private theorem add3Mod32_toNat (a b c : UInt32) :
    add3Mod32 a.toNat b.toNat c.toNat = (a + b + c).toNat := by
  rw [UInt32.toNat_add, UInt32.toNat_add]
  unfold add3Mod32
  change (a.toNat + b.toNat + c.toNat) % 4294967296 =
    ((a.toNat + b.toNat) % 4294967296 + c.toNat) % 4294967296
  rw [Nat.mod_add_mod]

private theorem toNat_xor_symm (a b : UInt32) : a.toNat ^^^ b.toNat = (a ^^^ b).toNat :=
  (UInt32.toNat_xor a b).symm

private theorem rotrN_toNat (w : UInt32) (r : Nat)
    (hr1 : (UInt32.ofNat r).toNat % 32 = r)
    (hr2 : (32 - UInt32.ofNat r).toNat % 32 = 32 - r) :
    rotrN w.toNat r = (Blake3.Pure.rotateRight w (UInt32.ofNat r)).toNat := by
  unfold Blake3.Pure.rotateRight rotrN
  rw [UInt32.toNat_or, UInt32.toNat_shiftRight, hr1, UInt32.toNat_shiftLeft, hr2]

private theorem rotrN_16 (w : UInt32) :
    rotrN w.toNat 16 = (Blake3.Pure.rotateRight w 16).toNat :=
  rotrN_toNat w 16 (by decide) (by decide)

private theorem rotrN_12 (w : UInt32) :
    rotrN w.toNat 12 = (Blake3.Pure.rotateRight w 12).toNat :=
  rotrN_toNat w 12 (by decide) (by decide)

private theorem rotrN_8 (w : UInt32) :
    rotrN w.toNat 8 = (Blake3.Pure.rotateRight w 8).toNat :=
  rotrN_toNat w 8 (by decide) (by decide)

private theorem rotrN_7 (w : UInt32) :
    rotrN w.toNat 7 = (Blake3.Pure.rotateRight w 7).toNat :=
  rotrN_toNat w 7 (by decide) (by decide)

private def mixN {α : Type} (a b c d x y : Nat) (k : Nat → Nat → Nat → Nat → α) : α :=
  letN (add3Mod32 a b x) fun a1 =>
  letN (rotrN (d ^^^ a1) 16) fun d1 =>
  letN (add2Mod32 c d1) fun c1 =>
  letN (rotrN (b ^^^ c1) 12) fun b1 =>
  letN (add3Mod32 a1 b1 y) fun a2 =>
  letN (rotrN (d1 ^^^ a2) 8) fun d2 =>
  letN (add2Mod32 c1 d2) fun c2 =>
  letN (rotrN (b1 ^^^ c2) 7) fun b2 =>
  k a2 b2 c2 d2

private theorem mixN_spec {α : Type} (a b c d x y : UInt32) (k : Nat → Nat → Nat → Nat → α) :
    mixN a.toNat b.toNat c.toNat d.toNat x.toNat y.toNat k =
      k (Blake3.Pure.mix a b c d x y)[0].toNat
        (Blake3.Pure.mix a b c d x y)[1].toNat
        (Blake3.Pure.mix a b c d x y)[2].toNat
        (Blake3.Pure.mix a b c d x y)[3].toNat := by
  unfold mixN
  simp only [letN_eq, add3Mod32_toNat, add2Mod32_toNat, toNat_xor_symm,
    rotrN_16, rotrN_12, rotrN_8, rotrN_7]
  rfl

private def g0 (s : W16) (x y : Nat) : W16 :=
  W16.casesOn (motive := fun _ => W16) s fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =>
    mixN w0 w4 w8 w12 x y fun a b c d => .mk a w1 w2 w3 b w5 w6 w7 c w9 w10 w11 d w13 w14 w15

private def g1 (s : W16) (x y : Nat) : W16 :=
  W16.casesOn (motive := fun _ => W16) s fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =>
    mixN w1 w5 w9 w13 x y fun a b c d => .mk w0 a w2 w3 w4 b w6 w7 w8 c w10 w11 w12 d w14 w15

private def g2 (s : W16) (x y : Nat) : W16 :=
  W16.casesOn (motive := fun _ => W16) s fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =>
    mixN w2 w6 w10 w14 x y fun a b c d => .mk w0 w1 a w3 w4 w5 b w7 w8 w9 c w11 w12 w13 d w15

private def g3 (s : W16) (x y : Nat) : W16 :=
  W16.casesOn (motive := fun _ => W16) s fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =>
    mixN w3 w7 w11 w15 x y fun a b c d => .mk w0 w1 w2 a w4 w5 w6 b w8 w9 w10 c w12 w13 w14 d

private def g4 (s : W16) (x y : Nat) : W16 :=
  W16.casesOn (motive := fun _ => W16) s fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =>
    mixN w0 w5 w10 w15 x y fun a b c d => .mk a w1 w2 w3 w4 b w6 w7 w8 w9 c w11 w12 w13 w14 d

private def g5 (s : W16) (x y : Nat) : W16 :=
  W16.casesOn (motive := fun _ => W16) s fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =>
    mixN w1 w6 w11 w12 x y fun a b c d => .mk w0 a w2 w3 w4 w5 b w7 w8 w9 w10 c d w13 w14 w15

private def g6 (s : W16) (x y : Nat) : W16 :=
  W16.casesOn (motive := fun _ => W16) s fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =>
    mixN w2 w7 w8 w13 x y fun a b c d => .mk w0 w1 a w3 w4 w5 w6 b c w9 w10 w11 w12 d w14 w15

private def g7 (s : W16) (x y : Nat) : W16 :=
  W16.casesOn (motive := fun _ => W16) s fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =>
    mixN w3 w4 w9 w14 x y fun a b c d => .mk w0 w1 w2 a b w5 w6 w7 w8 c w10 w11 w12 w13 d w15

private theorem g0_ofBlock (s : Blake3.Pure.Block) (x y : UInt32) :
    g0 (W16.ofBlock s) x.toNat y.toNat = W16.ofBlock (Blake3.Pure.g s 0 4 8 12 x y) := by
  unfold g0 W16.ofBlock; dsimp only; rw [mixN_spec]; unfold Blake3.Pure.g
  simp [Fin.getElem_fin, Vector.getElem_set]

private theorem g1_ofBlock (s : Blake3.Pure.Block) (x y : UInt32) :
    g1 (W16.ofBlock s) x.toNat y.toNat = W16.ofBlock (Blake3.Pure.g s 1 5 9 13 x y) := by
  unfold g1 W16.ofBlock; dsimp only; rw [mixN_spec]; unfold Blake3.Pure.g
  simp [Fin.getElem_fin, Vector.getElem_set]

private theorem g2_ofBlock (s : Blake3.Pure.Block) (x y : UInt32) :
    g2 (W16.ofBlock s) x.toNat y.toNat = W16.ofBlock (Blake3.Pure.g s 2 6 10 14 x y) := by
  unfold g2 W16.ofBlock; dsimp only; rw [mixN_spec]; unfold Blake3.Pure.g
  simp [Fin.getElem_fin, Vector.getElem_set]

private theorem g3_ofBlock (s : Blake3.Pure.Block) (x y : UInt32) :
    g3 (W16.ofBlock s) x.toNat y.toNat = W16.ofBlock (Blake3.Pure.g s 3 7 11 15 x y) := by
  unfold g3 W16.ofBlock; dsimp only; rw [mixN_spec]; unfold Blake3.Pure.g
  simp [Fin.getElem_fin, Vector.getElem_set]

private theorem g4_ofBlock (s : Blake3.Pure.Block) (x y : UInt32) :
    g4 (W16.ofBlock s) x.toNat y.toNat = W16.ofBlock (Blake3.Pure.g s 0 5 10 15 x y) := by
  unfold g4 W16.ofBlock; dsimp only; rw [mixN_spec]; unfold Blake3.Pure.g
  simp [Fin.getElem_fin, Vector.getElem_set]

private theorem g5_ofBlock (s : Blake3.Pure.Block) (x y : UInt32) :
    g5 (W16.ofBlock s) x.toNat y.toNat = W16.ofBlock (Blake3.Pure.g s 1 6 11 12 x y) := by
  unfold g5 W16.ofBlock; dsimp only; rw [mixN_spec]; unfold Blake3.Pure.g
  simp [Fin.getElem_fin, Vector.getElem_set]

private theorem g6_ofBlock (s : Blake3.Pure.Block) (x y : UInt32) :
    g6 (W16.ofBlock s) x.toNat y.toNat = W16.ofBlock (Blake3.Pure.g s 2 7 8 13 x y) := by
  unfold g6 W16.ofBlock; dsimp only; rw [mixN_spec]; unfold Blake3.Pure.g
  simp [Fin.getElem_fin, Vector.getElem_set]

private theorem g7_ofBlock (s : Blake3.Pure.Block) (x y : UInt32) :
    g7 (W16.ofBlock s) x.toNat y.toNat = W16.ofBlock (Blake3.Pure.g s 3 4 9 14 x y) := by
  unfold g7 W16.ofBlock; dsimp only; rw [mixN_spec]; unfold Blake3.Pure.g
  simp [Fin.getElem_fin, Vector.getElem_set]

private def roundN (s m : W16) : W16 :=
  W16.casesOn (motive := fun _ => W16) m fun m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 =>
    g7 (g6 (g5 (g4 (g3 (g2 (g1 (g0 s m0 m1) m2 m3) m4 m5) m6 m7) m8 m9) m10 m11) m12 m13) m14 m15

private theorem roundN_expand (s : W16) (m : Blake3.Pure.Block) :
    roundN s (W16.ofBlock m) =
      g7 (g6 (g5 (g4 (g3 (g2 (g1 (g0 s m[0].toNat m[1].toNat)
        m[2].toNat m[3].toNat) m[4].toNat m[5].toNat) m[6].toNat m[7].toNat)
        m[8].toNat m[9].toNat) m[10].toNat m[11].toNat) m[12].toNat m[13].toNat)
        m[14].toNat m[15].toNat := rfl

private theorem roundN_ofBlock (s m : Blake3.Pure.Block) :
    roundN (W16.ofBlock s) (W16.ofBlock m) =
      W16.ofBlock (Aiur.Library.Blake3.compressInnerJ s m) := by
  rw [roundN_expand, g0_ofBlock, g1_ofBlock, g2_ofBlock, g3_ofBlock,
      g4_ofBlock, g5_ofBlock, g6_ofBlock, g7_ofBlock]
  rfl

private def permuteN (m : W16) : W16 :=
  W16.casesOn (motive := fun _ => W16) m fun m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 =>
    .mk m2 m6 m3 m10 m7 m0 m4 m13 m1 m11 m12 m5 m9 m14 m15 m8

private theorem permuteN_ofBlock (m : Blake3.Pure.Block) :
    permuteN (W16.ofBlock m) = W16.ofBlock (Aiur.Library.Blake3.permute m) := rfl

private def compressInnerIN (s m : W16) : W16 :=
  bindW16 (roundN s m) fun s0 =>
  bindW16 (permuteN m) fun m1 =>
  bindW16 (roundN s0 m1) fun s1 =>
  bindW16 (permuteN m1) fun m2 =>
  bindW16 (roundN s1 m2) fun s2 =>
  bindW16 (permuteN m2) fun m3 =>
  bindW16 (roundN s2 m3) fun s3 =>
  bindW16 (permuteN m3) fun m4 =>
  bindW16 (roundN s3 m4) fun s4 =>
  bindW16 (permuteN m4) fun m5 =>
  bindW16 (roundN s4 m5) fun s5 =>
  bindW16 (permuteN m5) fun m6 =>
  roundN s5 m6

private theorem compressInnerIN_ofBlock (s m : Blake3.Pure.Block) :
    compressInnerIN (W16.ofBlock s) (W16.ofBlock m) =
      W16.ofBlock (Aiur.Library.Blake3.compressInnerI s m) := by
  unfold compressInnerIN Aiur.Library.Blake3.compressInnerI
  simp only [bindW16_eq, roundN_ofBlock, permuteN_ofBlock]

private def ivN : CV8 :=
  .mk 0x6A09E667 0xBB67AE85 0x3C6EF372 0xA54FF53A
      0x510E527F 0x9B05688C 0x1F83D9AB 0x5BE0CD19

private theorem ivN_eq : ivN = CV8.ofCV Blake3.Pure.iv := by decide

private def initialWordsN (cv : CV8) (counter blockLen flags : Nat) : W16 :=
  CV8.casesOn (motive := fun _ => W16) cv fun c0 c1 c2 c3 c4 c5 c6 c7 =>
    letN (counter % 4294967296) fun ctrLo =>
    letN ((counter >>> 32) % 4294967296) fun ctrHi =>
    .mk c0 c1 c2 c3 c4 c5 c6 c7
        0x6A09E667 0xBB67AE85 0x3C6EF372 0xA54FF53A
        ctrLo ctrHi blockLen flags

private theorem hiv0 : (0x6A09E667 : Nat) = Blake3.Pure.iv[0].toNat := by decide
private theorem hiv1 : (0xBB67AE85 : Nat) = Blake3.Pure.iv[1].toNat := by decide
private theorem hiv2 : (0x3C6EF372 : Nat) = Blake3.Pure.iv[2].toNat := by decide
private theorem hiv3 : (0xA54FF53A : Nat) = Blake3.Pure.iv[3].toNat := by decide

private theorem initialWordsN_eq (cv : Blake3.Pure.CV) (counter : UInt64)
    (blockLen flags : UInt32) :
    initialWordsN (CV8.ofCV cv) counter.toNat blockLen.toNat flags.toNat =
      W16.ofBlock (Blake3.Pure.initialWords cv counter blockLen flags) := by
  have hlo : counter.toNat % 4294967296 = counter.toUInt32.toNat := by
    rw [UInt64.toNat_toUInt32]
  have hhi : (counter.toNat >>> 32) % 4294967296 = (counter >>> 32).toUInt32.toNat := by
    rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
    have hs : (32 : UInt64).toNat % 64 = 32 := by decide +revert
    rw [hs]
  simp only [initialWordsN, CV8.ofCV, letN_eq, hlo, hhi, hiv0, hiv1, hiv2, hiv3,
    Blake3.Pure.initialWords, W16.ofBlock]
  rfl

private def finalizeStateN (s : W16) : CV8 :=
  W16.casesOn (motive := fun _ => CV8) s fun s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 =>
    letN (s0 ^^^ s8) fun c0 =>
    letN (s1 ^^^ s9) fun c1 =>
    letN (s2 ^^^ s10) fun c2 =>
    letN (s3 ^^^ s11) fun c3 =>
    letN (s4 ^^^ s12) fun c4 =>
    letN (s5 ^^^ s13) fun c5 =>
    letN (s6 ^^^ s14) fun c6 =>
    letN (s7 ^^^ s15) fun c7 =>
    .mk c0 c1 c2 c3 c4 c5 c6 c7

private theorem finalizeStateN_eq (s : Blake3.Pure.Block) :
    finalizeStateN (W16.ofBlock s) = CV8.ofCV (Aiur.Library.Blake3.finalizeState s) := by
  simp only [finalizeStateN, W16.ofBlock, letN_eq, CV8.ofCV,
    Aiur.Library.Blake3.finalizeState, Vector.getElem_ofFn, UInt32.toNat_xor]

private def compressN (cv : CV8) (m : W16) (counter blockLen flags : Nat) : CV8 :=
  finalizeStateN (compressInnerIN (initialWordsN cv counter blockLen flags) m)

private theorem compressN_eq (cv : Blake3.Pure.CV) (m : Blake3.Pure.Block)
    (counter : UInt64) (blockLen flags : UInt32) :
    compressN (CV8.ofCV cv) (W16.ofBlock m) counter.toNat blockLen.toNat flags.toNat =
      CV8.ofCV (Blake3.Pure.compress cv m counter blockLen flags) := by
  unfold compressN
  rw [initialWordsN_eq, compressInnerIN_ofBlock, finalizeStateN_eq,
      Aiur.Library.Blake3.compress_spec]

private def byteAtN (bs : List UInt8) (i : Nat) : Nat := (bs[i]?.getD 0).toNat

private def wordAtN (bs : List UInt8) (w : Nat) : Nat :=
  Aiur.Library.U32.pack (byteAtN bs (w * 4)) (byteAtN bs (w * 4 + 1))
    (byteAtN bs (w * 4 + 2)) (byteAtN bs (w * 4 + 3))

private def blockWordsN (bs : List UInt8) : W16 :=
  letN (wordAtN bs 0) fun w0 => letN (wordAtN bs 1) fun w1 =>
  letN (wordAtN bs 2) fun w2 => letN (wordAtN bs 3) fun w3 =>
  letN (wordAtN bs 4) fun w4 => letN (wordAtN bs 5) fun w5 =>
  letN (wordAtN bs 6) fun w6 => letN (wordAtN bs 7) fun w7 =>
  letN (wordAtN bs 8) fun w8 => letN (wordAtN bs 9) fun w9 =>
  letN (wordAtN bs 10) fun w10 => letN (wordAtN bs 11) fun w11 =>
  letN (wordAtN bs 12) fun w12 => letN (wordAtN bs 13) fun w13 =>
  letN (wordAtN bs 14) fun w14 => letN (wordAtN bs 15) fun w15 =>
  .mk w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

private theorem blockWords_getElem_toNat (bs : List UInt8) (i : Nat) (hi : i < 16) :
    (Blake3.Pure.blockWords bs)[i].toNat = wordAtN bs i := by
  unfold Blake3.Pure.blockWords wordAtN byteAtN
  simp only [Vector.getElem_ofFn, List.getElem?_toArray]
  have hv : (Vector.ofFn fun byte : Fin 4 => bs[i * 4 + byte.val]?.getD 0) =
      #v[bs[i * 4]?.getD 0, bs[i * 4 + 1]?.getD 0, bs[i * 4 + 2]?.getD 0, bs[i * 4 + 3]?.getD 0] := by
    ext j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> simp
  rw [hv, Aiur.Library.Blake3.bytesWord_eq_wordOfBytes, Aiur.Library.Blake3.wordOfBytes_toNat]

private theorem blockWordsN_eq (bs : List UInt8) :
    blockWordsN bs = W16.ofBlock (Blake3.Pure.blockWords bs) := by
  simp only [blockWordsN, letN_eq, W16.ofBlock, blockWords_getElem_toNat]

private def chunkLoopCVN : Nat → Nat → CV8 → Bool → List UInt8 → CV8
  | 0, counter, cv, start, input =>
    compressN cv (blockWordsN input) counter (input.length % 4294967296)
      ((if start then 1 else 0) ||| 2)
  | fuel + 1, counter, cv, start, input =>
    if input.length ≤ 64 then
      compressN cv (blockWordsN input) counter (input.length % 4294967296)
        ((if start then 1 else 0) ||| 2)
    else
      bindCV8 (compressN cv (blockWordsN (input.take 64)) counter 64 (if start then 1 else 0))
        fun next => chunkLoopCVN fuel counter next false (input.drop 64)

private def chunkLoopRootCVN : Nat → CV8 → Bool → List UInt8 → CV8
  | 0, cv, start, input =>
    compressN cv (blockWordsN input) 0 (input.length % 4294967296)
      ((if start then 1 else 0) ||| 10)
  | fuel + 1, cv, start, input =>
    if input.length ≤ 64 then
      compressN cv (blockWordsN input) 0 (input.length % 4294967296)
        ((if start then 1 else 0) ||| 10)
    else
      bindCV8 (compressN cv (blockWordsN (input.take 64)) 0 64 (if start then 1 else 0))
        fun next => chunkLoopRootCVN fuel next false (input.drop 64)

private theorem chunkLoopCVN_eq :
    ∀ (fuel : Nat) (counter : UInt64) (cv : Blake3.Pure.CV) (start : Bool) (input : List UInt8),
      input.length ≤ 64 * (fuel + 1) →
      chunkLoopCVN fuel counter.toNat (CV8.ofCV cv) start input =
        CV8.ofCV (Blake3.Pure.chunkLoop counter cv start input).chainingValue
  | 0, counter, cv, start, input, hlen => by
    have hle : input.length ≤ 64 := by omega
    have hblen : input.length % 4294967296 = input.length.toUInt32.toNat := by
      change input.length % 4294967296 = (UInt32.ofNat input.length).toNat
      rw [UInt32.toNat_ofNat']
    have hfl : ((if start then 1 else 0) ||| 2) =
        (((if start then (1 : UInt32) else 0) ||| 2)).toNat := by cases start <;> decide
    rw [Blake3.Pure.chunkLoop_of_le counter cv start input hle]
    unfold chunkLoopCVN Blake3.Pure.Output.chainingValue
    rw [blockWordsN_eq, hblen, hfl, compressN_eq]
  | fuel + 1, counter, cv, start, input, hlen => by
    by_cases hle : input.length ≤ 64
    · have hblen : input.length % 4294967296 = input.length.toUInt32.toNat := by
        change input.length % 4294967296 = (UInt32.ofNat input.length).toNat
        rw [UInt32.toNat_ofNat']
      have hfl : ((if start then 1 else 0) ||| 2) =
          (((if start then (1 : UInt32) else 0) ||| 2)).toNat := by cases start <;> decide
      rw [Blake3.Pure.chunkLoop_of_le counter cv start input hle, chunkLoopCVN, ite_eq_left hle]
      unfold Blake3.Pure.Output.chainingValue
      rw [blockWordsN_eq, hblen, hfl, compressN_eq]
    · have hgt : 64 < input.length := by omega
      have hfl : (if start then 1 else 0) = (if start then (1 : UInt32) else 0).toNat := by
        cases start <;> decide
      have hstep :
          compressN (CV8.ofCV cv) (blockWordsN (input.take 64)) counter.toNat 64
              (if start then 1 else 0) =
            CV8.ofCV (Blake3.Pure.compress cv (Blake3.Pure.blockWords (input.take 64)) counter 64
              (if start then 1 else 0)) := by
        rw [blockWordsN_eq, hfl]
        exact compressN_eq cv (Blake3.Pure.blockWords (input.take 64)) counter 64
          (if start then 1 else 0)
      rw [Blake3.Pure.chunkLoop_of_gt counter cv start input hgt, chunkLoopCVN, ite_eq_right hle,
          bindCV8_eq, hstep]
      exact chunkLoopCVN_eq fuel counter _ false (input.drop 64) (by rw [List.length_drop]; omega)

private theorem chunkLoopRootCVN_eq :
    ∀ (fuel : Nat) (cv : Blake3.Pure.CV) (start : Bool) (input : List UInt8),
      input.length ≤ 64 * (fuel + 1) →
      Blake3.Pure.cvBytes (chunkLoopRootCVN fuel (CV8.ofCV cv) start input).toCV =
        (Blake3.Pure.chunkLoop 0 cv start input).rootHash
  | 0, cv, start, input, hlen => by
    have hle : input.length ≤ 64 := by omega
    have hblen : input.length % 4294967296 = input.length.toUInt32.toNat := by
      change input.length % 4294967296 = (UInt32.ofNat input.length).toNat
      rw [UInt32.toNat_ofNat']
    have hfl : ((if start then 1 else 0) ||| 10) =
        ((((if start then (1 : UInt32) else 0) ||| 2) ||| 8)).toNat := by cases start <;> decide
    have hc := congrArg (fun x => Blake3.Pure.cvBytes x.toCV)
      (compressN_eq cv (Blake3.Pure.blockWords input) 0 input.length.toUInt32
        (((if start then (1 : UInt32) else 0) ||| 2) ||| 8))
    rw [toCV_ofCV] at hc
    rw [Blake3.Pure.chunkLoop_of_le 0 cv start input hle]
    unfold chunkLoopRootCVN Blake3.Pure.Output.rootHash
    dsimp only
    rw [blockWordsN_eq, hblen, hfl]
    exact hc
  | fuel + 1, cv, start, input, hlen => by
    by_cases hle : input.length ≤ 64
    · have hblen : input.length % 4294967296 = input.length.toUInt32.toNat := by
        change input.length % 4294967296 = (UInt32.ofNat input.length).toNat
        rw [UInt32.toNat_ofNat']
      have hfl : ((if start then 1 else 0) ||| 10) =
          ((((if start then (1 : UInt32) else 0) ||| 2) ||| 8)).toNat := by cases start <;> decide
      have hc := congrArg (fun x => Blake3.Pure.cvBytes x.toCV)
        (compressN_eq cv (Blake3.Pure.blockWords input) 0 input.length.toUInt32
          (((if start then (1 : UInt32) else 0) ||| 2) ||| 8))
      rw [toCV_ofCV] at hc
      rw [Blake3.Pure.chunkLoop_of_le 0 cv start input hle, chunkLoopRootCVN, ite_eq_left hle]
      unfold Blake3.Pure.Output.rootHash
      dsimp only
      rw [blockWordsN_eq, hblen, hfl]
      exact hc
    · have hgt : 64 < input.length := by omega
      have hfl : (if start then 1 else 0) = (if start then (1 : UInt32) else 0).toNat := by
        cases start <;> decide
      have hstep :
          compressN (CV8.ofCV cv) (blockWordsN (input.take 64)) 0 64
              (if start then 1 else 0) =
            CV8.ofCV (Blake3.Pure.compress cv (Blake3.Pure.blockWords (input.take 64)) 0 64
              (if start then 1 else 0)) := by
        rw [blockWordsN_eq, hfl]
        exact compressN_eq cv (Blake3.Pure.blockWords (input.take 64)) 0 64
          (if start then 1 else 0)
      rw [Blake3.Pure.chunkLoop_of_gt 0 cv start input hgt, chunkLoopRootCVN, ite_eq_right hle,
          bindCV8_eq, hstep]
      exact chunkLoopRootCVN_eq fuel _ false (input.drop 64)
        (by rw [List.length_drop]; omega)

private theorem single_chunk_digest_eq_gen (fuel : Nat) (input : List UInt8)
    (hfuel : input.length ≤ 64 * (fuel + 1)) (hlen : input.length ≤ 1024) :
    Blake3.Pure.cvBytes (chunkLoopRootCVN fuel ivN true input).toCV =
      Blake3.Pure.digest input := by
  rw [ivN_eq, chunkLoopRootCVN_eq fuel Blake3.Pure.iv true input hfuel]
  exact Aiur.Library.Blake3.chunk_single_root_spec input hlen

private theorem single_chunk_digest_eq (input : List UInt8) (hlen : input.length ≤ 1024) :
    Blake3.Pure.cvBytes (chunkLoopRootCVN 15 ivN true input).toCV =
      Blake3.Pure.digest input :=
  single_chunk_digest_eq_gen 15 input (by omega) hlen

private theorem cv_toList_eight (v : Vector UInt32 8) :
    v.toList = [v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rcases (by simp at h1; omega :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem block_toList_sixteen (v : Vector UInt32 16) :
    v.toList = [v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7],
                v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rcases (by simp at h1; omega :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private def concatCV8 (l r : CV8) : W16 :=
  CV8.casesOn (motive := fun _ => W16) l fun l0 l1 l2 l3 l4 l5 l6 l7 =>
    CV8.casesOn (motive := fun _ => W16) r fun r0 r1 r2 r3 r4 r5 r6 r7 =>
      .mk l0 l1 l2 l3 l4 l5 l6 l7 r0 r1 r2 r3 r4 r5 r6 r7

private theorem concatCV8_eq (l r : Blake3.Pure.CV) :
    concatCV8 (CV8.ofCV l) (CV8.ofCV r) = W16.ofBlock (l ++ r) := by
  have hl : (l ++ r : Blake3.Pure.Block).toList =
      [l[0], l[1], l[2], l[3], l[4], l[5], l[6], l[7],
       r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7]] := by
    show (l ++ r).toList = _
    rw [Vector.toList_append, cv_toList_eight l, cv_toList_eight r]
    rfl
  rw [block_toList_sixteen (l ++ r)] at hl
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := hl
  simp only [concatCV8, CV8.ofCV, W16.ofBlock,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]

private def parentCVN (l r : CV8) : CV8 := compressN ivN (concatCV8 l r) 0 64 4
private def parentRootCVN (l r : CV8) : CV8 := compressN ivN (concatCV8 l r) 0 64 12

private theorem parentCVN_eq (l r : Blake3.Pure.CV) :
    parentCVN (CV8.ofCV l) (CV8.ofCV r) =
      CV8.ofCV (Blake3.Pure.parentOutput l r).chainingValue := by
  unfold parentCVN Blake3.Pure.parentOutput Blake3.Pure.Output.chainingValue
  rw [ivN_eq, concatCV8_eq]
  exact compressN_eq Blake3.Pure.iv (l ++ r) 0 64 4

private theorem parentRootCVN_toCV_eq (l r : Blake3.Pure.CV) :
    (parentRootCVN (CV8.ofCV l) (CV8.ofCV r)).toCV =
      Aiur.Library.Blake3.compressLayer [l, r] := by
  unfold parentRootCVN
  rw [ivN_eq, concatCV8_eq, Aiur.Library.Blake3.compressLayer]
  have hc := congrArg CV8.toCV (compressN_eq Blake3.Pure.iv (l ++ r) 0 64 12)
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h64 : (64 : UInt32).toNat = 64 := rfl
  have h12 : (12 : UInt32).toNat = 12 := rfl
  rw [toCV_ofCV, h0, h64, h12] at hc
  exact hc

private def nextLayerCV8 : List CV8 → List CV8
  | [] => []
  | [c] => [c]
  | l :: r :: rest => parentCVN l r :: nextLayerCV8 rest

private theorem nextLayerCV8_eq :
    ∀ (cvs : List Blake3.Pure.CV),
      nextLayerCV8 (cvs.map CV8.ofCV) = (Aiur.Library.Blake3.nextLayer cvs).map CV8.ofCV
  | [] => rfl
  | [_] => rfl
  | l :: r :: rest => by
    simp only [List.map_cons, nextLayerCV8, Aiur.Library.Blake3.nextLayer,
      parentCVN_eq, nextLayerCV8_eq rest]

private def mergeRootCV8 : Nat → List CV8 → CV8
  | _, [] => ivN
  | _, [c] => c
  | _, [l, r] => parentRootCVN l r
  | 0, l :: r :: _ :: _ => parentRootCVN l r
  | fuel + 1, l :: r :: c :: rest => mergeRootCV8 fuel (nextLayerCV8 (l :: r :: c :: rest))

private theorem mergeRootCV8_eq :
    ∀ (fuel : Nat) (cvs : List Blake3.Pure.CV),
      cvs.length ≤ fuel + 2 →
      2 ≤ cvs.length →
      (mergeRootCV8 fuel (cvs.map CV8.ofCV)).toCV = Aiur.Library.Blake3.compressLayer cvs
  | _, [], _, h2 => absurd h2 (by simp)
  | _, [_], _, h2 => absurd h2 (by simp)
  | fuel, [l, r], _, _ => by
    cases fuel <;> exact parentRootCVN_toCV_eq l r
  | 0, _ :: _ :: _ :: _, hle, _ => by simp at hle
  | fuel + 1, l :: r :: c :: rest, hle, _ => by
    have hlt := Aiur.Library.Blake3.next_layer_length_lt (cvs := l :: r :: c :: rest) (by simp)
    have h2' : 2 ≤ (Aiur.Library.Blake3.nextLayer (l :: r :: c :: rest)).length := by
      rcases rest with _ | ⟨d, ds⟩ <;> simp [Aiur.Library.Blake3.nextLayer]
    simp only [List.map_cons, mergeRootCV8]
    change (mergeRootCV8 fuel (nextLayerCV8 ((l :: r :: c :: rest).map CV8.ofCV))).toCV = _
    rw [nextLayerCV8_eq, Aiur.Library.Blake3.compress_layer_step_spec]
    exact mergeRootCV8_eq fuel _ (by simp only [List.length_cons] at hle hlt; omega) h2'

private def chunksCV8 : Nat → List (List UInt8) → List CV8
  | _, [] => []
  | ctr, c :: cs =>
    bindCV8 (chunkLoopCVN 15 ctr ivN true c) fun cv =>
      cv :: chunksCV8 (ctr + 1) cs

private def validChunksBool : List (List UInt8) → Bool
  | [] => false
  | [c] => decide (c.length ≤ 1024)
  | c :: d :: cs => decide (c.length = 1024) && decide (0 < d.length) && validChunksBool (d :: cs)

private theorem chunks_flatten_pos :
    ∀ {c : List UInt8} {cs : List (List UInt8)}, 0 < c.length → 0 < (c :: cs).flatten.length
  | c, cs, hc => by simp only [List.flatten_cons, List.length_append]; omega

private theorem chunkLoopCVN_iv_eq_gen (fuel ctr : Nat) (c : List UInt8)
    (hctr : ctr < 18446744073709551616) (hfuel : c.length ≤ 64 * (fuel + 1)) :
    chunkLoopCVN fuel ctr ivN true c =
      CV8.ofCV (Blake3.Pure.chunkOutput ctr.toUInt64 c).chainingValue := by
  have hto : ctr.toUInt64.toNat = ctr := by
    change (UInt64.ofNat ctr).toNat = ctr
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hctr
  unfold Blake3.Pure.chunkOutput
  have heq := chunkLoopCVN_eq fuel ctr.toUInt64 Blake3.Pure.iv true c hfuel
  rw [hto, ← ivN_eq] at heq
  exact heq

private theorem chunkLoopCVN_iv_eq (ctr : Nat) (c : List UInt8)
    (hctr : ctr < 18446744073709551616) (hc : c.length ≤ 1024) :
    chunkLoopCVN 15 ctr ivN true c =
      CV8.ofCV (Blake3.Pure.chunkOutput ctr.toUInt64 c).chainingValue :=
  chunkLoopCVN_iv_eq_gen 15 ctr c hctr (by omega)

private theorem chunksCV8_eq :
    ∀ (chunks : List (List UInt8)) (ctr : Nat),
      validChunksBool chunks = true →
      ctr + chunks.length < 18446744073709551616 →
      chunksCV8 ctr chunks =
        ((Blake3.Pure.chunkOutputs ctr chunks.flatten).map Blake3.Pure.Output.chainingValue).map
          CV8.ofCV
  | [], _, hv, _ => by cases hv
  | [c], ctr, hv, hctr => by
    have hc : c.length ≤ 1024 := of_decide_eq_true hv
    have hflat : [c].flatten = c := List.append_nil c
    rw [hflat, Blake3.Pure.chunkOutputs_small ctr c hc]
    simp only [chunksCV8, bindCV8_eq, List.map_cons, List.map_nil]
    exact congrArg (· :: [])
      (chunkLoopCVN_iv_eq ctr c (by simp only [List.length_cons, List.length_nil] at hctr; omega) hc)
  | c :: d :: cs, ctr, hv, hctr => by
    simp only [validChunksBool, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hclen, hdpos⟩, htail⟩ := hv
    have hpos : 0 < (d :: cs).flatten.length := chunks_flatten_pos hdpos
    rw [List.flatten_cons,
        Blake3.Pure.chunkOutputs_append ctr 1 c (d :: cs).flatten (by omega) (by omega) hpos,
        Blake3.Pure.chunkOutputs_small ctr c (by omega)]
    simp only [chunksCV8, bindCV8_eq, List.singleton_append, List.map_cons]
    exact congrArg₂ List.cons
      (chunkLoopCVN_iv_eq ctr c (by simp only [List.length_cons] at hctr; omega) (by omega))
      (chunksCV8_eq (d :: cs) (ctr + 1) htail (by simp only [List.length_cons] at hctr ⊢; omega))

private def digestCV8 : List (List UInt8) → CV8
  | [] => ivN
  | [c] => chunkLoopRootCVN 15 ivN true c
  | c0 :: c1 :: cs =>
    let cvs := chunksCV8 0 (c0 :: c1 :: cs)
    mergeRootCV8 cvs.length cvs

private theorem chunksCV8_length (ctr : Nat) :
    ∀ chunks : List (List UInt8), (chunksCV8 ctr chunks).length = chunks.length
  | [] => rfl
  | c :: cs => by simp only [chunksCV8, bindCV8_eq, List.length_cons, chunksCV8_length (ctr + 1) cs]

private theorem digestCV8_spec (chunks : List (List UInt8))
    (hv : validChunksBool chunks = true)
    (hctr : chunks.length < 18446744073709551616) :
    Blake3.Pure.cvBytes (digestCV8 chunks).toCV = Blake3.Pure.digest chunks.flatten := by
  match chunks with
  | [] => cases hv
  | [c] =>
    have hc : c.length ≤ 1024 := of_decide_eq_true hv
    unfold digestCV8
    rw [show [c].flatten = c from List.append_nil c]
    exact single_chunk_digest_eq c hc
  | c0 :: c1 :: cs =>
    have hcveq := chunksCV8_eq (c0 :: c1 :: cs) 0 hv (by omega)
    have hlen_out :
        ((Blake3.Pure.chunkOutputs 0 (c0 :: c1 :: cs).flatten).map
          Blake3.Pure.Output.chainingValue).length = (c0 :: c1 :: cs).length := by
      have h1 := congrArg List.length hcveq
      rw [chunksCV8_length, List.length_map] at h1
      exact h1.symm
    have hlen_map :
        2 ≤ ((Blake3.Pure.chunkOutputs 0 (c0 :: c1 :: cs).flatten).map
          Blake3.Pure.Output.chainingValue).length := by
      rw [hlen_out]
      simp only [List.length_cons]
      omega
    have hlen_raw : 2 ≤ (Blake3.Pure.chunkOutputs 0 (c0 :: c1 :: cs).flatten).length := by
      simpa only [List.length_map] using hlen_map
    show Blake3.Pure.cvBytes
      (mergeRootCV8 (chunksCV8 0 (c0 :: c1 :: cs)).length (chunksCV8 0 (c0 :: c1 :: cs))).toCV = _
    rw [chunksCV8_length, hcveq,
        mergeRootCV8_eq _ _ (by rw [hlen_out]; omega) hlen_map,
        Aiur.Library.Blake3.compress_layer_spec _ hlen_raw,
        ← Blake3.Pure.digest_eq_mergeLevels]

def checkHashChunks (chunks : List (List UInt8)) (addrBytes : List UInt8) : Bool :=
  validChunksBool chunks &&
  decide (chunks.length < 18446744073709551616) &&
  ((Blake3.Pure.cvBytes (digestCV8 chunks).toCV).toList == addrBytes)

private theorem ixAddr_eq_mkAddr_toList (d : Vector UInt8 32) :
    L1.ixAddr d = mkAddr d.toList := by
  rcases d with ⟨arr, _⟩
  simp [L1.ixAddr, mkAddr]

theorem admissionHash_of_checkHashChunks {chunks : List (List UInt8)} {addrBytes : List UInt8}
    (h : checkHashChunks chunks addrBytes = true) :
    Address.admissionHash ⟨chunks.flatten.toArray⟩ = mkAddr addrBytes := by
  simp only [checkHashChunks, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hv, hctr⟩, hbytes⟩ := h
  rw [Address.admissionHash_eq, L1.blake3Pure_eq, ← digestCV8_spec chunks hv hctr,
      ixAddr_eq_mkAddr_toList, hbytes]

/-! ## Proof-free structural `wireWF` checker (`validConstantFast`) -/

private def checkUnivFast : Ixon.Univ → Option Nat
  | .zero => some 0
  | .var _ => some 0
  | .succ inner =>
    match checkUnivFast inner with
    | some cnt => if decide (1 + cnt < UInt64.size) then some (1 + cnt) else none
    | none => none
  | .max l r =>
    match checkUnivFast l, checkUnivFast r with
    | some _, some _ => some 0
    | _, _ => none
  | .imax l r =>
    match checkUnivFast l, checkUnivFast r with
    | some _, some _ => some 0
    | _, _ => none

private theorem checkUnivFast_spec :
    ∀ (u : Ixon.Univ) {cnt : Nat}, checkUnivFast u = some cnt → cnt = u.succCountNat ∧ u.wireWF
  | .zero, _, h => by injection h with hc; subst hc; exact ⟨rfl, trivial⟩
  | .var _, _, h => by injection h with hc; subst hc; exact ⟨rfl, trivial⟩
  | .succ inner, cnt, h => by
    unfold checkUnivFast at h
    cases hi : checkUnivFast inner with
    | none => rw [hi] at h; cases h
    | some ic =>
      rw [hi] at h; dsimp only at h
      by_cases hlt : 1 + ic < UInt64.size
      · rw [decide_eq_true hlt] at h
        simp only [↓reduceIte, Option.some.injEq] at h
        subst h
        obtain ⟨heq, hwf⟩ := checkUnivFast_spec inner hi
        subst heq
        exact ⟨rfl, hlt, hwf⟩
      · rw [decide_eq_false hlt] at h
        simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | .max l r, cnt, h => by
    unfold checkUnivFast at h
    cases hl : checkUnivFast l with
    | none => rw [hl] at h; cases h
    | some _ =>
      cases hr : checkUnivFast r with
      | none => rw [hl, hr] at h; cases h
      | some _ =>
        rw [hl, hr] at h
        injection h with hc; subst hc
        exact ⟨rfl, (checkUnivFast_spec l hl).2, (checkUnivFast_spec r hr).2⟩
  | .imax l r, cnt, h => by
    unfold checkUnivFast at h
    cases hl : checkUnivFast l with
    | none => rw [hl] at h; cases h
    | some _ =>
      cases hr : checkUnivFast r with
      | none => rw [hl, hr] at h; cases h
      | some _ =>
        rw [hl, hr] at h
        injection h with hc; subst hc
        exact ⟨rfl, (checkUnivFast_spec l hl).2, (checkUnivFast_spec r hr).2⟩

private inductive ECounts where
  | mk : Nat → Nat → Nat → ECounts

private def checkExprFast : Ixon.Expr → Option ECounts
  | .sort _ | .var _ | .str _ | .nat _ | .share _ => some (.mk 0 0 0)
  | .ref _ idxs | .recur _ idxs =>
    if decide (idxs.size < UInt64.size) then some (.mk 0 0 0) else none
  | .prj _ _ val =>
    match checkExprFast val with
    | some _ => some (.mk 0 0 0)
    | none => none
  | .app f arg =>
    match checkExprFast f, checkExprFast arg with
    | some (.mk apps _ _), some _ =>
      if decide (apps + 1 < UInt64.size) then some (.mk (apps + 1) 0 0) else none
    | _, _ => none
  | .lam ty body =>
    match checkExprFast ty, checkExprFast body with
    | some _, some (.mk _ lams _) =>
      if decide (lams + 1 < UInt64.size) then some (.mk 0 (lams + 1) 0) else none
    | _, _ => none
  | .all ty body =>
    match checkExprFast ty, checkExprFast body with
    | some _, some (.mk _ _ alls) =>
      if decide (alls + 1 < UInt64.size) then some (.mk 0 0 (alls + 1)) else none
    | _, _ => none
  | .letE _ _ ty val body =>
    match checkExprFast ty, checkExprFast val, checkExprFast body with
    | some _, some _, some _ => some (.mk 0 0 0)
    | _, _, _ => none

private theorem checkExprFast_spec :
    ∀ (e : Ixon.Expr) {a l q : Nat},
      checkExprFast e = some (.mk a l q) →
      a = e.appCount ∧ l = e.lamCount ∧ q = e.allCount ∧ e.wireWF
  | .sort _, _, _, _, h => by injection h with hk; injection hk with h1 h2 h3; subst h1 h2 h3; exact ⟨rfl, rfl, rfl, trivial⟩
  | .var _, _, _, _, h => by injection h with hk; injection hk with h1 h2 h3; subst h1 h2 h3; exact ⟨rfl, rfl, rfl, trivial⟩
  | .str _, _, _, _, h => by injection h with hk; injection hk with h1 h2 h3; subst h1 h2 h3; exact ⟨rfl, rfl, rfl, trivial⟩
  | .nat _, _, _, _, h => by injection h with hk; injection hk with h1 h2 h3; subst h1 h2 h3; exact ⟨rfl, rfl, rfl, trivial⟩
  | .share _, _, _, _, h => by injection h with hk; injection hk with h1 h2 h3; subst h1 h2 h3; exact ⟨rfl, rfl, rfl, trivial⟩
  | .ref _ idxs, _, _, _, h => by
    unfold checkExprFast at h
    by_cases hlt : idxs.size < UInt64.size
    · rw [decide_eq_true hlt] at h
      simp only [↓reduceIte, Option.some.injEq] at h
      injection h with h1 h2 h3; subst h1 h2 h3
      exact ⟨rfl, rfl, rfl, hlt⟩
    · rw [decide_eq_false hlt] at h
      simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | .recur _ idxs, _, _, _, h => by
    unfold checkExprFast at h
    by_cases hlt : idxs.size < UInt64.size
    · rw [decide_eq_true hlt] at h
      simp only [↓reduceIte, Option.some.injEq] at h
      injection h with h1 h2 h3; subst h1 h2 h3
      exact ⟨rfl, rfl, rfl, hlt⟩
    · rw [decide_eq_false hlt] at h
      simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | .prj _ _ val, _, _, _, h => by
    unfold checkExprFast at h
    cases hv : checkExprFast val with
    | none => rw [hv] at h; cases h
    | some c =>
      cases c; rw [hv] at h; dsimp only at h
      injection h with hk; injection hk with h1 h2 h3; subst h1 h2 h3
      exact ⟨rfl, rfl, rfl, (checkExprFast_spec val hv).2.2.2⟩
  | .app f arg, _, _, _, h => by
    unfold checkExprFast at h
    cases hf : checkExprFast f with
    | none => rw [hf] at h; cases h
    | some cf =>
      rcases cf with ⟨apps, _, _⟩
      cases ha : checkExprFast arg with
      | none => rw [hf, ha] at h; cases h
      | some ca =>
        cases ca; rw [hf, ha] at h; dsimp only at h
        by_cases hlt : apps + 1 < UInt64.size
        · rw [decide_eq_true hlt] at h
          simp only [↓reduceIte, Option.some.injEq] at h
          injection h with h1 h2 h3; subst h1 h2 h3
          obtain ⟨hae, _, _, hwff⟩ := checkExprFast_spec f hf
          subst hae
          exact ⟨rfl, rfl, rfl, hwff, (checkExprFast_spec arg ha).2.2.2, hlt⟩
        · rw [decide_eq_false hlt] at h
          simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | .lam ty body, _, _, _, h => by
    unfold checkExprFast at h
    cases ht : checkExprFast ty with
    | none => rw [ht] at h; cases h
    | some ct =>
      cases ct
      cases hb : checkExprFast body with
      | none => rw [ht, hb] at h; cases h
      | some cb =>
        rcases cb with ⟨_, lams, _⟩; rw [ht, hb] at h; dsimp only at h
        by_cases hlt : lams + 1 < UInt64.size
        · rw [decide_eq_true hlt] at h
          simp only [↓reduceIte, Option.some.injEq] at h
          injection h with h1 h2 h3; subst h1 h2 h3
          obtain ⟨_, hle, _, hwfb⟩ := checkExprFast_spec body hb
          subst hle
          exact ⟨rfl, rfl, rfl, (checkExprFast_spec ty ht).2.2.2, hwfb, hlt⟩
        · rw [decide_eq_false hlt] at h
          simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | .all ty body, _, _, _, h => by
    unfold checkExprFast at h
    cases ht : checkExprFast ty with
    | none => rw [ht] at h; cases h
    | some ct =>
      cases ct
      cases hb : checkExprFast body with
      | none => rw [ht, hb] at h; cases h
      | some cb =>
        rcases cb with ⟨_, _, alls⟩; rw [ht, hb] at h; dsimp only at h
        by_cases hlt : alls + 1 < UInt64.size
        · rw [decide_eq_true hlt] at h
          simp only [↓reduceIte, Option.some.injEq] at h
          injection h with h1 h2 h3; subst h1 h2 h3
          obtain ⟨_, _, hqe, hwfb⟩ := checkExprFast_spec body hb
          subst hqe
          exact ⟨rfl, rfl, rfl, (checkExprFast_spec ty ht).2.2.2, hwfb, hlt⟩
        · rw [decide_eq_false hlt] at h
          simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | .letE _ _ ty val body, _, _, _, h => by
    unfold checkExprFast at h
    cases ht : checkExprFast ty with
    | none => rw [ht] at h; cases h
    | some ct =>
      cases ct
      cases hv : checkExprFast val with
      | none => rw [ht, hv] at h; cases h
      | some cv =>
        cases cv
        cases hb : checkExprFast body with
        | none => rw [ht, hv, hb] at h; cases h
        | some cb =>
          cases cb; rw [ht, hv, hb] at h; dsimp only at h
          injection h with hk; injection hk with h1 h2 h3; subst h1 h2 h3
          exact ⟨rfl, rfl, rfl, (checkExprFast_spec ty ht).2.2.2,
            (checkExprFast_spec val hv).2.2.2, (checkExprFast_spec body hb).2.2.2⟩

private def validUnivFast (u : Ixon.Univ) : Bool := (checkUnivFast u).isSome
private def validExprFast (e : Ixon.Expr) : Bool := (checkExprFast e).isSome

private theorem validUnivFast_ok {u : Ixon.Univ} (h : validUnivFast u = true) : u.wireWF := by
  unfold validUnivFast at h
  cases hc : checkUnivFast u with
  | none => rw [hc] at h; cases h
  | some cnt => exact (checkUnivFast_spec u hc).2

private theorem validExprFast_ok {e : Ixon.Expr} (h : validExprFast e = true) : e.wireWF := by
  unfold validExprFast at h
  cases hc : checkExprFast e with
  | none => rw [hc] at h; cases h
  | some cnts => cases cnts; exact (checkExprFast_spec e hc).2.2.2

private def validArrayFast {α : Type} (values : Array α) (valid : α → Bool) : Bool :=
  decide (values.size < UInt64.size) && values.toList.all valid

private theorem validArrayFast_ok {α : Type} {values : Array α} {valid : α → Bool} {P : α → Prop}
    (hp : ∀ x, valid x = true → P x) (h : validArrayFast values valid = true) :
    values.size < UInt64.size ∧ ∀ x ∈ values, P x := by
  simp only [validArrayFast, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1, fun x hx => hp x (h.2 x (Array.mem_toList_iff.mpr hx))⟩

private def validDefFast (d : Ixon.Definition) : Bool :=
  validExprFast d.typ && validExprFast d.value

private def validRecFast (r : Ixon.Recursor) : Bool :=
  validExprFast r.typ && validArrayFast r.rules (fun rule => validExprFast rule.rhs)

private def validIndFast (i : Ixon.Inductive) : Bool :=
  validExprFast i.typ && validArrayFast i.ctors (fun ctor => validExprFast ctor.typ)

private def validMutFast : Ixon.MutConst → Bool
  | .defn d => validDefFast d
  | .indc i => validIndFast i
  | .recr r => validRecFast r

private def validInfoFast : Ixon.ConstantInfo → Bool
  | .defn d => validDefFast d
  | .recr r => validRecFast r
  | .axio a => validExprFast a.typ
  | .quot q => validExprFast q.typ
  | .cPrj p => p.block.hash.size == 32
  | .rPrj p => p.block.hash.size == 32
  | .iPrj p => p.block.hash.size == 32
  | .dPrj p => p.block.hash.size == 32
  | .muts ms => validArrayFast ms validMutFast

private def validBinderNodeFast : Ixon.BinderNode → Bool
  | .ifAllZero params _ => decide (params.size < UInt64.size)
  | _ => true

private def validBinderBlockFast (b : Ixon.BinderBlock) : Bool :=
  validArrayFast b.nodes validBinderNodeFast

private def validConstantFast (c : Ixon.Constant) : Bool :=
  validInfoFast c.info &&
  validArrayFast c.sharing validExprFast &&
  validArrayFast c.refs (fun a => a.hash.size == 32) &&
  validArrayFast c.univs validUnivFast &&
  validArrayFast c.binders validBinderBlockFast

private theorem validMutFast_ok : ∀ {m : Ixon.MutConst}, validMutFast m = true → m.wireWF
  | .defn d, h => by
    simp only [validMutFast, validDefFast, Bool.and_eq_true] at h
    exact ⟨validExprFast_ok h.1, validExprFast_ok h.2⟩
  | .indc i, h => by
    simp only [validMutFast, validIndFast, Bool.and_eq_true] at h
    obtain ⟨hsz, hct⟩ := validArrayFast_ok (fun c hc => validExprFast_ok hc) h.2
    exact ⟨validExprFast_ok h.1, hsz, hct⟩
  | .recr r, h => by
    simp only [validMutFast, validRecFast, Bool.and_eq_true] at h
    obtain ⟨hsz, hrl⟩ := validArrayFast_ok (fun rl hr => validExprFast_ok hr) h.2
    exact ⟨validExprFast_ok h.1, hsz, hrl⟩

private theorem validInfoFast_ok : ∀ {ci : Ixon.ConstantInfo}, validInfoFast ci = true → ci.wireWF
  | .defn d, h => validMutFast_ok (m := .defn d) h
  | .recr r, h => validMutFast_ok (m := .recr r) h
  | .axio a, h => validExprFast_ok h
  | .quot q, h => validExprFast_ok h
  | .cPrj p, h => beq_iff_eq.mp h
  | .rPrj p, h => beq_iff_eq.mp h
  | .iPrj p, h => beq_iff_eq.mp h
  | .dPrj p, h => beq_iff_eq.mp h
  | .muts ms, h => validArrayFast_ok (fun _ hm => validMutFast_ok hm) h

private theorem validConstantFast_ok {c : Ixon.Constant} (h : validConstantFast c = true) :
    c.wireWF := by
  simp only [validConstantFast, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hinfo, hsh⟩, hrefs⟩, hunivs⟩, hbind⟩ := h
  obtain ⟨hsh_sz, hsh_wf⟩ := validArrayFast_ok (fun _ he => validExprFast_ok he) hsh
  obtain ⟨hrefs_sz, hrefs_wf⟩ := validArrayFast_ok (fun _ ha => beq_iff_eq.mp ha) hrefs
  obtain ⟨hunivs_sz, hunivs_wf⟩ := validArrayFast_ok (fun _ hu => validUnivFast_ok hu) hunivs
  obtain ⟨hbind_sz, hbind_wf⟩ := validArrayFast_ok (P := Ixon.BinderBlock.wireWF)
    (fun b hb => validArrayFast_ok (P := Ixon.BinderNode.wireWF)
      (fun n hn => by cases n <;> simp_all [validBinderNodeFast, Ixon.BinderNode.wireWF]) hb)
    hbind
  exact ⟨validInfoFast_ok hinfo, hsh_sz, hsh_wf, hrefs_sz, hrefs_wf, hunivs_sz, hunivs_wf,
    hbind_sz, hbind_wf⟩

/-! ## Fuel-indexed pure Ixon serializer (`encConstantFuel`) -/

private def EncodesTo (m : Ixon.PutM Unit) (k out : List UInt8) : Prop :=
  ∀ s : ByteArray, (m.run s).2.data.toList ++ k = s.data.toList ++ out

private theorem EncodesTo.pure {k : List UInt8} : EncodesTo (Pure.pure ()) k k := fun _ => rfl

private theorem EncodesTo.bindUnit {m₁ m₂ : Ixon.PutM Unit} {k mid out : List UInt8}
    (h₁ : EncodesTo m₁ mid out) (h₂ : EncodesTo m₂ k mid) :
    EncodesTo (m₁ >>= fun _ => m₂) k out := by
  intro s
  change (m₂.run (m₁.run s).2).2.data.toList ++ k = s.data.toList ++ out
  rw [h₂, h₁]

private theorem EncodesTo.seqRight {m₁ m₂ : Ixon.PutM Unit} {k mid out : List UInt8}
    (h₁ : EncodesTo m₁ mid out) (h₂ : EncodesTo m₂ k mid) :
    EncodesTo (m₁ *> m₂) k out := by
  rw [seqRight_eq_bind]
  exact EncodesTo.bindUnit h₁ h₂

private theorem EncodesTo.putU8 (x : UInt8) (k : List UInt8) :
    EncodesTo (Ixon.putU8 x) k (x :: k) := by
  intro s
  have hp : ((Ixon.putU8 x).run s).2 = s.push x := rfl
  rw [hp]
  cases s with
  | mk arr =>
    have hd : (ByteArray.mk arr).push x = ByteArray.mk (arr.push x) := rfl
    rw [hd]; dsimp only
    rw [Array.toList_push, List.append_assoc]; rfl

private theorem EncodesTo.putBytes (b : ByteArray) (k : List UInt8) :
    EncodesTo (Ixon.putBytes b) k (b.data.toList ++ k) := by
  intro s
  have hw := Ixon.Verify.Codec.ConstantTables.putBytes_writes b s
  change ((), ((Ixon.putBytes b).run s).2) = ((), s ++ b) at hw
  injection hw with _ h2
  rw [h2, ByteArray.data_append, Array.toList_append, List.append_assoc]

private def encList {α : Type} (enc : α → List UInt8 → List UInt8) :
    List α → List UInt8 → List UInt8
  | [], k => k
  | x :: xs, k => enc x (encList enc xs k)

private theorem encList_spec {α : Type} {putm : α → Ixon.PutM Unit}
    {enc : α → List UInt8 → List UInt8}
    (h : ∀ x k, EncodesTo (putm x) k (enc x k)) :
    ∀ (xs : List α) (k : List UInt8),
      EncodesTo (Ixon.Verify.Codec.ConstantTables.putMany putm xs) k (encList enc xs k)
  | [], _ => EncodesTo.pure
  | x :: xs, k => by
    unfold Ixon.Verify.Codec.ConstantTables.putMany
    rw [List.foldlM_cons]
    exact EncodesTo.bindUnit (h x _) (encList_spec h xs k)

private theorem forArray_encList_spec {α : Type} {putm : α → Ixon.PutM Unit}
    {enc : α → List UInt8 → List UInt8} {arr : Array α} {k : List UInt8}
    (h : ∀ x k, EncodesTo (putm x) k (enc x k)) :
    EncodesTo (do for x in arr do putm x) k (encList enc arr.toList k) := by
  rw [Ixon.Verify.Codec.ConstantTables.arrayPut_eq_putMany]
  exact encList_spec h arr.toList k

private def encManyOpt {α : Type} (enc : α → List UInt8 → Option (List UInt8)) :
    List α → List UInt8 → Option (List UInt8)
  | [], k => some k
  | x :: xs, k =>
    match encManyOpt enc xs k with
    | some mid => enc x mid
    | none => none

private theorem encManyOpt_spec {α : Type} {putm : α → Ixon.PutM Unit}
    {enc : α → List UInt8 → Option (List UInt8)}
    (h : ∀ x k out, enc x k = some out → EncodesTo (putm x) k out) :
    ∀ (xs : List α) {k out : List UInt8},
      encManyOpt enc xs k = some out →
      EncodesTo (Ixon.Verify.Codec.ConstantTables.putMany putm xs) k out
  | [], _, _, hok => by injection hok with hk; subst hk; exact EncodesTo.pure
  | x :: xs, k, out, hok => by
    unfold encManyOpt at hok
    cases hm : encManyOpt enc xs k with
    | none => rw [hm] at hok; cases hok
    | some mid =>
      rw [hm] at hok
      unfold Ixon.Verify.Codec.ConstantTables.putMany
      rw [List.foldlM_cons]
      exact EncodesTo.bindUnit (h x mid out hok) (encManyOpt_spec h xs hm)

private theorem forArray_encManyOpt_spec {α : Type} {putm : α → Ixon.PutM Unit}
    {enc : α → List UInt8 → Option (List UInt8)} {arr : Array α} {k out : List UInt8}
    (h : ∀ x k out, enc x k = some out → EncodesTo (putm x) k out)
    (hok : encManyOpt enc arr.toList k = some out) :
    EncodesTo (do for x in arr do putm x) k out := by
  rw [Ixon.Verify.Codec.ConstantTables.arrayPut_eq_putMany]
  exact encManyOpt_spec h arr.toList hok

private theorem listPut_eq_putMany {α : Type} (putm : α → Ixon.PutM Unit) (xs : List α) :
    (do for x in xs do putm x) = Ixon.Verify.Codec.ConstantTables.putMany putm xs := by
  simp [Ixon.Verify.Codec.ConstantTables.putMany]

private theorem forList_bind_encManyOpt_spec {α : Type} {putm : α → Ixon.PutM Unit}
    {enc : α → List UInt8 → Option (List UInt8)} {xs : List α} {next : Ixon.PutM Unit}
    {k mid out : List UInt8}
    (h : ∀ x k out, enc x k = some out → EncodesTo (putm x) k out)
    (hok : encManyOpt enc xs mid = some out)
    (hnext : EncodesTo next k mid) :
    EncodesTo (do
      for x in xs do putm x
      next) k out := by
  have heq :
      (do
        for x in xs do putm x
        next) =
      (Ixon.Verify.Codec.ConstantTables.putMany putm xs >>= fun _ => next) := by
    simp [Ixon.Verify.Codec.ConstantTables.putMany]
  rw [heq]
  exact EncodesTo.bindUnit (encManyOpt_spec h xs hok) hnext

private theorem forArray_bind_encList_spec {α : Type} {putm : α → Ixon.PutM Unit}
    {enc : α → List UInt8 → List UInt8} {arr : Array α} {next : Ixon.PutM Unit}
    {k mid : List UInt8}
    (h : ∀ x k, EncodesTo (putm x) k (enc x k))
    (hnext : EncodesTo next k mid) :
    EncodesTo (do
      for x in arr do putm x
      next) k (encList enc arr.toList mid) := by
  have heq :
      (do
        for x in arr do putm x
        next) =
      (Ixon.Verify.Codec.ConstantTables.putMany putm arr.toList >>= fun _ => next) := by
    rw [← Array.forIn_toList]
    simp [Ixon.Verify.Codec.ConstantTables.putMany]
  rw [heq]
  exact EncodesTo.bindUnit (encList_spec h arr.toList mid) hnext

private theorem forArray_bind_encManyOpt_spec {α : Type} {putm : α → Ixon.PutM Unit}
    {enc : α → List UInt8 → Option (List UInt8)} {arr : Array α} {next : Ixon.PutM Unit}
    {k mid out : List UInt8}
    (h : ∀ x k out, enc x k = some out → EncodesTo (putm x) k out)
    (hok : encManyOpt enc arr.toList mid = some out)
    (hnext : EncodesTo next k mid) :
    EncodesTo (do
      for x in arr do putm x
      next) k out := by
  have heq :
      (do
        for x in arr do putm x
        next) =
      (Ixon.Verify.Codec.ConstantTables.putMany putm arr.toList >>= fun _ => next) := by
    rw [← Array.forIn_toList]
    simp [Ixon.Verify.Codec.ConstantTables.putMany]
  rw [heq]
  exact EncodesTo.bindUnit (encManyOpt_spec h arr.toList hok) hnext

private def encU64TrimmedLEAux (x : UInt64) : Nat → List UInt8 → List UInt8
  | 0, k => k
  | len + 1, k => x.toUInt8 :: encU64TrimmedLEAux (x >>> 8) len k

private theorem encU64TrimmedLEAux_spec (x : UInt64) :
    ∀ (len : Nat) (k : List UInt8),
      EncodesTo (Ixon.putU64TrimmedLEAux x len) k (encU64TrimmedLEAux x len k)
  | 0, _ => EncodesTo.pure
  | len + 1, k =>
    EncodesTo.bindUnit (EncodesTo.putU8 x.toUInt8 _) (encU64TrimmedLEAux_spec (x >>> 8) len k)

private def encTagN (f : Nat) (flag : UInt8) (value : UInt64) (k : List UInt8) : List UInt8 :=
  let v := value.toNat
  let lead := 2 ^ (8 - f - 1)
  let mbit := 2 ^ (8 - f - 2)
  if v < Ixon.tagNEnd1 f then
    Ixon.tagNHeader f flag v :: k
  else if v < Ixon.tagNEnd2 f then
    Ixon.tagNHeader f flag (lead + (v - Ixon.tagNEnd1 f) / 256) ::
      ((v - Ixon.tagNEnd1 f) % 256).toUInt8 :: k
  else if v < Ixon.tagNEnd3 f then
    Ixon.tagNHeader f flag (lead + mbit) ::
      encU64TrimmedLEAux (v - Ixon.tagNEnd2 f).toUInt64 2 k
  else if v < Ixon.tagNEnd4 f then
    Ixon.tagNHeader f flag (lead + mbit + 1) ::
      encU64TrimmedLEAux (v - Ixon.tagNEnd3 f).toUInt64 3 k
  else if v < Ixon.tagNEnd5 f then
    Ixon.tagNHeader f flag (lead + mbit + 2) ::
      encU64TrimmedLEAux (v - Ixon.tagNEnd4 f).toUInt64 4 k
  else
    Ixon.tagNHeader f flag (lead + mbit + 3) ::
      encU64TrimmedLEAux (v - Ixon.tagNEnd5 f).toUInt64 8 k

private theorem encTagN_spec (f : Nat) (flag : UInt8) (value : UInt64) (k : List UInt8) :
    EncodesTo (Ixon.putTagN f flag value) k (encTagN f flag value k) := by
  unfold Ixon.putTagN encTagN
  dsimp only
  split
  · exact EncodesTo.putU8 _ _
  · split
    · exact EncodesTo.bindUnit (EncodesTo.putU8 _ _) (EncodesTo.putU8 _ _)
    · split
      · exact EncodesTo.bindUnit (EncodesTo.putU8 _ _) (encU64TrimmedLEAux_spec _ 2 _)
      · split
        · exact EncodesTo.bindUnit (EncodesTo.putU8 _ _) (encU64TrimmedLEAux_spec _ 3 _)
        · split
          · exact EncodesTo.bindUnit (EncodesTo.putU8 _ _) (encU64TrimmedLEAux_spec _ 4 _)
          · exact EncodesTo.bindUnit (EncodesTo.putU8 _ _) (encU64TrimmedLEAux_spec _ 8 _)

private def encUnivFuel : Nat → Ixon.Univ → List UInt8 → Option (List UInt8)
  | 0, _, _ => none
  | _ + 1, .zero, k => some (encTagN 2 Ixon.Univ.FLAG_ZERO_SUCC 0 k)
  | fuel + 1, u@(.succ _), k =>
    match encUnivFuel fuel u.succBase k with
    | some rest => some (encTagN 2 Ixon.Univ.FLAG_ZERO_SUCC u.succCount rest)
    | none => none
  | fuel + 1, .max a b, k =>
    match encUnivFuel fuel b k with
    | some rb =>
      match encUnivFuel fuel a rb with
      | some ra => some (encTagN 2 Ixon.Univ.FLAG_MAX 0 ra)
      | none => none
    | none => none
  | fuel + 1, .imax a b, k =>
    match encUnivFuel fuel b k with
    | some rb =>
      match encUnivFuel fuel a rb with
      | some ra => some (encTagN 2 Ixon.Univ.FLAG_IMAX 0 ra)
      | none => none
    | none => none
  | _ + 1, .var idx, k => some (encTagN 2 Ixon.Univ.FLAG_VAR idx k)

private theorem encUnivFuel_spec :
    ∀ (fuel : Nat) (u : Ixon.Univ) {k out : List UInt8},
      encUnivFuel fuel u k = some out → EncodesTo (Ixon.putUniv u) k out
  | 0, _, _, _, h => nomatch h
  | _ + 1, .zero, k, _, h => by
    injection h with ho; subst ho; rw [Ixon.putUniv]; exact encTagN_spec 2 _ 0 k
  | fuel + 1, .succ inner, k, _, h => by
    unfold encUnivFuel at h
    cases hr : encUnivFuel fuel (Ixon.Univ.succ inner).succBase k with
    | none => rw [hr] at h; cases h
    | some rest =>
      rw [hr] at h; injection h with ho; subst ho
      rw [Ixon.putUniv]
      exact EncodesTo.bindUnit (encTagN_spec 2 _ _ rest) (encUnivFuel_spec fuel _ hr)
  | fuel + 1, .max a b, k, _, h => by
    unfold encUnivFuel at h
    cases hb : encUnivFuel fuel b k with
    | none => rw [hb] at h; cases h
    | some rb =>
      rw [hb] at h; dsimp only at h
      cases ha : encUnivFuel fuel a rb with
      | none => rw [ha] at h; cases h
      | some ra =>
        rw [ha] at h; injection h with ho; subst ho
        rw [Ixon.putUniv]
        exact EncodesTo.bindUnit (encTagN_spec 2 _ 0 ra)
          (EncodesTo.bindUnit (encUnivFuel_spec fuel a ha) (encUnivFuel_spec fuel b hb))
  | fuel + 1, .imax a b, k, _, h => by
    unfold encUnivFuel at h
    cases hb : encUnivFuel fuel b k with
    | none => rw [hb] at h; cases h
    | some rb =>
      rw [hb] at h; dsimp only at h
      cases ha : encUnivFuel fuel a rb with
      | none => rw [ha] at h; cases h
      | some ra =>
        rw [ha] at h; injection h with ho; subst ho
        rw [Ixon.putUniv]
        exact EncodesTo.bindUnit (encTagN_spec 2 _ 0 ra)
          (EncodesTo.bindUnit (encUnivFuel_spec fuel a ha) (encUnivFuel_spec fuel b hb))
  | _ + 1, .var idx, k, _, h => by
    injection h with ho; subst ho; rw [Ixon.putUniv]; exact encTagN_spec 2 _ idx k

private def encExprFuel : Nat → Ixon.Expr → List UInt8 → Option (List UInt8)
  | 0, _, _ => none
  | _ + 1, .sort idx, k => some (encTagN 4 Ixon.Expr.FLAG_SORT idx k)
  | _ + 1, .var idx, k => some (encTagN 4 Ixon.Expr.FLAG_VAR idx k)
  | _ + 1, .ref refIdx univIdxs, k =>
    some (encTagN 4 Ixon.Expr.FLAG_REF univIdxs.size.toUInt64
      (encTagN 0 0 refIdx (encList (encTagN 0 0) univIdxs.toList k)))
  | _ + 1, .recur recIdx univIdxs, k =>
    some (encTagN 4 Ixon.Expr.FLAG_REC univIdxs.size.toUInt64
      (encTagN 0 0 recIdx (encList (encTagN 0 0) univIdxs.toList k)))
  | fuel + 1, .prj typeRefIdx fieldIdx val, k =>
    match encExprFuel fuel val k with
    | some rv => some (encTagN 4 Ixon.Expr.FLAG_PRJ fieldIdx (encTagN 0 0 typeRefIdx rv))
    | none => none
  | _ + 1, .str refIdx, k => some (encTagN 4 Ixon.Expr.FLAG_STR refIdx k)
  | _ + 1, .nat refIdx, k => some (encTagN 4 Ixon.Expr.FLAG_NAT refIdx k)
  | fuel + 1, e@(.app _ _), k =>
    let p := e.collectAppArgs
    match encManyOpt (encExprFuel fuel) p.1 k with
    | some rargs =>
      match encExprFuel fuel p.2 rargs with
      | some rfn => some (encTagN 4 Ixon.Expr.FLAG_APP p.1.length.toUInt64 rfn)
      | none => none
    | none => none
  | fuel + 1, e@(.lam _ _), k =>
    let p := e.collectLamBinders
    match encExprFuel fuel p.2 k with
    | some rbody =>
      match encManyOpt (encExprFuel fuel) p.1 rbody with
      | some rtys => some (encTagN 4 Ixon.Expr.FLAG_LAM p.1.length.toUInt64 rtys)
      | none => none
    | none => none
  | fuel + 1, e@(.all _ _), k =>
    let p := e.collectAllBinders
    match encExprFuel fuel p.2 k with
    | some rbody =>
      match encManyOpt (encExprFuel fuel) p.1 rbody with
      | some rtys => some (encTagN 4 Ixon.Expr.FLAG_ALL p.1.length.toUInt64 rtys)
      | none => none
    | none => none
  | fuel + 1, .letE nonDep mode ty val body, k =>
    match encExprFuel fuel body k with
    | some rb =>
      match encExprFuel fuel val rb with
      | some rv =>
        match encExprFuel fuel ty rv with
        | some rt => some (encTagN 4 Ixon.Expr.FLAG_LET (Ixon.LetMode.header nonDep mode) rt)
        | none => none
      | none => none
    | none => none
  | _ + 1, .share idx, k => some (encTagN 4 Ixon.Expr.FLAG_SHARE idx k)

private theorem encExprFuel_spec :
    ∀ (fuel : Nat) (e : Ixon.Expr) {k out : List UInt8},
      encExprFuel fuel e k = some out → EncodesTo (Ixon.putExpr e) k out
  | 0, _, _, _, h => nomatch h
  | _ + 1, .sort idx, k, _, h => by
    injection h with ho; subst ho; rw [Ixon.putExpr]; exact encTagN_spec 4 _ idx k
  | _ + 1, .var idx, k, _, h => by
    injection h with ho; subst ho; rw [Ixon.putExpr]; exact encTagN_spec 4 _ idx k
  | _ + 1, .ref refIdx univIdxs, k, _, h => by
    injection h with ho; subst ho; rw [Ixon.putExpr]
    exact EncodesTo.bindUnit (encTagN_spec 4 _ _ _)
      (EncodesTo.bindUnit (encTagN_spec 0 0 refIdx _)
        (forArray_encList_spec (fun u ku => encTagN_spec 0 0 u ku)))
  | _ + 1, .recur recIdx univIdxs, k, _, h => by
    injection h with ho; subst ho; rw [Ixon.putExpr]
    exact EncodesTo.bindUnit (encTagN_spec 4 _ _ _)
      (EncodesTo.bindUnit (encTagN_spec 0 0 recIdx _)
        (forArray_encList_spec (fun u ku => encTagN_spec 0 0 u ku)))
  | fuel + 1, .prj typeRefIdx fieldIdx val, k, _, h => by
    unfold encExprFuel at h
    cases hv : encExprFuel fuel val k with
    | none => rw [hv] at h; cases h
    | some rv =>
      rw [hv] at h; injection h with ho; subst ho
      rw [Ixon.putExpr]
      exact EncodesTo.bindUnit (encTagN_spec 4 _ _ _)
        (EncodesTo.bindUnit (encTagN_spec 0 0 typeRefIdx _) (encExprFuel_spec fuel val hv))
  | _ + 1, .str refIdx, k, _, h => by
    injection h with ho; subst ho; rw [Ixon.putExpr]; exact encTagN_spec 4 _ refIdx k
  | _ + 1, .nat refIdx, k, _, h => by
    injection h with ho; subst ho; rw [Ixon.putExpr]; exact encTagN_spec 4 _ refIdx k
  | fuel + 1, .app f arg, k, _, h => by
    unfold encExprFuel at h; dsimp only at h
    cases ha : encManyOpt (encExprFuel fuel) (Ixon.Expr.app f arg).collectAppArgs.1 k with
    | none => rw [ha] at h; cases h
    | some rargs =>
      rw [ha] at h; dsimp only at h
      cases hf : encExprFuel fuel (Ixon.Expr.app f arg).collectAppArgs.2 rargs with
      | none => rw [hf] at h; cases h
      | some rfn =>
        rw [hf] at h; injection h with ho; subst ho
        rw [Ixon.putExpr, listPut_eq_putMany]
        exact EncodesTo.bindUnit (encTagN_spec 4 _ _ _)
          (EncodesTo.bindUnit (encExprFuel_spec fuel _ hf)
            (encManyOpt_spec (fun x _ _ hx => encExprFuel_spec fuel x hx) _ ha))
  | fuel + 1, .lam ty body, k, _, h => by
    unfold encExprFuel at h; dsimp only at h
    cases hb : encExprFuel fuel (Ixon.Expr.lam ty body).collectLamBinders.2 k with
    | none => rw [hb] at h; cases h
    | some rbody =>
      rw [hb] at h; dsimp only at h
      cases ht : encManyOpt (encExprFuel fuel) (Ixon.Expr.lam ty body).collectLamBinders.1 rbody with
      | none => rw [ht] at h; cases h
      | some rtys =>
        rw [ht] at h; injection h with ho; subst ho
        rw [Ixon.putExpr]
        exact EncodesTo.bindUnit (encTagN_spec 4 _ _ _)
          (forList_bind_encManyOpt_spec (fun x _ _ hx => encExprFuel_spec fuel x hx) ht
            (encExprFuel_spec fuel _ hb))
  | fuel + 1, .all ty body, k, _, h => by
    unfold encExprFuel at h; dsimp only at h
    cases hb : encExprFuel fuel (Ixon.Expr.all ty body).collectAllBinders.2 k with
    | none => rw [hb] at h; cases h
    | some rbody =>
      rw [hb] at h; dsimp only at h
      cases ht : encManyOpt (encExprFuel fuel) (Ixon.Expr.all ty body).collectAllBinders.1 rbody with
      | none => rw [ht] at h; cases h
      | some rtys =>
        rw [ht] at h; injection h with ho; subst ho
        rw [Ixon.putExpr]
        exact EncodesTo.bindUnit (encTagN_spec 4 _ _ _)
          (forList_bind_encManyOpt_spec (fun x _ _ hx => encExprFuel_spec fuel x hx) ht
            (encExprFuel_spec fuel _ hb))
  | fuel + 1, .letE nonDep mode ty val body, k, _, h => by
    unfold encExprFuel at h
    cases hb : encExprFuel fuel body k with
    | none => rw [hb] at h; cases h
    | some rb =>
      rw [hb] at h; dsimp only at h
      cases hv : encExprFuel fuel val rb with
      | none => rw [hv] at h; cases h
      | some rv =>
        rw [hv] at h; dsimp only at h
        cases ht : encExprFuel fuel ty rv with
        | none => rw [ht] at h; cases h
        | some rt =>
          rw [ht] at h; injection h with ho; subst ho
          rw [Ixon.putExpr]
          exact EncodesTo.bindUnit (encTagN_spec 4 _ _ _)
            (EncodesTo.bindUnit (encExprFuel_spec fuel ty ht)
              (EncodesTo.bindUnit (encExprFuel_spec fuel val hv)
                (encExprFuel_spec fuel body hb)))
  | _ + 1, .share idx, k, _, h => by
    injection h with ho; subst ho; rw [Ixon.putExpr]; exact encTagN_spec 4 _ idx k

private def encAddress (a : _root_.Address) (k : List UInt8) : List UInt8 :=
  a.hash.data.toList ++ k

private theorem encAddress_spec (a : _root_.Address) (k : List UInt8) :
    EncodesTo (Ixon.Serialize.put a) k (encAddress a k) :=
  EncodesTo.putBytes a.hash k

private def encDefFuel (fuel : Nat) (d : Ixon.Definition) (k : List UInt8) : Option (List UInt8) :=
  match encExprFuel fuel d.value k with
  | some rv =>
    match encExprFuel fuel d.typ rv with
    | some rt => some (Ixon.packDefinitionFlags d :: encTagN 0 0 d.lvls rt)
    | none => none
  | none => none

private theorem encDefFuel_spec (fuel : Nat) (d : Ixon.Definition) {k out : List UInt8}
    (h : encDefFuel fuel d k = some out) :
    EncodesTo (Ixon.putDefinition d) k out := by
  unfold encDefFuel at h
  cases hv : encExprFuel fuel d.value k with
  | none => rw [hv] at h; cases h
  | some rv =>
    rw [hv] at h; dsimp only at h
    cases ht : encExprFuel fuel d.typ rv with
    | none => rw [ht] at h; cases h
    | some rt =>
      rw [ht] at h; injection h with ho; subst ho
      exact EncodesTo.bindUnit (EncodesTo.putU8 _ _)
        (EncodesTo.bindUnit (encTagN_spec 0 0 d.lvls _)
          (EncodesTo.bindUnit (encExprFuel_spec fuel d.typ ht) (encExprFuel_spec fuel d.value hv)))

private def encRecRuleFuel (fuel : Nat) (r : Ixon.RecursorRule) (k : List UInt8) : Option (List UInt8) :=
  match encExprFuel fuel r.rhs k with
  | some rr => some (encTagN 0 0 r.fields rr)
  | none => none

private theorem encRecRuleFuel_spec (fuel : Nat) (r : Ixon.RecursorRule) {k out : List UInt8}
    (h : encRecRuleFuel fuel r k = some out) :
    EncodesTo (Ixon.putRecursorRule r) k out := by
  unfold encRecRuleFuel at h
  cases hr : encExprFuel fuel r.rhs k with
  | none => rw [hr] at h; cases h
  | some rr =>
    rw [hr] at h; injection h with ho; subst ho
    exact EncodesTo.bindUnit (encTagN_spec 0 0 r.fields _) (encExprFuel_spec fuel r.rhs hr)

private def encRecFuel (fuel : Nat) (r : Ixon.Recursor) (k : List UInt8) : Option (List UInt8) :=
  match encManyOpt (encRecRuleFuel fuel) r.rules.toList k with
  | some rrules =>
    match encExprFuel fuel r.typ (encTagN 0 0 r.rules.size.toUInt64 rrules) with
    | some rt =>
      some (Ixon.packBools [r.k, r.isUnsafe] ::
        encTagN 0 0 r.lvls (encTagN 0 0 r.params (encTagN 0 0 r.indices
          (encTagN 0 0 r.motives (encTagN 0 0 r.minors rt)))))
    | none => none
  | none => none

private theorem encRecFuel_spec (fuel : Nat) (r : Ixon.Recursor) {k out : List UInt8}
    (h : encRecFuel fuel r k = some out) :
    EncodesTo (Ixon.putRecursor r) k out := by
  unfold encRecFuel at h
  cases hrl : encManyOpt (encRecRuleFuel fuel) r.rules.toList k with
  | none => rw [hrl] at h; cases h
  | some rrules =>
    rw [hrl] at h; dsimp only at h
    cases ht : encExprFuel fuel r.typ (encTagN 0 0 r.rules.size.toUInt64 rrules) with
    | none => rw [ht] at h; cases h
    | some rt =>
      rw [ht] at h; injection h with ho; subst ho
      exact EncodesTo.bindUnit (EncodesTo.putU8 _ _)
        (EncodesTo.bindUnit (encTagN_spec 0 0 r.lvls _)
          (EncodesTo.bindUnit (encTagN_spec 0 0 r.params _)
            (EncodesTo.bindUnit (encTagN_spec 0 0 r.indices _)
              (EncodesTo.bindUnit (encTagN_spec 0 0 r.motives _)
                (EncodesTo.bindUnit (encTagN_spec 0 0 r.minors _)
                  (EncodesTo.bindUnit (encExprFuel_spec fuel r.typ ht)
                    (EncodesTo.bindUnit (encTagN_spec 0 0 _ _)
                      (forArray_encManyOpt_spec (fun x _ _ hx => encRecRuleFuel_spec fuel x hx) hrl))))))))

private def encAxioFuel (fuel : Nat) (a : Ixon.Axiom) (k : List UInt8) : Option (List UInt8) :=
  match encExprFuel fuel a.typ k with
  | some rt => some ((if a.isUnsafe then 1 else 0) :: encTagN 0 0 a.lvls rt)
  | none => none

private theorem encAxioFuel_spec (fuel : Nat) (a : Ixon.Axiom) {k out : List UInt8}
    (h : encAxioFuel fuel a k = some out) :
    EncodesTo (Ixon.putAxiom a) k out := by
  unfold encAxioFuel at h
  cases ht : encExprFuel fuel a.typ k with
  | none => rw [ht] at h; cases h
  | some rt =>
    rw [ht] at h; injection h with ho; subst ho
    exact EncodesTo.bindUnit (EncodesTo.putU8 _ _)
      (EncodesTo.bindUnit (encTagN_spec 0 0 a.lvls _) (encExprFuel_spec fuel a.typ ht))

private def encQuotFuel (fuel : Nat) (q : Ixon.Quotient) (k : List UInt8) : Option (List UInt8) :=
  match encExprFuel fuel q.typ k with
  | some rt =>
    let kb : UInt8 := match q.kind with | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3
    some (kb :: encTagN 0 0 q.lvls rt)
  | none => none

private theorem encQuotFuel_spec (fuel : Nat) (q : Ixon.Quotient) {k out : List UInt8}
    (h : encQuotFuel fuel q k = some out) :
    EncodesTo (Ixon.putQuotient q) k out := by
  unfold encQuotFuel at h
  cases ht : encExprFuel fuel q.typ k with
  | none => rw [ht] at h; cases h
  | some rt =>
    rw [ht] at h; injection h with ho; subst ho
    exact EncodesTo.bindUnit (EncodesTo.putU8 _ _)
      (EncodesTo.bindUnit (encTagN_spec 0 0 q.lvls _) (encExprFuel_spec fuel q.typ ht))

private def encCtorFuel (fuel : Nat) (c : Ixon.Constructor) (k : List UInt8) : Option (List UInt8) :=
  match encExprFuel fuel c.typ k with
  | some rt =>
    some (Ixon.packConstructorFlags c ::
      encTagN 0 0 c.lvls (encTagN 0 0 c.cidx (encTagN 0 0 c.params
        (encTagN 0 0 c.fields
          (encList (fun (m : Ixon.FieldMode) acc => m.toCode :: acc) c.fieldModes.toArray.toList rt)))))
  | none => none

private theorem encCtorFuel_spec (fuel : Nat) (c : Ixon.Constructor) {k out : List UInt8}
    (h : encCtorFuel fuel c k = some out) :
    EncodesTo (Ixon.putConstructor c) k out := by
  unfold encCtorFuel at h
  cases ht : encExprFuel fuel c.typ k with
  | none => rw [ht] at h; cases h
  | some rt =>
    rw [ht] at h; injection h with ho; subst ho
    exact EncodesTo.bindUnit (EncodesTo.putU8 _ _)
      (EncodesTo.bindUnit (encTagN_spec 0 0 c.lvls _)
        (EncodesTo.bindUnit (encTagN_spec 0 0 c.cidx _)
          (EncodesTo.bindUnit (encTagN_spec 0 0 c.params _)
            (EncodesTo.bindUnit (encTagN_spec 0 0 c.fields _)
              (forArray_bind_encList_spec (fun m km => EncodesTo.putU8 m.toCode km)
                (encExprFuel_spec fuel c.typ ht))))))

private def encIndFuel (fuel : Nat) (i : Ixon.Inductive) (k : List UInt8) : Option (List UInt8) :=
  match encManyOpt (encCtorFuel fuel) i.ctors.toList k with
  | some rctors =>
    match encExprFuel fuel i.typ (encTagN 0 0 i.ctors.size.toUInt64 rctors) with
    | some rt =>
      some (Ixon.packBools [i.isUnsafe] ::
        encTagN 0 0 i.lvls (encTagN 0 0 i.params (encTagN 0 0 i.indices rt)))
    | none => none
  | none => none

private theorem encIndFuel_spec (fuel : Nat) (i : Ixon.Inductive) {k out : List UInt8}
    (h : encIndFuel fuel i k = some out) :
    EncodesTo (Ixon.putInductive i) k out := by
  unfold encIndFuel at h
  cases hc : encManyOpt (encCtorFuel fuel) i.ctors.toList k with
  | none => rw [hc] at h; cases h
  | some rctors =>
    rw [hc] at h; dsimp only at h
    cases ht : encExprFuel fuel i.typ (encTagN 0 0 i.ctors.size.toUInt64 rctors) with
    | none => rw [ht] at h; cases h
    | some rt =>
      rw [ht] at h; injection h with ho; subst ho
      exact EncodesTo.bindUnit (EncodesTo.putU8 _ _)
        (EncodesTo.bindUnit (encTagN_spec 0 0 i.lvls _)
          (EncodesTo.bindUnit (encTagN_spec 0 0 i.params _)
            (EncodesTo.bindUnit (encTagN_spec 0 0 i.indices _)
              (EncodesTo.bindUnit (encExprFuel_spec fuel i.typ ht)
                (EncodesTo.bindUnit (encTagN_spec 0 0 _ _)
                  (forArray_encManyOpt_spec (fun x _ _ hx => encCtorFuel_spec fuel x hx) hc))))))

private def encMutFuel (fuel : Nat) : Ixon.MutConst → List UInt8 → Option (List UInt8)
  | .defn d, k => (encDefFuel fuel d k).map (0 :: ·)
  | .indc i, k => (encIndFuel fuel i k).map (1 :: ·)
  | .recr r, k => (encRecFuel fuel r k).map (2 :: ·)

private theorem encMutFuel_spec (fuel : Nat) :
    ∀ (m : Ixon.MutConst) {k out : List UInt8},
      encMutFuel fuel m k = some out → EncodesTo (Ixon.putMutConst m) k out
  | .defn d, k, out, h => by
    change (encDefFuel fuel d k).map (0 :: ·) = some out at h
    cases hd : encDefFuel fuel d k with
    | none => rw [hd] at h; cases h
    | some rd => rw [hd] at h; dsimp only [Option.map] at h; injection h with ho; subst ho; exact EncodesTo.seqRight (EncodesTo.putU8 0 _) (encDefFuel_spec fuel d hd)
  | .indc i, k, out, h => by
    change (encIndFuel fuel i k).map (1 :: ·) = some out at h
    cases hi : encIndFuel fuel i k with
    | none => rw [hi] at h; cases h
    | some ri => rw [hi] at h; dsimp only [Option.map] at h; injection h with ho; subst ho; exact EncodesTo.seqRight (EncodesTo.putU8 1 _) (encIndFuel_spec fuel i hi)
  | .recr r, k, out, h => by
    change (encRecFuel fuel r k).map (2 :: ·) = some out at h
    cases hr : encRecFuel fuel r k with
    | none => rw [hr] at h; cases h
    | some rr => rw [hr] at h; dsimp only [Option.map] at h; injection h with ho; subst ho; exact EncodesTo.seqRight (EncodesTo.putU8 2 _) (encRecFuel_spec fuel r hr)

private def encInfoFuel (fuel : Nat) : Ixon.ConstantInfo → List UInt8 → Option (List UInt8)
  | .defn d, k => (encDefFuel fuel d k).map (encTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_DEFN)
  | .recr r, k => (encRecFuel fuel r k).map (encTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_RECR)
  | .axio a, k => (encAxioFuel fuel a k).map (encTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_AXIO)
  | .quot q, k => (encQuotFuel fuel q k).map (encTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_QUOT)
  | .cPrj p, k => some (encTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_CPRJ
      (encTagN 0 0 p.idx (encTagN 0 0 p.cidx (encAddress p.block k))))
  | .rPrj p, k => some (encTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_RPRJ
      (encTagN 0 0 p.idx (encAddress p.block k)))
  | .iPrj p, k => some (encTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_IPRJ
      (encTagN 0 0 p.idx (encAddress p.block k)))
  | .dPrj p, k => some (encTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_DPRJ
      (encTagN 0 0 p.idx (encAddress p.block k)))
  | .muts ms, k =>
    (encManyOpt (encMutFuel fuel) ms.toList k).map
      (encTagN 4 Ixon.Constant.FLAG_MUTS ms.size.toUInt64)

private theorem encInfoFuel_spec (fuel : Nat) :
    ∀ (ci : Ixon.ConstantInfo) {k out : List UInt8},
      encInfoFuel fuel ci k = some out → EncodesTo (Ixon.putConstantInfo ci) k out
  | .defn d, k, out, h => by
    change (encDefFuel fuel d k).map (encTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_DEFN) = some out at h
    cases hd : encDefFuel fuel d k with
    | none => rw [hd] at h; cases h
    | some rd => rw [hd] at h; dsimp only [Option.map] at h; injection h with ho; subst ho; exact EncodesTo.seqRight (encTagN_spec 4 _ _ _) (encDefFuel_spec fuel d hd)
  | .recr r, k, out, h => by
    change (encRecFuel fuel r k).map (encTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_RECR) = some out at h
    cases hr : encRecFuel fuel r k with
    | none => rw [hr] at h; cases h
    | some rr => rw [hr] at h; dsimp only [Option.map] at h; injection h with ho; subst ho; exact EncodesTo.seqRight (encTagN_spec 4 _ _ _) (encRecFuel_spec fuel r hr)
  | .axio a, k, out, h => by
    change (encAxioFuel fuel a k).map (encTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_AXIO) = some out at h
    cases ha : encAxioFuel fuel a k with
    | none => rw [ha] at h; cases h
    | some ra => rw [ha] at h; dsimp only [Option.map] at h; injection h with ho; subst ho; exact EncodesTo.seqRight (encTagN_spec 4 _ _ _) (encAxioFuel_spec fuel a ha)
  | .quot q, k, out, h => by
    change (encQuotFuel fuel q k).map (encTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_QUOT) = some out at h
    cases hq : encQuotFuel fuel q k with
    | none => rw [hq] at h; cases h
    | some rq => rw [hq] at h; dsimp only [Option.map] at h; injection h with ho; subst ho; exact EncodesTo.seqRight (encTagN_spec 4 _ _ _) (encQuotFuel_spec fuel q hq)
  | .cPrj p, k, _, h => by
    injection h with ho; subst ho
    exact EncodesTo.seqRight (encTagN_spec 4 _ _ _)
      (EncodesTo.bindUnit (encTagN_spec 0 0 p.idx _)
        (EncodesTo.bindUnit (encTagN_spec 0 0 p.cidx _) (encAddress_spec p.block k)))
  | .rPrj p, k, _, h => by
    injection h with ho; subst ho
    exact EncodesTo.seqRight (encTagN_spec 4 _ _ _)
      (EncodesTo.bindUnit (encTagN_spec 0 0 p.idx _) (encAddress_spec p.block k))
  | .iPrj p, k, _, h => by
    injection h with ho; subst ho
    exact EncodesTo.seqRight (encTagN_spec 4 _ _ _)
      (EncodesTo.bindUnit (encTagN_spec 0 0 p.idx _) (encAddress_spec p.block k))
  | .dPrj p, k, _, h => by
    injection h with ho; subst ho
    exact EncodesTo.seqRight (encTagN_spec 4 _ _ _)
      (EncodesTo.bindUnit (encTagN_spec 0 0 p.idx _) (encAddress_spec p.block k))
  | .muts ms, k, out, h => by
    change (encManyOpt (encMutFuel fuel) ms.toList k).map
      (encTagN 4 Ixon.Constant.FLAG_MUTS ms.size.toUInt64) = some out at h
    cases hm : encManyOpt (encMutFuel fuel) ms.toList k with
    | none => rw [hm] at h; cases h
    | some rm =>
      rw [hm] at h; dsimp only [Option.map] at h; injection h with ho; subst ho
      exact EncodesTo.bindUnit (encTagN_spec 4 _ _ _)
        (forArray_encManyOpt_spec (fun x _ _ hx => encMutFuel_spec fuel x hx) hm)

private def encBinderNode : Ixon.BinderNode → List UInt8 → List UInt8
  | .never m, k => Ixon.binderNodeByte 0 m :: k
  | .zero m, k => Ixon.binderNodeByte 1 m :: k
  | .ifAllZero params m, k =>
    Ixon.binderNodeByte 2 m ::
      encTagN 0 0 params.size.toUInt64 (encList (encTagN 0 0) params.toList k)
  | .share variant, k => 3 :: encTagN 0 0 variant k
  | .undecided m, k => Ixon.binderNodeByte 4 m :: k

private theorem encBinderNode_spec :
    ∀ (n : Ixon.BinderNode) (k : List UInt8), EncodesTo (Ixon.putBinderNode n) k (encBinderNode n k)
  | .never _, _ => EncodesTo.putU8 _ _
  | .zero _, _ => EncodesTo.putU8 _ _
  | .ifAllZero _ _, _ =>
    EncodesTo.bindUnit (EncodesTo.putU8 _ _)
      (EncodesTo.bindUnit (encTagN_spec 0 0 _ _)
        (forArray_encList_spec (fun p kp => encTagN_spec 0 0 p kp)))
  | .share variant, _ => EncodesTo.bindUnit (EncodesTo.putU8 3 _) (encTagN_spec 0 0 variant _)
  | .undecided _, _ => EncodesTo.putU8 _ _

private def encBinderBlock (b : Ixon.BinderBlock) (k : List UInt8) : List UInt8 :=
  (if b.shared then 1 else 0) ::
    encTagN 0 0 b.index
      (encTagN 0 0 b.variant
        (encTagN 0 0 b.nodes.size.toUInt64 (encList encBinderNode b.nodes.toList k)))

private theorem encBinderBlock_spec (b : Ixon.BinderBlock) (k : List UInt8) :
    EncodesTo (Ixon.putBinderBlock b) k (encBinderBlock b k) :=
  EncodesTo.bindUnit (EncodesTo.putU8 _ _)
    (EncodesTo.bindUnit (encTagN_spec 0 0 b.index _)
      (EncodesTo.bindUnit (encTagN_spec 0 0 b.variant _)
        (EncodesTo.bindUnit (encTagN_spec 0 0 _ _)
          (forArray_encList_spec encBinderNode_spec))))

private def encBinders (blocks : Array Ixon.BinderBlock) (k : List UInt8) : List UInt8 :=
  encTagN 0 0 blocks.size.toUInt64 (encList encBinderBlock blocks.toList k)

private theorem encBinders_spec (blocks : Array Ixon.BinderBlock) (k : List UInt8) :
    EncodesTo (Ixon.putBinders blocks) k (encBinders blocks k) :=
  EncodesTo.bindUnit (encTagN_spec 0 0 _ _) (forArray_encList_spec encBinderBlock_spec)

private def encConstantFuel (fuel : Nat) (c : Ixon.Constant) (k : List UInt8) : Option (List UInt8) :=
  let rbind := encBinders c.binders k
  match encManyOpt (encUnivFuel fuel) c.univs.toList rbind with
  | some runivs =>
    let rrefs := encTagN 0 0 c.refs.size.toUInt64
      (encList encAddress c.refs.toList (encTagN 0 0 c.univs.size.toUInt64 runivs))
    match encManyOpt (encExprFuel fuel) c.sharing.toList rrefs with
    | some rsh =>
      encInfoFuel fuel c.info (encTagN 0 0 c.sharing.size.toUInt64 rsh)
    | none => none
  | none => none

private theorem encConstantFuel_spec (fuel : Nat) (c : Ixon.Constant) {k out : List UInt8}
    (h : encConstantFuel fuel c k = some out) :
    EncodesTo (Ixon.putConstant c) k out := by
  unfold encConstantFuel at h
  dsimp only at h
  cases hu : encManyOpt (encUnivFuel fuel) c.univs.toList (encBinders c.binders k) with
  | none => rw [hu] at h; cases h
  | some runivs =>
    rw [hu] at h; dsimp only at h
    cases hs : encManyOpt (encExprFuel fuel) c.sharing.toList
        (encTagN 0 0 c.refs.size.toUInt64
          (encList encAddress c.refs.toList (encTagN 0 0 c.univs.size.toUInt64 runivs))) with
    | none => rw [hs] at h; cases h
    | some rsh =>
      rw [hs] at h; dsimp only at h
      exact EncodesTo.bindUnit (encInfoFuel_spec fuel c.info h)
        (EncodesTo.bindUnit (encTagN_spec 0 0 _ _)
          (forArray_bind_encManyOpt_spec (fun x _ _ hx => encExprFuel_spec fuel x hx) hs
            (EncodesTo.bindUnit (encTagN_spec 0 0 _ _)
              (forArray_bind_encList_spec encAddress_spec
                (EncodesTo.bindUnit (encTagN_spec 0 0 _ _)
                  (forArray_bind_encManyOpt_spec (fun x _ _ hx => encUnivFuel_spec fuel x hx) hu
                    (encBinders_spec c.binders k)))))))

private theorem serConstant_of_encConstantFuel {fuel : Nat} {c : Ixon.Constant} {bs : List UInt8}
    (h : encConstantFuel fuel c [] = some bs) :
    Ixon.serConstant c = ⟨bs.toArray⟩ := by
  have henc := encConstantFuel_spec fuel c h ByteArray.empty
  have hemp : ByteArray.empty.data.toList = [] := rfl
  rw [List.append_nil, hemp, List.nil_append] at henc
  show ((Ixon.putConstant c).run ByteArray.empty).2 = ⟨bs.toArray⟩
  cases hr : ((Ixon.putConstant c).run ByteArray.empty).2 with
  | mk arr =>
    rw [hr] at henc
    dsimp only at henc
    rw [← henc, Array.toArray_toList]

private theorem array_isEmpty_eq_toList_isEmpty {α : Type} (a : Array α) :
    a.isEmpty = a.toList.isEmpty := by
  cases a with
  | mk l => cases l <;> simp [Array.isEmpty, List.isEmpty]

private def mutBinderRootsStep (acc : Array Ixon.Expr) (m : Ixon.MutConst) : Array Ixon.Expr :=
  acc ++ match m with
    | .defn d => #[d.typ, d.value]
    | .indc i => #[i.typ] ++ i.ctors.map (·.typ)
    | .recr r => #[r.typ] ++ r.rules.map (·.rhs)

private theorem mutBinderRootsStep_nonempty (acc : Array Ixon.Expr) (m : Ixon.MutConst) :
    (mutBinderRootsStep acc m).toList ≠ [] := by
  cases m <;> simp [mutBinderRootsStep, Array.toList_append]

private theorem foldl_mutBinderRootsStep_nonempty :
    ∀ (xs : List Ixon.MutConst) (acc : Array Ixon.Expr),
      acc.toList ≠ [] → (xs.foldl mutBinderRootsStep acc).toList ≠ []
  | [], acc, h => h
  | m :: xs, acc, _ =>
    foldl_mutBinderRootsStep_nonempty xs (mutBinderRootsStep acc m)
      (mutBinderRootsStep_nonempty acc m)

private def binderRootsEmptyFast : Ixon.ConstantInfo → Bool
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => true
  | .defn _ | .recr _ | .axio _ | .quot _ => false
  | .muts ms => ms.toList.isEmpty

private theorem binderRootsEmptyFast_eq :
    ∀ (ci : Ixon.ConstantInfo), binderRootsEmptyFast ci = ci.binderRoots.isEmpty
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => rfl
  | .defn _ | .axio _ | .quot _ => rfl
  | .recr r => by
    unfold binderRootsEmptyFast Ixon.ConstantInfo.binderRoots
    rw [array_isEmpty_eq_toList_isEmpty]
    simp [Array.toList_append]
  | .muts ms => by
    dsimp only [binderRootsEmptyFast, Ixon.ConstantInfo.binderRoots]
    rw [← Array.foldl_toList, array_isEmpty_eq_toList_isEmpty]
    have hstep :
        (ms.toList.foldl
          (fun acc m => acc ++ match m with
            | .defn d => #[d.typ, d.value]
            | .indc i => #[i.typ] ++ i.ctors.map (·.typ)
            | .recr r => #[r.typ] ++ r.rules.map (·.rhs)) #[]) =
        ms.toList.foldl mutBinderRootsStep #[] := by
      congr 1
      funext acc m
      cases m <;> rfl
    rw [hstep]
    cases hms : ms.toList with
    | nil => rfl
    | cons m xs =>
      have hne : ((m :: xs).foldl mutBinderRootsStep #[]).toList ≠ [] :=
        foldl_mutBinderRootsStep_nonempty xs (mutBinderRootsStep #[] m)
          (mutBinderRootsStep_nonempty #[] m)
      cases hfl : ((m :: xs).foldl mutBinderRootsStep #[]).toList with
      | nil => exact absurd hfl hne
      | cons _ _ => rfl

private def mutMaxLvlsStep (acc : Nat) : Ixon.MutConst → Nat
  | .defn d => max acc d.lvls.toNat
  | .indc i => max acc i.lvls.toNat
  | .recr r => max acc r.lvls.toNat

private def maxLvlsFast : Ixon.ConstantInfo → Nat
  | .defn d => d.lvls.toNat
  | .recr r => r.lvls.toNat
  | .axio a => a.lvls.toNat
  | .quot q => q.lvls.toNat
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => 0
  | .muts ms => ms.toList.foldl mutMaxLvlsStep 0

private theorem maxLvlsFast_eq : ∀ (ci : Ixon.ConstantInfo), maxLvlsFast ci = ci.maxLvls
  | .defn _ | .recr _ | .axio _ | .quot _ | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => rfl
  | .muts ms => by
    dsimp only [maxLvlsFast, Ixon.ConstantInfo.maxLvls]
    rw [← Array.foldl_toList]
    congr 1
    funext acc m
    cases m <;> rfl

private def binderNodeCanonicalFast (lvls : Nat) : Ixon.BinderNode → Bool
  | .ifAllZero params _ =>
    !params.toList.isEmpty && Ixon.paramsAscending params.toList &&
      params.toList.all (·.toNat < lvls)
  | _ => true

private theorem binderNodeCanonicalFast_eq (lvls : Nat) :
    ∀ (n : Ixon.BinderNode), binderNodeCanonicalFast lvls n = Ixon.BinderNode.canonical lvls n
  | .never _ | .zero _ | .undecided _ | .share _ => rfl
  | .ifAllZero params _ => by
    dsimp only [binderNodeCanonicalFast, Ixon.BinderNode.canonical]
    rw [array_isEmpty_eq_toList_isEmpty, ← Array.all_toList]

private def bindersCanonicalFast (c : Ixon.Constant) : Bool :=
  if binderRootsEmptyFast c.info then c.binders.toList.isEmpty
  else
    decide (maxLvlsFast c.info < Ixon.maxLevelCount) &&
    Ixon.blocksAscending c.binders.toList &&
      c.binders.toList.all fun block =>
        (block.shared || block.variant == 0) && !block.nodes.toList.isEmpty &&
          block.nodes.toList.all (binderNodeCanonicalFast (maxLvlsFast c.info))

private theorem bindersCanonicalFast_eq (c : Ixon.Constant) :
    bindersCanonicalFast c = c.bindersCanonical := by
  unfold bindersCanonicalFast Ixon.Constant.bindersCanonical
  rw [binderRootsEmptyFast_eq, array_isEmpty_eq_toList_isEmpty c.binders, maxLvlsFast_eq, ← Array.all_toList]
  have hfun :
      (fun (block : Ixon.BinderBlock) =>
        (block.shared || block.variant == 0) && !block.nodes.toList.isEmpty &&
          block.nodes.toList.all (binderNodeCanonicalFast c.info.maxLvls)) =
      (fun (block : Ixon.BinderBlock) =>
        (block.shared || block.variant == 0) && !block.nodes.isEmpty &&
          block.nodes.all (Ixon.BinderNode.canonical c.info.maxLvls)) := by
    funext block
    rw [array_isEmpty_eq_toList_isEmpty block.nodes, ← Array.all_toList]
    have hnd : binderNodeCanonicalFast c.info.maxLvls = Ixon.BinderNode.canonical c.info.maxLvls :=
      funext (binderNodeCanonicalFast_eq c.info.maxLvls)
    rw [hnd]
  rw [hfun]

private def modesCanonicalFast (c : Ixon.Constant) : Bool :=
  match c.info with
  | .defn d => d.assertsCanonical
  | .muts ms => ms.toList.all fun
    | .defn d => d.assertsCanonical
    | _ => true
  | _ => true

private theorem modesCanonicalFast_eq : ∀ (c : Ixon.Constant), modesCanonicalFast c = c.modesCanonical
  | ⟨.defn _, _, _, _, _⟩
  | ⟨.recr _, _, _, _, _⟩
  | ⟨.axio _, _, _, _, _⟩
  | ⟨.quot _, _, _, _, _⟩
  | ⟨.cPrj _, _, _, _, _⟩
  | ⟨.rPrj _, _, _, _, _⟩
  | ⟨.iPrj _, _, _, _, _⟩
  | ⟨.dPrj _, _, _, _, _⟩ => rfl
  | ⟨.muts ms, _, _, _, _⟩ => by
    unfold modesCanonicalFast Ixon.Constant.modesCanonical
    dsimp only
    rw [← Array.all_toList]

def checkConstBytesFast (c : Ixon.Constant) (bs : List UInt8) : Bool :=
  validConstantFast c &&
  (encConstantFuel (bs.length + 1) c [] == some bs) &&
  decide (bs.length ≤ Ix.Kernel.Reader.preludeMaxBytes) &&
  decide (Ixon.Bounded.univNodes c.univs ≤ Ix.Kernel.Reader.preludeMaxUnivNodes) &&
  bindersCanonicalFast c &&
  modesCanonicalFast c

theorem deConstant_of_checkConstBytesFast {c : Ixon.Constant} {bs : List UInt8}
    (h : checkConstBytesFast c bs = true) :
    Ixon.Canonical.deConstant Ix.Kernel.Reader.preludeMaxBytes
      Ix.Kernel.Reader.preludeMaxUnivNodes ⟨bs.toArray⟩ = .ok c := by
  simp only [checkConstBytesFast, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hval, henc⟩, hbytes⟩, huniv⟩, hbind⟩, hmodes⟩ := h
  rw [bindersCanonicalFast_eq] at hbind
  rw [modesCanonicalFast_eq] at hmodes
  rw [Ixon.Verify.Canonical.deConstant_ok_iff]
  refine ⟨validConstantFast_ok hval, serConstant_of_encConstantFuel henc, ?_, huniv, hbind, hmodes⟩
  simpa [ByteArray.size] using hbytes

/-! ## Pure `defn`-only witness decoder for `RoleData.evidence` -/

private def deU8 : List UInt8 → Option (UInt8 × List UInt8)
  | b :: bs => some (b, bs)
  | [] => none

private def deBytes : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, b :: bs => do
    let (xs, rest) ← deBytes n bs
    pure (b :: xs, rest)
  | _ + 1, [] => none

private def deLE : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, bs => some (0, bs)
  | n + 1, b :: bs => do
    let (hi, rest) ← deLE n bs
    pure (b.toNat + 256 * hi, rest)
  | _ + 1, [] => none

private def deTagN (f : Nat) (bs : List UInt8) : Option ((UInt8 × UInt64) × List UInt8) := do
  let (b, bs) ← deU8 bs
  let shift := 8 - f
  let mod := 1 <<< shift
  let flag : UInt8 := UInt8.ofNat (b.toNat / mod)
  let pay : Nat := b.toNat % mod
  let r1 := 1 <<< (shift - 1)
  let r2bits := 1 <<< (shift - 2)
  if pay < r1 then
    pure ((flag, pay.toUInt64), bs)
  else if pay - r1 < r2bits then
    let (lo, bs) ← deU8 bs
    pure ((flag, (r1 + (pay - r1) * 256 + lo.toNat).toUInt64), bs)
  else
    let c := pay - r1 - r2bits
    let r2 := r1 + r2bits * 256
    let r3 := r2 + 65536
    let r4 := r3 + 16777216
    let r5 := r4 + 4294967296
    let (len, base) ← match c with
      | 0 => some (2, r2)
      | 1 => some (3, r3)
      | 2 => some (4, r4)
      | 3 => some (8, r5)
      | _ => none
    let (x, bs) ← deLE len bs
    pure ((flag, (base + x).toUInt64), bs)

private def deMany {α : Type} (rd : List UInt8 → Option (α × List UInt8)) :
    Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (x, bs) ← rd bs
    let (xs, bs) ← deMany rd n bs
    pure (x :: xs, bs)

private def deTagN0Val (bs : List UInt8) : Option (UInt64 × List UInt8) := do
  let ((_, v), bs) ← deTagN 0 bs
  pure (v, bs)

private def deUnivFuel : Nat → List UInt8 → Option (Ixon.Univ × List UInt8)
  | 0, _ => none
  | fuel + 1, bs => do
    let ((fl, val), bs) ← deTagN 2 bs
    match fl with
    | 0 =>
      if val == 0 then pure (.zero, bs)
      else
        let (u, bs) ← deUnivFuel fuel bs
        pure (u.addSucc val.toNat, bs)
    | 1 =>
      let (a, bs) ← deUnivFuel fuel bs
      let (b, bs) ← deUnivFuel fuel bs
      pure (.max a b, bs)
    | 2 =>
      let (a, bs) ← deUnivFuel fuel bs
      let (b, bs) ← deUnivFuel fuel bs
      pure (.imax a b, bs)
    | 3 => pure (.var val, bs)
    | _ => none

private def deExprFuel : Nat → List UInt8 → Option (Ixon.Expr × List UInt8)
  | 0, _ => none
  | fuel + 1, bs => do
    let ((fl, val), bs) ← deTagN 4 bs
    match fl with
    | 0x0 => pure (.sort val, bs)
    | 0x1 => pure (.var val, bs)
    | 0x2 =>
      let (r, bs) ← deTagN0Val bs
      let (us, bs) ← deMany deTagN0Val val.toNat bs
      pure (.ref r us.toArray, bs)
    | 0x3 =>
      let (r, bs) ← deTagN0Val bs
      let (us, bs) ← deMany deTagN0Val val.toNat bs
      pure (.recur r us.toArray, bs)
    | 0x4 =>
      let (t, bs) ← deTagN0Val bs
      let (e, bs) ← deExprFuel fuel bs
      pure (.prj t val e, bs)
    | 0x5 => pure (.str val, bs)
    | 0x6 => pure (.nat val, bs)
    | 0x7 =>
      let (f, bs) ← deExprFuel fuel bs
      let (args, bs) ← deMany (deExprFuel fuel) val.toNat bs
      pure (args.foldl Ixon.Expr.app f, bs)
    | 0x8 =>
      let (tys, bs) ← deMany (deExprFuel fuel) val.toNat bs
      let (body, bs) ← deExprFuel fuel bs
      pure (tys.foldr Ixon.Expr.lam body, bs)
    | 0x9 =>
      let (tys, bs) ← deMany (deExprFuel fuel) val.toNat bs
      let (body, bs) ← deExprFuel fuel bs
      pure (tys.foldr Ixon.Expr.all body, bs)
    | 0xA =>
      let (nonDep, mode) ← Ixon.LetMode.ofHeader? val
      let (ty, bs) ← deExprFuel fuel bs
      let (v, bs) ← deExprFuel fuel bs
      let (b, bs) ← deExprFuel fuel bs
      pure (.letE nonDep mode ty v b, bs)
    | 0xB => pure (.share val, bs)
    | _ => none

private def deBinderNode (bs : List UInt8) : Option (Ixon.BinderNode × List UInt8) := do
  let (b, bs) ← deU8 bs
  if b == 3 then
    let (v, bs) ← deTagN0Val bs
    pure (.share v, bs)
  else
    let m ← Ixon.AllMode.ofCode? (b >>> 3)
    match b &&& 7 with
    | 0 => pure (.never m, bs)
    | 1 => pure (.zero m, bs)
    | 2 =>
      let (cnt, bs) ← deTagN0Val bs
      let (ps, bs) ← deMany deTagN0Val cnt.toNat bs
      pure (.ifAllZero ps.toArray m, bs)
    | 4 => pure (.undecided m, bs)
    | _ => none

private def deBinderBlock (bs : List UInt8) : Option (Ixon.BinderBlock × List UInt8) := do
  let (sh, bs) ← deU8 bs
  let (index, bs) ← deTagN0Val bs
  let (variant, bs) ← deTagN0Val bs
  let (cnt, bs) ← deTagN0Val bs
  let (nodes, bs) ← deMany deBinderNode cnt.toNat bs
  pure (⟨sh != 0, index, variant, nodes.toArray⟩, bs)

def listDeDefnConstant (bs : List UInt8) : Option Ixon.Constant := do
  let fuel := bs.length + 1
  let ((fl, val), bs) ← deTagN 4 bs
  guard (fl == Ixon.Constant.FLAG && val == Ixon.ConstantInfo.CONST_DEFN)
  let (dfl, bs) ← deU8 bs
  let asserts ← Ixon.DefAsserts.ofCode? (dfl >>> 4)
  let (kind, safety) := Ixon.unpackDefKindSafety (dfl &&& 15)
  let (lvls, bs) ← deTagN0Val bs
  let (typ, bs) ← deExprFuel fuel bs
  let (value, bs) ← deExprFuel fuel bs
  let (nsh, bs) ← deTagN0Val bs
  let (sh, bs) ← deMany (deExprFuel fuel) nsh.toNat bs
  let (nrefs, bs) ← deTagN0Val bs
  let (refs, bs) ← deMany (fun s => do let (ab, s) ← deBytes 32 s; pure (mkAddr ab, s)) nrefs.toNat bs
  let (nunivs, bs) ← deTagN0Val bs
  let (univs, bs) ← deMany (deUnivFuel fuel) nunivs.toNat bs
  let (nbinders, bs) ← deTagN0Val bs
  let (binders, bs) ← deMany deBinderBlock nbinders.toNat bs
  guard bs.isEmpty
  pure ⟨.defn ⟨kind, safety, asserts, lvls, typ, value⟩,
    sh.toArray, refs.toArray, univs.toArray, binders.toArray⟩

/-! ## Row-level helpers -/

theorem mem_of_array_eq {α : Type} {arr : Array α} {xs : List α} {x : α}
    (heq : arr = xs.toArray) (hx : x ∈ arr.toList) : x ∈ xs := by
  rw [heq, List.toList_toArray] at hx
  exact hx

def hexRowOfChunks (addrBytes : List UInt8) (chunks : List (List UInt8)) :
    String × String :=
  (String.ofList (Claim.hexCharsOfBytes addrBytes),
   String.ofList (Claim.hexCharsOfBytes chunks.flatten))

theorem row_hashed_of_checkHashChunks {addrBytes : List UInt8} {chunks : List (List UInt8)}
    (h : checkHashChunks chunks addrBytes = true) :
    (bytesOfHex (hexRowOfChunks addrBytes chunks).2).map Address.admissionHash =
      Ix.Kernel.Reader.addressOfHex (hexRowOfChunks addrBytes chunks).1 := by
  unfold hexRowOfChunks Ix.Kernel.Reader.addressOfHex
  rw [Claim.bytesOfHex_ofList_hexChars, Claim.bytesOfHex_ofList_hexChars]
  simp only [Option.map_some, bind, Option.bind, pure, Option.some.injEq]
  exact admissionHash_of_checkHashChunks h

def checkPreRow (ab : List UInt8) (chunks : List (List UInt8))
    (a : _root_.Address) (c : Ixon.Constant) : Bool :=
  checkHashChunks chunks ab &&
  (a == mkAddr ab) &&
  checkConstBytesFast c chunks.flatten

def checkEvRow (ab : List UInt8) (chunks : List (List UInt8)) : Bool :=
  checkHashChunks chunks ab &&
  match listDeDefnConstant chunks.flatten with
  | some c =>
    match c.info with
    | .defn _ => checkConstBytesFast c chunks.flatten
    | _ => false
  | none => false

theorem preRow_spec {ab : List UInt8} {chunks : List (List UInt8)}
    {a : _root_.Address} {c : Ixon.Constant}
    (h : checkPreRow ab chunks a c = true) :
    (bytesOfHex (hexRowOfChunks ab chunks).2).map Address.admissionHash =
      Ix.Kernel.Reader.addressOfHex (hexRowOfChunks ab chunks).1 ∧
    Ix.Kernel.Reader.addressOfHex (hexRowOfChunks ab chunks).1 = some a ∧
    ∃ b, bytesOfHex (hexRowOfChunks ab chunks).2 = some b ∧
      Ixon.Canonical.deConstant Ix.Kernel.Reader.preludeMaxBytes
        Ix.Kernel.Reader.preludeMaxUnivNodes b = .ok c := by
  simp only [checkPreRow, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hhash, rfl⟩, hconst⟩ := h
  refine ⟨row_hashed_of_checkHashChunks hhash, ?_, ⟨chunks.flatten.toArray⟩, ?_,
    deConstant_of_checkConstBytesFast hconst⟩
  · unfold hexRowOfChunks Ix.Kernel.Reader.addressOfHex
    rw [Claim.bytesOfHex_ofList_hexChars ab]; rfl
  · unfold hexRowOfChunks
    exact Claim.bytesOfHex_ofList_hexChars chunks.flatten

def EvRowSpec (raw : List UInt8 × List (List UInt8)) : Prop :=
  (bytesOfHex (hexRowOfChunks raw.1 raw.2).2).map Address.admissionHash =
    Ix.Kernel.Reader.addressOfHex (hexRowOfChunks raw.1 raw.2).1 ∧
  ∃ c, (∃ d, c.info = .defn d) ∧
    Ix.Kernel.Reader.addressOfHex (hexRowOfChunks raw.1 raw.2).1 = some (mkAddr raw.1) ∧
    ∃ b, bytesOfHex (hexRowOfChunks raw.1 raw.2).2 = some b ∧
      Ixon.Canonical.deConstant Ix.Kernel.Reader.preludeMaxBytes
        Ix.Kernel.Reader.preludeMaxUnivNodes b = .ok c

theorem evRow_spec {ab : List UInt8} {chunks : List (List UInt8)}
    (h : checkEvRow ab chunks = true) :
    EvRowSpec (ab, chunks) := by
  unfold checkEvRow at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hhash, hdec⟩ := h
  refine ⟨row_hashed_of_checkHashChunks hhash, ?_⟩
  cases hd : listDeDefnConstant chunks.flatten with
  | none => rw [hd] at hdec; cases hdec
  | some c =>
    rw [hd] at hdec; dsimp only at hdec
    cases hci : c.info with
    | defn d =>
      rw [hci] at hdec; dsimp only at hdec
      refine ⟨c, ⟨d, hci⟩, ?_, ⟨chunks.flatten.toArray⟩, ?_, deConstant_of_checkConstBytesFast hdec⟩
      · unfold hexRowOfChunks Ix.Kernel.Reader.addressOfHex
        rw [Claim.bytesOfHex_ofList_hexChars ab]; rfl
      · unfold hexRowOfChunks
        exact Claim.bytesOfHex_ofList_hexChars chunks.flatten
    | recr _ | axio _ | quot _ | cPrj _ | rPrj _ | iPrj _ | dPrj _ | muts _ =>
      rw [hci] at hdec; cases hdec

theorem except_mapM_forall₂ {ε α β : Type} {f : α → Except ε β} {R : α → β → Prop}
    (hf : ∀ x y, R x y → f x = Except.ok y) :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → xs.mapM f = Except.ok ys
  | _, _, .nil => rfl
  | x :: _, y :: _, .cons hxy htl => by
    rw [List.mapM_cons, hf x y hxy, except_mapM_forall₂ hf htl]
    rfl

theorem except_mapM_rows {ε α β : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β},
      xs.mapM f = Except.ok ys →
      ∀ y ∈ ys, ∃ x ∈ xs, f x = Except.ok y
  | [], _, h, y, hy => by injection h with ho; subst ho; cases hy
  | x :: xs, _, h, y, hy => by
    rw [List.mapM_cons] at h
    cases hfx : f x with
    | error _ => rw [hfx] at h; cases h
    | ok y0 =>
      rw [hfx] at h; dsimp only [bind, Except.bind] at h
      cases htl : xs.mapM f with
      | error _ => rw [htl] at h; cases h
      | ok tail =>
        rw [htl] at h
        injection h with ho; subst ho
        rcases List.mem_cons.mp hy with rfl | hmem
        · exact ⟨x, List.mem_cons_self, hfx⟩
        · obtain ⟨x', hx', hfx'⟩ := except_mapM_rows htl y hmem
          exact ⟨x', List.mem_cons_of_mem _ hx', hfx'⟩

theorem decodeCommitted_of_forall₂ (what : String) :
    ∀ {rows : List (String × String)} {out : List (_root_.Address × Ixon.Constant)},
      List.Forall₂ (fun row p =>
        Ix.Kernel.Reader.addressOfHex row.1 = some p.1 ∧
        ∃ b, bytesOfHex row.2 = some b ∧
          Ixon.Canonical.deConstant Ix.Kernel.Reader.preludeMaxBytes
            Ix.Kernel.Reader.preludeMaxUnivNodes b = Except.ok p.2) rows out →
      Ix.Kernel.Reader.decodeCommitted what rows.toArray = Except.ok out.toArray := by
  intro rows out hf
  unfold Ix.Kernel.Reader.decodeCommitted
  rw [Array.mapM_eq_mapM_toList, List.toList_toArray]
  rw [except_mapM_forall₂ (fun row p ⟨ha, b, hb, hc⟩ => by
    simp [ha, hb, hc, Except.mapError, bind, Except.bind, pure, Except.pure]) hf]
  rfl

theorem evRows_spec_of_forall {rows : List (List UInt8 × List (List UInt8))}
    (hall : ∀ r ∈ rows, EvRowSpec r) :
    (∀ row ∈ rows.map (fun p => hexRowOfChunks p.1 p.2),
      (bytesOfHex row.2).map Address.admissionHash = Ix.Kernel.Reader.addressOfHex row.1) ∧
    ∃ out : List (_root_.Address × Ixon.Constant),
      List.Forall₂ (fun row p =>
        Ix.Kernel.Reader.addressOfHex row.1 = some p.1 ∧
        ∃ b, bytesOfHex row.2 = some b ∧
          Ixon.Canonical.deConstant Ix.Kernel.Reader.preludeMaxBytes
            Ix.Kernel.Reader.preludeMaxUnivNodes b = Except.ok p.2)
        (rows.map fun p => hexRowOfChunks p.1 p.2) out ∧
      out.map Prod.fst = rows.map (fun p => mkAddr p.1) ∧
      ∀ p ∈ out, ∃ d, p.2.info = .defn d := by
  induction rows with
  | nil =>
    exact And.intro (fun _ hm => nomatch hm)
      (Exists.intro [] (And.intro List.Forall₂.nil (And.intro rfl (fun _ hm => nomatch hm))))
  | cons r rs ih =>
    rcases hall r List.mem_cons_self with ⟨hhash, c, hd, ha, hb⟩
    rcases ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) with
      ⟨hhash_tl, out_tl, hf_tl, hfst_tl, hdefn_tl⟩
    refine And.intro ?_ (Exists.intro ((mkAddr r.1, c) :: out_tl)
      (And.intro (List.Forall₂.cons ⟨ha, hb⟩ hf_tl) (And.intro (by simp [hfst_tl]) ?_)))
    · intro row hmem
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact hhash
      · exact hhash_tl row htl
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | htl
      · exact hd
      · exact hdefn_tl p htl

end IxVM.Refinement.RoleVal
