import IxCC.Lir.Proof.Opt.Arith
import IxCC.X86.Memory
import IxCC.X86.StreamMemory

/-!
# Segment memory soundness (store-to-load forwarding, load CSE, DSE)

Formal proofs for the byte-level memory laws underlying `SymMem`:

1. **Modulo-2^64 non-aliasing (`constAddrDisjoint_bytes`)**: two same-base
   addresses with signed 32-bit displacements whose byte intervals
   `[d1, d1 + w1.bytes)` and `[d2, d2 + w2.bytes)` do not overlap touch
   disjoint byte addresses modulo 2^64 for *every* 64-bit base word.
2. **Store-to-load forwarding (`read_write_same`, `forwardVal_sound`)**: reading
   `w` bytes from `mem.write w addr v` returns `w.truncate v`.
3. **Disjoint load invariance (`loadWord_write_disjoint`)**: a store to a
   byte-disjoint range leaves `loadWord` unchanged.
4. **Disjoint store commutation (`write_write_comm`)** and **shadowed store
   absorption (`write_write_overwrite`)**: exact `X86.Memory` equality!
5. **Symbolic write-log soundness (`applyWrites`, `dropShadowed_sound`,
   `SymMem.readAux_sound`, `writesEquiv_sound`)**.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Width Ext Base Addr Arg Word Env sext dispWord loadWord)

/-! ## Byte-level memory laws -/

theorem mem_ext {m1 m2 : X86.Memory}
    (hb : ∀ a, m1.bytes a = m2.bytes a)
    (hr : m1.readable = m2.readable)
    (hw : m1.writable = m2.writable) : m1 = m2 := by
  cases m1; cases m2
  simp only at hb hr hw
  subst hr hw
  congr 1
  funext a
  exact hb a

theorem width_bytes_le_8 (w : Width) : w.bytes ≤ 8 := by cases w <;> decide

/-- `dispWord d + ofNat i` modulo 2^64 represents `d + i` uniquely for `i32` displacements
and offsets `i < 8`. -/
theorem dispWord_add_ne {base : Word} {d1 d2 : Int} {w1 w2 i j : Nat}
    (hd1 : -2147483648 ≤ d1 ∧ d1 < 2147483648)
    (hd2 : -2147483648 ≤ d2 ∧ d2 < 2147483648)
    (hw1 : w1 ≤ 8) (hw2 : w2 ≤ 8)
    (hdisj : d1 + (w1 : Int) ≤ d2 ∨ d2 + (w2 : Int) ≤ d1)
    (hi : i < w1) (hj : j < w2) :
    (base + dispWord d1) + UInt64.ofNat i ≠ (base + dispWord d2) + UInt64.ofNat j := by
  intro heq
  -- Cancel `base` in `UInt64` (additive group mod 2^64)
  have h1 : dispWord d1 + UInt64.ofNat i = dispWord d2 + UInt64.ofNat j := by
    have hsub := congrArg (fun x => x - base) heq
    have cancel : ∀ x y : Word, (base + x) + y - base = x + y := fun x y => by
      apply UInt64.toNat_inj.mp
      have hb : base.toNat < 2 ^ 64 := base.toNat_lt_size
      have hxy : (x + y).toNat < 2 ^ 64 := (x + y).toNat_lt_size
      rw [UInt64.add_assoc, UInt64.add_comm base (x + y), UInt64.toNat_sub, UInt64.toNat_add,
        Nat.add_mod_mod]
      have hsum : 2 ^ 64 - base.toNat + ((x + y).toNat + base.toNat) = (x + y).toNat + 2 ^ 64 := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hxy]
    rwa [cancel, cancel] at hsub
  -- Compare `.toBitVec.toInt` (exact since both lie strictly in [-2^63, 2^63))
  have hv : ∀ (d : Int) (k : Nat), -2147483648 ≤ d → d < 2147483648 → k < 8 →
      (dispWord d + UInt64.ofNat k).toBitVec = BitVec.ofInt 64 (d + (k : Int)) := by
    intro d k _ _ _
    simp only [dispWord, UInt64.toBitVec_add, BitVec.ofInt_add]
    rfl
  have hbv := congrArg UInt64.toBitVec h1
  rw [hv d1 i hd1.1 hd1.2 (by omega), hv d2 j hd2.1 hd2.2 (by omega)] at hbv
  have hint := congrArg BitVec.toInt hbv
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega),
      BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)] at hint
  omega

/-- Byte-level disjointness of two `writeLittle` ranges. -/
def BytesDisjoint (a1 : Word) (n1 : Nat) (a2 : Word) (n2 : Nat) : Prop :=
  ∀ i < n1, ∀ j < n2, a1 + UInt64.ofNat i ≠ a2 + UInt64.ofNat j

theorem BytesDisjoint.symm {a1 a2 : Word} {n1 n2 : Nat} (h : BytesDisjoint a1 n1 a2 n2) :
    BytesDisjoint a2 n2 a1 n1 :=
  fun i hi j hj heq => h j hj i hi heq.symm

/-- Reading `w` bytes immediately after writing `w` bytes at the same address returns `w.truncate v`. -/
theorem read_write_same (mem : X86.Memory) (w : Width) (addr v : Word) :
    (mem.write w addr v).read w addr = w.truncate v := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hle := width_bytes_le_8 w
  rw [X86.Memory.read, X86.Memory.write, Xv.Select.Proof.readLittle_bit _ _ _ _ hle,
    X86.Encode.truncate_bits, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth,
    Xv.Select.Proof.width_bytes_bits]
  by_cases hlt : i < 8 * w.bytes
  · simp only [hlt, decide_true, Bool.true_and, hi]
    have hdiv : i / 8 < w.bytes := by omega
    rw [X86.Memory.writeLittle_bytes _ _ _ hle hdiv]
    simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_shiftRight,
      BitVec.getLsbD_setWidth, show i % 8 < 8 from Nat.mod_lt _ (by decide), decide_true,
      Bool.true_and, BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight]
    have hshift : ((UInt64.ofNat (8 * (i / 8))).toBitVec % 64).toNat = 8 * (i / 8) := by
      rw [BitVec.toNat_umod]
      change (UInt64.ofNat (8 * (i / 8))).toNat % 64 = 8 * (i / 8)
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show 8 * (i / 8) < UInt64.size by simp [UInt64.size]; omega),
        Nat.mod_eq_of_lt (by omega : 8 * (i / 8) < 64)]
    rw [hshift, show 8 * (i / 8) + i % 8 = i by omega]
  · simp [hlt]

/-- Store-to-load forwarding for `loadWord` when `forwardVal w e` succeeds. -/
theorem forwardVal_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {mem : X86.Memory} {w : Width} {e : Ext} {addr v v' : Word} {ve fe : SymExpr}
    (hfw : forwardVal w e ve = some fe)
    (hve : ve.eval ρ ctx snaps = some v)
    (hld : loadWord (mem.write w addr v) w e addr = some v') :
    fe.eval ρ ctx snaps = some v' := by
  unfold loadWord X86.Memory.read? at hld
  split at hld
  · rename_i vread hread
    split at hread
    · cases hread
      rw [read_write_same] at hld
      simp only [Option.some.injEq] at hld
      unfold forwardVal at hfw
      cases w with
      | w64 =>
          simp only [Option.some.injEq] at hfw; subst hfw
          cases e <;> simp only [sext, X86.Encode.truncate64] at hld <;> rw [← hld, hve]
      | w8 | w16 | w32 =>
          cases e with
          | zero =>
              simp only [Option.some.injEq] at hfw; subst hfw
              rw [← hld]
              exact mkBin_sound hve (o := .and) (w := .w64) (b := .imm _) (vb := _) rfl
                (by simp only [BinOp.eval, X86.Encode.truncate64]; rfl)
          | sign =>
              cases ve with
              | imm k =>
                  simp only [SymExpr.eval, Option.some.injEq] at hfw hve; subst hfw hve
                  rw [← hld]; rfl
              | _ => cases hfw
    · cases hread
  · cases hld

/-- A store to a byte-disjoint range does not affect `loadWord`. -/
theorem loadWord_write_disjoint (mem : X86.Memory) {w1 w2 : Width} {e : Ext} {a1 a2 v : Word}
    (hdisj : BytesDisjoint a1 w1.bytes a2 w2.bytes) :
    loadWord (mem.write w2 a2 v) w1 e a1 = loadWord mem w1 e a1 := by
  unfold loadWord X86.Memory.read? X86.Memory.write X86.Memory.read
  rw [X86.Stream.writeLittle_readable]
  by_cases hr : X86.Memory.rangeAllowed mem.readable a1 w1.bytes = true
  · simp only [hr, ↓reduceIte]
    have hrl : (mem.writeLittle a2 v w2.bytes).readLittle a1 w1.bytes = mem.readLittle a1 w1.bytes := by
      apply X86.Memory.readLittle_congr
      intro i hi
      exact X86.Memory.writeLittle_bytes_outside _ _ _ _ _ fun j hj => hdisj i hi j hj
    rw [hrl]
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]

/-- Byte-disjoint stores commute to identical `X86.Memory`. -/
theorem write_write_comm (mem : X86.Memory) {w1 w2 : Width} {a1 a2 v1 v2 : Word}
    (hdisj : BytesDisjoint a1 w1.bytes a2 w2.bytes) :
    (mem.write w1 a1 v1).write w2 a2 v2 = (mem.write w2 a2 v2).write w1 a1 v1 := by
  have hb1 := width_bytes_le_8 w1
  have hb2 := width_bytes_le_8 w2
  apply mem_ext
  · intro x
    simp only [X86.Memory.write]
    by_cases h2 : ∃ j < w2.bytes, x = a2 + UInt64.ofNat j
    · obtain ⟨j, hj, rfl⟩ := h2
      rw [X86.Memory.writeLittle_bytes _ _ _ hb2 hj,
          X86.Memory.writeLittle_bytes_outside _ _ _ _ _ (fun i hi heq => hdisj i hi j hj heq.symm),
          X86.Memory.writeLittle_bytes _ _ _ hb2 hj]
    · have hout2 : ∀ j < w2.bytes, x ≠ a2 + UInt64.ofNat j := fun j hj heq => h2 ⟨j, hj, heq⟩
      rw [X86.Memory.writeLittle_bytes_outside _ _ _ _ _ hout2]
      by_cases h1 : ∃ i < w1.bytes, x = a1 + UInt64.ofNat i
      · obtain ⟨i, hi, rfl⟩ := h1
        rw [X86.Memory.writeLittle_bytes _ _ _ hb1 hi, X86.Memory.writeLittle_bytes _ _ _ hb1 hi]
      · have hout1 : ∀ i < w1.bytes, x ≠ a1 + UInt64.ofNat i := fun i hi heq => h1 ⟨i, hi, heq⟩
        rw [X86.Memory.writeLittle_bytes_outside _ _ _ _ _ hout1,
            X86.Memory.writeLittle_bytes_outside _ _ _ _ _ hout1,
            X86.Memory.writeLittle_bytes_outside _ _ _ _ _ hout2]
  · simp [X86.Memory.write]
  · simp [X86.Memory.write]

/-- An overwriting store of the same width at the same address completely shadows an earlier store. -/
theorem write_write_overwrite (mem : X86.Memory) (w : Width) (addr v1 v2 : Word) :
    (mem.write w addr v1).write w addr v2 = mem.write w addr v2 := by
  have hb := width_bytes_le_8 w
  apply mem_ext
  · intro x
    simp only [X86.Memory.write]
    by_cases h : ∃ i < w.bytes, x = addr + UInt64.ofNat i
    · obtain ⟨i, hi, rfl⟩ := h
      rw [X86.Memory.writeLittle_bytes _ _ _ hb hi, X86.Memory.writeLittle_bytes _ _ _ hb hi]
    · have hout : ∀ i < w.bytes, x ≠ addr + UInt64.ofNat i := fun i hi heq => h ⟨i, hi, heq⟩
      rw [X86.Memory.writeLittle_bytes_outside _ _ _ _ _ hout,
          X86.Memory.writeLittle_bytes_outside _ _ _ _ _ hout,
          X86.Memory.writeLittle_bytes_outside _ _ _ _ _ hout]
  · simp [X86.Memory.write]
  · simp [X86.Memory.write]

/-! ## `ConstAddr` evaluation and non-aliasing soundness -/

/-- Evaluate a `MemBase` in `(ρ, ctx, snaps)`. -/
def MemBase.eval (ρ : Env) (ctx : Word) (snaps : MemSnaps) : MemBase → Option Word
  | .zero => some 0
  | .ctx => some ctx
  | .expr e => e.eval ρ ctx snaps

/-- Evaluate a `ConstAddr` in `(ρ, ctx, snaps)`. -/
def ConstAddr.eval (ρ : Env) (ctx : Word) (snaps : MemSnaps) (ca : ConstAddr) : Option Word := do
  let b ← ca.base.eval ρ ctx snaps
  some (b + dispWord ca.disp)

theorem toConstAddr_eval {ρ : Env} {ctx : Word} {snaps : MemSnaps} {lookup : VReg → SymExpr}
    {m : Addr} {ca : ConstAddr} {va : Word}
    (hca : toConstAddr lookup m = some ca)
    (haddr : (addrToSym lookup m).eval ρ ctx snaps = some va) :
    ca.eval ρ ctx snaps = some va := by
  unfold toConstAddr at hca
  split at hca
  · cases hca
  · rename_i hok
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hok
    obtain ⟨hidx, _⟩ := hok
    have hnone : m.index = none := by cases h : m.index with | none => rfl | some _ => simp [h] at hidx
    simp only [Option.some.injEq] at hca
    subst hca
    unfold addrToSym at haddr
    rw [hnone] at haddr
    dsimp only at haddr
    -- Evaluate baseExpr + 0 + dispWord m.disp
    cases hb : m.base with
    | none =>
        rw [hb] at haddr; dsimp only at haddr
        have h1 : (mkBin .add .w64 (.imm 0) (.imm 0)).eval ρ ctx snaps = some (0 + 0) :=
          mkBin_sound (o := .add) (w := .w64) (va := 0) (vb := 0) rfl rfl (by simp [BinOp.eval, X86.Encode.truncate64])
        have h2 : (mkBin .add .w64 (mkBin .add .w64 (.imm 0) (.imm 0)) (.imm (dispWord m.disp))).eval ρ ctx snaps =
            some ((0 + 0) + dispWord m.disp) :=
          mkBin_sound (o := .add) (w := .w64) h1 (b := .imm (dispWord m.disp)) (vb := dispWord m.disp) rfl
            (by simp [BinOp.eval, X86.Encode.truncate64])
        rw [h2] at haddr; cases haddr
        simp [ConstAddr.eval, MemBase.eval]
    | some b =>
        rw [hb] at haddr
        cases b with
        | ctx =>
            have h1 : (mkBin .add .w64 .ctx (.imm 0)).eval ρ ctx snaps = some (ctx + 0) :=
              mkBin_sound (o := .add) (w := .w64) (va := ctx) (vb := 0) rfl rfl (by simp [BinOp.eval, X86.Encode.truncate64])
            have h2 : (mkBin .add .w64 (mkBin .add .w64 .ctx (.imm 0)) (.imm (dispWord m.disp))).eval ρ ctx snaps =
                some ((ctx + 0) + dispWord m.disp) :=
              mkBin_sound (o := .add) (w := .w64) h1 (b := .imm (dispWord m.disp)) (vb := dispWord m.disp) rfl
                (by simp [BinOp.eval, X86.Encode.truncate64])
            rw [h2] at haddr; cases haddr
            simp [ConstAddr.eval, MemBase.eval]
        | v x =>
            cases hx : (lookup x).eval ρ ctx snaps with
            | none =>
                exfalso
                have hnotimm : ∀ k, lookup x ≠ .imm k := fun k hk => by rw [hk] at hx; cases hx
                have hadd0 : mkBin .add .w64 (lookup x) (.imm 0) = lookup x := by
                  unfold mkBin mkBinOrdered mkAdd64
                  have hcmp : (SymExpr.cmp (.imm 0) (lookup x) == .lt) = false := by
                    cases hlx : lookup x with
                    | imm k => exact absurd hlx (hnotimm k)
                    | _ => rfl
                  simp only [binOpIsComm, hcmp, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                  cases hlx : lookup x with
                  | imm k => exact absurd hlx (hnotimm k)
                  | _ => rfl
                rw [hadd0] at haddr
                have hmk_none : ∀ (e : SymExpr) (d : Word), e.eval ρ ctx snaps = none →
                    (mkBin .add .w64 e (.imm d)).eval ρ ctx snaps = none := by
                  intro e d he
                  have hni : ∀ k, e ≠ .imm k := fun k hk => by rw [hk] at he; cases he
                  have hcm : (SymExpr.cmp (.imm d) e == .lt) = false := by
                    cases h : e with | imm k => exact absurd h (hni k) | _ => rfl
                  have hcore : (mkAdd64Core e (.imm d)).eval ρ ctx snaps = none := by
                    have hne : (e == .imm d) = false := by
                      cases h : e with | imm k => exact absurd h (hni k) | _ => rfl
                    have hmas : matchAddShlSelf e (.imm d) = none := by
                      cases e with
                      | bin o w y z =>
                          cases o <;> cases w <;> cases z <;> try rfl
                          rename_i k
                          unfold matchAddShlSelf
                          by_cases h1 : k = 1
                          · subst h1
                            by_cases hy : (y == .imm d) = true
                            · have hy' : y = .imm d := by simpa using hy
                              subst hy'; simp [SymExpr.eval, BinOp.eval] at he
                            · simp; intro h; exact hy (by simp [h])
                          · by_cases h2 : k = 2
                            · subst h2
                              by_cases hy : (y == .imm d) = true
                              · have hy' : y = .imm d := by simpa using hy
                                subst hy'; simp [SymExpr.eval, BinOp.eval] at he
                              · simp; intro h; exact hy (by simp [h])
                            · by_cases h3 : k = 3
                              · subst h3
                                by_cases hy : (y == .imm d) = true
                                · have hy' : y = .imm d := by simpa using hy
                                  subst hy'; simp [SymExpr.eval, BinOp.eval] at he
                                · simp; intro h; exact hy (by simp [h])
                              · simp [h1, h2, h3]
                      | _ => rfl
                    unfold mkAdd64Core
                    rw [hne, hmas, hcm]
                    simp [SymExpr.eval, he]
                  unfold mkBin mkBinOrdered
                  simp only [binOpIsComm, hcm, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                  cases e with
                  | imm k => exact absurd rfl (hni k)
                  | bin o w a b =>
                      by_cases hd0 : d = 0
                      · subst hd0
                        cases o <;> cases w <;> cases b <;> exact he
                      · cases o with
                        | add =>
                            cases w with
                            | w64 =>
                                cases b with
                                | imm c1 =>
                                    have ha_none : a.eval ρ ctx snaps = none := by
                                      cases hav : a.eval ρ ctx snaps with
                                      | none => rfl
                                      | some va => simp [SymExpr.eval, BinOp.eval, hav] at he
                                    simp only [mkAdd64]
                                    split
                                    · exact ha_none
                                    · simp [SymExpr.eval, ha_none]
                                | _ => simp [mkAdd64, hd0, hcore]
                            | _ => simp [mkAdd64, hd0, hcore]
                        | _ => simp [mkAdd64, hd0, hcore]
                  | _ =>
                      by_cases hd0 : d = 0
                      · subst hd0; exact he
                      · simp [mkAdd64, hd0, hcore]
                rw [hmk_none (lookup x) (dispWord m.disp) hx] at haddr
                cases haddr
            | some vx =>
                have h1 : (mkBin .add .w64 (lookup x) (.imm 0)).eval ρ ctx snaps = some (vx + 0) :=
                  mkBin_sound (o := .add) (w := .w64) hx (b := .imm 0) (vb := 0) rfl
                    (by simp [BinOp.eval, X86.Encode.truncate64])
                have h2 : (mkBin .add .w64 (mkBin .add .w64 (lookup x) (.imm 0)) (.imm (dispWord m.disp))).eval ρ ctx snaps =
                    some ((vx + 0) + dispWord m.disp) :=
                  mkBin_sound (o := .add) (w := .w64) h1 (b := .imm (dispWord m.disp)) (vb := dispWord m.disp) rfl
                    (by simp [BinOp.eval, X86.Encode.truncate64])
                rw [h2] at haddr; cases haddr
                simp only [ConstAddr.eval, MemBase.eval, SymExpr.norm_sound hx, Option.bind_eq_bind,
                  Option.bind_some, UInt64.add_zero]

theorem constAddrSame_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {w1 w2 : Width} {ca1 ca2 : Option ConstAddr} {a1 a2 : Word}
    (hsame : constAddrSame w1 ca1 w2 ca2 = true)
    (h1 : ca1.bind (ConstAddr.eval ρ ctx snaps) = some a1)
    (h2 : ca2.bind (ConstAddr.eval ρ ctx snaps) = some a2) :
    w1 = w2 ∧ a1 = a2 := by
  unfold constAddrSame at hsame
  simp only [Bool.and_eq_true, beq_iff_eq] at hsame
  obtain ⟨⟨rfl, _⟩, rfl⟩ := hsame
  rw [h1] at h2; cases h2
  exact ⟨rfl, rfl⟩

theorem constAddrDisjoint_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {w1 w2 : Width} {ca1 ca2 : Option ConstAddr} {a1 a2 : Word}
    (hdisj : constAddrDisjoint w1 ca1 w2 ca2 = true)
    (h1 : ca1.bind (ConstAddr.eval ρ ctx snaps) = some a1)
    (h2 : ca2.bind (ConstAddr.eval ρ ctx snaps) = some a2) :
    BytesDisjoint a1 w1.bytes a2 w2.bytes := by
  unfold constAddrDisjoint at hdisj
  cases ca1 with
  | none => cases hdisj
  | some c1 =>
    cases ca2 with
    | none => cases hdisj
    | some c2 =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hdisj
      obtain ⟨⟨⟨hbase, hd1⟩, hd2⟩, hgap⟩ := hdisj
      simp only [Option.bind_some, ConstAddr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h1 h2
      obtain ⟨b1, hb1, rfl⟩ := h1
      obtain ⟨b2, hb2, rfl⟩ := h2
      rw [hbase, hb2] at hb1; cases hb1
      intro i hi j hj
      exact dispWord_add_ne hd1 hd2 (width_bytes_le_8 w1) (width_bytes_le_8 w2) hgap hi hj

/-! ## Symbolic write-log semantics -/

/-- A `MemWrite` is well-formed w.r.t. `(ρ, ctx, snaps)` when its `addr` and `val` evaluate to
concrete words and (if present) its `caddr` evaluates to the same address. -/
def MemWrite.Valid (ρ : Env) (ctx : Word) (snaps : MemSnaps) (wr : MemWrite) : Prop :=
  ∃ va vv, wr.addr.eval ρ ctx snaps = some va ∧ wr.val.eval ρ ctx snaps = some vv ∧
    (∀ ca, wr.caddr = some ca → ca.eval ρ ctx snaps = some va)

/-- Apply a newest-first `List MemWrite` on top of base memory `mem₀`. -/
def applyWrites (ρ : Env) (ctx : Word) (snaps : MemSnaps) (mem₀ : X86.Memory) :
    List MemWrite → Option X86.Memory
  | [] => some mem₀
  | wr :: rest => do
      let m ← applyWrites ρ ctx snaps mem₀ rest
      let va ← wr.addr.eval ρ ctx snaps
      let vv ← wr.val.eval ρ ctx snaps
      some (m.write wr.width va vv)

theorem applyWrites_perms {ρ : Env} {ctx : Word} {snaps : MemSnaps} {mem₀ mem : X86.Memory}
    {ws : List MemWrite} (h : applyWrites ρ ctx snaps mem₀ ws = some mem) :
    mem.readable = mem₀.readable ∧ mem.writable = mem₀.writable := by
  induction ws generalizing mem with
  | nil => simp only [applyWrites, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | cons wr rest ih =>
      simp only [applyWrites, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨m, hm, va, _, vv, _, rfl⟩ := h
      obtain ⟨hr, hw⟩ := ih hm
      exact ⟨by simpa [X86.Memory.write] using hr, by simpa [X86.Memory.write] using hw⟩

theorem dropShadowed_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {mem₀ : X86.Memory}
    {w : Width} {ca : Option ConstAddr} {va vv : Word}
    (hca : ∀ c, ca = some c → c.eval ρ ctx snaps = some va) :
    ∀ {ws : List MemWrite} {m : X86.Memory},
      (∀ wr ∈ ws, wr.Valid ρ ctx snaps) →
      applyWrites ρ ctx snaps mem₀ ws = some m →
      ∃ m', applyWrites ρ ctx snaps mem₀ (dropShadowed w ca ws) = some m' ∧
        m'.write w va vv = m.write w va vv
  | [], m, _, hm => ⟨m, hm, rfl⟩
  | wr :: rest, m, hvalid, hm => by
      simp only [applyWrites, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hm
      obtain ⟨mr, hmr, wva, hwva, wvv, hwvv, rfl⟩ := hm
      have hwr := hvalid wr (by simp)
      have hrest : ∀ u ∈ rest, u.Valid ρ ctx snaps := fun u hu => hvalid u (by simp [hu])
      unfold dropShadowed
      by_cases hsame : constAddrSame w ca wr.width wr.caddr = true
      · simp only [hsame, ↓reduceIte]
        -- Extract that ca = some c and wr.caddr = some c
        have hca_some : ca.isSome = true := by
          unfold constAddrSame at hsame; simp only [Bool.and_eq_true] at hsame; exact hsame.1.2
        cases hca_eq : ca with
        | none => simp [hca_eq] at hca_some
        | some c =>
            have h1 : ca.bind (ConstAddr.eval ρ ctx snaps) = some va := by
              rw [hca_eq]; exact hca c hca_eq
            have hwr_eq : wr.caddr = some c := by
              unfold constAddrSame at hsame
              simp only [Bool.and_eq_true, beq_iff_eq, hca_eq] at hsame
              exact hsame.2.symm
            obtain ⟨va', vv', hva', _, hca'⟩ := hwr
            rw [hwva] at hva'; cases hva'
            have h2 : wr.caddr.bind (ConstAddr.eval ρ ctx snaps) = some wva := by
              rw [hwr_eq]; exact hca' c hwr_eq
            obtain ⟨hw_eq, hva_eq⟩ := constAddrSame_sound hsame h1 h2
            rw [hw_eq, hva_eq]
            exact ⟨mr, hmr, (write_write_overwrite mr wr.width wva wvv vv).symm⟩
      · simp only [hsame, Bool.false_eq_true, ↓reduceIte]
        by_cases hdisj : constAddrDisjoint w ca wr.width wr.caddr = true
        · simp only [hdisj, ↓reduceIte]
          obtain ⟨mr', hmr', heq⟩ := dropShadowed_sound (w := w) (vv := vv) hca hrest hmr
          refine ⟨mr'.write wr.width wva wvv, ?_, ?_⟩
          · simp only [applyWrites, Option.bind_eq_bind, hmr', hwva, hwvv, Option.bind_some]
          · -- Extract byte disjointness of `(w, va)` and `(wr.width, wva)`
            have hbd : BytesDisjoint va w.bytes wva wr.width.bytes := by
              cases hca_eq : ca with
              | none => unfold constAddrDisjoint at hdisj; rw [hca_eq] at hdisj; cases hdisj
              | some c =>
                  cases hwc_eq : wr.caddr with
                  | none => unfold constAddrDisjoint at hdisj; rw [hca_eq, hwc_eq] at hdisj; cases hdisj
                  | some c' =>
                      obtain ⟨va', _, hva', _, hca'⟩ := hwr
                      rw [hwva] at hva'; cases hva'
                      exact constAddrDisjoint_sound hdisj
                        (by rw [hca_eq]; exact hca c hca_eq)
                        (by rw [hwc_eq]; exact hca' c' hwc_eq)
            rw [write_write_comm mr' hbd.symm, heq, write_write_comm mr hbd]
        · simp only [hdisj, Bool.false_eq_true, ↓reduceIte]
          exact ⟨mr.write wr.width wva wvv,
            by simp only [applyWrites, Option.bind_eq_bind, hmr, hwva, hwvv, Option.bind_some], rfl⟩

theorem dropShadowed_valid {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {w : Width} {ca : Option ConstAddr} :
    ∀ {ws : List MemWrite}, (∀ wr ∈ ws, wr.Valid ρ ctx snaps) →
      ∀ wr ∈ dropShadowed w ca ws, wr.Valid ρ ctx snaps
  | [], _, _, h => by simp [dropShadowed] at h
  | u :: rest, hv, wr, hmem => by
      unfold dropShadowed at hmem
      split at hmem
      · exact hv wr (by simp [hmem])
      · split at hmem
        · simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hv _ (by simp)
          · exact dropShadowed_valid (fun x hx => hv x (by simp [hx])) wr hmem
        · exact hv wr hmem

theorem SymMem.readAux_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {mem₀ : X86.Memory}
    {w : Width} {e : Ext} {ca : Option ConstAddr} {va v : Word}
    (hca : ∀ c, ca = some c → c.eval ρ ctx snaps = some va) :
    ∀ {ws : List MemWrite} {m : X86.Memory},
      (∀ wr ∈ ws, wr.Valid ρ ctx snaps) →
      applyWrites ρ ctx snaps mem₀ ws = some m →
      loadWord m w e va = some v →
      match SymMem.readAux w e ca ws with
      | .inl fe => fe.eval ρ ctx snaps = some v
      | .inr ws' => ∃ m', applyWrites ρ ctx snaps mem₀ ws' = some m' ∧ loadWord m' w e va = some v
  | [], m, _, hm, hld => by
      simp only [SymMem.readAux]
      exact ⟨m, hm, hld⟩
  | wr :: rest, m, hvalid, hm, hld => by
      have hm_orig := hm
      simp only [applyWrites, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hm
      obtain ⟨mr, hmr, wva, hwva, wvv, hwvv, rfl⟩ := hm
      have hwr := hvalid wr (by simp)
      have hrest : ∀ u ∈ rest, u.Valid ρ ctx snaps := fun u hu => hvalid u (by simp [hu])
      unfold SymMem.readAux
      by_cases hsame : constAddrSame w ca wr.width wr.caddr = true
      · simp only [hsame, ↓reduceIte]
        cases hfw : forwardVal w e wr.val with
        | none => exact ⟨mr.write wr.width wva wvv, hm_orig, hld⟩
        | some fe =>
            have hca_some : ca.isSome = true := by
              unfold constAddrSame at hsame; simp only [Bool.and_eq_true] at hsame; exact hsame.1.2
            cases hca_eq : ca with
            | none => simp [hca_eq] at hca_some
            | some c =>
                have hwr_eq : wr.caddr = some c := by
                  unfold constAddrSame at hsame
                  simp only [Bool.and_eq_true, beq_iff_eq, hca_eq] at hsame
                  exact hsame.2.symm
                obtain ⟨va', _, hva', _, hca'⟩ := hwr
                rw [hwva] at hva'; cases hva'
                obtain ⟨rfl, rfl⟩ := constAddrSame_sound hsame
                  (by rw [hca_eq]; exact hca c hca_eq)
                  (by rw [hwr_eq]; exact hca' c hwr_eq)
                exact forwardVal_sound hfw hwvv hld
      · simp only [hsame, Bool.false_eq_true, ↓reduceIte]
        by_cases hdisj : constAddrDisjoint w ca wr.width wr.caddr = true
        · simp only [hdisj, ↓reduceIte]
          have hbd : BytesDisjoint va w.bytes wva wr.width.bytes := by
            cases hca_eq : ca with
            | none => unfold constAddrDisjoint at hdisj; rw [hca_eq] at hdisj; cases hdisj
            | some c =>
                cases hwc_eq : wr.caddr with
                | none => unfold constAddrDisjoint at hdisj; rw [hca_eq, hwc_eq] at hdisj; cases hdisj
                | some c' =>
                    obtain ⟨va', _, hva', _, hca'⟩ := hwr
                    rw [hwva] at hva'; cases hva'
                    exact constAddrDisjoint_sound hdisj
                      (by rw [hca_eq]; exact hca c hca_eq)
                      (by rw [hwc_eq]; exact hca' c' hwc_eq)
          rw [loadWord_write_disjoint mr hbd] at hld
          exact SymMem.readAux_sound hca hrest hmr hld
        · simp only [hdisj, Bool.false_eq_true, ↓reduceIte]
          exact ⟨mr.write wr.width wva wvv, hm_orig, hld⟩

theorem writesEquiv_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {mem₀ : X86.Memory} :
    ∀ {ws1 ws2 : List MemWrite} {m1 m2 : X86.Memory},
      writesEquiv ws1 ws2 = true →
      applyWrites ρ ctx snaps mem₀ ws1 = some m1 →
      applyWrites ρ ctx snaps mem₀ ws2 = some m2 →
      m1 = m2
  | [], [], m1, m2, _, h1, h2 => by
      simp only [applyWrites, Option.some.injEq] at h1 h2; rw [← h1, ← h2]
  | w1 :: r1, w2 :: r2, m1, m2, heq, h1, h2 => by
      simp only [writesEquiv, Bool.and_eq_true, beq_iff_eq] at heq
      obtain ⟨⟨⟨hw, ha⟩, hv⟩, hr⟩ := heq
      simp only [applyWrites, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h1 h2
      obtain ⟨m1', hm1', a1, ha1, v1, hv1, rfl⟩ := h1
      obtain ⟨m2', hm2', a2, ha2, v2, hv2, rfl⟩ := h2
      have hm := writesEquiv_sound hr hm1' hm2'
      have ha_eq := exprEquiv_sound ha ha1 ha2
      have hv_eq := exprEquiv_sound hv hv1 hv2
      rw [hm, hw, ha_eq, hv_eq]
  | [], _ :: _, _, _, heq, _, _ => by cases heq
  | _ :: _, [], _, _, heq, _, _ => by cases heq

/-! ## `SnapTable` semantics -/

/-- A `MemSnaps` function is consistent with snapshot table `st` over base memory `mem₀`
when every valid index `id < st.size` maps to the exact memory produced by `applyWrites st[id]`. -/
def SnapsConsistent (ρ : Env) (ctx : Word) (mem₀ : X86.Memory)
    (st : SnapTable) (snaps : MemSnaps) : Prop :=
  ∀ (id : Nat) (ws : List MemWrite), st[id]? = some ws →
    applyWrites ρ ctx snaps mem₀ ws = some (snaps id)

/-- Every `load` node inside `e` uses a snapshot index strictly below `bound`. -/
def SymExpr.snapsLt (bound : Nat) : SymExpr → Prop
  | .reg _ | .imm _ | .ctx => True
  | .bin _ _ a b | .test _ _ a b | .mulHi a b => a.snapsLt bound ∧ b.snapsLt bound
  | .select _ _ a b t f => a.snapsLt bound ∧ b.snapsLt bound ∧ t.snapsLt bound ∧ f.snapsLt bound
  | .bsr64 a => a.snapsLt bound
  | .divQ a b c | .divR a b c | .addCLo a b c | .addCHi a b c
  | .subBLo a b c | .subBHi a b c => a.snapsLt bound ∧ b.snapsLt bound ∧ c.snapsLt bound
  | .load snap _ _ a => snap < bound ∧ a.snapsLt bound

theorem SymExpr.eval_snaps_congr {ρ : Env} {ctx : Word} {snaps1 snaps2 : MemSnaps} {bound : Nat}
    (hagree : ∀ id < bound, snaps1 id = snaps2 id) :
    ∀ {e : SymExpr}, e.snapsLt bound → e.eval ρ ctx snaps1 = e.eval ρ ctx snaps2
  | .reg _, _ => rfl
  | .imm _, _ => rfl
  | .ctx, _ => rfl
  | .bin o w a b, ⟨ha, hb⟩ => by
      simp only [SymExpr.eval, eval_snaps_congr hagree ha, eval_snaps_congr hagree hb]
  | .select c w a b t f, ⟨ha, hb, ht, hf⟩ => by
      simp only [SymExpr.eval, eval_snaps_congr hagree ha, eval_snaps_congr hagree hb,
        eval_snaps_congr hagree ht, eval_snaps_congr hagree hf]
  | .test c w a b, ⟨ha, hb⟩ => by
      simp only [SymExpr.eval, eval_snaps_congr hagree ha, eval_snaps_congr hagree hb]
  | .bsr64 a, ha => by simp only [SymExpr.eval, eval_snaps_congr hagree (e := a) ha]
  | .mulHi a b, ⟨ha, hb⟩ => by
      simp only [SymExpr.eval, eval_snaps_congr hagree ha, eval_snaps_congr hagree hb]
  | .divQ a b c, ⟨ha, hb, hc⟩ => by
      simp only [SymExpr.eval, eval_snaps_congr hagree ha, eval_snaps_congr hagree hb,
        eval_snaps_congr hagree hc]
  | .divR a b c, ⟨ha, hb, hc⟩ => by
      simp only [SymExpr.eval, eval_snaps_congr hagree ha, eval_snaps_congr hagree hb,
        eval_snaps_congr hagree hc]
  | .addCLo a b c, ⟨ha, hb, hc⟩ => by
      simp only [SymExpr.eval, eval_snaps_congr hagree ha, eval_snaps_congr hagree hb,
        eval_snaps_congr hagree hc]
  | .addCHi a b c, ⟨ha, hb, hc⟩ => by
      simp only [SymExpr.eval, eval_snaps_congr hagree ha, eval_snaps_congr hagree hb,
        eval_snaps_congr hagree hc]
  | .subBLo a b c, ⟨ha, hb, hc⟩ => by
      simp only [SymExpr.eval, eval_snaps_congr hagree ha, eval_snaps_congr hagree hb,
        eval_snaps_congr hagree hc]
  | .subBHi a b c, ⟨ha, hb, hc⟩ => by
      simp only [SymExpr.eval, eval_snaps_congr hagree ha, eval_snaps_congr hagree hb,
        eval_snaps_congr hagree hc]
  | .load snap w e a, ⟨hs, ha⟩ => by
      simp only [SymExpr.eval, eval_snaps_congr hagree ha, hagree snap hs]

theorem SymExpr.snapsLt_mono {b1 b2 : Nat} (hle : b1 ≤ b2) :
    ∀ {e : SymExpr}, e.snapsLt b1 → e.snapsLt b2
  | .reg _, h => h
  | .imm _, h => h
  | .ctx, h => h
  | .bin _ _ a b, ⟨ha, hb⟩ => ⟨snapsLt_mono hle (e := a) ha, snapsLt_mono hle (e := b) hb⟩
  | .select _ _ a b t f, ⟨ha, hb, ht, hf⟩ =>
      ⟨snapsLt_mono hle (e := a) ha, snapsLt_mono hle (e := b) hb,
       snapsLt_mono hle (e := t) ht, snapsLt_mono hle (e := f) hf⟩
  | .test _ _ a b, ⟨ha, hb⟩ => ⟨snapsLt_mono hle (e := a) ha, snapsLt_mono hle (e := b) hb⟩
  | .bsr64 a, ha => snapsLt_mono hle (e := a) ha
  | .mulHi a b, ⟨ha, hb⟩ => ⟨snapsLt_mono hle (e := a) ha, snapsLt_mono hle (e := b) hb⟩
  | .divQ a b c, ⟨ha, hb, hc⟩ | .divR a b c, ⟨ha, hb, hc⟩
  | .addCLo a b c, ⟨ha, hb, hc⟩ | .addCHi a b c, ⟨ha, hb, hc⟩
  | .subBLo a b c, ⟨ha, hb, hc⟩ | .subBHi a b c, ⟨ha, hb, hc⟩ =>
      ⟨snapsLt_mono hle (e := a) ha, snapsLt_mono hle (e := b) hb, snapsLt_mono hle (e := c) hc⟩
  | .load _ _ _ a, ⟨hs, ha⟩ => ⟨Nat.lt_of_lt_of_le hs hle, snapsLt_mono hle (e := a) ha⟩

theorem SymExpr.snapsLt_of_isMemFree :
    ∀ {e : SymExpr}, e.isMemFree = true → ∀ (b : Nat), e.snapsLt b
  | .reg _, _, _ | .imm _, _, _ | .ctx, _, _ => trivial
  | .load .., h, _ => by simp [SymExpr.isMemFree] at h
  | .bin _ _ a b, h, bd | .test _ _ a b, h, bd | .mulHi a b, h, bd => by
      simp only [SymExpr.isMemFree, Bool.and_eq_true] at h
      exact ⟨snapsLt_of_isMemFree h.1 bd, snapsLt_of_isMemFree h.2 bd⟩
  | .select _ _ a b t f, h, bd => by
      simp only [SymExpr.isMemFree, Bool.and_eq_true] at h
      exact ⟨snapsLt_of_isMemFree h.1.1.1 bd, snapsLt_of_isMemFree h.1.1.2 bd,
        snapsLt_of_isMemFree h.1.2 bd, snapsLt_of_isMemFree h.2 bd⟩
  | .bsr64 a, h, bd => snapsLt_of_isMemFree (e := a) h bd
  | .divQ a b c, h, bd | .divR a b c, h, bd
  | .addCLo a b c, h, bd | .addCHi a b c, h, bd
  | .subBLo a b c, h, bd | .subBHi a b c, h, bd => by
      simp only [SymExpr.isMemFree, Bool.and_eq_true] at h
      exact ⟨snapsLt_of_isMemFree h.1.1 bd, snapsLt_of_isMemFree h.1.2 bd, snapsLt_of_isMemFree h.2 bd⟩

theorem applyWrites_snaps_congr {ρ : Env} {ctx : Word} {snaps1 snaps2 : MemSnaps} {mem₀ : X86.Memory}
    {bound : Nat} (hagree : ∀ id < bound, snaps1 id = snaps2 id) :
    ∀ {ws : List MemWrite}, (∀ wr ∈ ws, wr.addr.snapsLt bound ∧ wr.val.snapsLt bound) →
      applyWrites ρ ctx snaps1 mem₀ ws = applyWrites ρ ctx snaps2 mem₀ ws
  | [], _ => rfl
  | wr :: rest, hlt => by
      have hwr := hlt wr (by simp)
      have hrest := applyWrites_snaps_congr (ρ := ρ) (ctx := ctx) (mem₀ := mem₀)
        hagree (ws := rest) (fun u hu => hlt u (by simp [hu]))
      simp only [applyWrites, hrest, SymExpr.eval_snaps_congr hagree hwr.1,
        SymExpr.eval_snaps_congr hagree hwr.2]

/-- Interning a write list `ws` whose concrete memory is `m` extends `snaps` consistently
without modifying any existing snapshot `< st.size`. -/
theorem SnapTable.intern_sound {ρ : Env} {ctx : Word} {mem₀ m : X86.Memory}
    {st : SnapTable} {snaps : MemSnaps} {ws : List MemWrite}
    (hcons : SnapsConsistent ρ ctx mem₀ st snaps)
    (hlt_st : ∀ (id : Nat) (u : List MemWrite), st[id]? = some u →
      ∀ wr ∈ u, wr.addr.snapsLt st.size ∧ wr.val.snapsLt st.size)
    (hlt_ws : ∀ wr ∈ ws, wr.addr.snapsLt st.size ∧ wr.val.snapsLt st.size)
    (hm : applyWrites ρ ctx snaps mem₀ ws = some m) :
    let (id, st') := st.intern ws
    ∃ snaps',
      id < st'.size ∧ st.size ≤ st'.size ∧
      (∀ k < st.size, snaps' k = snaps k) ∧
      snaps' id = m ∧
      SnapsConsistent ρ ctx mem₀ st' snaps' ∧
      (∀ (j : Nat) (u : List MemWrite), st'[j]? = some u →
        ∀ wr ∈ u, wr.addr.snapsLt st'.size ∧ wr.val.snapsLt st'.size) := by
  unfold SnapTable.intern
  -- Analyze `find` helper
  have hfind : ∀ (i id : Nat), SnapTable.intern.find st ws i = some id →
      id < st.size ∧ ∃ existing, st[id]? = some existing ∧ writesEquiv existing ws = true := by
    intro i
    induction i with
    | zero => intro id h; cases h
    | succ i ih =>
        intro id h
        unfold SnapTable.intern.find at h
        dsimp only at h
        cases hget : st[st.size - (i + 1)]? with
        | none => rw [hget] at h; exact ih id h
        | some existing =>
            rw [hget] at h
            by_cases heq : writesEquiv existing ws = true
            · simp only [heq, ↓reduceIte, Option.some.injEq] at h
              subst h
              exact ⟨(Array.getElem?_eq_some_iff.1 hget).1, existing, hget, heq⟩
            · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
              exact ih id h
  cases hf : SnapTable.intern.find st ws st.size with
  | some id =>
      dsimp only
      obtain ⟨hid, existing, hget, heq⟩ := hfind st.size id hf
      have hex := hcons id existing hget
      have hmeq : snaps id = m := writesEquiv_sound heq hex hm
      exact ⟨snaps, hid, Nat.le_refl _, fun _ _ => rfl, hmeq, hcons, hlt_st⟩
  | none =>
      dsimp only
      let snaps' : MemSnaps := fun k => if k == st.size then m else snaps k
      have hagree : ∀ k < st.size, snaps' k = snaps k := fun k hk => by
        simp [snaps', Nat.ne_of_lt hk]
      refine ⟨snaps', by simp, by simp, hagree, by simp [snaps'], ?_, ?_⟩
      · intro j u hj
        by_cases hlt : j < st.size
        · rw [Array.getElem?_push_lt hlt] at hj
          have hj' : st[j]? = some u := by rwa [Array.getElem?_eq_getElem hlt]
          rw [applyWrites_snaps_congr hagree (hlt_st j u hj'), hcons j u hj', hagree j hlt]
        · have hj_eq : j = st.size := by
            have := (Array.getElem?_eq_some_iff.1 hj).1
            simp only [Array.size_push] at this; omega
          subst hj_eq
          rw [Array.getElem?_push_size] at hj; cases hj
          rw [applyWrites_snaps_congr hagree hlt_ws, hm]
          simp [snaps']
      · intro j u hj wr hwr
        have hle : st.size ≤ (st.push ws).size := by simp
        by_cases hlt : j < st.size
        · rw [Array.getElem?_push_lt hlt] at hj
          have hj' : st[j]? = some u := by rwa [Array.getElem?_eq_getElem hlt]
          have ⟨ha, hv⟩ := hlt_st j u hj' wr hwr
          exact ⟨SymExpr.snapsLt_mono hle ha, SymExpr.snapsLt_mono hle hv⟩
        · have hj_eq : j = st.size := by
            have := (Array.getElem?_eq_some_iff.1 hj).1
            simp only [Array.size_push] at this; omega
          subst hj_eq
          rw [Array.getElem?_push_size] at hj; cases hj
          have ⟨ha, hv⟩ := hlt_ws wr hwr
          exact ⟨SymExpr.snapsLt_mono hle ha, SymExpr.snapsLt_mono hle hv⟩

end IxCC.Lir.Opt
