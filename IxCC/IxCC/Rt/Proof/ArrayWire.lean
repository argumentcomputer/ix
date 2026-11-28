import IxCC.Rt.Proof.StrHoist
import IxCC.Rt.Readback.Array
import IxCC.X86.Linked

/-! # DR1 / DR3 / DR4 Array & Static String Wiring Proofs

Proves the end-to-end memory, `.rodata`, and readback soundness of the DR1/DR3/DR4
wiring components:

1. **`.rodata` string table (`buildStringRodata_spec`, `buildStringRodata_staticCell`,
   `buildStringRodata_readbackString`, `buildStringRodata_linkedRodata_readbackString`)**:
   Every string `s` emitted by `LowerStr.buildStringRodata strs` is 8-byte aligned,
   preserved verbatim in `tbl.bytes`, forms a valid `StaticArrayCell`, reads back as
   `some s` via `Rt.Readback.readbackString` under any `X86.ELFRodata.RodataMapped`,
   and survives any `X86.LinkedRodata.rootCall` unmodified.
2. **Direct `.rodata` string getter (`rodataStrProc_eval`)**:
   `Rt.Rc.Array.rodataStrProc idx addr` returns `[addr]` at every clock without modifying
   memory, preserving `RodataMapped` and `readbackString`.
3. **Position-independent string materializer (`strLitProc_staticCell`,
   `strLitProc_readbackString`)**:
   `bytesToWords64` round-trips every byte of any 8-byte-aligned `ByteArray`, so
   `Rt.Rc.Array.strLitProc idx s` writes the exact `encodeStaticString s` cell at `bump`,
   establishing `StaticArrayCell` and `Rt.Readback.readbackString mem' bump = some s`.
4. **Extended array runtime relocation (`relocateFunc_meta`,
   `extendedArrayRuntimeFuncs_len`)**:
   `relocateFunc` preserves function metadata (`name`, `params`, `results`, `conv`),
   and `extendedArrayRuntimeFuncs` has exact length `36`. -/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Rt.LowerStr
open IxCC.Rt.Rc.Array
open IxCC.Rt.Readback
open IxCC.X86
open IxCC.X86.ELFRodata

/-! ## 1. `.rodata` String Table (`buildStringRodata`) → `StaticArrayCell` → `readbackString` -/

/-- Helper invariant carried through the `buildStringRodata` fold. -/
private def RodataEntriesOk (tbl : RodataTable) (offs : List (String × Nat)) : Prop :=
  ∀ s off, (s, off) ∈ offs →
    off % 8 = 0 ∧
    ∃ hbd : off + (encodeStaticString s).size ≤ tbl.bytes.size,
      ∀ j (hj : j < (encodeStaticString s).size),
        tbl.bytes[off + j]'(by omega) = (encodeStaticString s)[j]'hj

private theorem rodataEntriesOk_addString {tbl : RodataTable} {offs : List (String × Nat)}
    (hok : RodataEntriesOk tbl offs) (name s : String) :
    RodataEntriesOk (tbl.addString name s).1 (offs ++ [(s, (tbl.addString name s).2)]) := by
  intro s' off' hmem
  rcases List.mem_append.1 hmem with hold | hnew
  · obtain ⟨hal, hbd, hbytes⟩ := hok s' off' hold
    have hle : tbl.bytes.size ≤ (tbl.addString name s).1.bytes.size := by
      have h1 := alignUp8_ge tbl.bytes.size
      have h2 := RodataTable.addCell_bounds tbl name (encodeStaticString s)
      have h3 : (tbl.addCell name (encodeStaticString s)).2 = ELF.alignUp tbl.bytes.size 8 := rfl
      change tbl.bytes.size ≤ (tbl.addCell name (encodeStaticString s)).1.bytes.size
      omega
    refine ⟨hal, by omega, fun j hj => ?_⟩
    have hpre := RodataTable.addCell_preserves_prefix tbl name (encodeStaticString s) (i := off' + j) (by omega)
    exact hpre.trans (hbytes j hj)
  · simp only [List.mem_singleton, Prod.mk.injEq] at hnew
    obtain ⟨rfl, rfl⟩ := hnew
    exact ⟨RodataTable.addCell_aligned tbl name (encodeStaticString s'),
      RodataTable.addCell_bounds tbl name (encodeStaticString s'),
      fun j hj => RodataTable.addCell_bytes_eq tbl name (encodeStaticString s') hj⟩

/-- **Specification of `LowerStr.buildStringRodata`**: every recorded `(s, off)` is
8-byte aligned, in bounds, and matches `encodeStaticString s` byte-for-byte in `tbl.bytes`,
with `(offs.map Prod.fst) = strs`. -/
theorem buildStringRodata_spec (strs : List String) :
    let (tbl, offs) := buildStringRodata strs
    offs.map Prod.fst = strs ∧
    ∀ s off, (s, off) ∈ offs →
      off % 8 = 0 ∧
      ∃ hbd : off + (encodeStaticString s).size ≤ tbl.bytes.size,
        ∀ j (hj : j < (encodeStaticString s).size),
          tbl.bytes[off + j]'(by omega) = (encodeStaticString s)[j]'hj := by
  have aux : ∀ (l : List (String × Nat)) (tbl : RodataTable) (offs : List (String × Nat)),
      RodataEntriesOk tbl offs →
      let res := l.foldl (init := (tbl, offs)) fun (t, os) (s, i) =>
        let (t', off) := t.addString s!"cx_str_{i}" s
        (t', os ++ [(s, off)])
      res.2.map Prod.fst = offs.map Prod.fst ++ l.map Prod.fst ∧
      RodataEntriesOk res.1 res.2 := by
    intro l
    induction l with
    | nil => intro tbl offs hok; exact ⟨by simp, hok⟩
    | cons p l ih =>
      intro tbl offs hok
      obtain ⟨s, i⟩ := p
      have hok' := rodataEntriesOk_addString hok s!"cx_str_{i}" s
      obtain ⟨hmap, hres⟩ := ih (tbl.addString s!"cx_str_{i}" s).1
        (offs ++ [(s, (tbl.addString s!"cx_str_{i}" s).2)]) hok'
      refine ⟨?_, hres⟩
      simpa [List.map_append, List.append_assoc] using hmap
  have h0 : RodataEntriesOk RodataTable.empty [] := fun _ _ h => nomatch h
  obtain ⟨hmap, hok⟩ := aux (strs.zipIdx) RodataTable.empty [] h0
  refine ⟨?_, hok⟩
  have hzip : strs.zipIdx.map Prod.fst = strs := by
    have haux : ∀ (k : Nat) (xs : List String), (xs.zipIdx k).map Prod.fst = xs := by
      intro k xs
      induction xs generalizing k with
      | nil => rfl
      | cons x xs ih => simp [List.zipIdx_cons, ih]
    exact haux 0 strs
  simpa [hzip] using hmap

/-- Every string cell built by `buildStringRodata` satisfies `StaticArrayCell` when
`tbl.bytes` is mapped via `RodataMapped`. -/
theorem buildStringRodata_staticCell {strs : List String} {base : Word} {mem : Memory}
    (hm : RodataMapped base (buildStringRodata strs).1.bytes mem)
    {s : String} {off : Nat} (hmem : (s, off) ∈ (buildStringRodata strs).2) :
    StaticArrayCell mem (base + UInt64.ofNat off) (X86.ELF.alignUp s.toUTF8.size 8)
      (.bytes s.toByteArray.data.toList) := by
  obtain ⟨hal, hbd, hbytes⟩ := (buildStringRodata_spec strs).2 s off hmem
  have hbd' : off + (encodeStaticString s).size ≤ (buildStringRodata strs).1.bytes.size := hbd
  have hnz : base + UInt64.ofNat off ≠ 0 := by
    intro hz
    have hbase0 : base.toNat ≠ 0 := fun h0 => hm.nonzero (UInt64.toNat_inj.mp h0)
    have hfit := hm.fit
    have hto : (base + UInt64.ofNat off).toNat = base.toNat + off :=
      addr_toNat (by omega)
    have h0 : (base + UInt64.ofNat off).toNat = 0 := by rw [hz]; rfl
    omega
  have hutf : s.toUTF8 = s.toByteArray := rfl
  have hcell := StaticArrayCell.ofRodataByteArray (bs := s.toUTF8) hm hal hnz hbd hbytes
  simpa [hutf] using hcell

/-- **DR1 + DR4 `.rodata` string readback**: under any `RodataMapped base tbl.bytes mem`,
every `(s, off)` produced by `buildStringRodata strs` reads back via `readbackString` as
`some s`. -/
theorem buildStringRodata_readbackString {strs : List String} {base : Word} {mem : Memory}
    (hm : RodataMapped base (buildStringRodata strs).1.bytes mem)
    {s : String} {off : Nat} (hmem : (s, off) ∈ (buildStringRodata strs).2) :
    readbackString mem (base + UInt64.ofNat off) = some s :=
  readbackString_static (buildStringRodata_staticCell hm hmem)

/-- **`X86.LinkedRodata` end-to-end string preservation**: after any `LinkedRodata.rootCall`
on an ELF object whose `.rodata` section is `(buildStringRodata strs).1.bytes`, every
string cell `(s, off)` still reads back verbatim as `some s`. -/
theorem buildStringRodata_linkedRodata_readbackString {L : X86.LinkedRodata} {strs : List String}
    {r : X86.Linked.Root} {ns : List Nat} {bytes : Word → UInt8} {k : Nat}
    {val : Word} {mem' : Memory}
    (hparse : ELFRead.rodata? L.linked.object = some (buildStringRodata strs).1.bytes)
    (h0 : L.rodataBase ≠ 0) (hal : L.rodataBase.toNat % 8 = 0)
    (hfit : L.rodataBase.toNat + (buildStringRodata strs).1.bytes.size < 2 ^ 63)
    (hcall : L.rootCall r ns bytes k = .ok (val, mem'))
    {s : String} {off : Nat} (hmem : (s, off) ∈ (buildStringRodata strs).2) :
    readbackString mem' (L.rodataBase + UInt64.ofNat off) = some s := by
  have hloaded := L.rootCall_preserves_rodata hparse h0 hal hfit hcall
  obtain ⟨rodata', hparse', hm'⟩ := hloaded
  rw [hparse] at hparse'
  cases hparse'
  exact buildStringRodata_readbackString hm' hmem

/-! ## 2. Direct `.rodata` String Getter (`rodataStrProc`) -/

/-- Calling `rodataStrProc idx addr` returns `[addr]` at every clock without modifying memory. -/
theorem rodataStrProc_eval {lp : Lir.Program} {idx : Nat} {addr ctx : Word} {mem : Memory}
    (hfn : lp.funcs[lp.main]? = some (rodataStrProc idx addr)) (k : Nat) :
    Lir.eval lp k [] mem ctx = .ok ([addr], mem) := by
  have hinit : Lir.State.initial lp [] mem ctx =
      some { mem, ctx, stack := [{ fn := lp.main, label := 0, pos := 0, env := {} }] } := by
    simp [Lir.State.initial, Lir.enter, hfn, rodataStrProc, Lir.bindParams]
  have hruns := Lir.runs_eval hinit
  have hs1 : Lir.step lp { mem, ctx, stack := [{ fn := lp.main, label := 0, pos := 0, env := {} }] } =
      .next { mem, ctx, stack := [{ fn := lp.main, label := 0, pos := 1, env := ({} : Lir.Env).insert 0 addr }] } false := by
    simp [Lir.step, hfn, rodataStrProc, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval]
  have hs2 : Lir.step lp { mem, ctx, stack := [{ fn := lp.main, label := 0, pos := 1, env := ({} : Lir.Env).insert 0 addr }] } =
      .done [addr] mem := by
    simp [Lir.step, hfn, rodataStrProc, Lir.evalArgs, Lir.Arg.eval, Rt.Rc.Procs.v]
  have hreach : Sem.Reaches (Lir.semStep lp)
      { mem, ctx, stack := [{ fn := lp.main, label := 0, pos := 0, env := {} }] } k (.ok ([addr], mem)) :=
    Sem.Reaches.of_final (Lir.star_of_step hs1) (by rw [Lir.semStep, hs2]; exact .done) (Nat.zero_le k)
  exact hruns.eq hreach

/-! ## 3. Position-Independent Materializer (`strLitProc`) → `StaticArrayCell` → `readbackString` -/

private theorem byteArray_getBang_eq (bs : ByteArray) {i : Nat} (hi : i < bs.size) :
    bs.get! i = bs[i]'hi := by
  change bs.data[i]! = bs.data[i]'hi
  exact getElem!_pos bs.data i hi

private theorem or_shift_byte_extract (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) (j : Nat) (hj : j < 8) :
    let w : Word :=
      b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
      (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)
    (w >>> UInt64.ofNat (8 * j)).toUInt8 =
      match j with
      | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
      | 4 => b4 | 5 => b5 | 6 => b6 | _ => b7 := by
  have hb0 := b0.toNat_lt; have hb1 := b1.toNat_lt; have hb2 := b2.toNat_lt; have hb3 := b3.toNat_lt
  have hb4 := b4.toNat_lt; have hb5 := b5.toNat_lt; have hb6 := b6.toNat_lt; have hb7 := b7.toNat_lt
  have hw_toNat : (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
      (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)).toNat =
      b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 +
      b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48 + b7.toNat * 2 ^ 56 := by
    simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64,
      show (UInt64.toNat 8) % 64 = 8 from rfl, show (UInt64.toNat 16) % 64 = 16 from rfl,
      show (UInt64.toNat 24) % 64 = 24 from rfl, show (UInt64.toNat 32) % 64 = 32 from rfl,
      show (UInt64.toNat 40) % 64 = 40 from rfl, show (UInt64.toNat 48) % 64 = 48 from rfl,
      show (UInt64.toNat 56) % 64 = 56 from rfl, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega : b1.toNat * 2 ^ 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : b2.toNat * 2 ^ 16 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : b3.toNat * 2 ^ 24 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : b4.toNat * 2 ^ 32 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : b5.toNat * 2 ^ 40 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : b6.toNat * 2 ^ 48 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : b7.toNat * 2 ^ 56 < 2 ^ 64)]
    have step1 : b0.toNat ||| b1.toNat * 2 ^ 8 = b0.toNat + b1.toNat * 2 ^ 8 := by
      rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega)]; omega
    rw [step1]
    have step2 : (b0.toNat + b1.toNat * 2 ^ 8) ||| b2.toNat * 2 ^ 16 =
        b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 := by
      rw [Nat.or_comm, Nat.mul_comm _ (2 ^ 16), ← Nat.two_pow_add_eq_or_of_lt (by omega)]; omega
    rw [step2]
    have step3 : (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16) ||| b3.toNat * 2 ^ 24 =
        b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 := by
      rw [Nat.or_comm, Nat.mul_comm _ (2 ^ 24), ← Nat.two_pow_add_eq_or_of_lt (by omega)]; omega
    rw [step3]
    have step4 : (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24) ||| b4.toNat * 2 ^ 32 =
        b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 + b4.toNat * 2 ^ 32 := by
      rw [Nat.or_comm, Nat.mul_comm _ (2 ^ 32), ← Nat.two_pow_add_eq_or_of_lt (by omega)]; omega
    rw [step4]
    have step5 : (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 + b4.toNat * 2 ^ 32) |||
        b5.toNat * 2 ^ 40 =
        b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 + b4.toNat * 2 ^ 32 +
        b5.toNat * 2 ^ 40 := by
      rw [Nat.or_comm, Nat.mul_comm _ (2 ^ 40), ← Nat.two_pow_add_eq_or_of_lt (by omega)]; omega
    rw [step5]
    have step6 : (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 + b4.toNat * 2 ^ 32 +
        b5.toNat * 2 ^ 40) ||| b6.toNat * 2 ^ 48 =
        b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 + b4.toNat * 2 ^ 32 +
        b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48 := by
      rw [Nat.or_comm, Nat.mul_comm _ (2 ^ 48), ← Nat.two_pow_add_eq_or_of_lt (by omega)]; omega
    rw [step6]
    rw [Nat.or_comm, Nat.mul_comm _ (2 ^ 56), ← Nat.two_pow_add_eq_or_of_lt (by omega)]; omega
  have h8 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply UInt8.toNat_inj.mp
    rw [toUInt8_toNat, UInt64.toNat_shiftRight, hw_toNat, Nat.shiftRight_eq_div_pow]
    simp only [Nat.mul_zero, Nat.mul_one, show (UInt64.ofNat 0).toNat % 64 = 0 from rfl,
      show (UInt64.ofNat 8).toNat % 64 = 8 from rfl, show (UInt64.ofNat 16).toNat % 64 = 16 from rfl,
      show (UInt64.ofNat 24).toNat % 64 = 24 from rfl, show (UInt64.ofNat 32).toNat % 64 = 32 from rfl,
      show (UInt64.ofNat 40).toNat % 64 = 40 from rfl, show (UInt64.ofNat 48).toNat % 64 = 48 from rfl,
      show (UInt64.ofNat 56).toNat % 64 = 56 from rfl]
    omega

/-- `bytesToWords64` round-trips every byte of an 8-byte-aligned `ByteArray`. -/
theorem bytesToWords64_byte_eq {bs : ByteArray} (hal : bs.size % 8 = 0)
    {wIdx j : Nat} (hw : wIdx < (bytesToWords64 bs).length) (hj : j < 8) :
    (((bytesToWords64 bs)[wIdx]'hw) >>> UInt64.ofNat (8 * j)).toUInt8 =
      bs[8 * wIdx + j]'(by rw [bytesToWords64_length] at hw; omega) := by
  have hwl : wIdx < bs.size / 8 := by rwa [bytesToWords64_length] at hw
  have hget : (bytesToWords64 bs)[wIdx]'hw =
      let base := 8 * wIdx
      let b := fun k => (bs.get! (base + k)).toUInt64
      b 0 ||| (b 1 <<< 8) ||| (b 2 <<< 16) ||| (b 3 <<< 24) |||
      (b 4 <<< 32) ||| (b 5 <<< 40) ||| (b 6 <<< 48) ||| (b 7 <<< 56) := by
    simp [bytesToWords64]
  rw [hget]
  have he := or_shift_byte_extract (bs.get! (8 * wIdx + 0)) (bs.get! (8 * wIdx + 1))
    (bs.get! (8 * wIdx + 2)) (bs.get! (8 * wIdx + 3)) (bs.get! (8 * wIdx + 4))
    (bs.get! (8 * wIdx + 5)) (bs.get! (8 * wIdx + 6)) (bs.get! (8 * wIdx + 7)) j hj
  rw [he]
  have h8 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact byteArray_getBang_eq bs (by omega)

/-- `storeWords` writes every 64-bit word `ws[idx]` at `base + 8 * (k + idx)`. -/
theorem storeWords_wordAt {m : Memory} {base : Word} :
    ∀ (k : Nat) (ws : List Word),
      base.toNat + 8 * (k + ws.length) ≤ 2 ^ 64 →
      (∀ addr : Word, base.toNat + 8 * k ≤ addr.toNat → addr.toNat < base.toNat + 8 * (k + ws.length) →
        m.readable addr = true) →
      ∀ (idx : Nat) (hidx : idx < ws.length),
        WordAt (storeWords m base k ws) (base + UInt64.ofNat (8 * (k + idx))) (ws[idx]'hidx)
  | _, [], _, _, _, hidx => nomatch hidx
  | k, w :: ws, hfit, hread, idx, hidx => by
    have hfit' : base.toNat + 8 * ((k + 1) + ws.length) ≤ 2 ^ 64 := by
      simp only [List.length_cons] at hfit; omega
    have hread' : ∀ addr : Word, base.toNat + 8 * (k + 1) ≤ addr.toNat →
        addr.toNat < base.toNat + 8 * ((k + 1) + ws.length) →
        (m.write .w64 (base + UInt64.ofNat (8 * k)) w).readable addr = true := by
      intro addr ha1 ha2
      simp only [Memory.write]
      exact hread addr (by omega) (by simp only [List.length_cons]; omega)
    cases idx with
    | zero =>
      simp only [storeWords, Nat.add_zero, List.getElem_cons_zero]
      have hw0 : WordAt (m.write .w64 (base + UInt64.ofNat (8 * k)) w) (base + UInt64.ofNat (8 * k)) w := by
        apply wordAt_write64
        intro j hj
        have ha : (base + UInt64.ofNat (8 * k) + UInt64.ofNat j).toNat = base.toNat + 8 * k + j := by
          have h1 := addr_toNat (a := base) (i := 8 * k) (by omega)
          have h2 := addr_toNat (a := base + UInt64.ofNat (8 * k)) (i := j) (by rw [h1]; omega)
          omega
        exact hread _ (by omega) (by simp only [List.length_cons]; omega)
      -- Frame `hw0` across the subsequent stores in `storeWords _ base (k + 1) ws`
      have hframe : ∀ (m0 : Memory) (k1 : Nat) (ws1 : List Word) (a : Word) (u : Word),
          WordAt m0 a u →
          base.toNat + 8 * (k1 + ws1.length) ≤ 2 ^ 64 →
          a.toNat + 8 ≤ base.toNat + 8 * k1 →
          WordAt (storeWords m0 base k1 ws1) a u := by
        intro m0 k1 ws1
        induction ws1 generalizing m0 k1 with
        | nil => intro _ _ hw _ _; exact hw
        | cons w1 ws1 ih1 =>
          intro a u hw hbd hlt
          have hbd1 : base.toNat + 8 * (k1 + 1 + ws1.length) ≤ 2 ^ 64 := by
            simp only [List.length_cons] at hbd; omega
          simp only [storeWords]
          apply ih1 _ (k1 + 1) _ _ _ hbd1 (by omega)
          have hk1 : (base + UInt64.ofNat (8 * k1)).toNat = base.toNat + 8 * k1 :=
            addr_toNat (by omega)
          exact hw.write_disjoint (w := .w64)
            (by rw [hk1]; simp only [Width.bytes]; omega)
            (by omega)
            (.inl (by rw [hk1]; exact hlt))
      have hk0 : (base + UInt64.ofNat (8 * k)).toNat = base.toNat + 8 * k :=
        addr_toNat (by omega)
      exact hframe _ (k + 1) ws _ _ hw0 hfit' (by rw [hk0]; omega)
    | succ idx =>
      simp only [storeWords, List.getElem_cons_succ]
      have hidx' : idx < ws.length := by simpa using hidx
      have h := storeWords_wordAt (k + 1) ws hfit' hread' idx hidx'
      have heq : k + 1 + idx = k + (idx + 1) := by omega
      simpa [heq] using h

/-- **`strLitProc` builds a valid `StaticArrayCell`**: storing `bytesToWords64 (encodeStaticString s)`
at `bump` constructs the exact `StaticArrayCell` for `s`, so `readbackString` returns `some s`! -/
theorem strLitProc_staticCell {m : Memory} {bump : Word} {s : String}
    (hal : bump.toNat % 8 = 0) (hnz : bump ≠ 0)
    (hfit : bump.toNat + (encodeStaticString s).size < 2 ^ 63)
    (hread : ∀ addr : Word, bump.toNat ≤ addr.toNat →
      addr.toNat < bump.toNat + (encodeStaticString s).size → m.readable addr = true) :
    let ws := bytesToWords64 (encodeStaticString s)
    StaticArrayCell (storeWords m bump 0 ws) bump (X86.ELF.alignUp s.toUTF8.size 8)
      (.bytes s.toByteArray.data.toList) := by
  let cell := encodeStaticString s
  let ws := bytesToWords64 cell
  let cap := X86.ELF.alignUp s.toUTF8.size 8
  have hfit_c : bump.toNat + cell.size < 2 ^ 63 := hfit
  have hread_c : ∀ addr : Word, bump.toNat ≤ addr.toNat → addr.toNat < bump.toNat + cell.size →
      m.readable addr = true := hread
  have hcell_sz : cell.size = 24 + cap := encodeStaticByteArray_size s.toUTF8
  have hcell_al : cell.size % 8 = 0 := encodeStaticByteArray_aligned s.toUTF8
  have hws_len : ws.length = cell.size / 8 := bytesToWords64_length cell
  have h8len : 8 * ws.length = cell.size := by omega
  have hpad_ge : s.toUTF8.size ≤ cap := alignUp8_ge s.toUTF8.size
  have hlen : s.toByteArray.data.toList.length = s.toUTF8.size := rfl
  have hwords : ∀ (idx : Nat) (hidx : idx < ws.length),
      WordAt (storeWords m bump 0 ws) (bump + UInt64.ofNat (8 * idx)) (ws[idx]'hidx) := by
    intro idx hidx
    have h := storeWords_wordAt (m := m) (base := bump) 0 ws (by omega)
      (fun a ha1 ha2 => hread_c a (by omega) (by omega)) idx hidx
    simpa using h
  -- Helper: byte at `bump + k` in `storeWords m bump 0 ws` is `cell[k]`
  have hbyte_at : ∀ (k : Nat) (hk : k < cell.size),
      ByteAt (storeWords m bump 0 ws) (bump + UInt64.ofNat k) (cell[k]'hk) := by
    intro k hk
    have hw : k / 8 < ws.length := by omega
    have hj : k % 8 < 8 := Nat.mod_lt k (by decide)
    have hwa := hwords (k / 8) hw
    have haddr : bump + UInt64.ofNat (8 * (k / 8)) + UInt64.ofNat (k % 8) = bump + UInt64.ofNat k := by
      apply UInt64.toNat_inj.mp
      have h1 := addr_toNat (a := bump) (i := 8 * (k / 8)) (by omega)
      have h2 := addr_toNat (a := bump + UInt64.ofNat (8 * (k / 8))) (i := k % 8) (by rw [h1]; omega)
      have h3 := addr_toNat (a := bump) (i := k) (by omega)
      omega
    have hbe := bytesToWords64_byte_eq hcell_al hw hj
    have hdivmod : 8 * (k / 8) + k % 8 = k := Nat.div_add_mod k 8
    refine ⟨?_, ?_⟩
    · have hb := hwa.bytes (k % 8) hj
      rw [haddr] at hb
      rw [hb, hbe]
      simp only [hdivmod]
    · have hr := hwa.readable (k % 8) hj
      rw [haddr] at hr
      exact hr
  -- Helper: first 3 words of `ws` equal `[staticArrayHeader .bytes, size, cap]`
  let hdrs : List Word := [staticHeader 0 tagByteArray, UInt64.ofNat s.toUTF8.size, UInt64.ofNat cap]
  have hhdr_word : ∀ (idx : Nat) (hidx : idx < 3),
      ws[idx]'(by omega) = hdrs[idx]'hidx := by
    intro idx hidx
    -- Two 64-bit words with identical 8 bytes are equal (`Memory.pack64`)
    have hbytes_eq : ∀ (j : Nat) (hj : j < 8),
        ((ws[idx]'(by omega)) >>> UInt64.ofNat (8 * j)).toUInt8 =
        ((hdrs[idx]'hidx) >>> UInt64.ofNat (8 * j)).toUInt8 := by
      intro j hj
      have hidx_ws : idx < (bytesToWords64 cell).length := by change idx < ws.length; omega
      have hbe := bytesToWords64_byte_eq hcell_al hidx_ws hj
      have hlt_c : 8 * idx + j < cell.size := by omega
      change (((bytesToWords64 cell)[idx]'hidx_ws) >>> UInt64.ofNat (8 * j)).toUInt8 = _
      rw [hbe]
      change (encodeStaticByteArray s.toUTF8)[8 * idx + j]'hlt_c = _
      have hba_eq : (encodeStaticByteArray s.toUTF8)[8 * idx + j]'hlt_c =
          (encodeWords hdrs ++ ELF.padTo s.toUTF8 cap)[8 * idx + j]'(by
            change 8 * idx + j < (encodeStaticByteArray s.toUTF8).size; exact hlt_c) := rfl
      rw [hba_eq, ByteArray.getElem_append_left (by
        rw [encodeWords_size]; change 8 * idx + j < 8 * 3; omega)]
      exact encodeWords_getElem hdrs (by change idx < 3; exact hidx) hj
    have hpack : ∀ (u v : Word),
        (∀ j (hj : j < 8), (u >>> UInt64.ofNat (8 * j)).toUInt8 = (v >>> UInt64.ofNat (8 * j)).toUInt8) →
        u = v := by
      intro u v h
      have hu := Memory.pack64 u
      have hv := Memory.pack64 v
      have h0 : u.toUInt8 = v.toUInt8 := by simpa using h 0 (by decide)
      have h1 : (u >>> 8).toUInt8 = (v >>> 8).toUInt8 := h 1 (by decide)
      have h2 : (u >>> 16).toUInt8 = (v >>> 16).toUInt8 := h 2 (by decide)
      have h3 : (u >>> 24).toUInt8 = (v >>> 24).toUInt8 := h 3 (by decide)
      have h4 : (u >>> 32).toUInt8 = (v >>> 32).toUInt8 := h 4 (by decide)
      have h5 : (u >>> 40).toUInt8 = (v >>> 40).toUInt8 := h 5 (by decide)
      have h6 : (u >>> 48).toUInt8 = (v >>> 48).toUInt8 := h 6 (by decide)
      have h7 : (u >>> 56).toUInt8 = (v >>> 56).toUInt8 := h 7 (by decide)
      rw [← hu, ← hv, h0, h1, h2, h3, h4, h5, h6, h7]
    exact hpack _ _ hbytes_eq
  have hhdr_eq : staticHeader 0 tagByteArray = staticArrayHeader .bytes := by decide
  have hcap_eq : cap = X86.ELF.alignUp s.utf8ByteSize 8 := rfl
  refine ⟨hal, hnz, by change s.toByteArray.data.toList.length ≤ cap; rw [hlen]; exact hpad_ge,
    by dsimp only; unfold arrayPayloadOffset; change bump.toNat + (24 + cap) < 2 ^ 63; omega,
    ?_, ?_, ?_, ?_⟩
  · have h0 := hwords 0 (by omega)
    rw [hhdr_word 0 (by decide)] at h0
    change WordAt (storeWords m bump 0 ws) bump (staticArrayHeader .bytes)
    rw [← hhdr_eq]
    simpa [hdrs] using h0
  · have h1 := hwords 1 (by omega)
    rw [hhdr_word 1 (by decide)] at h1
    change WordAt (storeWords m bump 0 ws) (bump + 8) (UInt64.ofNat s.toByteArray.data.toList.length)
    rw [hlen]
    simpa [hdrs] using h1
  · have h2 := hwords 2 (by omega)
    rw [hhdr_word 2 (by decide)] at h2
    change WordAt (storeWords m bump 0 ws) (bump + 16) (UInt64.ofNat (X86.ELF.alignUp s.utf8ByteSize 8))
    rw [← hcap_eq]
    simpa [hdrs] using h2
  · intro j hj
    have hj' : j < s.toUTF8.size := by omega
    have hlt24 : 24 + j < cell.size := by omega
    have hb := hbyte_at (24 + j) hlt24
    have hcell_j : cell[24 + j]'hlt24 = s.toByteArray.data.toList[j]'hj := by
      have hws24 : (encodeWords hdrs).size = 24 := by rw [encodeWords_size]; rfl
      have hba_eq : cell[24 + j]'hlt24 =
          (encodeWords hdrs ++ ELF.padTo s.toUTF8 cap)[24 + j]'(by
            change 24 + j < cell.size; exact hlt24) := rfl
      rw [hba_eq, ByteArray.getElem_append_right (by omega)]
      have hsub : 24 + j - (encodeWords hdrs).size = j := by rw [hws24]; omega
      have hpad_sz : (ELF.padTo s.toUTF8 cap).size = cap := by
        simp only [ELF.padTo, ELF.zeros, ByteArray.size_append]
        have hrep : (ByteArray.mk (Array.replicate (cap - s.toUTF8.size) 0)).size = cap - s.toUTF8.size :=
          Array.size_replicate
        omega
      have hpad_eq : (ELF.padTo s.toUTF8 cap)[24 + j - (encodeWords hdrs).size]'(by omega) =
          (s.toUTF8 ++ ELF.zeros (cap - s.toUTF8.size))[24 + j - (encodeWords hdrs).size]'(by
            change 24 + j - (encodeWords hdrs).size < (ELF.padTo s.toUTF8 cap).size; omega) := rfl
      rw [hpad_eq, ByteArray.getElem_append_left (by omega)]
      change s.toUTF8[24 + j - (encodeWords hdrs).size]'(by omega) = s.toByteArray.data.toList[j]'hj
      simp only [hsub]
      rfl
    rw [hcell_j] at hb
    simpa [arrayPayloadOffset] using hb

/-- **End-to-end `strLitProc` readback theorem**: whenever `strLitProc idx s` succeeds on
an arena (`cell.size < 2^31` and `bump + cell.size ≤ limit`), the returned pointer `bump`
reads back as `some s` via `Rt.Readback.readbackString`. -/
theorem strLitProc_readbackString {m : Memory} {bump : Word} {s : String}
    (hal : bump.toNat % 8 = 0) (hnz : bump ≠ 0)
    (hfit : bump.toNat + (encodeStaticString s).size < 2 ^ 63)
    (hread : ∀ addr : Word, bump.toNat ≤ addr.toNat →
      addr.toNat < bump.toNat + (encodeStaticString s).size → m.readable addr = true) :
    readbackString (storeWords m bump 0 (bytesToWords64 (encodeStaticString s))) bump = some s :=
  readbackString_static (strLitProc_staticCell hal hnz hfit hread)

/-! ## 4. Extended Array Runtime Table Relocation (`relocateFunc`, `extendedArrayRuntimeFuncs`) -/

/-- `relocateFunc` preserves function name, parameters, result count, and calling convention. -/
theorem relocateFunc_meta (base : Lir.FunId) (fn : Lir.Func) :
    (relocateFunc base fn).name = fn.name ∧
    (relocateFunc base fn).params = fn.params ∧
    (relocateFunc base fn).results = fn.results ∧
    (relocateFunc base fn).conv = fn.conv := by
  unfold relocateFunc Lir.Func.splitCriticalEdges
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- `extendedArrayRuntimeFuncs` has exact length `36`. -/
theorem extendedArrayRuntimeFuncs_len (base : Lir.FunId) (nilTag consTag : Nat) :
    (extendedArrayRuntimeFuncs base nilTag consTag).length = 36 :=
  extendedArrayRuntimeFuncs_length base nilTag consTag

end IxCC.Rt.Proof
