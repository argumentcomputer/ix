import IxCC.X86.Driver
import IxCC.Backend.Proof.Ends
import IxCC.Rt.Proof.CxInit
import IxCC.Rt.Proof.Mem

/-!
# The driver's calls satisfy the entry invariant

The export wrapper's entry invariant (`Stacking.Proof.EntryBase`, what
`stacked_ends` and `wrapper_overflow` assume of the caller) holds for every
call the driver model makes (`X86.Driver.core`) under its contract
(`Driver.Ok`): the region pointer in `rdi`, an aligned `rsp` with the
return address at it, the budget word at `ctx − 48`, the call stack and
the context cells mapped in the machine and outside Lir's memory, and Lir's
memory inside the machine's (`Driver.entryBase`). What it needs of the
call's bytes and of Lir's memory is that the budget word is there, that
Lir's memory is the part of the region Lir uses, and that the two agree
on it: true of the first call (`initBytes`, `lirMem`) and, through the
first call's `Final`, of the second.

Also: the region the driver gives `cx_init` passes its checks and is
readable and writable where Lir uses it (`Driver.regionOk`,
`Driver.lirRegion`), and the arguments the wrapper computes from the
registers are the call's (`wrapperArgs_init`, `wrapperArgs_nat`).
-/

namespace IxCC.X86.Driver

open IxCC.Xv.Stacking.Proof (EntryBase InEntryStack budgetOf)
open IxCC.Rt.Proof (WordAt wordAt_write64 addr_toNat read?_ok)

variable {D : Driver} {n : Nat}

theorem Ok.ctx_toNat (hD : D.Ok n) : D.ctx.toNat = D.region.toNat + 64 := by
  have := hD.below
  simp only [Driver.ctx, UInt64.toNat_add]
  have : (64 : Word).toNat = 64 := rfl
  omega

theorem Ok.ctx_sub64 (hD : D.Ok n) : D.ctx - 64 = D.region := by
  apply UInt64.toNat_inj.mp
  rw [Rt.Proof.sub_toNat_of_le (by rw [hD.ctx_toNat]; show 64 ≤ _; omega), hD.ctx_toNat]
  show D.region.toNat + 64 - 64 = _
  omega

theorem Ok.ctx48_toNat (hD : D.Ok n) : (D.ctx - 48).toNat = D.region.toNat + 16 := by
  rw [Rt.Proof.sub_toNat_of_le (by rw [hD.ctx_toNat]; show 48 ≤ _; omega), hD.ctx_toNat]
  show D.region.toNat + 64 - 48 = _
  omega

theorem Ok.region_addr (hD : D.Ok n) {i : Nat} (hi : i < 2 ^ 63) :
    (D.region + UInt64.ofNat i).toNat = D.region.toNat + i := by
  have := hD.below
  exact addr_toNat (by omega)

theorem Ok.ctx48_addr (hD : D.Ok n) {i : Nat} (hi : i < 8) :
    (D.ctx - 48 + UInt64.ofNat i).toNat = D.region.toNat + 16 + i := by
  have := hD.below
  rw [addr_toNat (by rw [hD.ctx48_toNat]; omega), hD.ctx48_toNat]

theorem Ok.sp_addr (hD : D.Ok n) {i : Nat} (hi : i < 8) : (D.sp + UInt64.ofNat i).toNat = D.sp.toNat + i := by
  have := hD.spTop
  exact addr_toNat (by omega)

/-- The region the driver gives `cx_init` passes its checks. -/
theorem regionOk (hD : D.Ok n) : Rt.Proof.RegionOk D.ctx D.size := by
  refine ⟨?_, hD.minSize, ?_⟩
  · rw [hD.ctx_sub64]; exact hD.aligned
  · rw [hD.ctx_sub64]; exact hD.below

/-- Lir's memory is readable and writable where Lir uses the region. -/
theorem lirRegion (hD : D.Ok n) : Rt.Proof.LirRegion D.lirMem D.ctx D.size := by
  intro k h1 h2
  rw [hD.ctx_sub64] at h1 h2
  have := hD.below
  have hk : (UInt64.ofNat k : Word).toNat = k := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  simp only [lirMem, inLir, hk, decide_eq_true_eq, Bool.and_eq_true]
  exact ⟨⟨h1, h2⟩, ⟨h1, h2⟩⟩

/-- A call's memory has the mapping's permissions. -/
theorem mem_readable (bytes : Word → UInt8) : (D.mem bytes).readable = D.mapped := by
  simp [mem, Memory.write]

theorem mem_writable (bytes : Word → UInt8) : (D.mem bytes).writable = D.mapped := by
  simp [mem, Memory.write]

/-- The return address is in the word at `sp`. -/
theorem slot_wordAt (hD : D.Ok n) (bytes : Word → UInt8) : WordAt (D.mem bytes) D.sp D.ret :=
  wordAt_write64 fun i hi => by
    have := hD.spTop
    simp only [mapped, inStack, inRegion, hD.sp_addr hi, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    right
    omega

/-- A call's bytes outside the return slot are the given ones. -/
theorem mem_bytes (hD : D.Ok n) (bytes : Word → UInt8) {a : Word}
    (ha : a.toNat < D.sp.toNat ∨ D.sp.toNat + 8 ≤ a.toNat) : (D.mem bytes).bytes a = bytes a := by
  simp only [mem, Memory.write]
  exact Rt.Proof.writeLittle_bytes_out (by simp [X86.Width.bytes]) (by have := hD.spTop; simpa [X86.Width.bytes] using this) ha

/-- The budget word at `ctx − 48` survives the return address's store. -/
theorem budget_wordAt (hD : D.Ok n) {bytes : Word → UInt8}
    (hbudget : ∀ i < 8, bytes (D.ctx - 48 + UInt64.ofNat i) = (D.budget >>> UInt64.ofNat (8 * i)).toUInt8) :
    WordAt (D.mem bytes) (D.ctx - 48) D.budget := by
  have h₀ : WordAt (⟨bytes, D.mapped, D.mapped⟩ : Memory) (D.ctx - 48) D.budget := by
    refine ⟨hbudget, fun i hi => ?_⟩
    have := hD.below
    have := hD.minSize
    simp only [mapped, inRegion, hD.ctx48_addr hi, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    left
    omega
  have := hD.apart
  have := hD.spTop
  have := hD.below
  exact h₀.write_disjoint (by simpa [X86.Width.bytes] using hD.spTop) (by rw [hD.ctx48_toNat]; omega)
    (by rw [hD.ctx48_toNat]; simp only [X86.Width.bytes]; omega)

theorem budgetOf_core (hD : D.Ok n) {bytes : Word → UInt8} (args : List Word)
    (hbudget : ∀ i < 8, bytes (D.ctx - 48 + UInt64.ofNat i) = (D.budget >>> UInt64.ofNat (8 * i)).toUInt8) :
    budgetOf (D.core args bytes) D.ctx = D.budget := by
  have hw := budget_wordAt hD hbudget
  have hr := hw.read64
  rw [read?_ok (w := .w64) (fun i hi => hw.readable i (by simpa [X86.Width.bytes] using hi))] at hr
  simp only [Except.ok.injEq] at hr
  exact hr

/-- **The driver's calls satisfy the wrapper's entry invariant**, for bytes
holding the budget word and a Lir memory that is the part of the region
Lir uses, agreeing with the bytes there. -/
theorem entryBase (hD : D.Ok n) (args : List Word) {bytes : Word → UInt8} {mem : Memory}
    (hbudget : ∀ i < 8, bytes (D.ctx - 48 + UInt64.ofNat i) = (D.budget >>> UInt64.ofNat (8 * i)).toUInt8)
    (hr : mem.readable = D.inLir) (hw : mem.writable = D.inLir) (hbytes : ∀ a, D.inLir a = true → mem.bytes a = bytes a) :
    EntryBase (D.core args bytes) D.ret mem D.ctx := by
  have hB := budgetOf_core hD args hbudget
  have hsp : (D.core args bytes).readReg .rsp = D.sp := rfl
  have hbelow := hD.below
  have hmin := hD.minSize
  have hap := hD.apart
  have htop := hD.spTop
  have hlow := hD.spLow
  have hstack : ∀ x, InEntryStack (D.core args bytes) D.ctx x ↔ D.inStack x = true := by
    intro x
    simp only [InEntryStack, hsp, hB, inStack, Bool.and_eq_true, decide_eq_true_eq]
  have hlir : ∀ x, D.inLir x = true → D.inStack x = false := by
    intro x hx
    simp only [inLir, inStack, Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      at hx ⊢
    omega
  refine ⟨?_, ?_, ?_, htop, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show D.region = D.ctx - 64
    rw [hD.ctx_sub64]
  · rw [hsp]; exact hD.spAlign
  · rw [hsp]; exact (slot_wordAt hD bytes).read64
  · rw [hB]; exact hD.budgetMin
  · rw [hB, hsp]; show 2 ^ 20 + 64 + _ + 56 ≤ _; exact hlow
  · intro x hx
    have hs := (hstack x).1 hx
    have hl : D.inLir x = false := by
      cases h : D.inLir x
      · rfl
      · rw [hlir x h] at hs; cases hs
    refine ⟨?_, ?_, by rw [hr]; exact hl, by rw [hw]; exact hl⟩
    · show (D.mem bytes).readable x = true
      rw [mem_readable]; simp [mapped, hs]
    · show (D.mem bytes).writable x = true
      rw [mem_writable]; simp [mapped, hs]
  · intro i hi
    rw [hD.ctx_sub64]
    have ha := hD.region_addr (i := i) (by omega)
    have hreg : D.inRegion (D.region + UInt64.ofNat i) = true := by
      simp only [inRegion, ha, Bool.and_eq_true, decide_eq_true_eq]; omega
    have hl : D.inLir (D.region + UInt64.ofNat i) = false := by
      simp only [inLir, ha, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    refine ⟨?_, ?_, by rw [hr]; exact hl, by rw [hw]; exact hl, fun hs => ?_⟩
    · show (D.mem bytes).readable _ = true
      rw [mem_readable]; simp [mapped, hreg]
    · show (D.mem bytes).writable _ = true
      rw [mem_writable]; simp [mapped, hreg]
    · have := (hstack _).1 hs
      simp only [inStack, ha, Bool.and_eq_true, decide_eq_true_eq] at this
      omega
  · intro i hi
    have ha := hD.ctx48_addr hi
    have hreg : D.inRegion (D.ctx - 48 + UInt64.ofNat i) = true := by
      simp only [inRegion, ha, Bool.and_eq_true, decide_eq_true_eq]; omega
    refine ⟨?_, fun hs => ?_⟩
    · show (D.mem bytes).readable _ = true
      rw [mem_readable]; simp [mapped, hreg]
    · have := (hstack _).1 hs
      simp only [inStack, ha, Bool.and_eq_true, decide_eq_true_eq] at this
      omega
  · refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
    · rw [hr] at ha
      show (D.mem bytes).readable a = true
      rw [mem_readable]
      simp only [inLir, Bool.and_eq_true, decide_eq_true_eq] at ha
      simp only [mapped, inRegion, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      left; omega
    · rw [hw] at ha
      show (D.mem bytes).writable a = true
      rw [mem_writable]
      simp only [inLir, Bool.and_eq_true, decide_eq_true_eq] at ha
      simp only [mapped, inRegion, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      left; omega
    · have hl : D.inLir a = true := by
        rcases ha with ha | ha
        · rwa [hr] at ha
        · rwa [hw] at ha
      have hs := hlir a hl
      show (D.mem bytes).bytes a = mem.bytes a
      rw [hbytes a hl]
      apply mem_bytes hD
      simp only [inLir, inStack, Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at hl hs
      omega

/-! ## The first call -/

theorem initBytes_budget (D : Driver) :
    ∀ i < 8, D.initBytes (D.ctx - 48 + UInt64.ofNat i) = (D.budget >>> UInt64.ofNat (8 * i)).toUInt8 :=
  (wordAt_write64 (m := ⟨D.init, fun _ => true, fun _ => true⟩) (b := D.ctx - 48) (v := D.budget)
    fun _ _ => rfl).bytes

/-- The first call (`cx_init`'s) satisfies the entry invariant. -/
theorem entryBase_init (hD : D.Ok n) (args : List Word) :
    EntryBase (D.core args D.initBytes) D.ret D.lirMem D.ctx :=
  entryBase hD args (initBytes_budget D) rfl rfl fun _ _ => rfl

end IxCC.X86.Driver

namespace IxCC.X86.Driver

open IxCC.Xv.Stacking (ArgRep sysvArgs)
open IxCC.Xv.Stacking.Proof (wrapperArgs ArgsFit tagged)

variable {D : Driver}

/-! ## The arguments the wrapper computes -/

/-- `cx_init`'s wrapper passes its two word arguments as they are. -/
theorem wrapperArgs_words (a b : Word) (bytes : Word → UInt8) :
    wrapperArgs [.word, .word] (D.core [a, b] bytes) = [a, b] := rfl

/-- Word arguments are never out of range. -/
theorem argsFit_words (core : Core) : ArgsFit [.word, .word] core := by
  intro r rep h hn
  simp only [sysvArgs, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
    List.not_mem_nil, or_false] at h
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hn

/-- A root's wrapper tags its `Nat` arguments, read from `rsi`…`r9`. -/
theorem wrapperArgs_nat {ns : List Nat} (hlen : ns.length ≤ 5) (bytes : Word → UInt8) :
    wrapperArgs (List.replicate ns.length .nat) (D.core (ns.map UInt64.ofNat) bytes) =
      ns.map fun n => UInt64.ofNat n + UInt64.ofNat n + 1 := by
  match ns, hlen with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | [_, _, _, _], _ => rfl
  | [_, _, _, _, _], _ => rfl

/-- A root's `Nat` arguments fit the wrapper's check exactly when each is
below 2^63. -/
theorem argsFit_nat {ns : List Nat} (hlen : ns.length ≤ 5) (h64 : ∀ n ∈ ns, n < 2 ^ 64) (bytes : Word → UInt8) :
    ArgsFit (List.replicate ns.length .nat) (D.core (ns.map UInt64.ofNat) bytes) ↔ ∀ n ∈ ns, n < 2 ^ 63 := by
  have hv : ∀ n ∈ ns, (UInt64.ofNat n : Word).toNat = n := fun n hn => by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (h64 n hn)]
  unfold ArgsFit
  match ns, hlen with
  | [], _ => simp [sysvArgs]
  | [a], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hv ⊢
    simp [sysvArgs, Driver.core, Driver.regs, Core.readReg, hv]
  | [a, b], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hv ⊢
    simp [sysvArgs, Driver.core, Driver.regs, Core.readReg, hv, or_imp, forall_and]
  | [a, b, c], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hv ⊢
    simp [sysvArgs, Driver.core, Driver.regs, Core.readReg, hv, or_imp, forall_and]
  | [a, b, c, d], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hv ⊢
    simp [sysvArgs, Driver.core, Driver.regs, Core.readReg, hv, or_imp, forall_and]
  | [a, b, c, d, e], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hv ⊢
    simp [sysvArgs, Driver.core, Driver.regs, Core.readReg, hv, or_imp, forall_and]

end IxCC.X86.Driver

namespace IxCC.X86.Driver

/-- **The contract can be kept**: for any text of fewer than 2^64 bytes, a
driver with a 64 MiB region at 2^32, an 8 MiB stack budget, `rsp = 2^40 + 8`
and the caller's return address at the last address (the text at 0) keeps
it. So the entry invariant the backend's theorems assume
(`Driver.entryBase`) is satisfiable. -/
theorem exists_ok {n : Nat} (hn : n < 2 ^ 64) : ∃ D : Driver, D.Ok n := by
  refine ⟨{ base := 0, region := 2 ^ 32, size := 2 ^ 26, budget := 2 ^ 23, sp := 2 ^ 40 + 8,
            ret := UInt64.ofNat (2 ^ 64 - 1),
            init := fun _ => 0, flags := {}, other := fun _ => 0 }, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, .inr (by decide), ?_⟩
  show n ≤ (UInt64.ofNat (2 ^ 64 - 1) - 0 : Word).toNat
  have : (UInt64.ofNat (2 ^ 64 - 1) - 0 : Word).toNat = 2 ^ 64 - 1 := by decide
  omega

end IxCC.X86.Driver

namespace IxCC.Backend

open IxCC.Xv.Stacking.Proof (EntryBase)

/-- **The whole region and the wrapper's entry invariant exclude each other**:
`Rt.Proof.Region` makes the region's first byte (`entrySp`, at `ctx − 64`)
readable in Lir's memory, which `EntryBase.ctxCells` forbids. So
`Recheck.compile_sound`'s premises `hreg` and a backend refinement built on
the stacking theorem cannot hold together for one memory; the front half is
restated on the part of the region Lir uses (`Rt.Proof.LirRegion`). -/
theorem region_not_entryBase {mem : X86.Memory} {ctx size : X86.Word} (hreg : Rt.Proof.Region mem ctx size)
    (hsize : 0 < size.toNat) {core₀ : X86.Core} {retAddr : X86.Word} (base : EntryBase core₀ retAddr mem ctx) : False := by
  have h1 := (hreg (ctx - 64).toNat (Nat.le_refl _) (by omega)).1
  have h2 := (base.ctxCells 0 (by decide)).2.2.1
  rw [UInt64.ofNat_toNat] at h1
  have h0 : ctx - 64 + UInt64.ofNat 0 = ctx - 64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add]
    simp
  rw [h0, h1] at h2
  cases h2

end IxCC.Backend
