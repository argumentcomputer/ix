import IxCC.Cfg.Rc.Proof.Physical.AllocWrapper
import IxCC.Cfg.Rc.Proof.Physical.AllocationFreeReady
import IxCC.Cfg.Rc.Proof.Physical.AllocationBumpReady
import IxCC.Cfg.Rc.Proof.Physical.AllocationFailure
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ReadyTokens
import IxCC.Cfg.Rc.Proof.Physical.Bridge.IncrementWrapper
import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorTables
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords
import IxCC.Cfg.Rc.Proof.Physical.ConsumedMarkers
import IxCC.Cfg.Rc.Proof.Native.CtorBinding
import IxCC.Rt.Rc.Gen.Proof.InPlace
import IxCC.Rt.Rc.Gen.Proof.UniqueTest
import IxCC.Rt.Rc.Gen.Proof.ReadyOperations
import IxCC.Own.Plain.Proof.Owned.Reset

/-! # Concrete physical wrapper proofs for `reset` and `reuse` (Track A4)

Executes `mkReuseUWrapper`, `mkReuseWrapper` (in-place and fallback allocation),
`mkResetUWrapper`, and `mkResetWrapper` (unique, shared, and immediate paths) directly
in the ambient native LIR program, resting on `Rt.Rc.Gen.inPlace_ready`,
`Rt.Rc.Gen.unique_cell` / `unique_immediate`, `Gen.AllocatorReady.release_caller_ready`,
`Gen.AllocatorReady.increment_ready`, and `allocation_free_ready` / `allocation_bump_ready`. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt IxCC.Rt.Rc.Procs IxCC.Rt.Proof

/-! ## Pure heap, balance, bitmask, and constructor-metadata helpers -/

/-- Two balanced root lists against the same heap and external counts have identical reference counts. -/
theorem sameRefs_of_balance {H : Heap} {external : Nat → Nat} {a b : List RVal}
    (ha : Balance H external a) (hb : Balance H external b) :
    Own.Plain.SameRefs a b := by
  intro l
  have h1 := ha l
  have h2 := hb l
  unfold total at h1 h2
  omega

/-- `dropAll` distributes over list append (`[v] ++ ys` matches sequential single-value `Gen.dec` calls). -/
private theorem releaseOne_append (H : Heap) (v : RVal) (xs ys : List RVal) :
    releaseOne H v (xs ++ ys) = (releaseOne H v xs).map (fun p => (p.1, p.2 ++ ys)) := by
  cases v with
  | lit _ | ctor0 _ | erased => rfl
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [releaseOne, hc]
    | some c =>
      cases c with
      | dead => simp [releaseOne, hc]
      | live rc mode b =>
        cases mode with
        | static => simp [releaseOne, hc]
        | dyn =>
          cases rc with
          | zero => simp [releaseOne, hc]
          | succ rc' =>
            cases rc' with
            | zero => simp [releaseOne, hc, List.append_assoc]
            | succ _ => simp [releaseOne, hc]

theorem dropAll_append (H : Heap) (xs ys : List RVal) :
    dropAll H (xs ++ ys) = (dropAll H xs).bind (fun H' => dropAll H' ys) := by
  match xs with
  | [] => simp [dropAll]
  | v :: xs' =>
    have hrel := releaseOne_append H v xs' ys
    cases hr : releaseOne H v xs' with
    | none =>
      rw [List.cons_append, dropAll, hrel, hr]
      conv => rhs; rw [dropAll, hr]
      rfl
    | some p =>
      obtain ⟨H₁, xs₁⟩ := p
      rw [List.cons_append, dropAll, hrel, hr]
      simp only [Option.map_some]
      have ih := dropAll_append H₁ xs₁ ys
      rw [ih]
      conv => rhs; rw [dropAll, hr]
termination_by (mass H, xs.length)
decreasing_by
  have hd := Prod.lex_def.mp (releaseOne_decreases hr)
  apply Prod.lex_def.mpr
  rcases hd with h | ⟨he, h⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨he, by omega⟩

theorem dropAll_cons_eq (H : Heap) (v : RVal) (ys : List RVal) :
    dropAll H (v :: ys) = (dropAll H [v]).bind (fun H' => dropAll H' ys) :=
  dropAll_append H [v] ys

theorem heapOk_reuseCell {H : Heap} {l : Nat} {b' : Body}
    (hok : HeapOk H) (hl : l < H.size) (hbody : BodyOk H.size b') :
    HeapOk (reusedHeap H l b') := by
  unfold reusedHeap
  apply heapOk_alloc (heapOk_free hok hl)
  simpa [setCell_size] using hbody

theorem heapCtorOk_reuseCell {tables : Lower.Tables} {H : Heap} {l : Nat} {b' : Body}
    (hcok : HeapCtorOk tables H) (hl : l < H.size) (hbody : BodyCtorOk tables b') :
    HeapCtorOk tables (reusedHeap H l b') :=
  (hcok.free hl).alloc hbody

theorem heapOk_inc {H H' : Heap} {u : RVal} (hok : HeapOk H) (hi : Own.Rc.inc H u 1 = some H') :
    HeapOk H' := by
  cases u with
  | lit _ | ctor0 _ | erased =>
    simp only [Own.Rc.inc, changeCount, Option.some.injEq] at hi
    subst hi; exact hok
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [Own.Rc.inc, changeCount, hc] at hi
    | some c =>
      cases c with
      | dead => simp [Own.Rc.inc, changeCount, hc] at hi
      | live rc mode b =>
        cases mode with
        | static =>
          simp only [Own.Rc.inc, changeCount, hc, Option.some.injEq] at hi
          subst hi; exact hok
        | dyn =>
          by_cases hz : rc = 0
          · simp [Own.Rc.inc, changeCount, hc, hz] at hi
          · rw [inc_dyn hc (by omega) 1] at hi
            cases hi
            exact heapOk_set_count hok hc (by omega)

theorem heapOk_incList : ∀ {H H' : Heap} {vs : List RVal},
    HeapOk H → Own.Plain.incList H vs = some H' → HeapOk H'
  | H, H', [], hok, hi => by
    simp only [Own.Plain.incList, Option.some.injEq] at hi; subst hi; exact hok
  | H, H', u :: us, hok, hi => by
    simp only [Own.Plain.incList] at hi
    cases h1 : Own.Rc.inc H u 1 with
    | none => simp [h1] at hi
    | some H₁ =>
      simp only [h1] at hi
      exact heapOk_incList (heapOk_inc hok h1) hi

theorem heapCtorOk_inc {tables : Lower.Tables} {H H' : Heap} {u : RVal}
    (hcok : HeapCtorOk tables H) (hi : Own.Rc.inc H u 1 = some H') :
    HeapCtorOk tables H' := by
  cases u with
  | lit _ | ctor0 _ | erased =>
    simp only [Own.Rc.inc, changeCount, Option.some.injEq] at hi
    subst hi; exact hcok
  | loc l =>
    exact hcok.changeCount (by simpa [Own.Rc.inc] using hi)

theorem heapCtorOk_incList {tables : Lower.Tables} : ∀ {H H' : Heap} {vs : List RVal},
    HeapCtorOk tables H → Own.Plain.incList H vs = some H' → HeapCtorOk tables H'
  | H, H', [], hcok, hi => by
    simp only [Own.Plain.incList, Option.some.injEq] at hi; subst hi; exact hcok
  | H, H', u :: us, hcok, hi => by
    simp only [Own.Plain.incList] at hi
    cases h1 : Own.Rc.inc H u 1 with
    | none => simp [h1] at hi
    | some H₁ =>
      simp only [h1] at hi
      exact heapCtorOk_incList (heapCtorOk_inc hcok h1) hi

theorem inc_size {H H' : Heap} {u : RVal} (hi : Own.Rc.inc H u 1 = some H') :
    H'.size = H.size := by
  cases u with
  | lit _ | ctor0 _ | erased =>
    simp only [Own.Rc.inc, changeCount, Option.some.injEq] at hi; subst hi; rfl
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [Own.Rc.inc, changeCount, hc] at hi
    | some c =>
      cases c with
      | dead => simp [Own.Rc.inc, changeCount, hc] at hi
      | live rc mode b =>
        cases mode with
        | static =>
          simp only [Own.Rc.inc, changeCount, hc, Option.some.injEq] at hi; subst hi; rfl
        | dyn =>
          by_cases hz : rc = 0
          · simp [Own.Rc.inc, changeCount, hc, hz] at hi
          · rw [inc_dyn hc (by omega) 1] at hi; cases hi; exact setCell_size ..

theorem incList_size : ∀ {H H' : Heap} {vs : List RVal},
    Own.Plain.incList H vs = some H' → H'.size = H.size
  | _, _, [], hi => by simp only [Own.Plain.incList, Option.some.injEq] at hi; subst hi; rfl
  | H, H', u :: us, hi => by
    simp only [Own.Plain.incList] at hi
    cases h1 : Own.Rc.inc H u 1 with
    | none => simp [h1] at hi
    | some H₁ =>
      simp only [h1] at hi
      exact (incList_size hi).trans (inc_size h1)

theorem inc_preserves_cell_body {H H' : Heap} {u : RVal} {l rc : Nat} {b : Body}
    (hc : H.cell? l = some (.live rc .dyn b)) (hi : Own.Rc.inc H u 1 = some H') :
    ∃ rc', H'.cell? l = some (.live rc' .dyn b) := by
  cases u with
  | lit _ | ctor0 _ | erased =>
    simp only [Own.Rc.inc, changeCount, Option.some.injEq] at hi; subst hi; exact ⟨rc, hc⟩
  | loc k =>
    cases hck : H.cell? k with
    | none => simp [Own.Rc.inc, changeCount, hck] at hi
    | some c =>
      cases c with
      | dead => simp [Own.Rc.inc, changeCount, hck] at hi
      | live rck mk bk =>
        cases mk with
        | static =>
          simp only [Own.Rc.inc, changeCount, hck, Option.some.injEq] at hi
          subst hi; exact ⟨rc, hc⟩
        | dyn =>
          by_cases hz : rck = 0
          · simp [Own.Rc.inc, changeCount, hck, hz] at hi
          · rw [inc_dyn hck (by omega) 1] at hi
            cases hi
            have hk : k < H.size := Own.Proof.cell?_some hck
            rw [setCell_cell H k _ hk l]
            by_cases he : k = l
            · subst he; rw [hc] at hck
              obtain ⟨rfl, -, rfl⟩ := Cell.live.inj (Option.some.inj hck)
              simp only [↓reduceIte]; exact ⟨rc + 1, rfl⟩
            · rw [ite_eq_right he]; exact ⟨rc, hc⟩

theorem validReuseCtor_full {c : Fir.CtorInfo} {cls : Nat}
    (h : Own.Plain.Ctx.validReuseCtor c = some cls) :
    0 < c.arity ∧ c.arity ≤ 61 ∧ c.arity ≤ Rt.maxFields ∧ c.tag ≤ Rt.maxTag ∧
    c.nscalar = 0 ∧ c.nobj = c.arity ∧ c.fieldKinds = List.replicate c.arity .shared ∧
    Gen.layoutOf c = CellLayout.ofFields c.arity c.tag ∧
    (Gen.layoutOf c).ok = true ∧ (CellLayout.ofFields c.arity c.tag).cls? = some cls ∧
    Gen.classOf c = cls ∧ cls = Gen.fieldsClass c.arity := by
  unfold Own.Plain.Ctx.validReuseCtor at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨⟨⟨⟨hpos, h61⟩, hnsc⟩, hfklen⟩, hfkall⟩ := hcond
    have hnobj : c.nobj = c.arity := by simp [Fir.CtorInfo.arity, hnsc]
    have hfk : c.fieldKinds = List.replicate c.arity .shared := by
      apply List.ext_getElem
      · rw [List.length_replicate, hfklen, hnobj]
      · intro i hi1 hi2
        rw [List.getElem_replicate]
        exact beq_iff_eq.mp (List.all_eq_true.mp hfkall c.fieldKinds[i] (List.getElem_mem hi1))
    have hlayEq : Gen.layoutOf c = CellLayout.ofFields c.arity c.tag := by
      simp [Gen.layoutOf, CellLayout.ofFields, hnobj, hnsc]
    cases hok : (CellLayout.ofFields c.arity c.tag).ok with
    | false => simp [hok] at h
    | true =>
      simp only [hok, ↓reduceIte] at h
      have hmaxF : c.arity ≤ Rt.maxFields := by unfold Rt.maxFields; omega
      have htag : c.tag ≤ Rt.maxTag := by
        unfold CellLayout.ok CellLayout.ofFields at hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        exact hok.1.2
      have hclsEq : Gen.classOf c = cls := by
        simp [Gen.classOf, hlayEq, h]
      have hfcls : cls = Gen.fieldsClass c.arity := by
        have h1 := (Gen.ofFields_layout hpos hmaxF htag).2
        rw [h] at h1
        exact Option.some.inj h1
      exact ⟨hpos, h61, hmaxF, htag, hnsc, hnobj, hfk, hlayEq, by rw [hlayEq]; exact hok,
        h, hclsEq, hfcls⟩
  · cases h

theorem fieldsMask_lt : ∀ (fs : List (Option Fir.Var)),
    Own.Plain.fieldsMask fs < 2 ^ fs.length
  | [] => by simp [Own.Plain.fieldsMask]
  | none :: rest => by
    have ih := fieldsMask_lt rest
    simp only [Own.Plain.fieldsMask, List.length_cons, Nat.pow_succ]
    omega
  | some _ :: rest => by
    have ih := fieldsMask_lt rest
    simp only [Own.Plain.fieldsMask, List.length_cons, Nat.pow_succ]
    omega

theorem natWord_fieldsMask {fs : List (Option Fir.Var)} (hlen : fs.length ≤ 61) :
    Rt.natWord (Own.Plain.fieldsMask fs) = some (UInt64.ofNat (2 * Own.Plain.fieldsMask fs + 1)) := by
  have hlt : Own.Plain.fieldsMask fs < 2 ^ 61 :=
    Nat.lt_of_lt_of_le (fieldsMask_lt fs) (Nat.pow_le_pow_right (by omega) hlen)
  have hlim : Own.Plain.fieldsMask fs < Rt.natLimit := by
    unfold Rt.natLimit; omega
  simp [Rt.natWord, hlim]

theorem testBit_tagged_mask {mask j : Nat} (hm : mask < 2 ^ 61) (hj : j < 61) :
    Lir.Cond.holds .tnz .w64 (UInt64.ofNat (2 * mask + 1)) (UInt64.ofNat (2 ^ (j + 1))) =
      Nat.testBit mask j := by
  have h1 : 2 * mask + 1 < 2 ^ 64 := by omega
  have h2 : 2 ^ (j + 1) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by omega : j + 1 ≤ 61)) (by decide)
  have hand : (UInt64.ofNat (2 * mask + 1) &&& UInt64.ofNat (2 ^ (j + 1))).toNat =
      (2 * mask + 1) &&& (2 ^ (j + 1)) := by
    rw [UInt64.toNat_and, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  have hne : ((UInt64.ofNat (2 * mask + 1) &&& UInt64.ofNat (2 ^ (j + 1))) != 0) =
      decide (((2 * mask + 1) &&& (2 ^ (j + 1))) ≠ 0) := by
    cases hb : (UInt64.ofNat (2 * mask + 1) &&& UInt64.ofNat (2 ^ (j + 1)) == 0)
    · have hnz : (UInt64.ofNat (2 * mask + 1) &&& UInt64.ofNat (2 ^ (j + 1))).toNat ≠ 0 := by
        intro h0
        have heq : UInt64.ofNat (2 * mask + 1) &&& UInt64.ofNat (2 ^ (j + 1)) = 0 :=
          UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by simpa using h0))
        rw [heq] at hb; simp at hb
      rw [hand] at hnz
      simp only [bne, hb, Bool.not_false, ne_eq, hnz, not_false_eq_true, decide_true]
    · have hz : (UInt64.ofNat (2 * mask + 1) &&& UInt64.ofNat (2 ^ (j + 1))) = 0 :=
        beq_iff_eq.mp hb
      have h0 : (2 * mask + 1) &&& (2 ^ (j + 1)) = 0 := by
        rw [← hand, hz]; rfl
      simp only [bne, hb, Bool.not_true, h0, ne_eq, not_true_eq_false, decide_false]
  have hbit : decide (((2 * mask + 1) &&& (2 ^ (j + 1))) ≠ 0) = Nat.testBit mask j := by
    have htb : Nat.testBit (2 * mask + 1) (j + 1) = Nat.testBit mask j := by
      rw [Nat.testBit_succ, show (2 * mask + 1) / 2 = mask by omega]
    rw [← htb, Nat.testBit_eq_decide_div_mod_eq]
    have hpow : (2 * mask + 1) &&& (2 ^ (j + 1)) =
        if ((2 * mask + 1) / 2 ^ (j + 1)) % 2 = 1 then 2 ^ (j + 1) else 0 := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hk : j + 1 = k
      · subst hk
        simp only [decide_true, Bool.and_true, Nat.testBit_eq_decide_div_mod_eq]
        split
        · rename_i hm1
          simp only [hm1, decide_true, Nat.div_self (Nat.two_pow_pos _), Nat.one_mod]
        · rename_i hm0; simp [hm0]
      · simp only [hk, decide_false, Bool.and_false]
        split
        · simp only [Nat.testBit_two_pow, hk, decide_false]
        · simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rw [hpow]
    split
    · rename_i hm1
      simp [hm1]
    · rename_i hm0; simp [hm0]
  have hmask64 : ∀ w : UInt64, w &&& X86.Width.w64.mask = w := fun w => by
    apply UInt64.eq_of_toBitVec_eq
    show w.toBitVec &&& BitVec.allOnes 64 = w.toBitVec
    exact BitVec.and_allOnes
  simp only [Lir.Cond.holds, X86.Width.truncate, hmask64, hne, hbit]

/-! ## `consume` inversion and runtime-function lookups for `reset` and `reuse` -/

theorem layout_ctor_at_index {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true)
    {ctor : Fir.CtorInfo} (hof : Fir.CtorInfo.ofKey F.ctors ctor.key = some ctor)
    (hpos : 0 < ctor.arity) :
    ∃ row, (layoutOf P).ctors[heapCtorIndex F.ctors ctor.key]? = some row ∧
      row.tag = ctor.tag ∧ row.arity = ctor.arity := by
  have hctors : P.base.ctors = F.ctors :=
    generate_ctors (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have hofP : Fir.CtorInfo.ofKey P.base.ctors ctor.key = some ctor := by rwa [hctors]
  obtain ⟨expected, hfind, _, harity, _⟩ := table_row hofP
  have hmem : expected ∈ (layoutOf P).ctors :=
    List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hfind, decide_eq_true (by omega)⟩
  have hkey : (expected.key == ctor.key) = true :=
    List.find?_some (p := fun r : Lam.CtorInfo => r.key == ctor.key) hfind
  have hisSome : ((layoutOf P).ctors.zipIdx.find? fun p => p.1.key == ctor.key).isSome := by
    rw [List.find?_isSome]
    obtain ⟨idx, hlt, hget⟩ := List.mem_iff_getElem.mp hmem
    refine ⟨(expected, idx), ?_, hkey⟩
    rw [List.mem_iff_getElem]
    exact ⟨idx, by simp [hlt], by simp [hget]⟩
  cases hf : (layoutOf P).ctors.zipIdx.find? (fun p => p.1.key == ctor.key) with
  | none => simp [hf] at hisSome
  | some p =>
    obtain ⟨r, idx⟩ := p
    have hci : ctorIndex (layoutOf P) ctor.key = some idx := by
      simp [ctorIndex, hf]
    have hhi : heapCtorIndex F.ctors ctor.key = idx := by
      unfold heapCtorIndex
      have hlay : (layoutOf P).ctors = F.ctors.filter (fun c => decide (c.arity > 0)) := by
        simp [layoutOf, hctors]
      rw [← hlay, hf]
      rfl
    obtain ⟨row, hrow, htag', harity', _⟩ := ctorIndex_binding hofP hpos hci
    exact ⟨row, by rwa [hhi], htag', harity'⟩

theorem consume_reset_of {P : Program} {slotReg x ci mask : Nat} {uniq : Bool}
    {row : Lam.CtorInfo} (hrow : (layoutOf P).ctors[ci]? = some row)
    (htag : row.tag ≤ Rt.maxTag) (harity : row.arity ≤ Rt.maxFields) :
    consume P (layoutOf P)
      (.bind slotReg (.fir (.call (P.base.size + 2)
        [.var x, .lit (.nat ci), .lit (.nat mask), .lit (.nat (if uniq then 1 else 0))]))) =
    .ok (.bind slotReg (.fir (.call
      (if uniq then (layoutOf P).resetUWrapper ci else (layoutOf P).resetWrapper ci)
      [.var x, .lit (.nat mask)]))) := by
  have hnr : reserved P.base.size
      (.bind slotReg (.fir (.call (P.base.size + 2)
        [.var x, .lit (.nat ci), .lit (.nat mask), .lit (.nat (if uniq then 1 else 0))]))) = false := by
    simp [reserved]
  have hir : isReuseOp P.base.size
      (.bind slotReg (.fir (.call (P.base.size + 2)
        [.var x, .lit (.nat ci), .lit (.nat mask), .lit (.nat (if uniq then 1 else 0))]))) = true := by
    simp [isReuseOp]
  have hdr : decodeReset P.base.size
      (.bind slotReg (.fir (.call (P.base.size + 2)
        [.var x, .lit (.nat ci), .lit (.nat mask), .lit (.nat (if uniq then 1 else 0))]))) =
      some (slotReg, x, ci, mask, uniq) := by
    cases uniq <;> simp [decodeReset]
  have hdu : decodeReuse P.base.size
      (.bind slotReg (.fir (.call (P.base.size + 2)
        [.var x, .lit (.nat ci), .lit (.nat mask), .lit (.nat (if uniq then 1 else 0))]))) = none := by
    simp [decodeReuse]
  simp only [consume, hnr, hir, hdr, hdu, hrow, Bool.false_eq_true, ↓reduceIte,
    show ¬ (row.tag > Rt.maxTag) by omega, show ¬ (row.arity > Rt.maxFields) by omega,
    pure, Except.pure]

theorem consume_reuse_of {P : Program} {dst slotReg ci : Nat} {uniq : Bool} {args : List Fir.Arg}
    {result : Cfg.Instr}
    (accepted : consume P (layoutOf P)
      (.bind dst (.fir (.call (P.base.size + 3)
        (.var slotReg :: .lit (.nat ci) :: .lit (.nat (if uniq then 1 else 0)) :: args)))) =
      .ok result)
    {row : Lam.CtorInfo} (hrow : (layoutOf P).ctors[ci]? = some row) :
    result = .bind dst (.fir (.call
      (if uniq then (layoutOf P).reuseUWrapper ci else (layoutOf P).reuseWrapper ci)
      (.var slotReg :: args))) := by
  have hnr : reserved P.base.size
      (.bind dst (.fir (.call (P.base.size + 3)
        (.var slotReg :: .lit (.nat ci) :: .lit (.nat (if uniq then 1 else 0)) :: args)))) = false := by
    simp [reserved]
  have hir : isReuseOp P.base.size
      (.bind dst (.fir (.call (P.base.size + 3)
        (.var slotReg :: .lit (.nat ci) :: .lit (.nat (if uniq then 1 else 0)) :: args)))) = true := by
    simp [isReuseOp]
  have hdr : decodeReset P.base.size
      (.bind dst (.fir (.call (P.base.size + 3)
        (.var slotReg :: .lit (.nat ci) :: .lit (.nat (if uniq then 1 else 0)) :: args)))) = none := by
    simp [decodeReset]
  have hdu : decodeReuse P.base.size
      (.bind dst (.fir (.call (P.base.size + 3)
        (.var slotReg :: .lit (.nat ci) :: .lit (.nat (if uniq then 1 else 0)) :: args)))) =
      some (dst, slotReg, ci, uniq, args) := by
    cases uniq <;> simp [decodeReuse]
  simp only [consume, hnr, hir, hdr, hdu, hrow, Bool.false_eq_true, ↓reduceIte] at accepted
  split at accepted
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  · split at accepted
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
    · split at accepted
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
      · split at accepted
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
        · simp only [pure, Except.pure, Except.ok.injEq] at accepted
          exact accepted.symm

theorem source_stage_isUnique_runtime (P : Program) (functions : Nat → Lir.Func) (main : Nat) :
    (Public.Spec.sourceStage P functions main).funcs[(layoutOf P).isUniqueProc]? =
      some Gen.isUnique := by
  have length : ((List.range P.base.size).map functions).length = (layoutOf P).sourceCount := by
    simp [layoutOf]
  exact raw_public_runtime (raw_isUnique_proc length main)

theorem source_stage_reset_runtime (P : Program) (functions : Nat → Lir.Func) (main ci : Nat)
    {c : Lam.CtorInfo} (hc : (layoutOf P).ctors[ci]? = some c) {cls : Nat}
    (hcls : (CellLayout.ofFields c.arity c.tag).cls? = some cls) :
    (Public.Spec.sourceStage P functions main).funcs[(layoutOf P).resetWrapper ci]? =
      some (mkResetWrapper (layoutOf P).isUniqueProc (layoutOf P).incProc (layoutOf P).decProc
        (CellLayout.ofFields c.arity c.tag) cls) ∧
    (Public.Spec.sourceStage P functions main).funcs[(layoutOf P).resetUWrapper ci]? =
      some (mkResetUWrapper (layoutOf P).decProc (CellLayout.ofFields c.arity c.tag) cls) := by
  have length : ((List.range P.base.size).map functions).length = (layoutOf P).sourceCount := by
    simp [layoutOf]
  exact ⟨raw_public_runtime (raw_reset_wrapper length main ci hc hcls),
    raw_public_runtime (raw_resetU_wrapper length main ci hc hcls)⟩

theorem source_stage_reuse_runtime (P : Program) (functions : Nat → Lir.Func) (main ci : Nat)
    {c : Lam.CtorInfo} (hc : (layoutOf P).ctors[ci]? = some c) {cls : Nat}
    (hcls : (CellLayout.ofFields c.arity c.tag).cls? = some cls) :
    (Public.Spec.sourceStage P functions main).funcs[(layoutOf P).reuseWrapper ci]? =
      some (mkReuseWrapper ((layoutOf P).allocProc ci) (CellLayout.ofFields c.arity c.tag) cls) ∧
    (Public.Spec.sourceStage P functions main).funcs[(layoutOf P).reuseUWrapper ci]? =
      some (mkReuseUWrapper (CellLayout.ofFields c.arity c.tag) cls) ∧
    (Public.Spec.sourceStage P functions main).funcs[(layoutOf P).allocProc ci]? =
      some (Gen.alloc (CellLayout.ofFields c.arity c.tag)) := by
  have length : ((List.range P.base.size).map functions).length = (layoutOf P).sourceCount := by
    simp [layoutOf]
  exact ⟨raw_public_runtime (raw_reuse_wrapper length main ci hc hcls),
    raw_public_runtime (raw_reuseU_wrapper length main ci hc hcls),
    raw_public_runtime (raw_alloc_proc length main ci hc)⟩

/-! ## Straight-line load / store execution matching `Gen.writeCell` & `publishFields` -/

theorem writeFields_eq_publishFields_aux (addresses : AddressMap) (a : Lir.Word) (c : Fir.CtorInfo)
    (words : Nat → Lir.Word) :
    ∀ (vs : List RVal) (off : Nat) (mem : X86.Memory),
      (∀ j u, vs[j]? = some u → Gen.fieldWord addresses c (off + j) u = some (words (off + j))) →
      Gen.writeFields mem addresses a c (vs.zipIdx off) =
        publishFields mem a words ((List.range vs.length).map (off + ·))
  | [], _, _, _ => rfl
  | u :: us, off, mem, hw => by
    have h0 : Gen.fieldWord addresses c off u = some (words off) := by
      simpa using hw 0 u rfl
    have haddr : a + UInt64.ofNat (8 + 8 * off) = fieldAddress a off := by
      simp [fieldAddress, show 8 + 8 * off = 8 * (off + 1) by omega]
    rw [List.zipIdx_cons, Gen.writeFields_cons, h0, Option.getD_some, haddr]
    have hrange : (List.range (u :: us).length).map (off + ·) =
        off :: (List.range us.length).map (off + 1 + ·) := by
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _; dsimp only [Function.comp_apply]; omega
    rw [hrange]
    change Gen.writeFields _ addresses a c (us.zipIdx (off + 1)) =
      publishFields (mem.write .w64 (fieldAddress a off) (words off)) a words
        ((List.range us.length).map (off + 1 + ·))
    apply writeFields_eq_publishFields_aux addresses a c words us (off + 1) _
    intro j v hj
    have := hw (j + 1) v (by simpa using hj)
    rwa [show off + (j + 1) = off + 1 + j by omega] at this

theorem writeFields_eq_publishFields {addresses : AddressMap} {a : Lir.Word} {c : Fir.CtorInfo}
    {vs : List RVal} {words : Nat → Lir.Word} (mem : X86.Memory)
    (hw : ∀ j u, vs[j]? = some u → Gen.fieldWord addresses c j u = some (words j)) :
    Gen.writeFields mem addresses a c vs.zipIdx =
      publishFields mem a words (List.range vs.length) := by
  have h := writeFields_eq_publishFields_aux addresses a c words vs 0 mem (by simpa using hw)
  simpa using h

/-- Execute stores of `(.v (j + 1))` (for `reuseStores` / `allocStores`) into `[ptr + 8*(j+1)]`. -/
theorem publish_shifted_exec (indices : List Nat) (pointer : Nat) (env : Lir.Env)
    (address : Lir.Word) (words : Nat → Lir.Word) (ctx : Lir.Word)
    (pointerValue : env[pointer]? = some address)
    (fields : ∀ i ∈ indices, env[i + 1]? = some (words i))
    (mem : X86.Memory)
    (writable : ∀ i ∈ indices, ∀ byte < 8,
      mem.writable (fieldAddress address i + UInt64.ofNat byte) = true) :
    Lir.execList env mem ctx
      (indices.map fun j => Lir.Stmt.store .w64
        { base := some (.v pointer), disp := Int.ofNat (8 * (j + 1)) } (.v (j + 1))) =
      some (env, publishFields mem address words indices) := by
  induction indices generalizing mem with
  | nil => rfl
  | cons i indices ih =>
    have write := write?_ok (w := .w64) (v := words i)
      (a := fieldAddress address i) (writable i (by simp))
    have store : (Lir.Stmt.store .w64
        { base := some (.v pointer), disp := Int.ofNat (8 * (i + 1)) } (.v (i + 1))).exec env mem ctx =
        some (env, mem.write .w64 (fieldAddress address i) (words i)) := by
      simp only [Lir.Stmt.exec, Lir.Addr.eval, Lir.Arg.eval, pointerValue, fields i (by simp)]
      change (match mem.write? .w64
        (address + 0 + Lir.dispWord ((8 * (i + 1) : Nat) : Int)) (words i) with
        | .ok after => some (env, after)
        | .error _ => none) = _
      rw [UInt64.add_zero, Lir.dispWord_ofNat]
      change (match mem.write? .w64 (fieldAddress address i) (words i) with
        | .ok after => some (env, after)
        | .error _ => none) = _
      rw [write]
    rw [List.map_cons, Lir.execList, store]
    apply ih (fun j hj => fields j (by simp [hj]))
    intro j hj byte bound
    simpa [X86.Memory.write] using writable j (by simp [hj]) byte bound

/-- Execute stores of `(.imm 1)` (for `writeShell`) into `[v0 + 8*(j+1)]`. -/
theorem publish_const1_exec (indices : List Nat) (env : Lir.Env)
    (address : Lir.Word) (ctx : Lir.Word) (pointerValue : env[0]? = some address)
    (mem : X86.Memory)
    (writable : ∀ i ∈ indices, ∀ byte < 8,
      mem.writable (fieldAddress address i + UInt64.ofNat byte) = true) :
    Lir.execList env mem ctx
      (indices.map fun j => Lir.Stmt.store .w64
        { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.imm 1)) =
      some (env, publishFields mem address (fun _ => 1) indices) := by
  induction indices generalizing mem with
  | nil => rfl
  | cons i indices ih =>
    have write := write?_ok (w := .w64) (v := 1)
      (a := fieldAddress address i) (writable i (by simp))
    have store : (Lir.Stmt.store .w64
        { base := some (.v 0), disp := Int.ofNat (8 * (i + 1)) } (.imm 1)).exec env mem ctx =
        some (env, mem.write .w64 (fieldAddress address i) 1) := by
      simp only [Lir.Stmt.exec, Lir.Addr.eval, Lir.Arg.eval, pointerValue]
      change (match mem.write? .w64
        (address + 0 + Lir.dispWord ((8 * (i + 1) : Nat) : Int)) 1 with
        | .ok after => some (env, after)
        | .error _ => none) = _
      rw [UInt64.add_zero, Lir.dispWord_ofNat]
      change (match mem.write? .w64 (fieldAddress address i) 1 with
        | .ok after => some (env, after)
        | .error _ => none) = _
      rw [write]
    rw [List.map_cons, Lir.execList, store]
    apply ih
    intro j hj byte bound
    simpa [X86.Memory.write] using writable j (by simp [hj]) byte bound

/-- Execute `loadOld` loads from `[v0 + 8*(j+1)]` into `regBase + j`. -/
theorem loadOld_exec (indices : List Nat) (regBase : Nat) (hbase : 2 ≤ regBase)
    (address : Lir.Word) (words : Nat → Lir.Word) (mem : X86.Memory) (ctx : Lir.Word)
    (hload : ∀ j ∈ indices, Lir.loadWord mem .w64 .zero (fieldAddress address j) = some (words j))
    (hnd : indices.Nodup) :
    ∀ (env : Lir.Env), env[0]? = some address →
      ∃ env',
        Lir.execList env mem ctx
          (indices.map fun j => Lir.Stmt.assign (regBase + j)
            (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })) =
          some (env', mem) ∧
        (∀ r, (∀ j ∈ indices, r ≠ regBase + j) → env'[r]? = env[r]?) ∧
        (∀ j ∈ indices, env'[regBase + j]? = some (words j)) := by
  induction indices with
  | nil =>
    intro env _
    exact ⟨env, rfl, fun _ _ => rfl, fun _ h => by cases h⟩
  | cons idx indices ih =>
    intro env h0
    have hnd' := List.nodup_cons.mp hnd
    have hst : (Lir.Stmt.assign (regBase + idx)
        (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (idx + 1)) })).exec env mem ctx =
        some (env.insert (regBase + idx) (words idx), mem) := by
      simp only [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Addr.eval, h0,
        UInt64.add_zero, bind, Option.bind]
      have hdisp : Lir.dispWord (Int.ofNat (8 * (idx + 1))) = UInt64.ofNat (8 * (idx + 1)) :=
        Lir.dispWord_ofNat (8 * (idx + 1))
      rw [hdisp, show address + UInt64.ofNat (8 * (idx + 1)) = fieldAddress address idx from rfl,
        hload idx (by simp)]
    have h0' : (env.insert (regBase + idx) (words idx))[0]? = some address := by
      rw [Lir.env_insert_ne _ _ (by omega)]; exact h0
    obtain ⟨env', hex, hkeep, hset⟩ := ih
      (fun j hj => hload j (by simp [hj])) hnd'.2 (env.insert (regBase + idx) (words idx)) h0'
    refine ⟨env', ?_, ?_, ?_⟩
    · rw [List.map_cons, Lir.execList, hst]; exact hex
    · intro r hr
      rw [hkeep r (fun j hj => hr j (by simp [hj])), Lir.env_insert_ne _ _ (Ne.symm (hr idx (by simp)))]
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj'
      · rw [hkeep (regBase + j) (fun k hk hEq => hnd'.1 (by have : k = j := (by omega); exact this ▸ hk)),
          Lir.env_insert_self]
      · exact hset j hj'

/-- Header + payload stores of a cell equal `Gen.writeCell`. -/
theorem writeHeader_and_fields_exec {addresses : AddressMap} {a : Lir.Word} {b : Body} {cls : Nat}
    {env : Lir.Env} {mem : X86.Memory} {ctx : Lir.Word} {words : Nat → Lir.Word}
    {valArg : Nat → Lir.Arg}
    (hptr : env[0]? = some a)
    (_hnobj : b.ctor.nobj = b.fields.length)
    (hval : ∀ j < b.fields.length, Lir.Arg.eval env (valArg j) = some (words j))
    (hfw : ∀ j u, b.fields[j]? = some u → Gen.fieldWord addresses b.ctor j u = some (words j))
    (hhdrW : ∀ byte < 8, mem.writable (a + UInt64.ofNat byte) = true)
    (hpayW : ∀ j < b.fields.length, ∀ byte < 8,
      mem.writable (fieldAddress a j + UInt64.ofNat byte) = true) :
    let hdr := dynamicHeader b.ctor.nobj cls b.ctor.tag 1
    let stmts : List Lir.Stmt :=
      .store .w64 { base := some (.v 0), disp := 0 } (.imm hdr) ::
        (List.range b.fields.length).map fun j =>
          .store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (valArg j)
    Lir.execList env mem ctx stmts = some (env, Gen.writeCell mem addresses a b cls) := by
  intro hdr stmts
  have hwrite0 := write?_ok (w := .w64) (v := hdr) (a := a) hhdrW
  have hst0 : (Lir.Stmt.store .w64 { base := some (.v 0), disp := 0 } (.imm hdr)).exec env mem ctx =
      some (env, mem.write .w64 a hdr) := by
    simp only [Lir.Stmt.exec, Lir.Addr.eval, Lir.Arg.eval, hptr]
    change (match mem.write? .w64 (a + 0 + Lir.dispWord 0) hdr with
      | .ok after => some (env, after)
      | .error _ => none) = _
    rw [UInt64.add_zero, show Lir.dispWord 0 = 0 by rfl, UInt64.add_zero, hwrite0]
  have htail : ∀ (indices : List Nat) (m : X86.Memory),
      (∀ j ∈ indices, j < b.fields.length) →
      (∀ j ∈ indices, ∀ byte < 8, m.writable (fieldAddress a j + UInt64.ofNat byte) = true) →
      Lir.execList env m ctx
        (indices.map fun j => .store .w64
          { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (valArg j)) =
      some (env, publishFields m a words indices) := by
    intro indices
    induction indices with
    | nil => intro _ _ _; rfl
    | cons j js ih =>
      intro m hlt hw'
      have hj : j < b.fields.length := hlt j (by simp)
      have hwj := write?_ok (w := .w64) (v := words j) (a := fieldAddress a j) (hw' j (by simp))
      have hstj : (Lir.Stmt.store .w64
          { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (valArg j)).exec env m ctx =
          some (env, m.write .w64 (fieldAddress a j) (words j)) := by
        simp only [Lir.Stmt.exec, Lir.Addr.eval, hptr, hval j hj]
        change (match m.write? .w64 (a + 0 + Lir.dispWord ((8 * (j + 1) : Nat) : Int)) (words j) with
          | .ok after => some (env, after)
          | .error _ => none) = _
        rw [UInt64.add_zero, Lir.dispWord_ofNat]
        change (match m.write? .w64 (fieldAddress a j) (words j) with
          | .ok after => some (env, after)
          | .error _ => none) = _
        rw [hwj]
      rw [List.map_cons, Lir.execList, hstj]
      exact ih _ (fun k hk => hlt k (by simp [hk]))
        (fun k hk byte hb => by simpa [X86.Memory.write] using hw' k (by simp [hk]) byte hb)
  dsimp only [stmts]
  rw [Lir.execList, hst0]
  dsimp only
  rw [htail (List.range b.fields.length) (mem.write .w64 a hdr)
    (fun j hj => List.mem_range.mp hj)
    (fun j hj byte hb => by simpa [X86.Memory.write] using hpayW j (List.mem_range.mp hj) byte hb)]
  rw [Gen.writeCell, writeFields_eq_publishFields (mem.write .w64 a hdr) hfw]

private theorem execList_append (env : Lir.Env) (mem : X86.Memory) (ctx : Lir.Word)
    (xs ys : List Lir.Stmt) :
    Lir.execList env mem ctx (xs ++ ys) =
      (Lir.execList env mem ctx xs).bind (fun p => Lir.execList p.1 p.2 ctx ys) := by
  induction xs generalizing env mem with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, Lir.execList]
    cases hx : x.exec env mem ctx with
    | none => rfl
    | some p => exact ih p.1 p.2

/-- Every header and payload byte of a `LiveCell` is writable when its layout has class `cls`. -/
theorem liveCell_writable_header_fields {addresses : AddressMap} {mem : X86.Memory}
    {a : Lir.Word} {refs : Nat} {b : Body} (cell : Gen.LiveCell addresses mem a refs b)
    {n : Nat} (hlen : 8 * (1 + n) ≤ Gen.cellBytesOf b.ctor) :
    (∀ byte < 8, mem.writable (a + UInt64.ofNat byte) = true) ∧
    (∀ j < n, ∀ byte < 8, mem.writable (fieldAddress a j + UInt64.ofNat byte) = true) := by
  refine ⟨fun byte hb => cell.writable byte (by omega), fun j hj byte hb => ?_⟩
  have hfit := cell.fit
  have haddr : fieldAddress a j + UInt64.ofNat byte = a + UInt64.ofNat (8 * (j + 1) + byte) := by
    simp [fieldAddress, UInt64.add_assoc, UInt64.ofNat_add]
  rw [haddr]
  exact cell.writable (8 * (j + 1) + byte) (by omega)

/-! ## Lifting `Gen.isUnique` and `Rt.Rc.Procs.inc` into an ambient program -/

theorem isUnique_call_free : CallFree Gen.isUnique := by
  simp [CallFree, Gen.isUnique]

theorem isUnique_caller {P : Lir.Program} {proc dst : Nat}
    (hproc : P.funcs[proc]? = some Gen.isUnique)
    {mem : X86.Memory} {ctx word res : Lir.Word}
    (heval : Lir.eval Gen.uniqueProgram 0 [word] mem ctx = .ok ([res], mem))
    (caller : Lir.Frame) (callers : List Lir.Frame) (hdst : caller.dsts = [dst]) :
    Sem.Star (Lir.semStep P)
      { mem, ctx, stack := { fn := proc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 word } ::
          caller :: callers } 0
      { mem, ctx, stack := { caller with env := caller.env.insert dst res, dsts := [] } :: callers } := by
  have reaches := (Lir.runs_eval (Gen.unique_initial mem ctx word)) 0
  dsimp only at reaches
  rw [heval] at reaches
  let frame : Lir.Frame := { fn := 0, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 word }
  have localRun : Sem.Reaches (Lir.semStep (localProgram Gen.isUnique))
      (localState mem ctx frame) 0 (.ok ([res], mem)) := by
    simpa only [localProgram, Gen.uniqueProgram, localState, Gen.uniqueState, frame] using reaches
  obtain ⟨charges, hbound, trace⟩ := local_success_transport Gen.isUnique isUnique_call_free P proc
    hproc mem ctx frame rfl caller callers (env := caller.env.insert dst res) localRun
    (by simp [hdst, Lir.bindParams])
  have h0 : charges = 0 := by omega
  subst h0
  simpa only [ambientState, frame] using trace

theorem inc_caller_ready {P : Lir.Program} {incProc : Nat}
    (hinc : P.funcs[incProc]? = some Rt.Rc.Procs.inc)
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {roots : List RVal} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem (holdRoots external roots)
      context base bump limit slots lists)
    {value : RVal} {word : Lir.Word}
    (hperm : CanDup H value) (hword : valueWord addresses value = some word)
    (caller : Lir.Frame) (callers : List Lir.Frame) (hdst : caller.dsts = []) :
    (∃ H' mem',
      Own.Rc.inc H value 1 = some H' ∧
      Gen.AllocatorReady maxClass H' addresses mem' (holdRoots external (value :: roots))
        context base bump limit slots lists ∧
      Sem.Star (Lir.semStep P)
        { mem, ctx := context,
          stack := { fn := incProc, label := 0, pos := 0, env := incEnv word } :: caller :: callers } 0
        { mem := mem', ctx := context, stack := caller :: callers }) ∨
    Sem.Reaches (Lir.semStep P)
      { mem, ctx := context,
        stack := { fn := incProc, label := 0, pos := 0, env := incEnv word } :: caller :: callers }
      0 (.resource .heap) := by
  have hrebase : (fun k => holdRoots external roots k + refsIn k [value]) =
      holdRoots external (value :: roots) := by
    funext k; simp only [holdRoots, refsIn]; omega
  cases value with
  | loc l =>
    obtain ⟨refs, body, hcell⟩ := canDup_live hperm
    have haddr : addresses l = some word := hword
    obtain ⟨_, addr, haddr0, phys⟩ := ready.idle.live.cell l refs .dyn body hcell
    by_cases hroom : refs < Rt.Rc.maxCount
    · obtain ⟨heff, hready', heval⟩ := ready.increment_ready hcell haddr hroom
      rw [hrebase] at hready'
      have localRun := (Lir.runs_eval (inc_initial mem context word)) 0
      dsimp only at localRun
      rw [heval] at localRun
      let frame : Lir.Frame := { fn := 0, label := 0, pos := 0, env := incEnv word }
      have localTrace : Sem.Reaches (Lir.semStep (localProgram Rt.Rc.Procs.inc))
          (localState mem context frame) 0 (.ok ([], storeCount mem word (UInt64.ofNat refs))) := by
        simpa only [localProgram, incProgram, localState, incState, frame] using localRun
      obtain ⟨charges, hbd, trace⟩ := local_success_transport Rt.Rc.Procs.inc inc_call_free P incProc
        hinc mem context frame rfl caller callers (env := caller.env) localTrace
        (by simp [hdst, Lir.bindParams])
      have h0 : charges = 0 := by omega
      subst h0
      have hce : { caller with env := caller.env, dsts := [] } = caller := by
        cases caller; simp_all
      refine .inl ⟨_, _, heff, hready', ?_⟩
      simpa only [ambientState, frame, hce] using trace
    · have hmax : refs = Rt.Rc.maxCount := by have hb := phys.bounded; omega
      subst refs
      have heval := Gen.increment_max_failure ready.idle hcell haddr
      have localRun := (Lir.runs_eval (inc_initial mem context word)) 0
      dsimp only at localRun
      rw [heval] at localRun
      let frame : Lir.Frame := { fn := 0, label := 0, pos := 0, env := incEnv word }
      have localTrace : Sem.Reaches (Lir.semStep (localProgram Rt.Rc.Procs.inc))
          (localState mem context frame) 0 (.resource .heap) := by
        simpa only [localProgram, incProgram, localState, incState, frame] using localRun
      have failed := local_resource_transport Rt.Rc.Procs.inc inc_call_free P incProc hinc
        mem context frame rfl (caller :: callers) localTrace
      exact .inr (by simpa only [ambientState, frame] using failed)
  | lit lit =>
    have himm : ∀ l, RVal.lit lit ≠ RVal.loc l := fun _ h => by cases h
    obtain ⟨heff, _, heval⟩ := Gen.increment_immediate_entry ready.idle himm word hword
    have hsame : holdRoots external (RVal.lit lit :: roots) = holdRoots external roots := by
      funext k; simp [holdRoots, refsIn]
    have localRun := (Lir.runs_eval (inc_initial mem context word)) 0
    dsimp only at localRun
    rw [heval] at localRun
    let frame : Lir.Frame := { fn := 0, label := 0, pos := 0, env := incEnv word }
    have localTrace : Sem.Reaches (Lir.semStep (localProgram Rt.Rc.Procs.inc))
        (localState mem context frame) 0 (.ok ([], mem)) := by
      simpa only [localProgram, incProgram, localState, incState, frame] using localRun
    obtain ⟨charges, hbd, trace⟩ := local_success_transport Rt.Rc.Procs.inc inc_call_free P incProc
      hinc mem context frame rfl caller callers (env := caller.env) localTrace
      (by simp [hdst, Lir.bindParams])
    have h0 : charges = 0 := by omega
    subst h0
    have hce : { caller with env := caller.env, dsts := [] } = caller := by
      cases caller; simp_all
    refine .inl ⟨H, mem, heff, by rw [hsame]; exact ready, ?_⟩
    simpa only [ambientState, frame, hce] using trace
  | ctor0 c =>
    have himm : ∀ l, RVal.ctor0 c ≠ RVal.loc l := fun _ h => by cases h
    obtain ⟨heff, _, heval⟩ := Gen.increment_immediate_entry ready.idle himm word hword
    have hsame : holdRoots external (RVal.ctor0 c :: roots) = holdRoots external roots := by
      funext k; simp [holdRoots, refsIn]
    have localRun := (Lir.runs_eval (inc_initial mem context word)) 0
    dsimp only at localRun
    rw [heval] at localRun
    let frame : Lir.Frame := { fn := 0, label := 0, pos := 0, env := incEnv word }
    have localTrace : Sem.Reaches (Lir.semStep (localProgram Rt.Rc.Procs.inc))
        (localState mem context frame) 0 (.ok ([], mem)) := by
      simpa only [localProgram, incProgram, localState, incState, frame] using localRun
    obtain ⟨charges, hbd, trace⟩ := local_success_transport Rt.Rc.Procs.inc inc_call_free P incProc
      hinc mem context frame rfl caller callers (env := caller.env) localTrace
      (by simp [hdst, Lir.bindParams])
    have h0 : charges = 0 := by omega
    subst h0
    have hce : { caller with env := caller.env, dsts := [] } = caller := by
      cases caller; simp_all
    refine .inl ⟨H, mem, heff, by rw [hsame]; exact ready, ?_⟩
    simpa only [ambientState, frame, hce] using trace
  | erased =>
    have himm : ∀ l, RVal.erased ≠ RVal.loc l := fun _ h => by cases h
    obtain ⟨heff, _, heval⟩ := Gen.increment_immediate_entry ready.idle himm word hword
    have hsame : holdRoots external (RVal.erased :: roots) = holdRoots external roots := by
      funext k; simp [holdRoots, refsIn]
    have localRun := (Lir.runs_eval (inc_initial mem context word)) 0
    dsimp only at localRun
    rw [heval] at localRun
    let frame : Lir.Frame := { fn := 0, label := 0, pos := 0, env := incEnv word }
    have localTrace : Sem.Reaches (Lir.semStep (localProgram Rt.Rc.Procs.inc))
        (localState mem context frame) 0 (.ok ([], mem)) := by
      simpa only [localProgram, incProgram, localState, incState, frame] using localRun
    obtain ⟨charges, hbd, trace⟩ := local_success_transport Rt.Rc.Procs.inc inc_call_free P incProc
      hinc mem context frame rfl caller callers (env := caller.env) localTrace
      (by simp [hdst, Lir.bindParams])
    have h0 : charges = 0 := by omega
    subst h0
    have hce : { caller with env := caller.env, dsts := [] } = caller := by
      cases caller; simp_all
    refine .inl ⟨H, mem, heff, by rw [hsame]; exact ready, ?_⟩
    simpa only [ambientState, frame, hce] using trace

/-! ## `mkReuseUWrapper` and `mkReuseWrapper` execution -/

/-- Execute the in-place `reuseStores` block (block 0 of `mkReuseUWrapper` or block 1 of
`mkReuseWrapper`) and return `v0` (`addr`) to the caller. -/
theorem reuse_inplace_block_exec {P : Lir.Program} {wrapper fnBlk dst : Nat}
    {lay : CellLayout} {cls : Nat} {fn : Lir.Func}
    (hfn : P.funcs[wrapper]? = some fn)
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {l : Nat} {a : Lir.Word} {b : Body} {ctor : Fir.CtorInfo}
    {vs rest : List RVal} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (hlay : lay = CellLayout.ofFields ctor.arity ctor.tag)
    (hblk : fn.blocks[fnBlk]? = some {
      body := (Lir.Stmt.store .w64 { base := some (.v 0), disp := 0 }
          (.imm (dynamicHeader lay.nobj cls lay.tag 1)) ::
        (List.range lay.nobj).map fun j =>
          Lir.Stmt.store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.v (j + 1))).toArray
      term := .ret [.v 0] })
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (fun k => external k + refsIn k (.loc l :: (vs ++ rest)))
      context base bump limit slots lists)
    (hc : H.cell? l = some (.live 1 .dyn b)) (ha : addresses l = some a)
    (hbfZero : ∀ k, refsIn k b.fields = 0)
    (hvc : Own.Plain.Ctx.validReuseCtor ctor = some cls)
    (hclsB : Gen.classOf b.ctor = cls)
    (harity : vs.length = ctor.arity)
    {env : Lir.Env} {words : Nat → Lir.Word}
    (hptr : env[0]? = some a)
    (hregs : ∀ j < ctor.arity, env[j + 1]? = some (words j))
    (hvals : ∀ j u, vs[j]? = some u → valueWord addresses u = some (words j))
    (caller : Lir.Frame) (callers : List Lir.Frame) (hdst : caller.dsts = [dst]) :
    ∃ H' slots',
      reuseCell H l { ctor, fields := vs } = some (.loc H.size, H') ∧
      Gen.AllocatorReady maxClass H' (placeFresh addresses H.size a)
        (Gen.writeCell mem addresses a { ctor, fields := vs } cls)
        (fun k => external k + refsIn k (.loc H.size :: rest))
        context base bump limit slots' lists ∧
      Sem.Star (Lir.semStep P)
        { mem, ctx := context, stack := { fn := wrapper, label := fnBlk, pos := 0, env } :: caller :: callers } 0
        { mem := Gen.writeCell mem addresses a { ctor, fields := vs } cls, ctx := context,
          stack := { caller with env := caller.env.insert dst a, dsts := [] } :: callers } := by
  obtain ⟨_, _, _, _, hnsc, hnobj, hfk, hlayC, hokC, _, hclsC, _⟩ := validReuseCtor_full hvc
  have hclass : Gen.classOf ctor = Gen.classOf b.ctor := by rw [hclsC, hclsB]
  have hmass : ∀ k, refsIn k (b.fields ++ (vs ++ rest)) = refsIn k (vs ++ rest) := by
    intro k; simp only [refsIn_append, hbfZero k, Nat.zero_add]
  have hfw : ∀ j u, vs[j]? = some u → Gen.fieldWord addresses ctor j u = some (words j) := by
    intro j u hj
    have hlt : j < ctor.nobj := by
      have := (List.getElem?_eq_some_iff.mp hj).1; omega
    simp only [Gen.fieldWord, hlt, ↓reduceIte]
    exact hvals j u hj
  have hwords : ∀ j u, vs[j]? = some u → (Gen.fieldWord addresses ctor j u).isSome := by
    intro j u hj; rw [hfw j u hj]; rfl
  obtain ⟨H', slots', hrc, hready'⟩ :=
    Gen.inPlace_ready (b' := { ctor, fields := vs }) (kept := rest)
      ready hc ha hokC (by dsimp only; omega) (by dsimp only; rw [hnobj]; exact hfk) hclass hmass hwords
  rw [hclsB] at hready'
  obtain ⟨-, a0, ha0, oldCell0⟩ := ready.idle.live.cell l 1 .dyn b hc
  have ea0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
  have oldCell : Gen.LiveCell addresses mem a 1 b := ea0 ▸ oldCell0
  have hbytes : Gen.cellBytesOf ctor = Gen.cellBytesOf b.ctor := by
    unfold Gen.cellBytesOf; rw [hclass]
  have hlen : 8 * (1 + vs.length) ≤ Gen.cellBytesOf b.ctor := by
    have h1 := (Gen.cellBytesOf_le hokC).2.1
    rw [← hbytes]; omega
  obtain ⟨hhdrW, hpayW⟩ := liveCell_writable_header_fields oldCell hlen
  have hex := writeHeader_and_fields_exec (addresses := addresses) (b := { ctor, fields := vs })
    (cls := cls) (env := env) (mem := mem) (ctx := context) (words := words)
    (valArg := fun j => .v (j + 1)) hptr (by dsimp only; omega)
    (fun j hj => by dsimp only at hj; simpa [Lir.Arg.eval] using hregs j (by omega)) hfw hhdrW hpayW
  have hnobjLay : lay.nobj = vs.length := by rw [hlay]; simp [CellLayout.ofFields, harity]
  have htagLay : lay.tag = ctor.tag := by rw [hlay]; simp [CellLayout.ofFields]
  have hhdrEq : dynamicHeader lay.nobj cls lay.tag 1 = dynamicHeader ctor.nobj cls ctor.tag 1 := by
    rw [hnobjLay, htagLay, hnobj, harity]
  have hblk' : fn.blocks[fnBlk]? = some {
      body := (Lir.Stmt.store .w64 { base := some (.v 0), disp := 0 }
          (.imm (dynamicHeader ctor.nobj cls ctor.tag 1)) ::
        (List.range vs.length).map fun j =>
          Lir.Stmt.store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.v (j + 1))).toArray
      term := .ret [.v 0] } := by
    rw [hhdrEq, hnobjLay] at hblk
    exact hblk
  have hstmts := Lir.star_stmts (p := P) (ctx := context) (rest := caller :: callers) (dsts := [])
    hfn hblk' (pre := []) (post := []) (by simp) (by
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · rfl
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs'; rfl) hex
  have hret := Lir.step_ret_caller (p := P) (vals := [a]) (ρ := caller.env.insert dst a)
    (mem := Gen.writeCell mem addresses a { ctor, fields := vs } cls) (ctx := context)
    (fr := { fn := wrapper, label := fnBlk, pos := 1 + vs.length, env })
    (caller := caller) (rest' := callers) hfn hblk' (by simp; omega) rfl
    (by simp [Lir.evalArgs, Lir.Arg.eval, hptr]) (by simp [hdst, Lir.bindParams])
  refine ⟨H', slots', hrc, hready', ?_⟩
  have hstmts' : Sem.Star (Lir.semStep P)
      { mem, ctx := context, stack := { fn := wrapper, label := fnBlk, pos := 0, env } :: caller :: callers } 0
      { mem := Gen.writeCell mem addresses a { ctor, fields := vs } cls, ctx := context,
        stack := { fn := wrapper, label := fnBlk, pos := 1 + vs.length, env } :: caller :: callers } := by
    simpa [Nat.add_comm] using hstmts
  simpa using hstmts'.trans (Sem.Star.single (Lir.semStep_next.mpr hret))

/-- Execute `mkReuseWrapper` block 2 (fallback fresh allocation when `v0 = 1 = .erased`),
producing either a fresh published cell or `.resource .heap`. -/
theorem reuse_fallback_block_exec {P : Lir.Program} {wrapper allocProc dst : Nat}
    {ctor : Fir.CtorInfo} {cls : Nat}
    (hfn : P.funcs[wrapper]? = some (mkReuseWrapper allocProc (CellLayout.ofFields ctor.arity ctor.tag) cls))
    (halloc : P.funcs[allocProc]? = some (Gen.alloc (CellLayout.ofFields ctor.arity ctor.tag)))
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {vs : List RVal} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (fun k => external k + refsIn k vs) context base bump limit slots lists)
    (hvc : Own.Plain.Ctx.validReuseCtor ctor = some cls)
    (harity : vs.length = ctor.arity)
    {env : Lir.Env} {words : Nat → Lir.Word}
    (hregs : ∀ j < ctor.arity, env[j + 1]? = some (words j))
    (hvals : ∀ j u, vs[j]? = some u → valueWord addresses u = some (words j))
    (caller : Lir.Frame) (callers : List Lir.Frame) (hdst : caller.dsts = [dst]) :
    (∃ address next finalMem finalSlots finalLists,
      Gen.AllocatorReady maxClass (H.alloc .rc { ctor, fields := vs }).2
        (placeFresh addresses H.size address) finalMem
        (fun k => external k + refsIn k [(H.alloc .rc { ctor, fields := vs }).1])
        context base next limit finalSlots finalLists ∧
      Sem.Star (Lir.semStep P)
        { mem, ctx := context, stack := { fn := wrapper, label := 2, pos := 0, env } :: caller :: callers } 1
        { mem := finalMem, ctx := context,
          stack := { caller with env := caller.env.insert dst address, dsts := [] } :: callers }) ∨
    Sem.Reaches (Lir.semStep P)
      { mem, ctx := context, stack := { fn := wrapper, label := 2, pos := 0, env } :: caller :: callers }
      1 (.resource .heap) := by
  obtain ⟨hpos, _, hsmall, htag, hnsc, hnobj, hfk, _, _, _, _, _⟩ := validReuseCtor_full hvc
  have hblk2 : (mkReuseWrapper allocProc (CellLayout.ofFields ctor.arity ctor.tag) cls).blocks[2]? =
      some {
        body := (Lir.Stmt.call [ctor.arity + 1] allocProc [] ::
          (List.range ctor.arity).map fun j =>
            Lir.Stmt.store .w64 { base := some (.v (ctor.arity + 1)), disp := Int.ofNat (8 * (j + 1)) }
              (.v (j + 1))).toArray
        term := .ret [.v (ctor.arity + 1)]
        cold := true } := rfl
  have henter : Lir.enter P allocProc [] = some { fn := allocProc, label := 0, pos := 0, env := {} } := by
    simp [Lir.enter, halloc,
      Gen.alloc_eq (Gen.ofFields_layout hpos hsmall htag).1 (Gen.ofFields_layout (tag := ctor.tag) hpos hsmall htag).2,
      Gen.allocFunc, Lir.bindParams]
  have hcall := Lir.step_call (p := P) (mem := mem) (ctx := context) (rest := caller :: callers)
    (fr := { fn := wrapper, label := 2, pos := 0, env })
    hfn hblk2 (by simp only [List.size_toArray, List.length_cons]; omega) rfl (vs := []) rfl henter
  let cont : Lir.Frame := { fn := wrapper, label := 2, pos := 1, env, dsts := [ctor.arity + 1] }
  have finish : ∀ {address next : Lir.Word} {reserved : X86.Memory} {finalSlots : List Slot}
      {finalLists : Nat → List Lir.Word},
      Lir.eval (Gen.allocProgram (CellLayout.ofFields ctor.arity ctor.tag)) 0 [] mem context =
        .ok ([address], reserved) →
      (∀ i < ctor.arity, ∀ byte < 8,
        reserved.writable (fieldAddress address i + UInt64.ofNat byte) = true) →
      Gen.AllocatorReady maxClass (H.alloc .rc { ctor, fields := vs }).2
        (placeFresh addresses H.size address) (publishFields reserved address words (List.range ctor.arity))
        (fun k => external k + refsIn k [(H.alloc .rc { ctor, fields := vs }).1])
        context base next limit finalSlots finalLists →
      Sem.Star (Lir.semStep P)
        { mem, ctx := context, stack := { fn := wrapper, label := 2, pos := 0, env } :: caller :: callers } 1
        { mem := publishFields reserved address words (List.range ctor.arity), ctx := context,
          stack := { caller with env := caller.env.insert dst address, dsts := [] } :: callers } := by
    intro address next reserved finalSlots finalLists hexec hwr _
    have hprocTrace := allocator_caller hpos hsmall htag hexec halloc cont (caller :: callers) rfl
    have hex := publish_shifted_exec (List.range ctor.arity) (ctor.arity + 1)
      (env.insert (ctor.arity + 1) address) address words context (by simp) (by
        intro i hi
        have hlt := List.mem_range.mp hi
        rw [Lir.env_insert_ne _ _ (by omega)]
        exact hregs i hlt) reserved (fun i hi byte hb => hwr i (List.mem_range.mp hi) byte hb)
    have hstores := Lir.star_stmts (p := P) (ctx := context) (rest := caller :: callers) (dsts := [])
      hfn hblk2 (pre := [.call [ctor.arity + 1] allocProc []]) (post := []) (by simp) (by
        intro s hs; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs; rfl) hex
    have hret := Lir.step_ret_caller (p := P) (vals := [address]) (ρ := caller.env.insert dst address)
      (mem := publishFields reserved address words (List.range ctor.arity)) (ctx := context)
      (fr := { fn := wrapper, label := 2, pos := 1 + ctor.arity, env := env.insert (ctor.arity + 1) address })
      (caller := caller) (rest' := callers) hfn hblk2 (by simp; omega) rfl
      (by simp [Lir.evalArgs, Lir.Arg.eval]) (by simp [hdst, Lir.bindParams])
    have hstores' : Sem.Star (Lir.semStep P)
        { mem := reserved, ctx := context,
          stack := { fn := wrapper, label := 2, pos := 1, env := env.insert (ctor.arity + 1) address } :: caller :: callers } 0
        { mem := publishFields reserved address words (List.range ctor.arity), ctx := context,
          stack := { fn := wrapper, label := 2, pos := 1 + ctor.arity, env := env.insert (ctor.arity + 1) address } :: caller :: callers } := by
      simpa using hstores
    have hjoin := (Sem.Star.single (Lir.semStep_next.mpr hcall)).trans
      (hprocTrace.trans (hstores'.trans (Sem.Star.single (Lir.semStep_next.mpr hret))))
    simpa [cont] using hjoin
  cases hlist : lists (Gen.fieldsClass ctor.arity) with
  | nil =>
    by_cases hspace : bump.toNat + classBytes (Gen.fieldsClass ctor.arity) ≤ limit.toNat
    · obtain ⟨hexec, hready'⟩ := allocation_bump_ready (body := { ctor, fields := vs }) ready
        (by dsimp only; omega) (by dsimp only; omega) htag (by dsimp only; omega) hnsc
        (by dsimp only; rw [harity]; exact hfk)
        (by simpa [harity] using hlist) (by simpa [harity] using hspace) words hvals
      have hwr : ∀ i < ctor.arity, ∀ byte < 8,
          (Gen.reserveBump mem context bump
            (bump + UInt64.ofNat (classBytes (Gen.fieldsClass ctor.arity)))
            (CellLayout.ofFields ctor.arity ctor.tag) (Gen.fieldsClass ctor.arity)).writable
            (fieldAddress bump i + UInt64.ofNat byte) = true := by
        intro i hi byte hb
        have hbounds := ready.idle.partition.bounds
        obtain ⟨_, _, hlow, _⟩ := Gen.fieldsClass_spec hpos hsmall
        have hoff : 8 * (i + 1) + byte < classBytes (Gen.fieldsClass ctor.arity) := by omega
        have haNat : (bump + UInt64.ofNat (8 * (i + 1) + byte)).toNat =
            bump.toNat + (8 * (i + 1) + byte) := Rt.Proof.addr_toNat (by omega)
        have hacc := ready.arena_access (bump + UInt64.ofNat (8 * (i + 1) + byte))
          (by rw [haNat]; omega) (by rw [haNat]; omega)
        simpa [Gen.reserveBump, X86.Memory.write, fieldAddress_byte] using hacc.2
      rw [harity] at hexec hready'
      exact .inl ⟨bump, _, _, _, _, hready', finish hexec hwr hready'⟩
    · have hfail := ready.reserve_short (Gen.ofFields_layout hpos hsmall htag).1
        (Gen.ofFields_layout (tag := ctor.tag) hpos hsmall htag).2 hlist (by omega) 0
      have reaches := (Lir.runs_eval (Gen.alloc_free_initial mem context _ _
        (Gen.ofFields_layout hpos hsmall htag).1 (Gen.ofFields_layout (tag := ctor.tag) hpos hsmall htag).2)) 0
      dsimp only at reaches
      rw [hfail] at reaches
      let frame : Lir.Frame := { fn := 0, label := 0, pos := 0, env := {} }
      have localRun : Sem.Reaches (Lir.semStep (localProgram (Gen.alloc (CellLayout.ofFields ctor.arity ctor.tag))))
          (localState mem context frame) 0 (.resource .heap) := by
        simpa only [localProgram, Gen.allocProgram, localState, allocState, frame] using reaches
      have htrans := local_resource_transport (Gen.alloc (CellLayout.ofFields ctor.arity ctor.tag))
        (allocator_call_free ctor.arity ctor.tag) P allocProc halloc mem context frame rfl
        (cont :: caller :: callers) localRun
      have hjoin := Sem.Reaches.star (Sem.Star.single (Lir.semStep_next.mpr hcall)) htrans
      exact .inr (by simpa [cont, frame, ambientState] using hjoin)
  | cons address tail =>
    have hmem : address ∈ lists (Gen.fieldsClass ctor.arity) := by simp [hlist]
    obtain ⟨target, hslotMem, hslotAddr, hslotCls, _⟩ :=
      ready.idle.free_placed (Gen.fieldsClass ctor.arity) address hmem
    have hsel : lists target.cls = target.address :: tail := by rw [hslotCls, hslotAddr, hlist]
    obtain ⟨hexec, hready'⟩ := allocation_free_ready (body := { ctor, fields := vs }) ready
      hslotMem hsel (by simpa [harity] using hslotCls) (by dsimp only; omega) (by dsimp only; omega) htag
      (by dsimp only; omega) hnsc (by dsimp only; rw [harity]; exact hfk) words hvals
    have hwr : ∀ i < ctor.arity, ∀ byte < 8,
        (Gen.reserveFree mem context target.address (tail.headD 0)
          (CellLayout.ofFields ctor.arity ctor.tag) (Gen.fieldsClass ctor.arity)).writable
          (fieldAddress target.address i + UInt64.ofNat byte) = true := by
      intro i hi byte hb
      obtain ⟨_, _, hlow, _⟩ := Gen.fieldsClass_spec hpos hsmall
      unfold classBytes at hlow
      have hacc := ready.slot_access hslotMem (j := 8 * (i + 1) + byte) (by rw [hslotCls]; omega)
      simpa [Gen.reserveFree, X86.Memory.write, fieldAddress_byte] using hacc.2
    rw [harity] at hexec hready'
    exact .inl ⟨target.address, bump, _, _, _, hready', finish hexec hwr hready'⟩

/-! ## Parameterized loops for `mkResetWrapper` and `mkResetUWrapper` -/

private theorem flatMap_two_length {α : Type} (f g : Nat → α) (n : Nat) :
    ((List.range n).flatMap fun k => [f k, g k]).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ m ihm =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ihm]
    simp; omega

private theorem flatMap_two_getElem {α : Type} (f g : Nat → α) (n j : Nat) (hj : j < n) :
    ((List.range n).flatMap fun k => [f k, g k])[2 * j]? = some (f j) ∧
    ((List.range n).flatMap fun k => [f k, g k])[2 * j + 1]? = some (g j) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hlen := flatMap_two_length f g n
    by_cases hjn : j < n
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      exact ih j hjn
    · have hjeq : j = n := by omega
      subst hjeq
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      simp [hlen]

/-- Block lookups for `mkResetWrapper` at every statically indexed block. -/
private theorem mkResetWrapper_block0 (isU incProc decProc n tag cls : Nat) :
    (mkResetWrapper isU incProc decProc (CellLayout.ofFields n tag) cls).blocks[0]? =
      some { body := #[.call [2] isU [.v 0]],
             term := .br .eq .w64 (.v 2) (.imm 1) ⟨1, []⟩ ⟨3 + 2 * n, []⟩ } := by
  simp [mkResetWrapper, CellLayout.ofFields]

private theorem mkResetWrapper_block1 (isU incProc decProc n tag cls : Nat) :
    (mkResetWrapper isU incProc decProc (CellLayout.ofFields n tag) cls).blocks[1]? =
      some { body := ((List.range n).map (fun j =>
                 Lir.Stmt.assign (3 + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })) ++
               Lir.Stmt.store .w64 { base := some (.v 0), disp := 0 } (.imm (dynamicHeader n cls tag 1)) ::
               (List.range n).map (fun j =>
                 Lir.Stmt.store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.imm 1))).toArray,
             term := .jump ⟨2, []⟩ } := by
  simp [mkResetWrapper, CellLayout.ofFields]

private theorem fails_prefix {α β : Type} {step : α → Sem.Step α β} {s s' : α} {c : Nat}
    (h : Sem.Star step s c s') (hf : Sem.Fails step s') : Sem.Fails step s :=
  let ⟨c', t, r, ht, hr⟩ := hf
  ⟨c + c', t, r, h.trans ht, hr⟩

private theorem mkResetWrapper_dec_blocks (isU incProc decProc n tag cls j : Nat) (hj : j < n) :
    (mkResetWrapper isU incProc decProc (CellLayout.ofFields n tag) cls).blocks[2 + 2 * j]? =
      some { term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (j + 1))))
               ⟨2 + 2 * j + 2, []⟩ ⟨2 + 2 * j + 1, []⟩ } ∧
    (mkResetWrapper isU incProc decProc (CellLayout.ofFields n tag) cls).blocks[2 + 2 * j + 1]? =
      some { body := #[.call [] decProc [.v (3 + j)]],
             term := .jump ⟨2 + 2 * j + 2, []⟩ } := by
  unfold mkResetWrapper
  simp only [CellLayout.ofFields, List.getElem?_toArray, List.cons_append, List.nil_append,
    List.append_assoc]
  let f : Nat → Lir.Block := fun k =>
    { term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (k + 1)))) ⟨2 + 2 * k + 2, []⟩ ⟨2 + 2 * k + 1, []⟩ }
  let g : Nat → Lir.Block := fun k =>
    { body := #[.call [] decProc [.v (3 + k)]], term := .jump ⟨2 + 2 * k + 2, []⟩ }
  have hft := flatMap_two_getElem f g n j hj
  have hlen := flatMap_two_length f g n
  dsimp only [f, g] at hft hlen
  constructor
  · rw [show 2 + 2 * j = (2 * j + 1) + 1 by omega, List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [hlen]; omega)]
    simpa [show 2 * j + 1 + 1 = 2 + 2 * j by omega] using hft.1
  · rw [show 2 + 2 * j + 1 = (2 * j + 2) + 1 by omega, List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [hlen]; omega)]
    exact hft.2

private theorem mkResetWrapper_uniqueRet (isU incProc decProc n tag cls : Nat) :
    (mkResetWrapper isU incProc decProc (CellLayout.ofFields n tag) cls).blocks[2 + 2 * n]? =
      some { term := .ret [.v 0] } := by
  unfold mkResetWrapper
  simp only [CellLayout.ofFields, List.getElem?_toArray, List.cons_append, List.nil_append,
    List.append_assoc]
  let f : Nat → Lir.Block := fun k =>
    { term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (k + 1)))) ⟨2 + 2 * k + 2, []⟩ ⟨2 + 2 * k + 1, []⟩ }
  let g : Nat → Lir.Block := fun k =>
    { body := #[.call [] decProc [.v (3 + k)]], term := .jump ⟨2 + 2 * k + 2, []⟩ }
  have hlen := flatMap_two_length f g n
  dsimp only [f, g] at hlen
  rw [show 2 + 2 * n = (2 * n + 1) + 1 by omega, List.getElem?_cons_succ, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen]; omega), hlen, Nat.sub_self]
  rfl

private theorem mkResetWrapper_shared_blocks (isU incProc decProc n tag cls j : Nat) (hj : j < n) :
    (mkResetWrapper isU incProc decProc (CellLayout.ofFields n tag) cls).blocks[3 + 2 * n + 2 * j]? =
      some { term := (.br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (j + 1))))
               ⟨3 + 2 * n + 2 * j + 1, []⟩ ⟨3 + 2 * n + 2 * j + 2, []⟩) } ∧
    (mkResetWrapper isU incProc decProc (CellLayout.ofFields n tag) cls).blocks[3 + 2 * n + 2 * j + 1]? =
      some { body := #[
               .assign (3 + n + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) }),
               .call [] incProc [.v (3 + n + j)]],
             term := .jump ⟨3 + 2 * n + 2 * j + 2, []⟩ } := by
  unfold mkResetWrapper
  simp only [CellLayout.ofFields, List.getElem?_toArray, List.cons_append, List.nil_append,
    List.append_assoc]
  let f1 : Nat → Lir.Block := fun k =>
    { term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (k + 1)))) ⟨2 + 2 * k + 2, []⟩ ⟨2 + 2 * k + 1, []⟩ }
  let g1 : Nat → Lir.Block := fun k =>
    { body := #[.call [] decProc [.v (3 + k)]], term := .jump ⟨2 + 2 * k + 2, []⟩ }
  let f2 : Nat → Lir.Block := fun k =>
    { term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (k + 1)))) ⟨3 + 2 * n + 2 * k + 1, []⟩ ⟨3 + 2 * n + 2 * k + 2, []⟩ }
  let g2 : Nat → Lir.Block := fun k =>
    { body := #[.assign (3 + n + k) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (k + 1)) }),
                .call [] incProc [.v (3 + n + k)]],
      term := .jump ⟨3 + 2 * n + 2 * k + 2, []⟩ }
  have hlen1 := flatMap_two_length f1 g1 n
  have hlen2 := flatMap_two_length f2 g2 n
  have hft := flatMap_two_getElem f2 g2 n j hj
  dsimp only [f1, g1, f2, g2] at hlen1 hlen2 hft
  constructor
  · rw [show 3 + 2 * n + 2 * j = (2 * n + 2 * j + 2) + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_append_right (by rw [hlen1]; omega), hlen1,
      show 2 * n + 2 * j + 1 - 2 * n = 2 * j + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_append_left (by rw [hlen2]; omega)]
    simpa [show 2 * n + 2 * j + 2 + 1 = 3 + 2 * n + 2 * j by omega] using hft.1
  · rw [show 3 + 2 * n + 2 * j + 1 = (2 * n + 2 * j + 3) + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_append_right (by rw [hlen1]; omega), hlen1,
      show 2 * n + 2 * j + 2 - 2 * n = 2 * j + 2 by omega,
      List.getElem?_cons_succ, List.getElem?_append_left (by rw [hlen2]; omega)]
    exact hft.2

private theorem mkResetWrapper_sharedRet (isU incProc decProc n tag cls : Nat) :
    (mkResetWrapper isU incProc decProc (CellLayout.ofFields n tag) cls).blocks[3 + 2 * n + 2 * n]? =
      some { body := #[.call [] decProc [.v 0]], term := .ret [.imm 1] } := by
  unfold mkResetWrapper
  simp only [CellLayout.ofFields, List.getElem?_toArray, List.cons_append, List.nil_append,
    List.append_assoc]
  let f1 : Nat → Lir.Block := fun k =>
    { term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (k + 1)))) ⟨2 + 2 * k + 2, []⟩ ⟨2 + 2 * k + 1, []⟩ }
  let g1 : Nat → Lir.Block := fun k =>
    { body := #[.call [] decProc [.v (3 + k)]], term := .jump ⟨2 + 2 * k + 2, []⟩ }
  let f2 : Nat → Lir.Block := fun k =>
    { term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (k + 1)))) ⟨3 + 2 * n + 2 * k + 1, []⟩ ⟨3 + 2 * n + 2 * k + 2, []⟩ }
  let g2 : Nat → Lir.Block := fun k =>
    { body := #[.assign (3 + n + k) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (k + 1)) }),
                .call [] incProc [.v (3 + n + k)]],
      term := .jump ⟨3 + 2 * n + 2 * k + 2, []⟩ }
  have hlen1 := flatMap_two_length f1 g1 n
  have hlen2 := flatMap_two_length f2 g2 n
  dsimp only [f1, g1, f2, g2] at hlen1 hlen2
  rw [show 3 + 2 * n + 2 * n = (4 * n + 2) + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen1]; omega), hlen1,
    show 4 * n + 1 - 2 * n = 2 * n + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_append_right (by rw [hlen2]; omega), hlen2, Nat.sub_self]
  rfl

private theorem mkResetUWrapper_block0 (decProc n tag cls : Nat) :
    (mkResetUWrapper decProc (CellLayout.ofFields n tag) cls).blocks[0]? =
      some { body := ((List.range n).map (fun j =>
                 Lir.Stmt.assign (2 + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })) ++
               Lir.Stmt.store .w64 { base := some (.v 0), disp := 0 } (.imm (dynamicHeader n cls tag 1)) ::
               (List.range n).map (fun j =>
                 Lir.Stmt.store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.imm 1))).toArray,
             term := .jump ⟨1, []⟩ } := by
  simp [mkResetUWrapper, CellLayout.ofFields]

private theorem mkResetUWrapper_dec_blocks (decProc n tag cls j : Nat) (hj : j < n) :
    (mkResetUWrapper decProc (CellLayout.ofFields n tag) cls).blocks[1 + 2 * j]? =
      some { term := (.br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (j + 1))))
               ⟨1 + 2 * j + 2, []⟩ ⟨1 + 2 * j + 1, []⟩) } ∧
    (mkResetUWrapper decProc (CellLayout.ofFields n tag) cls).blocks[1 + 2 * j + 1]? =
      some { body := #[.call [] decProc [.v (2 + j)]],
             term := .jump ⟨1 + 2 * j + 2, []⟩ } := by
  unfold mkResetUWrapper
  simp only [CellLayout.ofFields, List.getElem?_toArray, List.cons_append, List.nil_append]
  let f : Nat → Lir.Block := fun k =>
    { term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (k + 1)))) ⟨1 + 2 * k + 2, []⟩ ⟨1 + 2 * k + 1, []⟩ }
  let g : Nat → Lir.Block := fun k =>
    { body := #[.call [] decProc [.v (2 + k)]], term := .jump ⟨1 + 2 * k + 2, []⟩ }
  have hft := flatMap_two_getElem f g n j hj
  have hlen := flatMap_two_length f g n
  dsimp only [f, g] at hft hlen
  constructor
  · rw [show 1 + 2 * j = 2 * j + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [hlen]; omega)]
    simpa [show 2 * j + 1 = 1 + 2 * j by omega] using hft.1
  · rw [show 1 + 2 * j + 1 = (2 * j + 1) + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [hlen]; omega)]
    exact hft.2

private theorem mkResetUWrapper_ret (decProc n tag cls : Nat) :
    (mkResetUWrapper decProc (CellLayout.ofFields n tag) cls).blocks[1 + 2 * n]? =
      some { term := .ret [.v 0] } := by
  unfold mkResetUWrapper
  simp only [CellLayout.ofFields, List.getElem?_toArray, List.cons_append, List.nil_append]
  let f : Nat → Lir.Block := fun k =>
    { term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (k + 1)))) ⟨1 + 2 * k + 2, []⟩ ⟨1 + 2 * k + 1, []⟩ }
  let g : Nat → Lir.Block := fun k =>
    { body := #[.call [] decProc [.v (2 + k)]], term := .jump ⟨1 + 2 * k + 2, []⟩ }
  have hlen := flatMap_two_length f g n
  dsimp only [f, g] at hlen
  rw [show 1 + 2 * n = 2 * n + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen]; omega), hlen, Nat.sub_self]
  rfl

/-- Parameterized dead-field release loop shared by `mkResetWrapper` (`baseLabel = 2, regBase = 3`)
and `mkResetUWrapper` (`baseLabel = 1, regBase = 2`). -/
theorem decLoop_exec {P : Lir.Program} {wrapper decProc baseLabel regBase n mask : Nat}
    {fn : Lir.Func} {bfields : List RVal}
    (hfn : P.funcs[wrapper]? = some fn)
    (hdec : P.funcs[decProc]? = some Gen.dec)
    (hlen : bfields.length = n) (h61 : n ≤ 61) (hmask : mask < 2 ^ 61)
    (hbr : ∀ j < n, fn.blocks[baseLabel + 2 * j]? = some {
      term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (j + 1))))
        ⟨baseLabel + 2 * j + 2, []⟩ ⟨baseLabel + 2 * j + 1, []⟩ })
    (hcall : ∀ j < n, fn.blocks[baseLabel + 2 * j + 1]? = some {
      body := #[.call [] decProc [.v (regBase + j)]]
      term := .jump ⟨baseLabel + 2 * j + 2, []⟩ })
    (hretBlk : ∃ b, fn.blocks[baseLabel + 2 * n]? = some b ∧ b.params = [])
    {addresses : AddressMap} {external : Nat → Nat} {kept : List RVal}
    {context base bump limit : Lir.Word} {env : Lir.Env} {oldWords : Nat → Lir.Word}
    (hmaskEnv : env[1]? = some (UInt64.ofNat (2 * mask + 1)))
    (hregs : ∀ j < n, env[regBase + j]? = some (oldWords j))
    (hvals : ∀ j u, bfields[j]? = some u → valueWord addresses u = some (oldWords j))
    (callers : List Lir.Frame) :
    ∀ (k : Nat), k ≤ n → ∀ (H : Heap) (mem : X86.Memory)
      (slots : List Slot) (lists : Nat → List Lir.Word),
      let rem := ((bfields.drop (n - k)).zipIdx (n - k)).filterMap
        (fun (u, j) => if !Nat.testBit mask j then some u else none)
      Gen.AllocatorReady maxClass H addresses mem (holdRoots external (rem ++ kept))
        context base bump limit slots lists →
      ∃ H' mem' slots' lists' cost,
        dropAll H rem = some H' ∧
        Gen.AllocatorReady maxClass H' addresses mem' (holdRoots external kept)
          context base bump limit slots' lists' ∧
        Sem.Star (Lir.semStep P)
          { mem, ctx := context,
            stack := { fn := wrapper, label := baseLabel + 2 * (n - k), pos := 0, env } :: callers }
          cost
          { mem := mem', ctx := context,
            stack := { fn := wrapper, label := baseLabel + 2 * n, pos := 0, env } :: callers } := by
  intro k
  induction k with
  | zero =>
    intro _ H mem slots lists rem hready
    have hrem : rem = [] := by
      dsimp only [rem]
      rw [Nat.sub_zero, List.drop_eq_nil_iff.mpr (by omega)]
      rfl
    rw [hrem] at hready ⊢
    refine ⟨H, mem, slots, lists, 0, by simp [dropAll], by simpa using hready, ?_⟩
    simpa [Nat.sub_zero] using Sem.Star.refl _
  | succ k ih =>
    intro hk H mem slots lists rem hready
    let j := n - (k + 1)
    have hj : j < n := by omega
    have hj1 : n - k = j + 1 := by omega
    have hjB : j < bfields.length := by omega
    let u := bfields[j]
    have hdrop : bfields.drop j = u :: bfields.drop (j + 1) := List.drop_eq_getElem_cons hjB
    have hremEq : rem = (if !Nat.testBit mask j then [u] else []) ++
        ((bfields.drop (j + 1)).zipIdx (j + 1)).filterMap
          (fun (v, idx) => if !Nat.testBit mask idx then some v else none) := by
      dsimp only [rem]
      rw [show n - (k + 1) = j from rfl, hdrop, List.zipIdx_cons, List.filterMap_cons]
      cases Nat.testBit mask j <;> simp
    have hnextBlk : ∃ tb, fn.blocks[baseLabel + 2 * j + 2]? = some tb ∧ tb.params = [] := by
      by_cases hlt : j + 1 < n
      · have hb := hbr (j + 1) hlt
        rw [show baseLabel + 2 * (j + 1) = baseLabel + 2 * j + 2 by omega] at hb
        exact ⟨_, hb, rfl⟩
      · have heq : baseLabel + 2 * j + 2 = baseLabel + 2 * n := by omega
        simpa [heq] using hretBlk
    have htb := testBit_tagged_mask hmask (by omega : j < 61)
    cases hbit : Nat.testBit mask j with
    | true =>
      have hrem' : rem = ((bfields.drop (n - k)).zipIdx (n - k)).filterMap
          (fun (v, idx) => if !Nat.testBit mask idx then some v else none) := by
        rw [hremEq, hbit, ← hj1]; simp
      have hstep :
          Lir.step P
            { mem := mem, ctx := context,
              stack := { fn := wrapper, label := baseLabel + 2 * j, pos := 0, env } :: callers } =
          .next
            { mem := mem, ctx := context,
              stack := { fn := wrapper, label := baseLabel + 2 * (n - k), pos := 0, env } :: callers }
            false := by
        obtain ⟨tb, htbBlk, htbPar⟩ := hnextBlk
        have hholds : Lir.Cond.holds .tnz .w64 (UInt64.ofNat (2 * mask + 1)) (UInt64.ofNat (2 ^ (j + 1))) = true := by
          rw [htb, hbit]
        have hbrStep := Lir.br_at (p := P) (mem := mem) (ctx := context) (rest := callers)
          (pos := 0) (ρ := env) (ρ' := env)
          (va := UInt64.ofNat (2 * mask + 1)) (vb := UInt64.ofNat (2 ^ (j + 1)))
          (e := ⟨baseLabel + 2 * j + 2, []⟩) (vals := []) (tb := tb)
          hfn (hbr j hj) rfl rfl (by simp only [Lir.Arg.eval, hmaskEnv]) rfl
          (by rw [hholds]; rfl) rfl htbBlk (by simp [htbPar, Lir.bindParams])
        simpa [Lir.atState, show baseLabel + 2 * j + 2 = baseLabel + 2 * (n - k) by omega,
          show ¬ (baseLabel + 2 * (n - k) ≤ baseLabel + 2 * j) by omega] using hbrStep
      obtain ⟨H', mem', slots', lists', cost, hda, hready', hstar⟩ :=
        ih (by omega) H mem slots lists (by rw [← hrem']; exact hready)
      exact ⟨H', mem', slots', lists', cost, by rw [hrem']; exact hda, hready',
        by simpa using (Sem.Star.single (Lir.semStep_next.mpr hstep)).trans hstar⟩
    | false =>
      let remNext := ((bfields.drop (n - k)).zipIdx (n - k)).filterMap
        (fun (v, idx) => if !Nat.testBit mask idx then some v else none)
      have hrem' : rem = u :: remNext := by
        rw [hremEq, hbit, ← hj1]; simp [remNext]
      have hstep1 :
          Lir.step P
            { mem := mem, ctx := context,
              stack := { fn := wrapper, label := baseLabel + 2 * j, pos := 0, env } :: callers } =
          .next
            { mem := mem, ctx := context,
              stack := { fn := wrapper, label := baseLabel + 2 * j + 1, pos := 0, env } :: callers }
            false := by
        have hholds : Lir.Cond.holds .tnz .w64 (UInt64.ofNat (2 * mask + 1)) (UInt64.ofNat (2 ^ (j + 1))) = false := by
          rw [htb, hbit]
        have hbrStep := Lir.br_at (p := P) (mem := mem) (ctx := context) (rest := callers)
          (pos := 0) (ρ := env) (ρ' := env)
          (va := UInt64.ofNat (2 * mask + 1)) (vb := UInt64.ofNat (2 ^ (j + 1)))
          (e := ⟨baseLabel + 2 * j + 1, []⟩) (vals := [])
          hfn (hbr j hj) rfl rfl (by simp only [Lir.Arg.eval, hmaskEnv]) rfl
          (by rw [hholds]; rfl) rfl (hcall j hj) (by simp [Lir.bindParams])
        simpa [Lir.atState, show ¬ (baseLabel + 2 * j + 1 ≤ baseLabel + 2 * j) by omega] using hbrStep
      have henterDec : Lir.enter P decProc [oldWords j] =
          some { fn := decProc, label := 0, pos := 0, env := Gen.decEnv (oldWords j) } := by
        simp [Lir.enter, hdec, Gen.dec, Lir.bindParams, Gen.decEnv]
      let afterCall : Lir.Frame := { fn := wrapper, label := baseLabel + 2 * j + 1, pos := 1, env, dsts := [] }
      have hstep2 := Lir.step_call (p := P) (mem := mem) (ctx := context) (rest := callers)
        (fr := { fn := wrapper, label := baseLabel + 2 * j + 1, pos := 0, env })
        hfn (hcall j hj) (by simp) rfl (vs := [oldWords j])
        (by simp [Lir.evalArgs, Lir.Arg.eval, hregs j hj]) henterDec
      have hrebase : holdRoots external (rem ++ kept) =
          fun loc => holdRoots external (remNext ++ kept) loc + refsIn loc [u] := by
        funext loc
        rw [hrem']
        simp only [holdRoots, List.cons_append, refsIn_append, refsIn]; omega
      rw [hrebase] at hready
      have hvu : valueWord addresses u = some (oldWords j) :=
        hvals j u (List.getElem?_eq_getElem hjB)
      obtain ⟨H₁, mem₁, slots₁, lists₁, ch₁, hda₁, hready₁, hdecTrace⟩ :=
        hready.release_caller_ready (oldWords j) hvu P decProc hdec afterCall callers rfl
      have hstep3 : Lir.step P { mem := mem₁, ctx := context, stack := afterCall :: callers } =
          .next { mem := mem₁, ctx := context,
                  stack := { fn := wrapper, label := baseLabel + 2 * (n - k), pos := 0, env } :: callers } false := by
        obtain ⟨tb, htbBlk, htbPar⟩ := hnextBlk
        have hjp := Lir.jump_at (p := P) (mem := mem₁) (ctx := context) (rest := callers)
          (pos := 1) (ρ := env) (ρ' := env) (vals := []) (tb := tb) hfn (hcall j hj) (by simp) rfl rfl htbBlk
          (by simp [htbPar, Lir.bindParams])
        simpa [Lir.atState, afterCall, show baseLabel + 2 * j + 2 = baseLabel + 2 * (n - k) by omega,
          show ¬ (baseLabel + 2 * (n - k) ≤ baseLabel + 2 * j + 1) by omega] using hjp
      obtain ⟨H₂, mem₂, slots₂, lists₂, cost₂, hda₂, hready₂, hrest⟩ :=
        ih (by omega) H₁ mem₁ slots₁ lists₁ hready₁
      refine ⟨H₂, mem₂, slots₂, lists₂, 1 + ch₁ + cost₂, ?_, hready₂, ?_⟩
      · rw [hrem', dropAll_cons_eq, hda₁]; exact hda₂
      · have htot := (Sem.Star.single (Lir.semStep_next.mpr hstep1)).trans
          ((Sem.Star.single (Lir.semStep_next.mpr hstep2)).trans
            (hdecTrace.trans ((Sem.Star.single (Lir.semStep_next.mpr hstep3)).trans hrest)))
        simpa [afterCall, Nat.add_assoc] using htot

/-- Shared-path live-field increment loop of `mkResetWrapper` on a live cell `l`. -/
theorem sharedIncLoop_exec {P : Lir.Program} {wrapper isU incProc decProc cls mask : Nat}
    {ctor : Fir.CtorInfo}
    (hfn : P.funcs[wrapper]? = some (mkResetWrapper isU incProc decProc
      (CellLayout.ofFields ctor.arity ctor.tag) cls))
    (hinc : P.funcs[incProc]? = some Rt.Rc.Procs.inc)
    (h61 : ctor.arity ≤ 61) (hmask : mask < 2 ^ 61)
    {addresses : AddressMap} {external : Nat → Nat} {l : Nat} {a : Lir.Word} {b : Body}
    (ha : addresses l = some a) (hbctor : b.ctor = ctor)
    (hnobj : ctor.nobj = ctor.arity) (hlen : b.fields.length = ctor.arity)
    {context base bump limit : Lir.Word} {slots : List Slot} {lists : Nat → List Lir.Word}
    (callers : List Lir.Frame) :
    let n := ctor.arity
    let sharedBase := 3 + 2 * n
    ∀ (k : Nat), k ≤ n → ∀ (H : Heap) (mem : X86.Memory) (env : Lir.Env)
      (held : List RVal) (rc : Nat),
      env[0]? = some a →
      env[1]? = some (UInt64.ofNat (2 * mask + 1)) →
      H.cell? l = some (.live rc .dyn b) →
      Gen.AllocatorReady maxClass H addresses mem (holdRoots external held)
        context base bump limit slots lists →
      let rem := ((b.fields.drop (n - k)).zipIdx (n - k)).filterMap
        (fun (u, j) => if Nat.testBit mask j then some u else none)
      (∃ H' mem' env' cost rc',
        Own.Plain.incList H rem = some H' ∧
        H'.cell? l = some (.live rc' .dyn b) ∧
        env'[0]? = some a ∧
        Gen.AllocatorReady maxClass H' addresses mem' (holdRoots external (rem ++ held))
          context base bump limit slots lists ∧
        Sem.Star (Lir.semStep P)
          { mem, ctx := context,
            stack := { fn := wrapper, label := sharedBase + 2 * (n - k), pos := 0, env } :: callers }
          cost
          { mem := mem', ctx := context,
            stack := { fn := wrapper, label := sharedBase + 2 * n, pos := 0, env := env' } :: callers }) ∨
      Sem.Fails (Lir.semStep P)
        { mem, ctx := context,
          stack := { fn := wrapper, label := sharedBase + 2 * (n - k), pos := 0, env } :: callers } := by
  intro n sharedBase k
  induction k with
  | zero =>
    intro _ H mem env held rc h0 _ hcl hready rem
    have hrem : rem = [] := by
      dsimp only [rem]
      rw [Nat.sub_zero, List.drop_eq_nil_iff.mpr (by omega)]
      rfl
    rw [hrem]
    exact .inl ⟨H, mem, env, 0, rc, rfl, hcl, h0, by simpa using hready,
      by simpa [Nat.sub_zero] using Sem.Star.refl _⟩
  | succ k ih =>
    intro hk H mem env held rc h0 h1 hcl hready rem
    let j := n - (k + 1)
    have hj : j < n := by omega
    have hj1 : n - k = j + 1 := by omega
    have hjB : j < b.fields.length := by omega
    let u := b.fields[j]
    have hdrop : b.fields.drop j = u :: b.fields.drop (j + 1) := List.drop_eq_getElem_cons hjB
    have hblks := mkResetWrapper_shared_blocks isU incProc decProc ctor.arity ctor.tag cls j hj
    have hnextBlk : ∃ tb,
        (mkResetWrapper isU incProc decProc (CellLayout.ofFields ctor.arity ctor.tag) cls).blocks[sharedBase + 2 * j + 2]? =
          some tb ∧ tb.params = [] := by
      by_cases hlt : j + 1 < n
      · have hb := (mkResetWrapper_shared_blocks isU incProc decProc ctor.arity ctor.tag cls (j + 1) hlt).1
        rw [show 3 + 2 * ctor.arity + 2 * (j + 1) = sharedBase + 2 * j + 2 by omega] at hb
        exact ⟨_, hb, rfl⟩
      · have hb := mkResetWrapper_sharedRet isU incProc decProc ctor.arity ctor.tag cls
        rw [show 3 + 2 * ctor.arity + 2 * ctor.arity = sharedBase + 2 * j + 2 by omega] at hb
        exact ⟨_, hb, rfl⟩
    have htb := testBit_tagged_mask hmask (by omega : j < 61)
    have hremEq : rem = (if Nat.testBit mask j then [u] else []) ++
        ((b.fields.drop (j + 1)).zipIdx (j + 1)).filterMap
          (fun (v, idx) => if Nat.testBit mask idx then some v else none) := by
      dsimp only [rem]
      rw [show n - (k + 1) = j from rfl, hdrop, List.zipIdx_cons, List.filterMap_cons]
      cases Nat.testBit mask j <;> simp
    cases hbit : Nat.testBit mask j with
    | false =>
      have hrem' : rem = ((b.fields.drop (n - k)).zipIdx (n - k)).filterMap
          (fun (v, idx) => if Nat.testBit mask idx then some v else none) := by
        rw [hremEq, hbit, ← hj1]; simp
      have hstep :
          Lir.step P
            { mem := mem, ctx := context,
              stack := { fn := wrapper, label := sharedBase + 2 * j, pos := 0, env } :: callers } =
          .next
            { mem := mem, ctx := context,
              stack := { fn := wrapper, label := sharedBase + 2 * (n - k), pos := 0, env } :: callers }
            false := by
        obtain ⟨tb, htbBlk, htbPar⟩ := hnextBlk
        have hholds : Lir.Cond.holds .tnz .w64 (UInt64.ofNat (2 * mask + 1)) (UInt64.ofNat (2 ^ (j + 1))) = false := by
          rw [htb, hbit]
        have hbrStep := Lir.br_at (p := P) (mem := mem) (ctx := context) (rest := callers)
          (pos := 0) (ρ := env) (ρ' := env)
          (va := UInt64.ofNat (2 * mask + 1)) (vb := UInt64.ofNat (2 ^ (j + 1)))
          (e := ⟨sharedBase + 2 * j + 2, []⟩) (vals := []) (tb := tb)
          hfn hblks.1 rfl rfl (by simp only [Lir.Arg.eval, h1]) rfl
          (by rw [hholds]; rfl) rfl htbBlk (by simp [htbPar, Lir.bindParams])
        simpa [Lir.atState, sharedBase, n, show 3 + 2 * ctor.arity + 2 * j + 2 = 3 + 2 * ctor.arity + 2 * (ctor.arity - k) by omega,
          show ¬ (3 + 2 * ctor.arity + 2 * (ctor.arity - k) ≤ 3 + 2 * ctor.arity + 2 * j) by omega] using hbrStep
      rcases ih (by omega) H mem env held rc h0 h1 hcl hready with
        ⟨H', mem', env', cost, rc', hi, hcl', h0', hready', hstar⟩ | failed
      · exact .inl ⟨H', mem', env', cost, rc', by rw [hrem']; exact hi, hcl', h0',
          by rw [hrem']; exact hready',
          by simpa using (Sem.Star.single (Lir.semStep_next.mpr hstep)).trans hstar⟩
      · exact .inr (fails_prefix (Sem.Star.single (Lir.semStep_next.mpr hstep)) failed)
    | true =>
      let remNext := ((b.fields.drop (n - k)).zipIdx (n - k)).filterMap
        (fun (v, idx) => if Nat.testBit mask idx then some v else none)
      have hrem' : rem = u :: remNext := by rw [hremEq, hbit, ← hj1]; simp [remNext]
      have hstep1 :
          Lir.step P
            { mem := mem, ctx := context,
              stack := { fn := wrapper, label := sharedBase + 2 * j, pos := 0, env } :: callers } =
          .next
            { mem := mem, ctx := context,
              stack := { fn := wrapper, label := sharedBase + 2 * j + 1, pos := 0, env } :: callers }
            false := by
        have hholds : Lir.Cond.holds .tnz .w64 (UInt64.ofNat (2 * mask + 1)) (UInt64.ofNat (2 ^ (j + 1))) = true := by
          rw [htb, hbit]
        have hbrStep := Lir.br_at (p := P) (mem := mem) (ctx := context) (rest := callers)
          (pos := 0) (ρ := env) (ρ' := env)
          (va := UInt64.ofNat (2 * mask + 1)) (vb := UInt64.ofNat (2 ^ (j + 1)))
          (e := ⟨sharedBase + 2 * j + 1, []⟩) (vals := [])
          hfn hblks.1 rfl rfl (by simp only [Lir.Arg.eval, h1]) rfl
          (by rw [hholds]; rfl) rfl hblks.2 (by simp [Lir.bindParams])
        simpa [Lir.atState, sharedBase, n, show ¬ (3 + 2 * ctor.arity + 2 * j + 1 ≤ 3 + 2 * ctor.arity + 2 * j) by omega] using hbrStep
      obtain ⟨-, a0, ha0, cell0⟩ := hready.idle.live.cell l rc .dyn b hcl
      have ea0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
      have cell : Gen.LiveCell addresses mem a rc b := ea0 ▸ cell0
      obtain ⟨uw, huw, hwat⟩ := cell.scanned (List.getElem?_eq_getElem hjB) (by rw [hbctor, hnobj]; exact hj)
      have hloadW : Lir.loadWord mem .w64 .zero (fieldAddress a j) = some uw := by
        have haddr : fieldAddress a j = a + UInt64.ofNat (8 + 8 * j) := by
          simp [fieldAddress, show 8 * (j + 1) = 8 + 8 * j by omega]
        rw [haddr]
        simp only [Lir.loadWord, hwat.read64]
      let env1 := env.insert (3 + n + j) uw
      have hstep2 :
          Lir.step P
            { mem := mem, ctx := context,
              stack := { fn := wrapper, label := sharedBase + 2 * j + 1, pos := 0, env } :: callers } =
          .next
            { mem := mem, ctx := context,
              stack := { fn := wrapper, label := sharedBase + 2 * j + 1, pos := 1, env := env1 } :: callers }
            false := by
        apply Lir.step_stmt (fr := { fn := wrapper, label := sharedBase + 2 * j + 1, pos := 0, env })
          (s := .assign (3 + n + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) }))
          hfn hblks.2 (by simp) rfl rfl
        simp only [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Addr.eval, h0,
          UInt64.add_zero, bind, Option.bind]
        have hdisp : Lir.dispWord (Int.ofNat (8 * (j + 1))) = UInt64.ofNat (8 * (j + 1)) :=
          Lir.dispWord_ofNat (8 * (j + 1))
        rw [hdisp, show a + UInt64.ofNat (8 * (j + 1)) = fieldAddress a j from rfl, hloadW]
      have hperm : CanDup H u := by
        have hbal : Balance H external held := Gen.balance_idle.mp hready.idle.balance
        have hbrw : Own.Plain.BorrowVal H u := by
          cases hu : u with
          | lit _ | ctor0 _ | erased => trivial
          | loc k' =>
            have hle := refsIn_fields_le hcl k'
            have hmem : RVal.loc k' ∈ b.fields := by rw [← hu]; exact List.getElem_mem hjB
            have hp : 0 < refsIn k' b.fields := refsIn_pos hmem
            change 0 < edgeCount H k'; omega
        exact hbrw.canDup hbal
      have henterInc : Lir.enter P incProc [uw] =
          some { fn := incProc, label := 0, pos := 0, env := incEnv uw } := by
        simp [Lir.enter, hinc, Rt.Rc.Procs.inc, Lir.bindParams, incEnv]
      let afterInc : Lir.Frame := { fn := wrapper, label := sharedBase + 2 * j + 1, pos := 2, env := env1, dsts := [] }
      have hstep3 := Lir.step_call (p := P) (mem := mem) (ctx := context) (rest := callers)
        (fr := { fn := wrapper, label := sharedBase + 2 * j + 1, pos := 1, env := env1 })
        hfn hblks.2 (by simp) rfl (vs := [uw])
        (by simp [Lir.evalArgs, Lir.Arg.eval, env1, n]) henterInc
      have hpre := (Sem.Star.single (Lir.semStep_next.mpr hstep1)).trans
        ((Sem.Star.single (Lir.semStep_next.mpr hstep2)).trans
          (Sem.Star.single (Lir.semStep_next.mpr hstep3)))
      rcases inc_caller_ready hinc hready hperm huw afterInc callers rfl with
        ⟨H₁, mem₁, hi1, hready₁, hincTrace⟩ | hfail
      · obtain ⟨rc₁, hcl₁⟩ := inc_preserves_cell_body hcl hi1
        have hstep4 :
            Lir.step P { mem := mem₁, ctx := context, stack := afterInc :: callers } =
            .next
              { mem := mem₁, ctx := context,
                stack := { fn := wrapper, label := sharedBase + 2 * (n - k), pos := 0, env := env1 } :: callers }
              false := by
          obtain ⟨tb, htbBlk, htbPar⟩ := hnextBlk
          have hjp := Lir.jump_at (p := P) (mem := mem₁) (ctx := context) (rest := callers)
            (pos := 2) (ρ := env1) (ρ' := env1) (vals := []) (tb := tb) hfn hblks.2 (by simp) rfl rfl htbBlk
            (by simp [htbPar, Lir.bindParams])
          simpa [Lir.atState, afterInc, sharedBase, n,
            show 3 + 2 * ctor.arity + 2 * j + 2 = 3 + 2 * ctor.arity + 2 * (ctor.arity - k) by omega,
            show ¬ (3 + 2 * ctor.arity + 2 * (ctor.arity - k) ≤ 3 + 2 * ctor.arity + 2 * j + 1) by omega] using hjp
        have h0' : env1[0]? = some a := by rw [Lir.env_insert_ne _ _ (by omega)]; exact h0
        have h1' : env1[1]? = some (UInt64.ofNat (2 * mask + 1)) := by
          rw [Lir.env_insert_ne _ _ (by omega)]; exact h1
        have hpreFull := hpre.trans (hincTrace.trans (Sem.Star.single (Lir.semStep_next.mpr hstep4)))
        rcases ih (by omega) H₁ mem₁ env1 (u :: held) rc₁ h0' h1' hcl₁ hready₁ with
          ⟨H₂, mem₂, env₂, cost₂, rc₂, hi2, hcl₂, h0₂, hready₂, hrest⟩ | failed
        · have hrootEq : holdRoots external (remNext ++ u :: held) =
              holdRoots external (rem ++ held) := by
            funext loc; rw [hrem']; simp only [holdRoots, List.cons_append, refsIn_append, refsIn]; omega
          refine .inl ⟨H₂, mem₂, env₂, 1 + cost₂, rc₂, ?_, hcl₂, h0₂,
            by rw [← hrootEq]; exact hready₂, ?_⟩
          · rw [hrem']; simp only [Own.Plain.incList, hi1]; exact hi2
          · simpa [afterInc, Nat.add_assoc] using hpreFull.trans hrest
        · exact .inr (fails_prefix hpreFull failed)
      · exact .inr (fails_prefix hpre (reaches_resource_fails hfail))

/-- Shared-path loop with `mask = 0`: skips all `n` iterations with zero loads or `inc` calls
(used for `.ctor0` / immediate scrutinee). -/
theorem sharedIncLoop_maskZero_exec {P : Lir.Program} {wrapper isU incProc decProc cls : Nat}
    {ctor : Fir.CtorInfo}
    (hfn : P.funcs[wrapper]? = some (mkResetWrapper isU incProc decProc
      (CellLayout.ofFields ctor.arity ctor.tag) cls))
    (h61 : ctor.arity ≤ 61)
    {mem : X86.Memory} {context : Lir.Word} {env : Lir.Env}
    (h1 : env[1]? = some 1) (callers : List Lir.Frame) :
    let n := ctor.arity
    let sharedBase := 3 + 2 * n
    ∀ (k : Nat), k ≤ n →
      Sem.Star (Lir.semStep P)
        { mem, ctx := context,
          stack := { fn := wrapper, label := sharedBase + 2 * (n - k), pos := 0, env } :: callers } 0
        { mem, ctx := context,
          stack := { fn := wrapper, label := sharedBase + 2 * n, pos := 0, env } :: callers } := by
  intro n sharedBase k
  induction k with
  | zero =>
    intro _; simpa [Nat.sub_zero] using Sem.Star.refl _
  | succ k ih =>
    intro hk
    let j := n - (k + 1)
    have hj : j < n := by omega
    have htb := testBit_tagged_mask (mask := 0) (j := j) (by decide) (by omega)
    have hholds : Lir.Cond.holds .tnz .w64 1 (UInt64.ofNat (2 ^ (j + 1))) = false := by
      simpa using htb
    have hblk := (mkResetWrapper_shared_blocks isU incProc decProc ctor.arity ctor.tag cls j hj).1
    have hnextBlk : ∃ tb,
        (mkResetWrapper isU incProc decProc (CellLayout.ofFields ctor.arity ctor.tag) cls).blocks[sharedBase + 2 * j + 2]? =
          some tb ∧ tb.params = [] := by
      by_cases hlt : j + 1 < n
      · have hb := (mkResetWrapper_shared_blocks isU incProc decProc ctor.arity ctor.tag cls (j + 1) hlt).1
        rw [show 3 + 2 * ctor.arity + 2 * (j + 1) = sharedBase + 2 * j + 2 by omega] at hb
        exact ⟨_, hb, rfl⟩
      · have hb := mkResetWrapper_sharedRet isU incProc decProc ctor.arity ctor.tag cls
        rw [show 3 + 2 * ctor.arity + 2 * ctor.arity = sharedBase + 2 * j + 2 by omega] at hb
        exact ⟨_, hb, rfl⟩
    have hstep :
        Lir.step P
          { mem := mem, ctx := context,
            stack := { fn := wrapper, label := sharedBase + 2 * j, pos := 0, env } :: callers } =
        .next
          { mem := mem, ctx := context,
            stack := { fn := wrapper, label := sharedBase + 2 * (n - k), pos := 0, env } :: callers }
          false := by
      obtain ⟨tb, htbBlk, htbPar⟩ := hnextBlk
      have hbrStep := Lir.br_at (p := P) (mem := mem) (ctx := context) (rest := callers)
        (pos := 0) (ρ := env) (ρ' := env)
        (va := 1) (vb := UInt64.ofNat (2 ^ (j + 1)))
        (e := ⟨sharedBase + 2 * j + 2, []⟩) (vals := []) (tb := tb)
        hfn hblk rfl rfl (by simp only [Lir.Arg.eval, h1]) rfl
        (by rw [hholds]; rfl) rfl htbBlk (by simp [htbPar, Lir.bindParams])
      simpa [Lir.atState, sharedBase, n,
        show 3 + 2 * ctor.arity + 2 * j + 2 = 3 + 2 * ctor.arity + 2 * (ctor.arity - k) by omega,
        show ¬ (3 + 2 * ctor.arity + 2 * (ctor.arity - k) ≤ 3 + 2 * ctor.arity + 2 * j) by omega] using hbrStep
    simpa using (Sem.Star.single (Lir.semStep_next.mpr hstep)).trans (ih (by omega))

/-- Execute the unique-cell body (`loadOld ++ writeShell`, `decLoop_exec`, `bRet`) shared by
`mkResetWrapper` (starting at block 1, `regBase = 3`) and `mkResetUWrapper` (starting at block 0,
`regBase = 2`). -/
theorem reset_unique_body_exec {P : Lir.Program} {wrapper decProc loadBlk decBase regBase dst mask : Nat}
    {fn : Lir.Func} {ctor : Fir.CtorInfo} {cls : Nat}
    (hfn : P.funcs[wrapper]? = some fn)
    (hdec : P.funcs[decProc]? = some Gen.dec)
    (hbase2 : 2 ≤ regBase) (hdecBase : decBase = loadBlk + 1)
    (hvc : Own.Plain.Ctx.validReuseCtor ctor = some cls) (hmask : mask < 2 ^ 61)
    (hloadBlk : fn.blocks[loadBlk]? = some {
      body := ((List.range ctor.arity).map (fun j =>
          Lir.Stmt.assign (regBase + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })) ++
        Lir.Stmt.store .w64 { base := some (.v 0), disp := 0 }
          (.imm (dynamicHeader ctor.arity cls ctor.tag 1)) ::
        (List.range ctor.arity).map (fun j =>
          Lir.Stmt.store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.imm 1))).toArray
      term := .jump ⟨decBase, []⟩ })
    (hbr : ∀ j < ctor.arity, fn.blocks[decBase + 2 * j]? = some {
      term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (j + 1))))
        ⟨decBase + 2 * j + 2, []⟩ ⟨decBase + 2 * j + 1, []⟩ })
    (hcall : ∀ j < ctor.arity, fn.blocks[decBase + 2 * j + 1]? = some {
      body := #[.call [] decProc [.v (regBase + j)]]
      term := .jump ⟨decBase + 2 * j + 2, []⟩ })
    (hretBlk : fn.blocks[decBase + 2 * ctor.arity]? = some { term := .ret [.v 0] })
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {l : Nat} {a : Lir.Word} {b : Body} {rest : List RVal}
    {context base bump limit : Lir.Word} {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (holdRoots external (.loc l :: rest)) context base bump limit slots lists)
    (hc : H.cell? l = some (.live 1 .dyn b)) (ha : addresses l = some a) (hbctor : b.ctor = ctor)
    {env : Lir.Env}
    (h0 : env[0]? = some a) (h1 : env[1]? = some (UInt64.ofNat (2 * mask + 1)))
    (caller : Lir.Frame) (callers : List Lir.Frame) (hdst : caller.dsts = [dst]) :
    let deadFields := b.fields.zipIdx.filterMap (fun (u, j) => if !Nat.testBit mask j then some u else none)
    let liveFields := b.fields.zipIdx.filterMap (fun (u, j) => if Nat.testBit mask j then some u else none)
    ∃ H₁ H₂ mem' slots' lists' cost,
      reuseCell H l (Own.Plain.resetShell ctor) = some (.loc H.size, H₁) ∧
      dropAll H₁ deadFields = some H₂ ∧
      Gen.AllocatorReady maxClass H₂ (placeFresh addresses H.size a) mem'
        (holdRoots external (.loc H.size :: (liveFields ++ rest)))
        context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep P)
        { mem, ctx := context, stack := { fn := wrapper, label := loadBlk, pos := 0, env } :: caller :: callers }
        cost
        { mem := mem', ctx := context,
          stack := { caller with env := caller.env.insert dst a, dsts := [] } :: callers } := by
  intro deadFields liveFields
  obtain ⟨hpos, h61, _, _, hnsc, hnobj, hfk, hlayC, hokC, _, hclsC, _⟩ := validReuseCtor_full hvc
  obtain ⟨-, a0, ha0, cell0⟩ := ready.idle.live.cell l 1 .dyn b hc
  have ea0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
  have cell : Gen.LiveCell addresses mem a 1 b := ea0 ▸ cell0
  have hblen : b.fields.length = ctor.arity := by
    have := cell.arity; rw [hbctor, hnobj, hnsc] at this; omega
  -- Extract the word for every scanned field of `b`.
  have hfieldWords : ∀ j < ctor.arity, ∃ w,
      valueWord addresses b.fields[j]! = some w ∧
      Lir.loadWord mem .w64 .zero (fieldAddress a j) = some w := by
    intro j hj
    have hjB : j < b.fields.length := by omega
    obtain ⟨w, hw, hwat⟩ := cell.scanned (List.getElem?_eq_getElem hjB) (by rw [hbctor, hnobj]; exact hj)
    have hbang : b.fields[j]! = b.fields[j] := by simp [hjB]
    refine ⟨w, by rwa [hbang], ?_⟩
    have haddr : fieldAddress a j = a + UInt64.ofNat (8 + 8 * j) := by
      simp [fieldAddress, show 8 * (j + 1) = 8 + 8 * j by omega]
    rw [haddr]; simp only [Lir.loadWord, hwat.read64]
  let oldWords : Nat → Lir.Word := fun j =>
    if hj : j < ctor.arity then (Classical.choose (hfieldWords j hj)) else 0
  have holdSpec : ∀ j (hj : j < ctor.arity),
      valueWord addresses b.fields[j]! = some (oldWords j) ∧
      Lir.loadWord mem .w64 .zero (fieldAddress a j) = some (oldWords j) := by
    intro j hj; simp only [oldWords, hj, ↓reduceDIte]
    exact Classical.choose_spec (hfieldWords j hj)
  -- Step 1: Execute `loadOld`.
  obtain ⟨env', hloadEx, hloadKeep, hloadSet⟩ := loadOld_exec (List.range ctor.arity) regBase hbase2
    a oldWords mem context (fun j hj => (holdSpec j (List.mem_range.mp hj)).2) List.nodup_range env h0
  have h0' : env'[0]? = some a := by
    rw [hloadKeep 0 (fun j _ => by omega)]; exact h0
  have h1' : env'[1]? = some (UInt64.ofNat (2 * mask + 1)) := by
    rw [hloadKeep 1 (fun j _ => by omega)]; exact h1
  -- Step 2: Execute `writeShell` matching `Gen.writeCell ... (resetShell ctor) cls`.
  have hlenBytes : 8 * (1 + (Own.Plain.resetShell ctor).fields.length) ≤ Gen.cellBytesOf b.ctor := by
    have h1 := (Gen.cellBytesOf_le hokC).2.1
    rw [hbctor]; simp only [Own.Plain.resetShell, List.length_replicate] at h1 ⊢; omega
  obtain ⟨hhdrW, hpayW⟩ := liveCell_writable_header_fields cell hlenBytes
  have hshellFw : ∀ j u, (Own.Plain.resetShell ctor).fields[j]? = some u →
      Gen.fieldWord addresses ctor j u = some 1 := by
    intro j u hj
    simp only [Own.Plain.resetShell, List.getElem?_replicate] at hj
    split at hj
    · rename_i hlt; cases hj; simp [Gen.fieldWord, hnobj, hlt, valueWord]
    · cases hj
  have hwriteEx := writeHeader_and_fields_exec (addresses := addresses) (b := Own.Plain.resetShell ctor)
    (cls := cls) (env := env') (mem := mem) (ctx := context) (words := fun _ => 1)
    (valArg := fun _ => .imm 1) h0' (by simp [Own.Plain.resetShell, hnobj])
    (fun _ _ => rfl) hshellFw hhdrW hpayW
  have hwriteEx' : Lir.execList env' mem context
      (Lir.Stmt.store .w64 { base := some (.v 0), disp := 0 } (.imm (dynamicHeader ctor.arity cls ctor.tag 1)) ::
        (List.range ctor.arity).map fun j =>
          Lir.Stmt.store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.imm 1)) =
      some (env', Gen.writeCell mem addresses a (Own.Plain.resetShell ctor) cls) := by
    simpa [Own.Plain.resetShell, hnobj] using hwriteEx
  have hcombEx : Lir.execList env mem context
      ((List.range ctor.arity).map (fun j =>
          Lir.Stmt.assign (regBase + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })) ++
        Lir.Stmt.store .w64 { base := some (.v 0), disp := 0 } (.imm (dynamicHeader ctor.arity cls ctor.tag 1)) ::
        (List.range ctor.arity).map fun j =>
          Lir.Stmt.store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.imm 1)) =
      some (env', Gen.writeCell mem addresses a (Own.Plain.resetShell ctor) cls) := by
    rw [execList_append, hloadEx]; exact hwriteEx'
  have hstmts := Lir.star_stmts (p := P) (ctx := context) (rest := caller :: callers) (dsts := [])
    hfn hloadBlk (pre := []) (post := []) (by simp) (by
      intro s hs
      rcases List.mem_append.mp hs with hL | hR
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hL; rfl
      · rcases List.mem_cons.mp hR with rfl | hR'
        · rfl
        · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hR'; rfl) hcombEx
  have hdecStartBlk : fn.blocks[decBase]? = some {
      term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ 1)))
        ⟨decBase + 2, []⟩ ⟨decBase + 1, []⟩ } := by
    simpa using hbr 0 hpos
  let loadLen : Nat :=
    ((List.range ctor.arity).map (fun j =>
        Lir.Stmt.assign (regBase + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })) ++
      Lir.Stmt.store .w64 { base := some (.v 0), disp := 0 } (.imm (dynamicHeader ctor.arity cls ctor.tag 1)) ::
      (List.range ctor.arity).map fun j =>
        Lir.Stmt.store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.imm 1)).length
  have hjump1 :
      Lir.step P
        { mem := Gen.writeCell mem addresses a (Own.Plain.resetShell ctor) cls,
          ctx := context,
          stack := { fn := wrapper, label := loadBlk, pos := loadLen, env := env' } :: caller :: callers } =
      .next
        { mem := Gen.writeCell mem addresses a (Own.Plain.resetShell ctor) cls,
          ctx := context,
          stack := { fn := wrapper, label := decBase, pos := 0, env := env' } :: caller :: callers }
        false := by
    have hjp := Lir.jump_at (p := P)
      (mem := Gen.writeCell mem addresses a (Own.Plain.resetShell ctor) cls)
      (ctx := context) (rest := caller :: callers) (pos := loadLen) (ρ := env') (ρ' := env') (vals := [])
      hfn hloadBlk (by simp [loadLen]) rfl rfl hdecStartBlk (by simp [Lir.bindParams])
    simpa [Lir.atState, hdecBase, show ¬ (loadBlk + 1 ≤ loadBlk) by omega] using hjp
  -- Step 3: Apply `Gen.inPlace_ready` for `resetShell ctor` with `kept := b.fields ++ rest`.
  have hrefsRepErased : ∀ (k n : Nat), refsIn k (List.replicate n RVal.erased) = 0 := by
    intro k n; induction n with
    | zero => rfl
    | succ m ih => simp [List.replicate, refsIn, ih]
  have hmassSimple : ∀ k, refsIn k (b.fields ++ rest) =
      refsIn k ((Own.Plain.resetShell ctor).fields ++ (b.fields ++ rest)) := by
    intro k
    simp only [Own.Plain.resetShell, refsIn_append, hrefsRepErased, Nat.zero_add]
  obtain ⟨H₁, slots₁, hrc, hready₁⟩ := Gen.inPlace_ready (b' := Own.Plain.resetShell ctor)
    (kept := b.fields ++ rest) ready hc ha hokC
    (by simp [Own.Plain.resetShell, hnobj, hnsc])
    (by dsimp only [Own.Plain.resetShell]; rw [hnobj]; exact hfk)
    (by dsimp only [Own.Plain.resetShell]; rw [hbctor])
    hmassSimple (fun j u hj => by dsimp only [Own.Plain.resetShell] at hj ⊢; rw [hshellFw j u hj]; rfl)
  rw [hbctor, hclsC] at hready₁
  have hrebase₁ : (fun k => external k + refsIn k (.loc H.size :: (b.fields ++ rest))) =
      holdRoots external (deadFields ++ (.loc H.size :: (liveFields ++ rest))) := by
    funext k
    have hpart := Own.Plain.refsIn_zipIdx_partition mask b.fields 0 k
    simp only [holdRoots, refsIn_append, refsIn, deadFields, liveFields] at hpart ⊢
    omega
  rw [hrebase₁] at hready₁
  change Gen.AllocatorReady maxClass H₁ (placeFresh addresses H.size a)
    (Gen.writeCell mem addresses a (Own.Plain.resetShell ctor) cls)
    (holdRoots external (deadFields ++ (.loc H.size :: (liveFields ++ rest))))
    context base bump limit slots₁ lists at hready₁
  -- Every old field location is `< H.size`, so `placeFresh addresses H.size a` preserves its word.
  have hvalsNew : ∀ j u, b.fields[j]? = some u →
      valueWord (placeFresh addresses H.size a) u = some (oldWords j) := by
    intro j u hj
    have hlt : j < ctor.arity := by have := (List.getElem?_eq_some_iff.mp hj).1; omega
    have hu : u = b.fields[j]! := by
      have hjB : j < b.fields.length := by omega
      rw [List.getElem?_eq_getElem hjB] at hj
      cases hj; simp [hjB]
    have hbound : Own.Plain.Bounded H.size u := by
      cases u with
      | lit _ | ctor0 _ | erased => trivial
      | loc k =>
        obtain ⟨_, _, hck⟩ := ready.idle.live.fields_live l 1 b k hc (List.mem_of_getElem? hj)
        exact Own.Proof.cell?_some hck
    rw [placeFresh_old hbound, hu]
    exact (holdSpec j hlt).1
  -- Step 4: Run `decLoop_exec` from `k = ctor.arity` down to `0`.
  obtain ⟨H₂, mem₂, slots₂, lists₂, costLoop, hda, hready₂, hloopTrace⟩ :=
    decLoop_exec (addresses := placeFresh addresses H.size a)
      (external := external) (kept := .loc H.size :: (liveFields ++ rest))
      hfn hdec hblen h61 hmask hbr hcall ⟨_, hretBlk, rfl⟩ h1'
      (fun j hj => hloadSet j (List.mem_range.mpr hj)) hvalsNew (caller :: callers)
      ctor.arity (Nat.le_refl _) H₁ (Gen.writeCell mem addresses a (Own.Plain.resetShell ctor) cls)
      slots₁ lists (by simpa [deadFields] using hready₁)
  -- Step 5: Execute `bRet` (`ret [.v 0]`).
  have hret := Lir.step_ret_caller (p := P) (vals := [a]) (ρ := caller.env.insert dst a)
    (mem := mem₂) (ctx := context)
    (fr := { fn := wrapper, label := decBase + 2 * ctor.arity, pos := 0, env := env' })
    (caller := caller) (rest' := callers) hfn hretBlk rfl rfl
    (by simp [Lir.evalArgs, Lir.Arg.eval, h0']) (by simp [hdst, Lir.bindParams])
  refine ⟨H₁, H₂, mem₂, slots₂, lists₂, costLoop, hrc, by simpa [deadFields] using hda, hready₂, ?_⟩
  have hstmts' : Sem.Star (Lir.semStep P)
      { mem, ctx := context, stack := { fn := wrapper, label := loadBlk, pos := 0, env } :: caller :: callers } 0
      { mem := Gen.writeCell mem addresses a (Own.Plain.resetShell ctor) cls, ctx := context,
        stack := { fn := wrapper, label := loadBlk, pos := loadLen, env := env' } :: caller :: callers } := by
    simpa [loadLen] using hstmts
  have hloopTrace' : Sem.Star (Lir.semStep P)
      { mem := Gen.writeCell mem addresses a (Own.Plain.resetShell ctor) cls, ctx := context,
        stack := { fn := wrapper, label := decBase, pos := 0, env := env' } :: caller :: callers }
      costLoop
      { mem := mem₂, ctx := context,
        stack := { fn := wrapper, label := decBase + 2 * ctor.arity, pos := 0, env := env' } :: caller :: callers } := by
    simpa using hloopTrace
  have hall := hstmts'.trans ((Sem.Star.single (Lir.semStep_next.mpr hjump1)).trans
    (hloopTrace'.trans (Sem.Star.single (Lir.semStep_next.mpr hret))))
  simpa using hall

/-! ## Top-level entry lemmas for `reuse` and `reset` wrappers -/

/-- Execute `mkReuseUWrapper` (`uniq = true`) or `mkReuseWrapper` (`uniq = false`) starting at
block 0 on a unique live shell `l` of matching size class `cls`, returning `a` in place. -/
theorem reuse_wrapper_inplace_exec {P : Lir.Program} {wrapper allocProc dst : Nat}
    {uniq : Bool} {ctor : Fir.CtorInfo} {cls : Nat}
    (hfn : P.funcs[wrapper]? = some (if uniq
      then mkReuseUWrapper (CellLayout.ofFields ctor.arity ctor.tag) cls
      else mkReuseWrapper allocProc (CellLayout.ofFields ctor.arity ctor.tag) cls))
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {l : Nat} {a : Lir.Word} {b : Body}
    {vs rest : List RVal} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (fun k => external k + refsIn k (.loc l :: (vs ++ rest)))
      context base bump limit slots lists)
    (hc : H.cell? l = some (.live 1 .dyn b)) (ha : addresses l = some a)
    (hbfZero : ∀ k, refsIn k b.fields = 0)
    (hvc : Own.Plain.Ctx.validReuseCtor ctor = some cls)
    (hclsB : Gen.classOf b.ctor = cls)
    (harity : vs.length = ctor.arity)
    {env : Lir.Env} {words : Nat → Lir.Word}
    (hptr : env[0]? = some a)
    (hregs : ∀ j < ctor.arity, env[j + 1]? = some (words j))
    (hvals : ∀ j u, vs[j]? = some u → valueWord addresses u = some (words j))
    (caller : Lir.Frame) (callers : List Lir.Frame) (hdst : caller.dsts = [dst]) :
    ∃ H' slots',
      reuseCell H l { ctor, fields := vs } = some (.loc H.size, H') ∧
      Gen.AllocatorReady maxClass H' (placeFresh addresses H.size a)
        (Gen.writeCell mem addresses a { ctor, fields := vs } cls)
        (fun k => external k + refsIn k (.loc H.size :: rest))
        context base bump limit slots' lists ∧
      Sem.Star (Lir.semStep P)
        { mem, ctx := context, stack := { fn := wrapper, label := 0, pos := 0, env } :: caller :: callers } 0
        { mem := Gen.writeCell mem addresses a { ctor, fields := vs } cls, ctx := context,
          stack := { caller with env := caller.env.insert dst a, dsts := [] } :: callers } := by
  cases uniq with
  | true =>
    simp only [↓reduceIte] at hfn
    exact reuse_inplace_block_exec hfn rfl rfl ready hc ha hbfZero hvc hclsB harity
      hptr hregs hvals caller callers hdst
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hfn
    obtain ⟨-, a0, ha0, cell0⟩ := ready.idle.live.cell l 1 .dyn b hc
    have ea0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
    have cell : Gen.LiveCell addresses mem a 1 b := ea0 ▸ cell0
    have hblk0 : (mkReuseWrapper allocProc (CellLayout.ofFields ctor.arity ctor.tag) cls).blocks[0]? =
        some { term := .br .tnz .w64 (.v 0) (.imm 1) ⟨2, []⟩ ⟨1, []⟩ } := rfl
    have hblk1 : (mkReuseWrapper allocProc (CellLayout.ofFields ctor.arity ctor.tag) cls).blocks[1]? =
        some {
          body := (Lir.Stmt.store .w64 { base := some (.v 0), disp := 0 }
              (.imm (dynamicHeader (CellLayout.ofFields ctor.arity ctor.tag).nobj cls
                (CellLayout.ofFields ctor.arity ctor.tag).tag 1)) ::
            (List.range (CellLayout.ofFields ctor.arity ctor.tag).nobj).map fun j =>
              Lir.Stmt.store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.v (j + 1))).toArray
          term := .ret [.v 0] } := rfl
    have hbr := Lir.br_at (p := P) (mem := mem) (ctx := context) (rest := caller :: callers)
      (pos := 0) (ρ := env) (ρ' := env) (va := a) (vb := 1) (e := ⟨1, []⟩) (vals := [])
      hfn hblk0 rfl rfl (by simp only [Lir.Arg.eval, hptr]) rfl
      (by rw [cell.pointer_branch]; rfl) rfl hblk1 (by simp [Lir.bindParams])
    obtain ⟨H', slots', hrc, hready', hstar⟩ :=
      reuse_inplace_block_exec hfn rfl hblk1 ready hc ha hbfZero hvc hclsB harity
        hptr hregs hvals caller callers hdst
    exact ⟨H', slots', hrc, hready',
      by simpa [Lir.atState] using (Sem.Star.single (Lir.semStep_next.mpr hbr)).trans hstar⟩

/-- Execute `mkReuseWrapper` starting at block 0 on `.erased` (`v0 = 1`), falling back to fresh
allocation (either publishing a fresh cell or failing with `.resource .heap`). -/
theorem reuse_wrapper_fallback_exec {P : Lir.Program} {wrapper allocProc dst : Nat}
    {ctor : Fir.CtorInfo} {cls : Nat}
    (hfn : P.funcs[wrapper]? = some (mkReuseWrapper allocProc (CellLayout.ofFields ctor.arity ctor.tag) cls))
    (halloc : P.funcs[allocProc]? = some (Gen.alloc (CellLayout.ofFields ctor.arity ctor.tag)))
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {vs : List RVal} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (fun k => external k + refsIn k vs) context base bump limit slots lists)
    (hvc : Own.Plain.Ctx.validReuseCtor ctor = some cls)
    (harity : vs.length = ctor.arity)
    {env : Lir.Env} {words : Nat → Lir.Word}
    (herased : env[0]? = some 1)
    (hregs : ∀ j < ctor.arity, env[j + 1]? = some (words j))
    (hvals : ∀ j u, vs[j]? = some u → valueWord addresses u = some (words j))
    (caller : Lir.Frame) (callers : List Lir.Frame) (hdst : caller.dsts = [dst]) :
    (∃ address next finalMem finalSlots finalLists,
      Gen.AllocatorReady maxClass (H.alloc .rc { ctor, fields := vs }).2
        (placeFresh addresses H.size address) finalMem
        (fun k => external k + refsIn k [(H.alloc .rc { ctor, fields := vs }).1])
        context base next limit finalSlots finalLists ∧
      Sem.Star (Lir.semStep P)
        { mem, ctx := context, stack := { fn := wrapper, label := 0, pos := 0, env } :: caller :: callers } 1
        { mem := finalMem, ctx := context,
          stack := { caller with env := caller.env.insert dst address, dsts := [] } :: callers }) ∨
    Sem.Reaches (Lir.semStep P)
      { mem, ctx := context, stack := { fn := wrapper, label := 0, pos := 0, env } :: caller :: callers }
      1 (.resource .heap) := by
  have hblk0 : (mkReuseWrapper allocProc (CellLayout.ofFields ctor.arity ctor.tag) cls).blocks[0]? =
      some { term := .br .tnz .w64 (.v 0) (.imm 1) ⟨2, []⟩ ⟨1, []⟩ } := rfl
  have hblk2 : (mkReuseWrapper allocProc (CellLayout.ofFields ctor.arity ctor.tag) cls).blocks[2]? =
      some {
        body := (Lir.Stmt.call [ctor.arity + 1] allocProc [] ::
          (List.range ctor.arity).map fun j =>
            Lir.Stmt.store .w64 { base := some (.v (ctor.arity + 1)), disp := Int.ofNat (8 * (j + 1)) }
              (.v (j + 1))).toArray
        term := .ret [.v (ctor.arity + 1)]
        cold := true } := rfl
  have hbr := Lir.br_at (p := P) (mem := mem) (ctx := context) (rest := caller :: callers)
    (pos := 0) (ρ := env) (ρ' := env) (va := 1) (vb := 1) (e := ⟨2, []⟩) (vals := [])
    hfn hblk0 rfl rfl (by simp only [Lir.Arg.eval, herased]) rfl
    (by decide) rfl hblk2 (by simp [Lir.bindParams])
  rcases reuse_fallback_block_exec hfn halloc ready hvc harity hregs hvals caller callers hdst with
    ⟨address, next, finalMem, finalSlots, finalLists, hready', hstar⟩ | hfail
  · exact .inl ⟨address, next, finalMem, finalSlots, finalLists, hready',
      by simpa [Lir.atState] using (Sem.Star.single (Lir.semStep_next.mpr hbr)).trans hstar⟩
  · exact .inr (by simpa [Lir.atState] using Sem.Reaches.star (Sem.Star.single (Lir.semStep_next.mpr hbr)) hfail)

/-- Execute `mkResetUWrapper` (`uniq = true`) or `mkResetWrapper` (`uniq = false`) starting at
block 0 on a unique live cell `l` (`rc = 1, mode = .dyn`). -/
theorem reset_wrapper_unique_exec {P : Lir.Program} {wrapper isU incProc decProc dst mask : Nat}
    {uniq : Bool} {ctor : Fir.CtorInfo} {cls : Nat}
    (hfn : P.funcs[wrapper]? = some (if uniq
      then mkResetUWrapper decProc (CellLayout.ofFields ctor.arity ctor.tag) cls
      else mkResetWrapper isU incProc decProc (CellLayout.ofFields ctor.arity ctor.tag) cls))
    (hisU : P.funcs[isU]? = some Gen.isUnique)
    (hdec : P.funcs[decProc]? = some Gen.dec)
    (hvc : Own.Plain.Ctx.validReuseCtor ctor = some cls) (hmask : mask < 2 ^ 61)
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {l : Nat} {a : Lir.Word} {b : Body} {rest : List RVal}
    {context base bump limit : Lir.Word} {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (holdRoots external (.loc l :: rest)) context base bump limit slots lists)
    (hc : H.cell? l = some (.live 1 .dyn b)) (ha : addresses l = some a) (hbctor : b.ctor = ctor)
    {env : Lir.Env}
    (h0 : env[0]? = some a) (h1 : env[1]? = some (UInt64.ofNat (2 * mask + 1)))
    (caller : Lir.Frame) (callers : List Lir.Frame) (hdst : caller.dsts = [dst]) :
    let deadFields := b.fields.zipIdx.filterMap (fun (u, j) => if !Nat.testBit mask j then some u else none)
    let liveFields := b.fields.zipIdx.filterMap (fun (u, j) => if Nat.testBit mask j then some u else none)
    ∃ H₁ H₂ mem' slots' lists' cost,
      reuseCell H l (Own.Plain.resetShell ctor) = some (.loc H.size, H₁) ∧
      dropAll H₁ deadFields = some H₂ ∧
      Gen.AllocatorReady maxClass H₂ (placeFresh addresses H.size a) mem'
        (holdRoots external (.loc H.size :: (liveFields ++ rest)))
        context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep P)
        { mem, ctx := context, stack := { fn := wrapper, label := 0, pos := 0, env } :: caller :: callers }
        cost
        { mem := mem', ctx := context,
          stack := { caller with env := caller.env.insert dst a, dsts := [] } :: callers } := by
  cases uniq with
  | true =>
    simp only [↓reduceIte] at hfn
    exact reset_unique_body_exec hfn hdec (by omega) rfl hvc hmask
      (mkResetUWrapper_block0 decProc ctor.arity ctor.tag cls)
      (fun j hj => (mkResetUWrapper_dec_blocks decProc ctor.arity ctor.tag cls j hj).1)
      (fun j hj => (mkResetUWrapper_dec_blocks decProc ctor.arity ctor.tag cls j hj).2)
      (mkResetUWrapper_ret decProc ctor.arity ctor.tag cls)
      ready hc ha hbctor h0 h1 caller callers hdst
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hfn
    obtain ⟨-, a0, ha0, cell0⟩ := ready.idle.live.cell l 1 .dyn b hc
    have ea0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
    have cell : Gen.LiveCell addresses mem a 1 b := ea0 ▸ cell0
    have hblk0 := mkResetWrapper_block0 isU incProc decProc ctor.arity ctor.tag cls
    have hblk1 := mkResetWrapper_block1 isU incProc decProc ctor.arity ctor.tag cls
    have henter : Lir.enter P isU [a] =
        some { fn := isU, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 a } := by
      simp [Lir.enter, hisU, Gen.isUnique, Lir.bindParams]
    let afterIsU : Lir.Frame := { fn := wrapper, label := 0, pos := 1, env, dsts := [2] }
    have hcall := Lir.step_call (p := P) (mem := mem) (ctx := context) (rest := caller :: callers)
      (fr := { fn := wrapper, label := 0, pos := 0, env })
      hfn hblk0 (by simp) rfl (vs := [a]) (by simp [Lir.evalArgs, Lir.Arg.eval, h0]) henter
    have hevalU : Lir.eval Gen.uniqueProgram 0 [a] mem context = .ok ([1], mem) := by
      simpa using Gen.unique_cell cell context 0
    have hisUTrace := isUnique_caller hisU hevalU afterIsU (caller :: callers) rfl
    have hbr := Lir.br_at (p := P) (mem := mem) (ctx := context) (rest := caller :: callers)
      (pos := 1) (ρ := env.insert 2 1) (ρ' := env.insert 2 1) (va := 1) (vb := 1) (e := ⟨1, []⟩) (vals := [])
      hfn hblk0 (by simp) rfl (by simp [Lir.Arg.eval]) rfl
      (by have : Lir.Cond.eq.holds .w64 1 1 = true := (by decide); rw [this]; rfl) rfl hblk1
      (by simp [Lir.bindParams])
    have h0' : (env.insert 2 1)[0]? = some a := by rw [Lir.env_insert_ne _ _ (by omega)]; exact h0
    have h1' : (env.insert 2 1)[1]? = some (UInt64.ofNat (2 * mask + 1)) := by
      rw [Lir.env_insert_ne _ _ (by omega)]; exact h1
    obtain ⟨H₁, H₂, mem', slots', lists', costBody, hrc, hda, hready', hbodyTrace⟩ :=
      reset_unique_body_exec hfn hdec (by omega) rfl hvc hmask hblk1
        (fun j hj => (mkResetWrapper_dec_blocks isU incProc decProc ctor.arity ctor.tag cls j hj).1)
        (fun j hj => (mkResetWrapper_dec_blocks isU incProc decProc ctor.arity ctor.tag cls j hj).2)
        (mkResetWrapper_uniqueRet isU incProc decProc ctor.arity ctor.tag cls)
        ready hc ha hbctor h0' h1' caller callers hdst
    refine ⟨H₁, H₂, mem', slots', lists', 1 + costBody, hrc, hda, hready', ?_⟩
    have hall := (Sem.Star.single (Lir.semStep_next.mpr hcall)).trans
      (hisUTrace.trans ((Sem.Star.single (Lir.semStep_next.mpr hbr)).trans hbodyTrace))
    simpa [Lir.atState, afterIsU, Nat.add_assoc] using hall

/-- Execute `mkResetWrapper` starting at block 0 on a shared live cell `l` (`rc ≠ 1, mode = .dyn`):
either increments every live field, releases `l`, and returns `1` (`.erased`), or fails with
`.resource .heap` (refcount overflow during `inc`). -/
theorem reset_wrapper_shared_exec {P : Lir.Program} {wrapper isU incProc decProc dst mask : Nat}
    {ctor : Fir.CtorInfo} {cls : Nat}
    (hfn : P.funcs[wrapper]? = some (mkResetWrapper isU incProc decProc
      (CellLayout.ofFields ctor.arity ctor.tag) cls))
    (hisU : P.funcs[isU]? = some Gen.isUnique)
    (hinc : P.funcs[incProc]? = some Rt.Rc.Procs.inc)
    (hdec : P.funcs[decProc]? = some Gen.dec)
    (hvc : Own.Plain.Ctx.validReuseCtor ctor = some cls) (hmask : mask < 2 ^ 61)
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {l rc : Nat} {a : Lir.Word} {b : Body} {rest : List RVal}
    {context base bump limit : Lir.Word} {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (holdRoots external (.loc l :: rest)) context base bump limit slots lists)
    (hc : H.cell? l = some (.live rc .dyn b)) (hrc : rc ≠ 1)
    (ha : addresses l = some a) (hbctor : b.ctor = ctor)
    {env : Lir.Env}
    (h0 : env[0]? = some a) (h1 : env[1]? = some (UInt64.ofNat (2 * mask + 1)))
    (caller : Lir.Frame) (callers : List Lir.Frame) (hdst : caller.dsts = [dst]) :
    let liveFields := b.fields.zipIdx.filterMap (fun (u, j) => if Nat.testBit mask j then some u else none)
    (∃ H₁ H₂ mem' slots' lists' cost,
      Own.Plain.incList H liveFields = some H₁ ∧
      dropAll H₁ [.loc l] = some H₂ ∧
      Gen.AllocatorReady maxClass H₂ addresses mem'
        (holdRoots external (liveFields ++ rest)) context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep P)
        { mem, ctx := context, stack := { fn := wrapper, label := 0, pos := 0, env } :: caller :: callers }
        cost
        { mem := mem', ctx := context,
          stack := { caller with env := caller.env.insert dst 1, dsts := [] } :: callers }) ∨
    Sem.Fails (Lir.semStep P)
      { mem, ctx := context, stack := { fn := wrapper, label := 0, pos := 0, env } :: caller :: callers } := by
  intro liveFields
  obtain ⟨hpos, h61, _, _, hnsc, hnobj, _, _, _, _, _, _⟩ := validReuseCtor_full hvc
  obtain ⟨-, a0, ha0, cell0⟩ := ready.idle.live.cell l rc .dyn b hc
  have ea0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
  have cell : Gen.LiveCell addresses mem a rc b := ea0 ▸ cell0
  have hblen : b.fields.length = ctor.arity := by
    have := cell.arity; rw [hbctor, hnobj, hnsc] at this; omega
  have hblk0 := mkResetWrapper_block0 isU incProc decProc ctor.arity ctor.tag cls
  have hshared0 := (mkResetWrapper_shared_blocks isU incProc decProc ctor.arity ctor.tag cls 0 hpos).1
  have hsharedRet := mkResetWrapper_sharedRet isU incProc decProc ctor.arity ctor.tag cls
  have henter : Lir.enter P isU [a] =
      some { fn := isU, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 a } := by
    simp [Lir.enter, hisU, Gen.isUnique, Lir.bindParams]
  let afterIsU : Lir.Frame := { fn := wrapper, label := 0, pos := 1, env, dsts := [2] }
  have hcall := Lir.step_call (p := P) (mem := mem) (ctx := context) (rest := caller :: callers)
    (fr := { fn := wrapper, label := 0, pos := 0, env })
    hfn hblk0 (by simp) rfl (vs := [a]) (by simp [Lir.evalArgs, Lir.Arg.eval, h0]) henter
  have hevalU : Lir.eval Gen.uniqueProgram 0 [a] mem context = .ok ([0], mem) := by
    simpa [hrc] using Gen.unique_cell cell context 0
  have hisUTrace := isUnique_caller hisU hevalU afterIsU (caller :: callers) rfl
  have hbr := Lir.br_at (p := P) (mem := mem) (ctx := context) (rest := caller :: callers)
    (pos := 1) (ρ := env.insert 2 0) (ρ' := env.insert 2 0) (va := 0) (vb := 1)
    (e := ⟨3 + 2 * ctor.arity, []⟩) (vals := [])
    hfn hblk0 (by simp) rfl (by simp [Lir.Arg.eval]) rfl
    (by have : Lir.Cond.eq.holds .w64 0 1 = false := (by decide); rw [this]; rfl) rfl
    (by simpa using hshared0) (by simp [Lir.bindParams])
  have hpre : Sem.Star (Lir.semStep P)
      { mem, ctx := context, stack := { fn := wrapper, label := 0, pos := 0, env } :: caller :: callers } 1
      { mem, ctx := context,
        stack := { fn := wrapper, label := 3 + 2 * ctor.arity, pos := 0, env := env.insert 2 0 } :: caller :: callers } := by
    have := (Sem.Star.single (Lir.semStep_next.mpr hcall)).trans
      (hisUTrace.trans (Sem.Star.single (Lir.semStep_next.mpr hbr)))
    simpa [Lir.atState, afterIsU] using this
  have h0' : (env.insert 2 0)[0]? = some a := by rw [Lir.env_insert_ne _ _ (by omega)]; exact h0
  have h1' : (env.insert 2 0)[1]? = some (UInt64.ofNat (2 * mask + 1)) := by
    rw [Lir.env_insert_ne _ _ (by omega)]; exact h1
  rcases sharedIncLoop_exec hfn hinc h61 hmask ha hbctor hnobj hblen (caller :: callers)
      ctor.arity (Nat.le_refl _) H mem (env.insert 2 0) (.loc l :: rest) rc h0' h1' hc ready with
    ⟨H₁, mem₁, env₁, costLoop, rc₁, hi, _, h0₁, hready₁, hloopTrace⟩ | failed
  · have hrebase : holdRoots external (liveFields ++ (.loc l :: rest)) =
        fun loc => holdRoots external (liveFields ++ rest) loc + refsIn loc [.loc l] := by
      funext loc
      simp only [holdRoots, refsIn_append, refsIn]; omega
    have hready₁' : Gen.AllocatorReady maxClass H₁ addresses mem₁
        (fun loc => holdRoots external (liveFields ++ rest) loc + refsIn loc [.loc l])
        context base bump limit slots lists := by
      rw [← hrebase]; simpa [liveFields] using hready₁
    have henterDec : Lir.enter P decProc [a] =
        some { fn := decProc, label := 0, pos := 0, env := Gen.decEnv a } := by
      simp [Lir.enter, hdec, Gen.dec, Lir.bindParams, Gen.decEnv]
    let afterDec : Lir.Frame :=
      { fn := wrapper, label := 3 + 2 * ctor.arity + 2 * ctor.arity, pos := 1, env := env₁, dsts := [] }
    have hcallDec := Lir.step_call (p := P) (mem := mem₁) (ctx := context) (rest := caller :: callers)
      (fr := { fn := wrapper, label := 3 + 2 * ctor.arity + 2 * ctor.arity, pos := 0, env := env₁ })
      hfn hsharedRet (by simp) rfl (vs := [a])
      (by simp [Lir.evalArgs, Lir.Arg.eval, h0₁]) henterDec
    obtain ⟨H₂, mem₂, slots₂, lists₂, chDec, hda, hready₂, hdecTrace⟩ :=
      hready₁'.release_caller_ready a ha P decProc hdec afterDec (caller :: callers) rfl
    have hret := Lir.step_ret_caller (p := P) (vals := [1]) (ρ := caller.env.insert dst 1)
      (mem := mem₂) (ctx := context)
      (fr := afterDec) (caller := caller) (rest' := callers) hfn hsharedRet (by simp [afterDec]) rfl
      (by simp [Lir.evalArgs, Lir.Arg.eval]) (by simp [hdst, Lir.bindParams])
    refine .inl ⟨H₁, H₂, mem₂, slots₂, lists₂, 1 + costLoop + 1 + chDec, by simpa [liveFields] using hi,
      hda, hready₂, ?_⟩
    have hloopTrace' : Sem.Star (Lir.semStep P)
        { mem, ctx := context,
          stack := { fn := wrapper, label := 3 + 2 * ctor.arity, pos := 0, env := env.insert 2 0 } :: caller :: callers }
        costLoop
        { mem := mem₁, ctx := context,
          stack := { fn := wrapper, label := 3 + 2 * ctor.arity + 2 * ctor.arity, pos := 0, env := env₁ } :: caller :: callers } := by
      simpa using hloopTrace
    have hall := hpre.trans (hloopTrace'.trans
      ((Sem.Star.single (Lir.semStep_next.mpr hcallDec)).trans
        (hdecTrace.trans (Sem.Star.single (Lir.semStep_next.mpr hret)))))
    simpa [afterDec, Nat.add_assoc] using hall
  · exact .inr (fails_prefix hpre (by simpa using failed))

/-- Execute `mkResetWrapper` starting at block 0 on an immediate value `v` (`.ctor0`, `.lit`, or
`.erased`) with `mask = 0` (`v1 = 1`): returns `1` (`.erased`) with unchanged heap. -/
theorem reset_wrapper_imm_exec {P : Lir.Program} {wrapper isU incProc decProc dst : Nat}
    {ctor : Fir.CtorInfo} {cls : Nat}
    (hfn : P.funcs[wrapper]? = some (mkResetWrapper isU incProc decProc
      (CellLayout.ofFields ctor.arity ctor.tag) cls))
    (hisU : P.funcs[isU]? = some Gen.isUnique)
    (hdec : P.funcs[decProc]? = some Gen.dec)
    (hvc : Own.Plain.Ctx.validReuseCtor ctor = some cls)
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {v : RVal} {w : Lir.Word} {rest : List RVal}
    {context base bump limit : Lir.Word} {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (holdRoots external (v :: rest)) context base bump limit slots lists)
    (himm : ∀ l, v ≠ .loc l) (hw : valueWord addresses v = some w)
    {env : Lir.Env} (h0 : env[0]? = some w) (h1 : env[1]? = some 1)
    (caller : Lir.Frame) (callers : List Lir.Frame) (hdst : caller.dsts = [dst]) :
    ∃ mem' slots' lists' cost,
      Gen.AllocatorReady maxClass H addresses mem'
        (holdRoots external rest) context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep P)
        { mem, ctx := context, stack := { fn := wrapper, label := 0, pos := 0, env } :: caller :: callers }
        cost
        { mem := mem', ctx := context,
          stack := { caller with env := caller.env.insert dst 1, dsts := [] } :: callers } := by
  obtain ⟨hpos, h61, _, _, _, _, _, _, _, _, _, _⟩ := validReuseCtor_full hvc
  have hblk0 := mkResetWrapper_block0 isU incProc decProc ctor.arity ctor.tag cls
  have hshared0 := (mkResetWrapper_shared_blocks isU incProc decProc ctor.arity ctor.tag cls 0 hpos).1
  have hsharedRet := mkResetWrapper_sharedRet isU incProc decProc ctor.arity ctor.tag cls
  have henter : Lir.enter P isU [w] =
      some { fn := isU, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 w } := by
    simp [Lir.enter, hisU, Gen.isUnique, Lir.bindParams]
  let afterIsU : Lir.Frame := { fn := wrapper, label := 0, pos := 1, env, dsts := [2] }
  have hcall := Lir.step_call (p := P) (mem := mem) (ctx := context) (rest := caller :: callers)
    (fr := { fn := wrapper, label := 0, pos := 0, env })
    hfn hblk0 (by simp) rfl (vs := [w]) (by simp [Lir.evalArgs, Lir.Arg.eval, h0]) henter
  have htag : w &&& 1 = 1 := Gen.valueWord_immediate_tag hw himm
  have hevalU : Lir.eval Gen.uniqueProgram 0 [w] mem context = .ok ([0], mem) :=
    Gen.unique_immediate mem context w 0 htag
  have hisUTrace := isUnique_caller hisU hevalU afterIsU (caller :: callers) rfl
  have hbr := Lir.br_at (p := P) (mem := mem) (ctx := context) (rest := caller :: callers)
    (pos := 1) (ρ := env.insert 2 0) (ρ' := env.insert 2 0) (va := 0) (vb := 1)
    (e := ⟨3 + 2 * ctor.arity, []⟩) (vals := [])
    hfn hblk0 (by simp) rfl (by simp [Lir.Arg.eval]) rfl
    (by have : Lir.Cond.eq.holds .w64 0 1 = false := (by decide); rw [this]; rfl) rfl
    (by simpa using hshared0) (by simp [Lir.bindParams])
  have h0' : (env.insert 2 0)[0]? = some w := by rw [Lir.env_insert_ne _ _ (by omega)]; exact h0
  have h1' : (env.insert 2 0)[1]? = some 1 := by rw [Lir.env_insert_ne _ _ (by omega)]; exact h1
  have hloop := sharedIncLoop_maskZero_exec hfn h61 (mem := mem) (context := context) h1'
    (caller :: callers) ctor.arity (Nat.le_refl _)
  have hsame : holdRoots external (v :: rest) =
      fun loc => holdRoots external rest loc + refsIn loc [v] := by
    funext loc; simp only [holdRoots, refsIn]; omega
  have hready' : Gen.AllocatorReady maxClass H addresses mem
      (fun loc => holdRoots external rest loc + refsIn loc [v])
      context base bump limit slots lists := by rwa [← hsame]
  have henterDec : Lir.enter P decProc [w] =
      some { fn := decProc, label := 0, pos := 0, env := Gen.decEnv w } := by
    simp [Lir.enter, hdec, Gen.dec, Lir.bindParams, Gen.decEnv]
  let afterDec : Lir.Frame :=
    { fn := wrapper, label := 3 + 2 * ctor.arity + 2 * ctor.arity, pos := 1, env := env.insert 2 0, dsts := [] }
  have hcallDec := Lir.step_call (p := P) (mem := mem) (ctx := context) (rest := caller :: callers)
    (fr := { fn := wrapper, label := 3 + 2 * ctor.arity + 2 * ctor.arity, pos := 0, env := env.insert 2 0 })
    hfn hsharedRet (by simp) rfl (vs := [w])
    (by simp [Lir.evalArgs, Lir.Arg.eval, h0']) henterDec
  obtain ⟨H', mem', slots', lists', chDec, hda, hreadyOut, hdecTrace⟩ :=
    hready'.release_caller_ready w hw P decProc hdec afterDec (caller :: callers) rfl
  have hHeq : H' = H := by
    cases v with
    | lit _ | ctor0 _ | erased => simp [dropAll, releaseOne] at hda; exact hda.symm
    | loc l => exact absurd rfl (himm l)
  subst hHeq
  have hret := Lir.step_ret_caller (p := P) (vals := [1]) (ρ := caller.env.insert dst 1)
    (mem := mem') (ctx := context)
    (fr := afterDec) (caller := caller) (rest' := callers) hfn hsharedRet (by simp [afterDec]) rfl
    (by simp [Lir.evalArgs, Lir.Arg.eval]) (by simp [hdst, Lir.bindParams])
  refine ⟨mem', slots', lists', 1 + (1 + chDec), hreadyOut, ?_⟩
  have hloop' : Sem.Star (Lir.semStep P)
      { mem, ctx := context,
        stack := { fn := wrapper, label := 3 + 2 * ctor.arity, pos := 0, env := env.insert 2 0 } :: caller :: callers } 0
      { mem, ctx := context,
        stack := { fn := wrapper, label := 3 + 2 * ctor.arity + 2 * ctor.arity, pos := 0, env := env.insert 2 0 } :: caller :: callers } := by
    simpa using hloop
  have hall := (Sem.Star.single (Lir.semStep_next.mpr hcall)).trans
    (hisUTrace.trans ((Sem.Star.single (Lir.semStep_next.mpr hbr)).trans
      (hloop'.trans ((Sem.Star.single (Lir.semStep_next.mpr hcallDec)).trans
        (hdecTrace.trans (Sem.Star.single (Lir.semStep_next.mpr hret)))))))
  simpa [Lir.atState, afterIsU, afterDec, Nat.add_assoc] using hall

end IxCC.Cfg.Rc.Native
