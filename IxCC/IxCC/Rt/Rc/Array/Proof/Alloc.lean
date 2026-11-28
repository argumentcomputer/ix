import IxCC.Rt.Rc.Array.Proof.Classes
import IxCC.Rt.Rc.Array.Proof.BasicOps
import IxCC.Rt.Rc.Proof.BumpMetadata

/-! # Operational Correctness of Array Cell Allocation & Constructors

Proves exact Lir operational correctness of `arrAllocCell`, `arrEmptyCapBoxed`,
`arrEmptyCapLimbs`, and `byteArrEmptyCap` over `ArrayAllocator`:
* `arrAllocCell_free_at_ret`: pops from a non-empty class free list
  `freeLists cls = addr :: tail`, initializes header/size/cap, establishes
  `LiveArrayCell`, and preserves `ArrayAllocator` with `freeLists[cls ↦ tail]`.
* `arrAllocCell_bump_at_ret`: bump-allocates from `[bump .. limit)` when
  `freeLists cls = []` and `bump + classBytes cls ≤ limit`, initializes
  header/size/cap, establishes `LiveArrayCell`, and preserves `ArrayAllocator`
  at `bump + classBytes cls`.
* `arrAllocCell_oom_eval`: cleanly fails `.resource .heap` when `freeLists cls = []`
  and `limit < bump + classBytes cls`.
* `arrEmptyCapBoxed_free_eval`, `arrEmptyCapBoxed_bump_eval`,
  `arrEmptyCapLimbs_free_eval`, `arrEmptyCapLimbs_bump_eval`, and
  `byteArrEmptyCap_bump_eval`: top-level `Lir.eval` theorems establishing
  `LiveArrayCell` (with exact `wordCapOfClass` / `byteCapOfClass` capacity)
  and preserving `ArrayAllocator`. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok wordAt_write64 sub_toNat_of_le)
open IxCC.Rt.Rc (maxClass classWords classFor classBytes maxCellWords maxCellWords_eq
  classWords_pos classWords_le_max)
open IxCC.Rt.Rc.Procs (v i to cellAddr FreeChain bumpAddress limitAddress freeHeadAddress
  bumpAddress_eq limitAddress_eq)
open IxCC.X86 (Memory)

/-- Empty `ArrayVal` corresponding to an `ArrayKind`. -/
def emptyValOfKind : ArrayKind → ArrayVal
  | .boxed => .boxed []
  | .bytes => .bytes []
  | .limbs => .limbs []

theorem emptyValOfKind_kind (k : ArrayKind) : (emptyValOfKind k).kind = k := by
  cases k <;> rfl

theorem emptyValOfKind_size (k : ArrayKind) : (emptyValOfKind k).size = 0 := by
  cases k <;> rfl

theorem emptyValOfKind_payload (mem : Memory) (addr : Word) (k : ArrayKind) :
    ArrayPayload mem addr (emptyValOfKind k) := by
  cases k <;> (intro j hj; simp at hj)

private theorem classBytes_ge_eight {c : Nat} (h1 : 1 ≤ c) (_h2 : c ≤ maxClass) :
    8 ≤ classBytes c := by
  have hpos := classWords_pos h1
  unfold classBytes; omega

private theorem ovf_addC_no_ovf {a b : Word} (h : a.toNat + b.toNat < 2 ^ 64) :
    Ovf.eval .addC a b = (a + b, false) := by
  have hsum : (a + b).toNat = a.toNat + b.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]
  have hlt : ¬ (a + b < a) := by
    rw [UInt64.lt_iff_toNat_lt, hsum]; omega
  simp [Ovf.eval, hlt]

private theorem classFor_ge_three {w : Nat} (h3 : 3 ≤ w) (hhi : w ≤ maxCellWords) :
    minArrayClass ≤ classForFast w ∧ classForFast w ≤ maxClass ∧ w ≤ classWords (classForFast w) := by
  have hcf := classForFast_eq (by omega) hhi
  obtain ⟨h1, h2, hfit, _⟩ := IxCC.Rt.Rc.classFor_spec hcf
  have hcls3 : minArrayClass ≤ classForFast w := by
    rcases Nat.lt_or_ge (classForFast w) minArrayClass with hlt | hge
    · have hle : classForFast w ≤ 2 := by unfold minArrayClass at hlt; omega
      rw [IxCC.Rt.Rc.classWords_small (by omega)] at hfit
      omega
    · exact hge
  exact ⟨hcls3, h2, hfit⟩

/-! ## `ArrayAllocator` arithmetic & framing helpers -/

theorem ArrayAllocator.bump_toNat {mem context base bump limit freeLists}
    (h : ArrayAllocator mem context base bump limit freeLists) :
    (bumpAddress context).toNat = context.toNat - 40 := by
  rw [bumpAddress_eq, sub_toNat_of_le]
  · rfl
  · simpa using h.context_lower

theorem ArrayAllocator.limit_toNat {mem context base bump limit freeLists}
    (h : ArrayAllocator mem context base bump limit freeLists) :
    (limitAddress context).toNat = context.toNat - 32 := by
  rw [limitAddress_eq, sub_toNat_of_le]
  · rfl
  · have := h.context_lower; simpa using (show 32 ≤ context.toNat by omega)

theorem ArrayAllocator.freeHead_toNat {mem context base bump limit freeLists}
    (h : ArrayAllocator mem context base bump limit freeLists)
    {cls : Nat} (hhi : cls ≤ maxClass) :
    (freeHeadAddress context (UInt64.ofNat cls)).toNat = context.toNat + 8 * cls := by
  have hfit := h.context_fit
  have hcm : maxClass = 71 := rfl
  unfold freeHeadAddress
  have hm : UInt64.ofNat cls * 8 = UInt64.ofNat (8 * cls) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mul, u64_toNat_ofNat_lt (by omega), show (8 : Word).toNat = 8 from rfl,
      u64_toNat_ofNat_lt (by omega), Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
  rw [hm]
  exact addr_toNat (by omega)

theorem ArrayAllocator.write64_arena_ok {mem context base bump limit freeLists}
    (h : ArrayAllocator mem context base bump limit freeLists)
    {wa : Word} (hlo : base.toNat ≤ wa.toNat) (hhi : wa.toNat + 8 ≤ limit.toNat) (val : Word) :
    mem.write? .w64 wa val = .ok (mem.write .w64 wa val) := by
  have hlim := h.limit_fit
  apply write?_ok
  intro j hj
  have hj8 : j < 8 := by simpa [X86.Width.bytes] using hj
  have hja : (wa + UInt64.ofNat j).toNat = wa.toNat + j := addr_toNat (by omega)
  exact (h.arena_access (wa + UInt64.ofNat j) (by omega) (by omega)).2

private theorem freeChain_write64_frame {mem : Memory} {wa val : Word} {chain : List Word}
    (hchain : FreeChain mem chain) (hwa : wa.toNat + 8 ≤ 2 ^ 64)
    (hfit : ∀ a ∈ chain, a.toNat + 8 ≤ 2 ^ 64)
    (hsep : ∀ a ∈ chain, a.toNat + 8 ≤ wa.toNat ∨ wa.toNat + 8 ≤ a.toNat) :
    FreeChain (mem.write .w64 wa val) chain := by
  induction chain with
  | nil => trivial
  | cons a tail ih =>
    obtain ⟨hw, ht⟩ := hchain
    exact ⟨wordAt_write64_disjoint hw hwa (hfit a (by simp)) (hsep a (by simp)),
      ih ht (fun b hb => hfit b (by simp [hb])) (fun b hb => hsep b (by simp [hb]))⟩

/-- Writing a 64-bit word inside the arena at `wa` that is disjoint from every
cell on `freeLists` preserves `ArrayAllocator`. -/
theorem ArrayAllocator.write64_disjoint {mem context base bump limit freeLists}
    (h : ArrayAllocator mem context base bump limit freeLists)
    {wa : Word} (hlo : base.toNat ≤ wa.toNat) (hhi : wa.toNat + 8 ≤ limit.toNat)
    (hdisj : ∀ c a, a ∈ freeLists c → a.toNat + 8 ≤ wa.toNat ∨ wa.toNat + 8 ≤ a.toNat)
    (val : Word) :
    ArrayAllocator (mem.write .w64 wa val) context base bump limit freeLists := by
  have hlim := h.limit_fit
  have hcb := h.context_before
  have hcl := h.context_lower
  have hcf := h.context_fit
  have hbn := h.bump_toNat
  have hln := h.limit_toNat
  refine ⟨h.context_lower, h.context_fit, h.context_before, h.base_le_bump, h.bump_le_limit,
    h.limit_fit, h.bump_aligned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.free_distinct, h.free_cls_pos,
    h.free_in_arena, h.free_disjoint⟩
  · exact wordAt_write64_disjoint h.bump_word (by omega) (by omega) (Or.inl (by omega))
  · exact wordAt_write64_disjoint h.limit_word (by omega) (by omega) (Or.inl (by omega))
  · intro j hj; simpa [Memory.write] using h.bump_writable j hj
  · intro a ha1 ha2; simpa [Memory.write] using h.arena_access a ha1 ha2
  · intro c hc1 hc2
    have hhn := h.freeHead_toNat hc2
    exact wordAt_write64_disjoint (h.free_heads c hc1 hc2) (by omega) (by omega) (Or.inl (by omega))
  · intro c hc1 hc2 j hj; simpa [Memory.write] using h.head_writable c hc1 hc2 j hj
  · intro c
    exact freeChain_write64_frame (h.free_chains c) (by omega)
      (fun a ha => by
        have hpos := h.free_cls_pos c a ha
        have h8 := classBytes_ge_eight hpos.1 hpos.2
        have hin := h.free_in_arena c a ha
        have hbl := h.bump_le_limit
        omega)
      (fun a ha => hdisj c a ha)

/-- Updating `freeLists` by popping `addr` from class `cls` preserves `ArrayAllocator`
after storing `tail.headD 0` into `[ctx + cls*8]`. -/
theorem ArrayAllocator.pop_free_head {mem context base bump limit freeLists}
    (h : ArrayAllocator mem context base bump limit freeLists)
    {cls : Nat} {addr : Word} {tail : List Word}
    (hlo : minArrayClass ≤ cls) (hhi : cls ≤ maxClass)
    (hlist : freeLists cls = addr :: tail) :
    let headAddr := freeHeadAddress context (UInt64.ofNat cls)
    let mem1 := mem.write .w64 headAddr (tail.headD 0)
    let lists' := fun c => if c = cls then tail else freeLists c
    mem.write? .w64 headAddr (tail.headD 0) = .ok mem1 ∧
    ArrayAllocator mem1 context base bump limit lists' ∧
    (∀ c a, a ∈ lists' c → a.toNat + classBytes c ≤ addr.toNat ∨ addr.toNat + classBytes cls ≤ a.toNat) := by
  intro headAddr mem1 lists'
  have hcl := h.context_lower
  have hcf := h.context_fit
  have hcb := h.context_before
  have hlim := h.limit_fit
  have hbn := h.bump_toNat
  have hln := h.limit_toNat
  have hhn : headAddr.toNat = context.toNat + 8 * cls := h.freeHead_toNat hhi
  have hwr : mem.write? .w64 headAddr (tail.headD 0) = .ok mem1 :=
    write?_ok (fun j hj => h.head_writable cls (by unfold minArrayClass at hlo; omega) hhi j
      (by simpa [X86.Width.bytes] using hj))
  have hmem_old : ∀ c a, a ∈ lists' c → a ∈ freeLists c := by
    intro c a ha
    by_cases hce : c = cls
    · subst hce; rw [hlist]; exact List.mem_cons_of_mem _ (by simpa [lists'] using ha)
    · simpa [lists', hce] using ha
  have hdisj_addr : ∀ c a, a ∈ lists' c →
      a.toNat + classBytes c ≤ addr.toNat ∨ addr.toNat + classBytes cls ≤ a.toNat := by
    intro c a ha
    by_cases hce : c = cls
    · subst hce
      have hat : a ∈ tail := by simpa [lists'] using ha
      have hnd := h.free_distinct c
      rw [hlist, List.nodup_cons] at hnd
      have hne : a ≠ addr := fun heq => hnd.1 (heq ▸ hat)
      have ha_mem := hmem_old c a ha
      have haddr_mem : addr ∈ freeLists c := by rw [hlist]; exact List.mem_cons_self
      rcases h.free_disjoint c c a addr ha_mem haddr_mem with ⟨_, heq⟩ | h1 | h2
      · exact absurd heq hne
      · exact Or.inl h1
      · exact Or.inr h2
    · have ha_mem := hmem_old c a ha
      have haddr_mem : addr ∈ freeLists cls := by rw [hlist]; exact List.mem_cons_self
      rcases h.free_disjoint c cls a addr ha_mem haddr_mem with ⟨heq, _⟩ | h1 | h2
      · exact absurd heq hce
      · exact Or.inl h1
      · exact Or.inr h2
  refine ⟨hwr, ?_, hdisj_addr⟩
  refine ⟨h.context_lower, h.context_fit, h.context_before, h.base_le_bump, h.bump_le_limit,
    h.limit_fit, h.bump_aligned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact wordAt_write64_disjoint h.bump_word (by omega) (by omega) (Or.inl (by unfold minArrayClass at hlo; omega))
  · exact wordAt_write64_disjoint h.limit_word (by omega) (by omega) (Or.inl (by unfold minArrayClass at hlo; omega))
  · intro j hj; simpa [mem1, Memory.write] using h.bump_writable j hj
  · intro a ha1 ha2; simpa [mem1, Memory.write] using h.arena_access a ha1 ha2
  · intro c hc1 hc2
    by_cases hce : c = cls
    · subst hce
      simpa [lists', mem1] using wordAt_write64 (v := tail.headD 0) (h.free_heads c hc1 hc2).readable
    · have hhn_c := h.freeHead_toNat hc2
      have hsep : (freeHeadAddress context (UInt64.ofNat c)).toNat + 8 ≤ headAddr.toNat ∨
          headAddr.toNat + 8 ≤ (freeHeadAddress context (UInt64.ofNat c)).toNat := by omega
      simpa [lists', hce] using wordAt_write64_disjoint (h.free_heads c hc1 hc2) (by omega) (by omega) hsep
  · intro c hc1 hc2 j hj; simpa [mem1, Memory.write] using h.head_writable c hc1 hc2 j hj
  · intro c
    have hch_old : FreeChain mem (lists' c) := by
      by_cases hce : c = cls
      · subst hce
        have hc := h.free_chains c
        rw [hlist] at hc
        simpa [lists'] using hc.2
      · simpa [lists', hce] using h.free_chains c
    exact freeChain_write64_frame hch_old (by omega)
      (fun a ha => by
        have hpos := h.free_cls_pos c a (hmem_old c a ha)
        have h8 := classBytes_ge_eight hpos.1 hpos.2
        have hin := h.free_in_arena c a (hmem_old c a ha)
        have hbl := h.bump_le_limit
        omega)
      (fun a ha => Or.inr (by have := h.free_in_arena c a (hmem_old c a ha); omega))
  · intro c
    by_cases hce : c = cls
    · subst hce
      have hnd := h.free_distinct c
      rw [hlist, List.nodup_cons] at hnd
      simpa [lists'] using hnd.2
    · simpa [lists', hce] using h.free_distinct c
  · intro c a ha; exact h.free_cls_pos c a (hmem_old c a ha)
  · intro c a ha; exact h.free_in_arena c a (hmem_old c a ha)
  · intro c₁ c₂ a₁ a₂ ha₁ ha₂
    exact h.free_disjoint c₁ c₂ a₁ a₂ (hmem_old c₁ a₁ ha₁) (hmem_old c₂ a₂ ha₂)

/-- Advancing `bump` to `bump + classBytes cls` (when `bump + classBytes cls ≤ limit`)
preserves `ArrayAllocator` after storing `newBump` into `[ctx + bumpOff]`. -/
theorem ArrayAllocator.advance_bump {mem context base bump limit freeLists}
    (h : ArrayAllocator mem context base bump limit freeLists)
    {cls : Nat} (hfit : bump.toNat + classBytes cls ≤ limit.toNat) :
    let newBump := bump + UInt64.ofNat (classBytes cls)
    let mem1 := mem.write .w64 (bumpAddress context) newBump
    mem.write? .w64 (bumpAddress context) newBump = .ok mem1 ∧
    ArrayAllocator mem1 context base newBump limit freeLists ∧
    (∀ c a, a ∈ freeLists c → a.toNat + classBytes c ≤ bump.toNat ∨ bump.toNat + classBytes cls ≤ a.toNat) := by
  intro newBump mem1
  have hcl := h.context_lower
  have hcf := h.context_fit
  have hcb := h.context_before
  have hlim := h.limit_fit
  have hbn := h.bump_toNat
  have hln := h.limit_toNat
  have hnb_nat : newBump.toNat = bump.toNat + classBytes cls := addr_toNat (by omega)
  have hwr : mem.write? .w64 (bumpAddress context) newBump = .ok mem1 :=
    write?_ok (fun j hj => h.bump_writable j (by simpa [X86.Width.bytes] using hj))
  refine ⟨hwr, ?_, fun c a ha => Or.inl (h.free_in_arena c a ha).2.1⟩
  refine ⟨h.context_lower, h.context_fit, h.context_before,
    by have := h.base_le_bump; omega, by omega, h.limit_fit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.free_distinct, h.free_cls_pos, ?_, h.free_disjoint⟩
  · rw [hnb_nat]; unfold classBytes; have := h.bump_aligned; omega
  · exact wordAt_write64 (v := newBump) h.bump_word.readable
  · exact wordAt_write64_disjoint h.limit_word (by omega) (by omega) (Or.inr (by omega))
  · intro j hj; simpa [mem1, Memory.write] using h.bump_writable j hj
  · intro a ha1 ha2; simpa [mem1, Memory.write] using h.arena_access a ha1 ha2
  · intro c hc1 hc2
    have hhn := h.freeHead_toNat hc2
    exact wordAt_write64_disjoint (h.free_heads c hc1 hc2) (by omega) (by omega) (Or.inr (by omega))
  · intro c hc1 hc2 j hj; simpa [mem1, Memory.write] using h.head_writable c hc1 hc2 j hj
  · intro c
    exact freeChain_write64_frame (h.free_chains c) (by omega)
      (fun a ha => by
        have hpos := h.free_cls_pos c a ha
        have h8 := classBytes_ge_eight hpos.1 hpos.2
        have hin := h.free_in_arena c a ha
        have hbl := h.bump_le_limit
        omega)
      (fun a ha => Or.inr (by have := h.free_in_arena c a ha; omega))
  · intro c a ha
    have hin := h.free_in_arena c a ha
    exact ⟨hin.1, by omega, hin.2.2.1, hin.2.2.2⟩

/-! ## Common block-5 cell initialization (`arrAllocCell` block 5) -/

private theorem arrAllocCell_block5_at_ret {mainFn : FunId}
    {m1 : Memory} {context base bump' limit addr : Word} {freeLists' : Nat → List Word}
    {kind : ArrayKind} {cls : Nat} {e5 : Env}
    (halloc : ArrayAllocator m1 context base bump' limit freeLists')
    (hlo : minArrayClass ≤ cls) (hhi : cls ≤ maxClass)
    (haligned : addr.toNat % 8 = 0) (hnz : addr ≠ 0)
    (halo : base.toNat ≤ addr.toNat) (hahi : addr.toNat + classBytes cls ≤ limit.toNat)
    (hdisj : ∀ c a, a ∈ freeLists' c →
      a.toNat + classBytes c ≤ addr.toNat ∨ addr.toNat + classBytes cls ≤ a.toNat)
    (he1 : e5[1]? = some (scanTagFixed kind))
    (he2 : e5[2]? = some (UInt64.ofNat cls))
    (he3 : e5[3]? = some (UInt64.ofNat (classWords cls)))
    (he10 : e5[10]? = some addr) {rest : List Frame} :
    let m2 := m1.write .w64 addr (arrayHeader kind cls 1)
    let m3 := m2.write .w64 (addr + 8) 0
    let m4 := m3.write .w64 (addr + 16) (UInt64.ofNat (wordCapOfClass cls))
    ∃ s',
      Sem.Star (semStep (arrayProgram mainFn))
        (State.mk m1 context ({ fn := fnAllocCell, label := 5, pos := 0, env := e5 } :: rest))
        0 s' ∧
      ArrayAllocator m4 context base bump' limit freeLists' ∧
      LiveArrayCell m4 addr 1 cls (wordCapOfClass cls) (emptyValOfKind kind) ∧
      (match rest with
       | [] => semStep (arrayProgram mainFn) s' = .done ([addr], m4)
       | caller :: tail =>
           ∀ dst, caller.dsts = [dst] →
             semStep (arrayProgram mainFn) s' =
               .next (State.mk m4 context ({ caller with env := caller.env.insert dst addr, dsts := [] } :: tail)) false) := by
  intro m2 m3 m4
  have hf := arrayProgram_func_allocCell mainFn
  have hcw3 : 3 ≤ classWords cls := classWords_ge_three hlo hhi
  have hcw_le : classWords cls ≤ maxCellWords := classWords_le_max hhi
  have hm_eq : maxCellWords = 2 ^ 26 := maxCellWords_eq
  have hcm : maxClass = 71 := rfl
  have h24 : 24 ≤ classBytes cls := by unfold classBytes; omega
  have hlim := halloc.limit_fit
  have h8_toNat : (addr + 8).toNat = addr.toNat + 8 := addr_toNat_8 (by omega)
  have h16_toNat : (addr + 16).toNat = addr.toNat + 16 := addr_toNat_16 (by omega)
  have hdisj_of : ∀ (wa : Word), addr.toNat ≤ wa.toNat → wa.toNat + 8 ≤ addr.toNat + classBytes cls →
      ∀ c a, a ∈ freeLists' c → a.toNat + 8 ≤ wa.toNat ∨ wa.toNat + 8 ≤ a.toNat := by
    intro wa hwa1 hwa2 c a ha
    have hpos := halloc.free_cls_pos c a ha
    have hc8 := classBytes_ge_eight hpos.1 hpos.2
    rcases hdisj c a ha with h1 | h2
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have halloc2 : ArrayAllocator m2 context base bump' limit freeLists' :=
    halloc.write64_disjoint halo (by omega) (hdisj_of addr (Nat.le_refl _) (by omega)) _
  have halloc3 : ArrayAllocator m3 context base bump' limit freeLists' :=
    halloc2.write64_disjoint (by rw [h8_toNat]; omega) (by rw [h8_toNat]; omega)
      (hdisj_of (addr + 8) (by rw [h8_toNat]; omega) (by rw [h8_toNat]; omega)) _
  have halloc4 : ArrayAllocator m4 context base bump' limit freeLists' :=
    halloc3.write64_disjoint (by rw [h16_toNat]; omega) (by rw [h16_toNat]; omega)
      (hdisj_of (addr + 16) (by rw [h16_toNat]; omega) (by rw [h16_toNat]; omega)) _
  have hwr2 : m1.write? .w64 addr (arrayHeader kind cls 1) = .ok m2 :=
    halloc.write64_arena_ok halo (by omega) _
  have hwr3 : m2.write? .w64 (addr + 8) 0 = .ok m3 :=
    halloc2.write64_arena_ok (by rw [h8_toNat]; omega) (by rw [h8_toNat]; omega) _
  have hwr4 : m3.write? .w64 (addr + 16) (UInt64.ofNat (wordCapOfClass cls)) = .ok m4 :=
    halloc3.write64_arena_ok (by rw [h16_toNat]; omega) (by rw [h16_toNat]; omega) _
  have hcls_shl : cls <<< 8 < 2 ^ 64 := by rw [Nat.shiftLeft_eq]; omega
  have hshl_eq : UInt64.ofNat (cls <<< 8) = UInt64.ofNat cls <<< 8 :=
    (u64_shl_ofNat (a := cls) (s := 8) (by decide) (by omega) hcls_shl).symm
  have hor_eq : BinOp.eval .or .w64 (scanTagFixed kind) (UInt64.ofNat (cls <<< 8)) =
      some (arrayHeader kind cls 1) := by
    rw [binOp_or64, hshl_eq, scanTagFixed_or_cls hhi]
  let e11 := e5.insert 11 (UInt64.ofNat (cls <<< 8))
  let e12 := e11.insert 12 (arrayHeader kind cls 1)
  let e13 := e12.insert 13 (UInt64.ofNat (wordCapOfClass cls))
  have s50 := step_assign (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 5) (pos := 0) (rest := rest)
    (mem := m1) (context := context) (env := e5) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, he2]) rfl (binOp_shl64 cls 8 (by decide) (by omega) hcls_shl))
  have s51 := step_assign (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 5) (pos := 1) (rest := rest)
    (mem := m1) (context := context) (env := e11) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e11, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he1])
      (by simp only [v, Arg.eval, e11, env_get_insert_self]) hor_eq)
  have s52 := step_assign (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 5) (pos := 2) (rest := rest)
    (mem := m1) (context := context) (env := e12) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e12, e11, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he3]) rfl
      (binOp_sub64 (classWords cls) 3 hcw3 (by omega)))
  have s53 := step_store (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 5) (pos := 3) (rest := rest)
    (mem := m1) (context := context) (env := e13) hf rfl (by decide) rfl
    (cellAddr0_eval (by simp only [e13, e12, e11, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he10]))
    (by simp only [v, Arg.eval, e13, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e12]) hwr2
  have s54 := step_store (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 5) (pos := 4) (rest := rest)
    (mem := m2) (context := context) (env := e13) hf rfl (by decide) rfl
    (cellAddr_eval_8 (by simp only [e13, e12, e11, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he10])) rfl hwr3
  have s55 := step_store (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 5) (pos := 5) (rest := rest)
    (mem := m3) (context := context) (env := e13) hf rfl (by decide) rfl
    (cellAddr_eval_16 (by simp only [e13, e12, e11, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he10]))
    (by simp only [v, Arg.eval, e13, env_get_insert_self]) hwr4
  have hcell_rd : ∀ (m : Memory), (∀ a, base.toNat ≤ a.toNat → a.toNat < limit.toNat → m.readable a = true ∧ m.writable a = true) →
      ∀ (off : Nat), off + 8 ≤ classBytes cls → ∀ j < 8, m.readable ((addr + UInt64.ofNat off) + UInt64.ofNat j) = true := by
    intro m hacc off hoff j hj
    have ho : (addr + UInt64.ofNat off).toNat = addr.toNat + off := addr_toNat (by omega)
    have hja : ((addr + UInt64.ofNat off) + UInt64.ofNat j).toNat = addr.toNat + off + j := by
      rw [addr_toNat (by rw [ho]; omega), ho]
    exact (hacc _ (by omega) (by omega)).1
  have hhdr4 : WordAt m4 addr (arrayHeader (emptyValOfKind kind).kind cls 1) := by
    rw [emptyValOfKind_kind]
    have h2 : WordAt m2 addr (arrayHeader kind cls 1) :=
      wordAt_write64 (fun j hj => by
        have hja : (addr + UInt64.ofNat j).toNat = addr.toNat + j := addr_toNat (by omega)
        exact (halloc.arena_access _ (by omega) (by omega)).1)
    exact wordAt_write64_disjoint
      (wordAt_write64_disjoint h2 (by rw [h8_toNat]; omega) (by omega) (Or.inl (by rw [h8_toNat]; omega)))
      (by rw [h16_toNat]; omega) (by omega) (Or.inl (by rw [h16_toNat]; omega))
  have hsz4 : WordAt m4 (addr + 8) (UInt64.ofNat (emptyValOfKind kind).size) := by
    rw [emptyValOfKind_size]
    have h3 : WordAt m3 (addr + 8) (UInt64.ofNat 0) :=
      wordAt_write64 (hcell_rd m2 halloc2.arena_access 8 (by omega))
    exact wordAt_write64_disjoint h3 (by rw [h16_toNat]; omega) (by rw [h8_toNat]; omega)
      (Or.inl (by rw [h8_toNat, h16_toNat]; omega))
  have hcap4 : WordAt m4 (addr + 16) (UInt64.ofNat (wordCapOfClass cls)) :=
    wordAt_write64 (hcell_rd m3 halloc3.arena_access 16 (by omega))
  have hlive4 : LiveArrayCell m4 addr 1 cls (wordCapOfClass cls) (emptyValOfKind kind) := by
    refine ⟨haligned, hnz, hlo, hhi, by omega, by unfold IxCC.Rt.Rc.maxCount; omega,
      by omega, by rw [emptyValOfKind_size]; omega, ?_, ?_, hhdr4, hsz4, hcap4, emptyValOfKind_payload m4 addr kind⟩
    · cases kind <;> simp only [emptyValOfKind]
      · exact Nat.le_refl _
      · unfold wordCapOfClass byteCapOfClass; omega
      · exact Nat.le_refl _
    · intro j hj
      have hja : (addr + UInt64.ofNat j).toNat = addr.toNat + j := addr_toNat (by omega)
      exact halloc4.arena_access (addr + UInt64.ofNat j) (by omega) (by omega)
  have sret := step_ret_one (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 5)
    (mem := m4) (context := context) (rest := rest) (env := e13) (res := addr)
    hf rfl rfl (by simp only [v, Arg.eval, e13, e12, e11, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, he10])
  refine ⟨_, .free s50 (.free s51 (.free s52 (.free s53 (.free s54 (.free s55 (.refl _)))))),
    halloc4, hlive4, ?_⟩
  cases rest with
  | nil => exact sret
  | cons caller tail => exact sret

/-! ## `arrAllocCell` free-list pop, bump refill, and OOM theorems -/

/-- `arrAllocCell` pops `addr` from a non-empty class free list `freeLists cls = addr :: tail`
(where `cls = classForFast words`), consumes 2 clock charges, preserves `ArrayAllocator`
with `freeLists[cls ↦ tail]`, and initializes `LiveArrayCell` at `addr`. -/
theorem arrAllocCell_free_at_ret {mainFn : FunId}
    {mem : Memory} {context base bump limit addr : Word} {freeLists : Nat → List Word}
    {tail : List Word} {kind : ArrayKind} {words : Nat} {rest : List Frame}
    (halloc : ArrayAllocator mem context base bump limit freeLists)
    (h3 : 3 ≤ words) (hhi : words ≤ maxCellWords)
    (hlist : freeLists (classForFast words) = addr :: tail) :
    let cls := classForFast words
    let lists' := fun c => if c = cls then tail else freeLists c
    ∃ mem' s',
      Sem.Star (semStep (arrayProgram mainFn))
        (State.mk mem context
          ({ fn := fnAllocCell, label := 0, pos := 0,
             env := (({} : Env).insert 0 (UInt64.ofNat words)).insert 1 (scanTagFixed kind) } :: rest))
        2 s' ∧
      ArrayAllocator mem' context base bump limit lists' ∧
      LiveArrayCell mem' addr 1 cls (wordCapOfClass cls) (emptyValOfKind kind) ∧
      (match rest with
       | [] => semStep (arrayProgram mainFn) s' = .done ([addr], mem')
       | caller :: ctail =>
           ∀ dst, caller.dsts = [dst] →
             semStep (arrayProgram mainFn) s' =
               .next (State.mk mem' context ({ caller with env := caller.env.insert dst addr, dsts := [] } :: ctail)) false) := by
  intro cls lists'
  have hf := arrayProgram_func_allocCell mainFn
  obtain ⟨hcls_lo, hcls_hi, _⟩ := classFor_ge_three h3 hhi
  have hcls1 : 1 ≤ cls := by unfold minArrayClass at hcls_lo; omega
  have hhead := halloc.free_heads cls hcls1 hcls_hi
  rw [hlist] at hhead
  have hchain := halloc.free_chains cls
  rw [hlist] at hchain
  have hin := halloc.free_in_arena cls addr (by rw [hlist]; exact List.mem_cons_self)
  have hbl := halloc.bump_le_limit
  obtain ⟨hwr_head, halloc1, hdisj⟩ := halloc.pop_free_head hcls_lo hcls_hi hlist
  let e0 : Env := (({} : Env).insert 0 (UInt64.ofNat words)).insert 1 (scanTagFixed kind)
  let e2 := e0.insert 2 (UInt64.ofNat cls)
  let e3 := e2.insert 3 (UInt64.ofNat (classWords cls))
  let e4 := e3.insert 4 addr
  let e5 := e4.insert 5 (tail.headD 0)
  let e_b5 := e5.insert 10 addr
  have s00 := step_call (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 0) (pos := 0) (rest := rest)
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (evalArgs_singleton (by simp only [v, Arg.eval, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]; rfl))
    (arrayProgram_func_classFor mainFn) rfl
  have c0 := arrClassFor_call_star (arrayProgram_func_classFor mainFn) (mem := mem) (context := context)
    (caller := { fn := fnAllocCell, label := 0, pos := 1, env := e0, dsts := [2] }) (tail := rest)
    (dst := 2) rfl (by omega) hhi
  have s01 := step_call (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 0) (pos := 1) (rest := rest)
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (evalArgs_singleton (by simp only [v, Arg.eval, e2, env_get_insert_self]; rfl))
    (arrayProgram_func_classWords mainFn) rfl
  have c1 := arrClassWords_call_star (arrayProgram_func_classWords mainFn) (mem := mem) (context := context)
    (caller := { fn := fnAllocCell, label := 0, pos := 2, env := e2, dsts := [3] }) (tail := rest)
    (dst := 3) rfl hcls1 hcls_hi
  have s02 := step_assign (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 0) (pos := 2) (rest := rest)
    (mem := mem) (context := context) (env := e3) hf rfl (by decide) rfl
    (rhs_load_eval (ctxHeadAddr_eval (by simp only [e3, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e2]))
      (wordAt_load64 hhead))
  have hne0 : Cond.holds .eq .w64 addr (UInt64.ofNat 0) = false := by
    rw [cond_eq_w64]; exact beq_false_of_ne hin.2.2.2
  have s0_1 := step_br_false (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 0) (rest := rest)
    (mem := mem) (context := context) (env := e4) hf rfl rfl
    (by simp only [v, Arg.eval, e4, env_get_insert_self]) rfl hne0 rfl rfl rfl
  have s10 := step_assign (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 1) (pos := 0) (rest := rest)
    (mem := mem) (context := context) (env := e4) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr0_eval (by simp only [e4, env_get_insert_self]))
      (wordAt_load64 hchain.1))
  have s11 := step_store (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 1) (pos := 1) (rest := rest)
    (mem := mem) (context := context) (env := e5) hf rfl (by decide) rfl
    (ctxHeadAddr_eval (by simp only [e5, e4, e3, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e2]; rfl))
    (by simp only [v, Arg.eval, e5, env_get_insert_self]) hwr_head
  have s15 := step_jump (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 1) (rest := rest)
    (mem := mem.write .w64 (freeHeadAddress context (UInt64.ofNat cls)) (tail.headD 0))
    (context := context) (env := e5) hf rfl rfl
    (evalArgs_singleton (by simp only [v, Arg.eval, e5, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e4]; rfl))
    rfl rfl
  obtain ⟨s', hstar5, halloc4, hlive4, hret⟩ :=
    arrAllocCell_block5_at_ret (mainFn := mainFn) (rest := rest) (e5 := e_b5)
      halloc1 hcls_lo hcls_hi hin.2.2.1 hin.2.2.2 hin.1 (by change addr.toNat + classBytes cls ≤ limit.toNat; omega) hdisj
      (by simp only [e_b5, e5, e4, e3, e2, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e0]; rfl)
      (by simp only [e_b5, e5, e4, e3, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e2]; rfl)
      (by simp only [e_b5, e5, e4, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e3]; rfl)
      (by simp only [e_b5, env_get_insert_self])
  refine ⟨_, s', ?_, halloc4, hlive4, hret⟩
  have hpref : Sem.Star (semStep (arrayProgram mainFn))
      (State.mk mem context ({ fn := fnAllocCell, label := 0, pos := 0, env := e0 } :: rest))
      2 (State.mk (mem.write .w64 (freeHeadAddress context (UInt64.ofNat cls)) (tail.headD 0)) context
          ({ fn := fnAllocCell, label := 5, pos := 0, env := e_b5 } :: rest)) :=
    Sem.Star.charge s00 (c0.trans (.charge s01 (c1.trans
      (.free s02 (.free s0_1 (.free s10 (.free s11 (.free s15 (.refl _)))))))))
  exact hpref.trans hstar5

/-- `arrAllocCell` bump-allocates at `bump` when `freeLists cls = []` and
`bump + classBytes cls ≤ limit`, consumes 2 clock charges, preserves `ArrayAllocator`
at `bump + classBytes cls`, and initializes `LiveArrayCell` at `bump`. -/
theorem arrAllocCell_bump_at_ret {mainFn : FunId}
    {mem : Memory} {context base bump limit : Word} {freeLists : Nat → List Word}
    {kind : ArrayKind} {words : Nat} {rest : List Frame}
    (halloc : ArrayAllocator mem context base bump limit freeLists)
    (h3 : 3 ≤ words) (hhi : words ≤ maxCellWords)
    (hempty : freeLists (classForFast words) = [])
    (hroom : bump.toNat + classBytes (classForFast words) ≤ limit.toNat) :
    let cls := classForFast words
    let newBump := bump + UInt64.ofNat (classBytes cls)
    ∃ mem' s',
      Sem.Star (semStep (arrayProgram mainFn))
        (State.mk mem context
          ({ fn := fnAllocCell, label := 0, pos := 0,
             env := (({} : Env).insert 0 (UInt64.ofNat words)).insert 1 (scanTagFixed kind) } :: rest))
        2 s' ∧
      ArrayAllocator mem' context base newBump limit freeLists ∧
      LiveArrayCell mem' bump 1 cls (wordCapOfClass cls) (emptyValOfKind kind) ∧
      (match rest with
       | [] => semStep (arrayProgram mainFn) s' = .done ([bump], mem')
       | caller :: ctail =>
           ∀ dst, caller.dsts = [dst] →
             semStep (arrayProgram mainFn) s' =
               .next (State.mk mem' context ({ caller with env := caller.env.insert dst bump, dsts := [] } :: ctail)) false) := by
  intro cls newBump
  have hf := arrayProgram_func_allocCell mainFn
  obtain ⟨hcls_lo, hcls_hi, _⟩ := classFor_ge_three h3 hhi
  have hcls1 : 1 ≤ cls := by unfold minArrayClass at hcls_lo; omega
  have hhead := halloc.free_heads cls hcls1 hcls_hi
  rw [hempty] at hhead
  have hcw_le : classWords cls ≤ maxCellWords := classWords_le_max hcls_hi
  have hm_eq : maxCellWords = 2 ^ 26 := maxCellWords_eq
  have hlim := halloc.limit_fit
  have hcl := halloc.context_lower
  have hcb := halloc.context_before
  have hbb := halloc.base_le_bump
  have hnz_bump : bump ≠ 0 := by intro h0; rw [h0] at hbb; simp at hbb; omega
  have hshl_cb : classWords cls <<< 3 = classBytes cls := by
    rw [Nat.shiftLeft_eq]; unfold classBytes; omega
  have hcb_lt : classBytes cls < 2 ^ 64 := by unfold classBytes; omega
  have hnb_nat : newBump.toNat = bump.toNat + classBytes cls := addr_toNat (by omega)
  have hule : Cond.holds .ule .w64 newBump limit = true := by
    rw [cond_ule_w64, hnb_nat]; exact decide_eq_true hroom
  obtain ⟨hwr_bump, halloc1, hdisj⟩ := halloc.advance_bump (cls := cls) hroom
  let e0 : Env := (({} : Env).insert 0 (UInt64.ofNat words)).insert 1 (scanTagFixed kind)
  let e2 := e0.insert 2 (UInt64.ofNat cls)
  let e3 := e2.insert 3 (UInt64.ofNat (classWords cls))
  let e4 := e3.insert 4 0
  let e6 := e4.insert 6 bump
  let e7 := e6.insert 7 limit
  let e8 := e7.insert 8 (UInt64.ofNat (classBytes cls))
  let e9 := e8.insert 9 newBump
  let e_b5 := e9.insert 10 bump
  have s00 := step_call (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 0) (pos := 0) (rest := rest)
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (evalArgs_singleton (by simp only [v, Arg.eval, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]; rfl))
    (arrayProgram_func_classFor mainFn) rfl
  have c0 := arrClassFor_call_star (arrayProgram_func_classFor mainFn) (mem := mem) (context := context)
    (caller := { fn := fnAllocCell, label := 0, pos := 1, env := e0, dsts := [2] }) (tail := rest)
    (dst := 2) rfl (by omega) hhi
  have s01 := step_call (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 0) (pos := 1) (rest := rest)
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (evalArgs_singleton (by simp only [v, Arg.eval, e2, env_get_insert_self]; rfl))
    (arrayProgram_func_classWords mainFn) rfl
  have c1 := arrClassWords_call_star (arrayProgram_func_classWords mainFn) (mem := mem) (context := context)
    (caller := { fn := fnAllocCell, label := 0, pos := 2, env := e2, dsts := [3] }) (tail := rest)
    (dst := 3) rfl hcls1 hcls_hi
  have s02 := step_assign (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 0) (pos := 2) (rest := rest)
    (mem := mem) (context := context) (env := e3) hf rfl (by decide) rfl
    (rhs_load_eval (ctxHeadAddr_eval (by simp only [e3, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e2]))
      (wordAt_load64 hhead))
  have s0_2 := step_br_true (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 0) (rest := rest)
    (mem := mem) (context := context) (env := e4) hf rfl rfl
    (by simp only [v, Arg.eval, e4, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s20 := step_assign (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 2) (pos := 0) (rest := rest)
    (mem := mem) (context := context) (env := e4) hf rfl (by decide) rfl
    (rhs_load_eval (ctxAddr_eval_bump e4 context) (wordAt_load64 halloc.bump_word))
  have s21 := step_assign (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 2) (pos := 1) (rest := rest)
    (mem := mem) (context := context) (env := e6) hf rfl (by decide) rfl
    (rhs_load_eval (ctxAddr_eval_limit e6 context) (wordAt_load64 halloc.limit_word))
  have hshl_op : BinOp.eval .shl .w64 (UInt64.ofNat (classWords cls)) (UInt64.ofNat 3) =
      some (UInt64.ofNat (classBytes cls)) := by
    rw [← hshl_cb]; exact binOp_shl64 (classWords cls) 3 (by decide) (by omega) (by rw [hshl_cb]; omega)
  have s22 := step_assign (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 2) (pos := 2) (rest := rest)
    (mem := mem) (context := context) (env := e7) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e7, e6, e4, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e3]) rfl hshl_op)
  have hovf : Ovf.eval .addC bump (UInt64.ofNat (classBytes cls)) = (newBump, false) :=
    ovf_addC_no_ovf (by rw [u64_toNat_ofNat_lt hcb_lt]; omega)
  have s23 := step_brOvf_ok (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 2) (rest := rest)
    (mem := mem) (context := context) (env := e8) hf rfl rfl
    (by simp only [v, Arg.eval, e8, e7, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e6])
    (by simp only [v, Arg.eval, e8, env_get_insert_self]) hovf rfl rfl rfl
  have s34 := step_br_true (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 3) (rest := rest)
    (mem := mem) (context := context) (env := e9) hf rfl rfl
    (by simp only [v, Arg.eval, e9, env_get_insert_self])
    (by simp only [v, Arg.eval, e9, e8, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e7]) hule rfl rfl rfl
  have s40 := step_store (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 4) (pos := 0) (rest := rest)
    (mem := mem) (context := context) (env := e9) hf rfl (by decide) rfl
    (ctxAddr_eval_bump e9 context) (by simp only [v, Arg.eval, e9, env_get_insert_self]; rfl) hwr_bump
  have s45 := step_jump (p := arrayProgram mainFn) (fn := fnAllocCell) (lbl := 4) (rest := rest)
    (mem := mem.write .w64 (bumpAddress context) newBump) (context := context) (env := e9) hf rfl rfl
    (evalArgs_singleton (by simp only [v, Arg.eval, e9, e8, e7, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e6]; rfl))
    rfl rfl
  obtain ⟨s', hstar5, halloc4, hlive4, hret⟩ :=
    arrAllocCell_block5_at_ret (mainFn := mainFn) (rest := rest) (e5 := e_b5)
      halloc1 hcls_lo hcls_hi halloc.bump_aligned hnz_bump hbb hroom hdisj
      (by simp only [e_b5, e9, e8, e7, e6, e4, e3, e2, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e0]; rfl)
      (by simp only [e_b5, e9, e8, e7, e6, e4, e3, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e2]; rfl)
      (by simp only [e_b5, e9, e8, e7, e6, e4, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e3]; rfl)
      (by simp only [e_b5, env_get_insert_self])
  refine ⟨_, s', ?_, halloc4, hlive4, hret⟩
  have hpref : Sem.Star (semStep (arrayProgram mainFn))
      (State.mk mem context ({ fn := fnAllocCell, label := 0, pos := 0, env := e0 } :: rest))
      2 (State.mk (mem.write .w64 (bumpAddress context) newBump) context
          ({ fn := fnAllocCell, label := 5, pos := 0, env := e_b5 } :: rest)) :=
    Sem.Star.charge s00 (c0.trans (.charge s01 (c1.trans
      (.free s02 (.free s0_2 (.free s20 (.free s21 (.free s22
        (.free s23 (.free s34 (.free s40 (.free s45 (.refl _)))))))))))))
  exact hpref.trans hstar5

/-- `arrAllocCell` cleanly fails `.resource .heap` when the class free list is empty
and the bump arena has insufficient remaining capacity (`limit < bump + classBytes cls`). -/
theorem arrAllocCell_oom_eval {mem : Memory} {context base bump limit : Word}
    {freeLists : Nat → List Word} (kind : ArrayKind) {words : Nat}
    (halloc : ArrayAllocator mem context base bump limit freeLists)
    (h3 : 3 ≤ words) (hhi : words ≤ maxCellWords)
    (hempty : freeLists (classForFast words) = [])
    (hoom : limit.toNat < bump.toNat + classBytes (classForFast words)) (clock : Nat) :
    eval (arrayProgram fnAllocCell) (clock + 2) [UInt64.ofNat words, scanTagFixed kind] mem context =
      .resource .heap := by
  let cls := classForFast words
  have hf := arrayProgram_func_allocCell fnAllocCell
  obtain ⟨hcls_lo, hcls_hi, _⟩ := classFor_ge_three h3 hhi
  have hcls1 : 1 ≤ cls := by unfold minArrayClass at hcls_lo; omega
  have hhead := halloc.free_heads cls hcls1 hcls_hi
  rw [hempty] at hhead
  have hcw_le : classWords cls ≤ maxCellWords := classWords_le_max hcls_hi
  have hm_eq : maxCellWords = 2 ^ 26 := maxCellWords_eq
  have hlim := halloc.limit_fit
  have hbl := halloc.bump_le_limit
  have hshl_cb : classWords cls <<< 3 = classBytes cls := by
    rw [Nat.shiftLeft_eq]; unfold classBytes; omega
  have hcb_lt : classBytes cls < 2 ^ 64 := by unfold classBytes; omega
  let newBump := bump + UInt64.ofNat (classBytes cls)
  have hnb_nat : newBump.toNat = bump.toNat + classBytes cls := addr_toNat (by omega)
  have hoom' : limit.toNat < bump.toNat + classBytes cls := hoom
  have hule_f : Cond.holds .ule .w64 newBump limit = false := by
    rw [cond_ule_w64, hnb_nat]; exact decide_eq_false (by omega)
  let e0 : Env := (({} : Env).insert 0 (UInt64.ofNat words)).insert 1 (scanTagFixed kind)
  let e2 := e0.insert 2 (UInt64.ofNat cls)
  let e3 := e2.insert 3 (UInt64.ofNat (classWords cls))
  let e4 := e3.insert 4 0
  let e6 := e4.insert 6 bump
  let e7 := e6.insert 7 limit
  let e8 := e7.insert 8 (UInt64.ofNat (classBytes cls))
  let e9 := e8.insert 9 newBump
  have hinit := state_initial_of (p := arrayProgram fnAllocCell)
    (args := [UInt64.ofNat words, scanTagFixed kind]) (mem := mem) (context := context) hf rfl
  have s00 := step_call (p := arrayProgram fnAllocCell) (fn := fnAllocCell) (lbl := 0) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
    (evalArgs_singleton (by simp only [v, Arg.eval, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]; rfl))
    (arrayProgram_func_classFor fnAllocCell) rfl
  have c0 := arrClassFor_call_star (arrayProgram_func_classFor fnAllocCell) (mem := mem) (context := context)
    (caller := { fn := fnAllocCell, label := 0, pos := 1, env := e0, dsts := [2] }) (tail := [])
    (dst := 2) rfl (by omega) hhi
  have s01 := step_call (p := arrayProgram fnAllocCell) (fn := fnAllocCell) (lbl := 0) (pos := 1) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
    (evalArgs_singleton (by simp only [v, Arg.eval, e2, env_get_insert_self]; rfl))
    (arrayProgram_func_classWords fnAllocCell) rfl
  have c1 := arrClassWords_call_star (arrayProgram_func_classWords fnAllocCell) (mem := mem) (context := context)
    (caller := { fn := fnAllocCell, label := 0, pos := 2, env := e2, dsts := [3] }) (tail := [])
    (dst := 3) rfl hcls1 hcls_hi
  have s02 := step_assign (p := arrayProgram fnAllocCell) (fn := fnAllocCell) (lbl := 0) (pos := 2) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl (by decide) rfl
    (rhs_load_eval (ctxHeadAddr_eval (by simp only [e3, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e2]))
      (wordAt_load64 hhead))
  have s0_2 := step_br_true (p := arrayProgram fnAllocCell) (fn := fnAllocCell) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e4) hf rfl rfl
    (by simp only [v, Arg.eval, e4, env_get_insert_self]; rfl) rfl (by decide) rfl rfl rfl
  have s20 := step_assign (p := arrayProgram fnAllocCell) (fn := fnAllocCell) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e4) hf rfl (by decide) rfl
    (rhs_load_eval (ctxAddr_eval_bump e4 context) (wordAt_load64 halloc.bump_word))
  have s21 := step_assign (p := arrayProgram fnAllocCell) (fn := fnAllocCell) (lbl := 2) (pos := 1) (rest := [])
    (mem := mem) (context := context) (env := e6) hf rfl (by decide) rfl
    (rhs_load_eval (ctxAddr_eval_limit e6 context) (wordAt_load64 halloc.limit_word))
  have hshl_op : BinOp.eval .shl .w64 (UInt64.ofNat (classWords cls)) (UInt64.ofNat 3) =
      some (UInt64.ofNat (classBytes cls)) := by
    rw [← hshl_cb]; exact binOp_shl64 (classWords cls) 3 (by decide) (by omega) (by rw [hshl_cb]; omega)
  have s22 := step_assign (p := arrayProgram fnAllocCell) (fn := fnAllocCell) (lbl := 2) (pos := 2) (rest := [])
    (mem := mem) (context := context) (env := e7) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e7, e6, e4, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e3]) rfl hshl_op)
  have hovf : Ovf.eval .addC bump (UInt64.ofNat (classBytes cls)) = (newBump, false) :=
    ovf_addC_no_ovf (by rw [u64_toNat_ofNat_lt hcb_lt]; omega)
  have s23 := step_brOvf_ok (p := arrayProgram fnAllocCell) (fn := fnAllocCell) (lbl := 2) (rest := [])
    (mem := mem) (context := context) (env := e8) hf rfl rfl
    (by simp only [v, Arg.eval, e8, e7, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e6])
    (by simp only [v, Arg.eval, e8, env_get_insert_self]) hovf rfl rfl rfl
  have s36 := step_br_false (p := arrayProgram fnAllocCell) (fn := fnAllocCell) (lbl := 3) (rest := [])
    (mem := mem) (context := context) (env := e9) hf rfl rfl
    (by simp only [v, Arg.eval, e9, env_get_insert_self])
    (by simp only [v, Arg.eval, e9, e8, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e7]) hule_f rfl rfl rfl
  have sfin := final_fail (p := arrayProgram fnAllocCell) (fn := fnAllocCell) (lbl := 6) (rest := [])
    (mem := mem) (context := context) (env := e9) hf rfl rfl
  apply (runs_eval hinit).eq
  have hstar := Sem.Star.charge s00 (c0.trans (.charge s01 (c1.trans
    (.free s02 (.free s0_2 (.free s20 (.free s21 (.free s22 (.free s23 (.free s36 (.refl _)))))))))))
  simpa using Sem.Reaches.star hstar (k := clock) (.final sfin)

/-! ## Top-level typed array constructors (`arrEmptyCapBoxed`, `arrEmptyCapLimbs`, `byteArrEmptyCap`) -/

private theorem arrEmptyCapWord_free_eval {mainFn : FunId} {kind : ArrayKind} {name : String}
    (hf : (arrayProgram mainFn).funcs[mainFn]? = some (arrEmptyCapWord kind name))
    {mem : Memory} {context base bump limit addr : Word} {freeLists : Nat → List Word}
    {tail : List Word} {cap : Nat}
    (halloc : ArrayAllocator mem context base bump limit freeLists)
    (hcap : cap ≤ maxWordCap)
    (hlist : freeLists (classForFast (wordArrayWords cap)) = addr :: tail) (clock : Nat) :
    let cls := classForFast (wordArrayWords cap)
    let lists' := fun c => if c = cls then tail else freeLists c
    ∃ mem',
      eval (arrayProgram mainFn) (clock + 3) [UInt64.ofNat cap] mem context = .ok ([addr], mem') ∧
      cap ≤ wordCapOfClass cls ∧
      ArrayAllocator mem' context base bump limit lists' ∧
      LiveArrayCell mem' addr 1 cls (wordCapOfClass cls) (emptyValOfKind kind) := by
  intro cls lists'
  have hw3 := wordArrayWords_ge_three cap
  have hw_le := wordArrayWords_le_max hcap
  have hm_eq : maxCellWords = 2 ^ 26 := maxCellWords_eq
  have hcap_lt : cap + 3 < 2 ^ 64 := by unfold wordArrayWords arrayHeaderWords at hw_le; omega
  have hcf := classForFast_eq (by omega) hw_le
  obtain ⟨_, _, hcap_fit, _⟩ := wordCapOfClass_spec hcf
  let e0 : Env := ({} : Env).insert 0 (UInt64.ofNat cap)
  let e1 := e0.insert 1 (UInt64.ofNat (wordArrayWords cap))
  have hinit := state_initial_of (p := arrayProgram mainFn) (args := [UInt64.ofNat cap])
    (mem := mem) (context := context) hf rfl
  have hovf : Ovf.eval .addC (UInt64.ofNat cap) (UInt64.ofNat 3) =
      (UInt64.ofNat (wordArrayWords cap), false) := by
    have h1 := ovf_addC_no_ovf (a := UInt64.ofNat cap) (b := UInt64.ofNat 3)
      (by rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)]; omega)
    rw [u64_add_ofNat hcap_lt] at h1
    simpa [wordArrayWords, arrayHeaderWords, Nat.add_comm] using h1
  have s01 := step_brOvf_ok (p := arrayProgram mainFn) (fn := mainFn) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl rfl
    (by simp only [v, Arg.eval, e0, env_get_insert_self]) rfl hovf rfl rfl rfl
  have s1t := step_tail (p := arrayProgram mainFn) (fn := mainFn) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (evalArgs_pair (by simp only [v, Arg.eval, e1, env_get_insert_self]; rfl) rfl)
    (arrayProgram_func_allocCell mainFn) rfl
  obtain ⟨mem', s', hstar, halloc', hlive', hdone⟩ :=
    arrAllocCell_free_at_ret (mainFn := mainFn) (kind := kind) (rest := []) halloc hw3 hw_le hlist
  refine ⟨mem', ?_, hcap_fit, halloc', hlive'⟩
  apply (runs_eval hinit).eq
  have hfull : Sem.Star (semStep (arrayProgram mainFn))
      (State.mk mem context [{ fn := mainFn, label := 0, pos := 0, env := e0 }]) 3 s' :=
    Sem.Star.free s01 (.charge s1t hstar)
  simpa using Sem.Reaches.star hfull (k := clock) (.final (by rw [hdone]; exact .done))

private theorem arrEmptyCapWord_bump_eval {mainFn : FunId} {kind : ArrayKind} {name : String}
    (hf : (arrayProgram mainFn).funcs[mainFn]? = some (arrEmptyCapWord kind name))
    {mem : Memory} {context base bump limit : Word} {freeLists : Nat → List Word} {cap : Nat}
    (halloc : ArrayAllocator mem context base bump limit freeLists)
    (hcap : cap ≤ maxWordCap)
    (hempty : freeLists (classForFast (wordArrayWords cap)) = [])
    (hroom : bump.toNat + classBytes (classForFast (wordArrayWords cap)) ≤ limit.toNat) (clock : Nat) :
    let cls := classForFast (wordArrayWords cap)
    let newBump := bump + UInt64.ofNat (classBytes cls)
    ∃ mem',
      eval (arrayProgram mainFn) (clock + 3) [UInt64.ofNat cap] mem context = .ok ([bump], mem') ∧
      cap ≤ wordCapOfClass cls ∧
      ArrayAllocator mem' context base newBump limit freeLists ∧
      LiveArrayCell mem' bump 1 cls (wordCapOfClass cls) (emptyValOfKind kind) := by
  intro cls newBump
  have hw3 := wordArrayWords_ge_three cap
  have hw_le := wordArrayWords_le_max hcap
  have hm_eq : maxCellWords = 2 ^ 26 := maxCellWords_eq
  have hcap_lt : cap + 3 < 2 ^ 64 := by unfold wordArrayWords arrayHeaderWords at hw_le; omega
  have hcf := classForFast_eq (by omega) hw_le
  obtain ⟨_, _, hcap_fit, _⟩ := wordCapOfClass_spec hcf
  let e0 : Env := ({} : Env).insert 0 (UInt64.ofNat cap)
  let e1 := e0.insert 1 (UInt64.ofNat (wordArrayWords cap))
  have hinit := state_initial_of (p := arrayProgram mainFn) (args := [UInt64.ofNat cap])
    (mem := mem) (context := context) hf rfl
  have hovf : Ovf.eval .addC (UInt64.ofNat cap) (UInt64.ofNat 3) =
      (UInt64.ofNat (wordArrayWords cap), false) := by
    have h1 := ovf_addC_no_ovf (a := UInt64.ofNat cap) (b := UInt64.ofNat 3)
      (by rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)]; omega)
    rw [u64_add_ofNat hcap_lt] at h1
    simpa [wordArrayWords, arrayHeaderWords, Nat.add_comm] using h1
  have s01 := step_brOvf_ok (p := arrayProgram mainFn) (fn := mainFn) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl rfl
    (by simp only [v, Arg.eval, e0, env_get_insert_self]) rfl hovf rfl rfl rfl
  have s1t := step_tail (p := arrayProgram mainFn) (fn := mainFn) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl rfl
    (evalArgs_pair (by simp only [v, Arg.eval, e1, env_get_insert_self]; rfl) rfl)
    (arrayProgram_func_allocCell mainFn) rfl
  obtain ⟨mem', s', hstar, halloc', hlive', hdone⟩ :=
    arrAllocCell_bump_at_ret (mainFn := mainFn) (kind := kind) (rest := []) halloc hw3 hw_le hempty hroom
  refine ⟨mem', ?_, hcap_fit, halloc', hlive'⟩
  apply (runs_eval hinit).eq
  have hfull : Sem.Star (semStep (arrayProgram mainFn))
      (State.mk mem context [{ fn := mainFn, label := 0, pos := 0, env := e0 }]) 3 s' :=
    Sem.Star.free s01 (.charge s1t hstar)
  simpa using Sem.Reaches.star hfull (k := clock) (.final (by rw [hdone]; exact .done))

/-- Allocating an empty boxed `Array α` from a non-empty free list establishes
`LiveArrayCell` with capacity `wordCapOfClass cls ≥ cap` and preserves `ArrayAllocator`. -/
theorem arrEmptyCapBoxed_free_eval {mem : Memory} {context base bump limit addr : Word}
    {freeLists : Nat → List Word} {tail : List Word} {cap : Nat}
    (halloc : ArrayAllocator mem context base bump limit freeLists)
    (hcap : cap ≤ maxWordCap)
    (hlist : freeLists (classForFast (wordArrayWords cap)) = addr :: tail) (clock : Nat) :
    let cls := classForFast (wordArrayWords cap)
    let lists' := fun c => if c = cls then tail else freeLists c
    ∃ mem',
      eval (arrayProgram fnEmptyCapBoxed) (clock + 3) [UInt64.ofNat cap] mem context = .ok ([addr], mem') ∧
      cap ≤ wordCapOfClass cls ∧
      ArrayAllocator mem' context base bump limit lists' ∧
      LiveArrayCell mem' addr 1 cls (wordCapOfClass cls) (.boxed []) :=
  arrEmptyCapWord_free_eval (arrayProgram_func_emptyCapBoxed fnEmptyCapBoxed) halloc hcap hlist clock

/-- Allocating an empty boxed `Array α` from the bump arena establishes
`LiveArrayCell` with capacity `wordCapOfClass cls ≥ cap` and preserves `ArrayAllocator`. -/
theorem arrEmptyCapBoxed_bump_eval {mem : Memory} {context base bump limit : Word}
    {freeLists : Nat → List Word} {cap : Nat}
    (halloc : ArrayAllocator mem context base bump limit freeLists)
    (hcap : cap ≤ maxWordCap)
    (hempty : freeLists (classForFast (wordArrayWords cap)) = [])
    (hroom : bump.toNat + classBytes (classForFast (wordArrayWords cap)) ≤ limit.toNat) (clock : Nat) :
    let cls := classForFast (wordArrayWords cap)
    let newBump := bump + UInt64.ofNat (classBytes cls)
    ∃ mem',
      eval (arrayProgram fnEmptyCapBoxed) (clock + 3) [UInt64.ofNat cap] mem context = .ok ([bump], mem') ∧
      cap ≤ wordCapOfClass cls ∧
      ArrayAllocator mem' context base newBump limit freeLists ∧
      LiveArrayCell mem' bump 1 cls (wordCapOfClass cls) (.boxed []) :=
  arrEmptyCapWord_bump_eval (arrayProgram_func_emptyCapBoxed fnEmptyCapBoxed) halloc hcap hempty hroom clock

/-- Allocating an empty unboxed `LimbArray` (`Array UInt64`) from a non-empty free list
establishes `LiveArrayCell` with capacity `wordCapOfClass cls ≥ cap` and preserves `ArrayAllocator`. -/
theorem arrEmptyCapLimbs_free_eval {mem : Memory} {context base bump limit addr : Word}
    {freeLists : Nat → List Word} {tail : List Word} {cap : Nat}
    (halloc : ArrayAllocator mem context base bump limit freeLists)
    (hcap : cap ≤ maxWordCap)
    (hlist : freeLists (classForFast (wordArrayWords cap)) = addr :: tail) (clock : Nat) :
    let cls := classForFast (wordArrayWords cap)
    let lists' := fun c => if c = cls then tail else freeLists c
    ∃ mem',
      eval (arrayProgram fnEmptyCapLimbs) (clock + 3) [UInt64.ofNat cap] mem context = .ok ([addr], mem') ∧
      cap ≤ wordCapOfClass cls ∧
      ArrayAllocator mem' context base bump limit lists' ∧
      LiveArrayCell mem' addr 1 cls (wordCapOfClass cls) (.limbs []) :=
  arrEmptyCapWord_free_eval (arrayProgram_func_emptyCapLimbs fnEmptyCapLimbs) halloc hcap hlist clock

/-- Allocating an empty unboxed `LimbArray` (`Array UInt64`) from the bump arena
establishes `LiveArrayCell` with capacity `wordCapOfClass cls ≥ cap` and preserves `ArrayAllocator`. -/
theorem arrEmptyCapLimbs_bump_eval {mem : Memory} {context base bump limit : Word}
    {freeLists : Nat → List Word} {cap : Nat}
    (halloc : ArrayAllocator mem context base bump limit freeLists)
    (hcap : cap ≤ maxWordCap)
    (hempty : freeLists (classForFast (wordArrayWords cap)) = [])
    (hroom : bump.toNat + classBytes (classForFast (wordArrayWords cap)) ≤ limit.toNat) (clock : Nat) :
    let cls := classForFast (wordArrayWords cap)
    let newBump := bump + UInt64.ofNat (classBytes cls)
    ∃ mem',
      eval (arrayProgram fnEmptyCapLimbs) (clock + 3) [UInt64.ofNat cap] mem context = .ok ([bump], mem') ∧
      cap ≤ wordCapOfClass cls ∧
      ArrayAllocator mem' context base newBump limit freeLists ∧
      LiveArrayCell mem' bump 1 cls (wordCapOfClass cls) (.limbs []) :=
  arrEmptyCapWord_bump_eval (arrayProgram_func_emptyCapLimbs fnEmptyCapLimbs) halloc hcap hempty hroom clock

/-- Allocating an empty unboxed `ByteArray` (or UTF-8 `String` buffer) from the bump
arena sets `cap = byteCapOfClass cls = 8 * (classWords cls - 3) ≥ byteCap`, establishes
`LiveArrayCell` on `.bytes []`, and preserves `ArrayAllocator`. -/
theorem byteArrEmptyCap_bump_eval {mem : Memory} {context base bump limit : Word}
    {freeLists : Nat → List Word} {byteCap : Nat}
    (halloc : ArrayAllocator mem context base bump limit freeLists)
    (hcap : byteCap ≤ maxByteCap)
    (hempty : freeLists (classForFast (byteArrayWords byteCap)) = [])
    (hroom : bump.toNat + classBytes (classForFast (byteArrayWords byteCap)) ≤ limit.toNat) (clock : Nat) :
    let cls := classForFast (byteArrayWords byteCap)
    let newBump := bump + UInt64.ofNat (classBytes cls)
    ∃ mem',
      eval (arrayProgram fnByteEmptyCap) (clock + 3) [UInt64.ofNat byteCap] mem context = .ok ([bump], mem') ∧
      byteCap ≤ byteCapOfClass cls ∧
      ArrayAllocator mem' context base newBump limit freeLists ∧
      LiveArrayCell mem' bump 1 cls (byteCapOfClass cls) (.bytes []) := by
  intro cls newBump
  have hf := arrayProgram_func_byteEmptyCap fnByteEmptyCap
  have hw3 := byteArrayWords_ge_three byteCap
  have hw_le := byteArrayWords_le_max hcap
  have hm_eq : maxCellWords = 2 ^ 26 := maxCellWords_eq
  have hcf := classForFast_eq (by omega) hw_le
  obtain ⟨hcls_lo, hcls_hi, hbcap_fit, _⟩ := byteCapOfClass_spec hcf
  have hmb : maxByteCap = 8 * (maxCellWords - 3) := rfl
  have hbc_lt : byteCap + 7 < 2 ^ 64 := by omega
  have hdiv_eq : (byteCap + 7) >>> 3 = (byteCap + 7) / 8 := by rw [Nat.shiftRight_eq_div_pow]
  have hbw_eq : (byteCap + 7) >>> 3 + 3 = byteArrayWords byteCap := by
    rw [hdiv_eq]; unfold byteArrayWords arrayHeaderWords; omega
  let e0 : Env := ({} : Env).insert 0 (UInt64.ofNat byteCap)
  let e1 := e0.insert 1 (UInt64.ofNat (byteCap + 7))
  let e2 := e1.insert 2 (UInt64.ofNat ((byteCap + 7) >>> 3))
  let e3 := e2.insert 3 (UInt64.ofNat (byteArrayWords byteCap))
  let e4 := e3.insert 4 bump
  let e5 := e4.insert 5 (UInt64.ofNat (wordCapOfClass cls))
  let e6 := e5.insert 6 (UInt64.ofNat (byteCapOfClass cls))
  have hinit := state_initial_of (p := arrayProgram fnByteEmptyCap) (args := [UInt64.ofNat byteCap])
    (mem := mem) (context := context) hf rfl
  have hovf1 : Ovf.eval .addC (UInt64.ofNat byteCap) (UInt64.ofNat 7) =
      (UInt64.ofNat (byteCap + 7), false) := by
    have h1 := ovf_addC_no_ovf (a := UInt64.ofNat byteCap) (b := UInt64.ofNat 7)
      (by rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)]; omega)
    rwa [u64_add_ofNat hbc_lt] at h1
  have hovf2 : Ovf.eval .addC (UInt64.ofNat ((byteCap + 7) >>> 3)) (UInt64.ofNat 3) =
      (UInt64.ofNat (byteArrayWords byteCap), false) := by
    have h1 := ovf_addC_no_ovf (a := UInt64.ofNat ((byteCap + 7) >>> 3)) (b := UInt64.ofNat 3)
      (by rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)]; omega)
    rw [u64_add_ofNat (by omega), hbw_eq] at h1
    exact h1
  have s01 := step_brOvf_ok (p := arrayProgram fnByteEmptyCap) (fn := fnByteEmptyCap) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl rfl
    (by simp only [v, Arg.eval, e0, env_get_insert_self]) rfl hovf1 rfl rfl rfl
  have s10 := step_assign (p := arrayProgram fnByteEmptyCap) (fn := fnByteEmptyCap) (lbl := 1) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e1, env_get_insert_self]) rfl
      (binOp_shr64 (byteCap + 7) 3 (by decide) hbc_lt))
  have s12 := step_brOvf_ok (p := arrayProgram fnByteEmptyCap) (fn := fnByteEmptyCap) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e2) hf rfl rfl
    (by simp only [v, Arg.eval, e2, env_get_insert_self]) rfl hovf2 rfl rfl rfl
  let caller : Frame := { fn := fnByteEmptyCap, label := 2, pos := 1, env := e3, dsts := [4] }
  have s20 := step_call (p := arrayProgram fnByteEmptyCap) (fn := fnByteEmptyCap) (lbl := 2) (pos := 0) (rest := [])
    (mem := mem) (context := context) (env := e3) hf rfl (by decide) rfl
    (evalArgs_pair (by simp only [v, Arg.eval, e3, env_get_insert_self]; rfl) rfl)
    (arrayProgram_func_allocCell fnByteEmptyCap) rfl
  obtain ⟨m4, s', hstar_alloc, halloc4, hlive4, hret_alloc⟩ :=
    arrAllocCell_bump_at_ret (mainFn := fnByteEmptyCap) (kind := .bytes) (rest := [caller])
      halloc hw3 hw_le hempty hroom
  have hcw_le : classWords cls ≤ maxCellWords := classWords_le_max hcls_hi
  have hwc_lt : wordCapOfClass cls < 2 ^ 64 := by unfold wordCapOfClass; omega
  have hbc_shl : wordCapOfClass cls <<< 3 = byteCapOfClass cls := by
    rw [Nat.shiftLeft_eq]; unfold wordCapOfClass byteCapOfClass; omega
  have hbc_lt64 : byteCapOfClass cls < 2 ^ 64 := by unfold byteCapOfClass; omega
  have h24 := hlive4.classBytes_ge_24
  have h16_toNat : (bump + 16).toNat = bump.toNat + 16 := addr_toNat_16 (by have := hlive4.fit; omega)
  let m5 := m4.write .w64 (bump + 16) (UInt64.ofNat (byteCapOfClass cls))
  have hwr5 : m4.write? .w64 (bump + 16) (UInt64.ofNat (byteCapOfClass cls)) = .ok m5 :=
    live_write64_ok hlive4 (off := 16) (by omega) _
  have halloc5 : ArrayAllocator m5 context base newBump limit freeLists := by
    apply halloc4.write64_disjoint (by rw [h16_toNat]; have := halloc.base_le_bump; omega)
      (by rw [h16_toNat]; omega)
    intro c a ha
    have hin := halloc.free_in_arena c a ha
    have hpos := halloc.free_cls_pos c a ha
    have h8 := classBytes_ge_eight hpos.1 hpos.2
    exact Or.inl (by rw [h16_toNat]; omega)
  have hlive5 : LiveArrayCell m5 bump 1 cls (byteCapOfClass cls) (.bytes []) := by
    have hfit := hlive4.fit
    have h8_toNat : (bump + 8).toNat = bump.toNat + 8 := addr_toNat_8 (by omega)
    refine ⟨hlive4.aligned, hlive4.nonzero, hlive4.cls_lo, hlive4.cls_hi, hlive4.refs_pos,
      hlive4.refs_le, hlive4.fit, by simp [ArrayVal.size], Nat.le_refl _,
      fun j hj => by simpa [m5, Memory.write] using hlive4.access j hj,
      wordAt_write64_disjoint hlive4.header_word (by rw [h16_toNat]; omega) (by omega) (Or.inl (by rw [h16_toNat]; omega)),
      wordAt_write64_disjoint hlive4.size_word (by rw [h16_toNat]; omega) (by rw [h8_toNat]; omega)
        (Or.inl (by rw [h8_toNat, h16_toNat]; omega)),
      wordAt_write64 hlive4.cap_word.readable,
      emptyValOfKind_payload m5 bump .bytes⟩
  have s21 := step_assign (p := arrayProgram fnByteEmptyCap) (fn := fnByteEmptyCap) (lbl := 2) (pos := 1) (rest := [])
    (mem := m4) (context := context) (env := e4) hf rfl (by decide) rfl
    (rhs_load_eval (cellAddr_eval_16 (by simp only [e4, env_get_insert_self]))
      (wordAt_load64 hlive4.cap_word))
  have hshl_cap : BinOp.eval .shl .w64 (UInt64.ofNat (wordCapOfClass cls)) (UInt64.ofNat 3) =
      some (UInt64.ofNat (byteCapOfClass cls)) := by
    rw [← hbc_shl]; exact binOp_shl64 (wordCapOfClass cls) 3 (by decide) hwc_lt (by rw [hbc_shl]; exact hbc_lt64)
  have s22 := step_assign (p := arrayProgram fnByteEmptyCap) (fn := fnByteEmptyCap) (lbl := 2) (pos := 2) (rest := [])
    (mem := m4) (context := context) (env := e5) hf rfl (by decide) rfl
    (rhs_bin_eval (by simp only [v, Arg.eval, e5, env_get_insert_self]) rfl hshl_cap)
  have s23 := step_store (p := arrayProgram fnByteEmptyCap) (fn := fnByteEmptyCap) (lbl := 2) (pos := 3) (rest := [])
    (mem := m4) (context := context) (env := e6) hf rfl (by decide) rfl
    (cellAddr_eval_16 (by simp only [e6, e5, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e4]))
    (by simp only [v, Arg.eval, e6, env_get_insert_self]) hwr5
  have sfin := final_ret_one (p := arrayProgram fnByteEmptyCap) (fn := fnByteEmptyCap) (lbl := 2)
    (mem := m5) (context := context) (env := e6) (res := bump) hf rfl rfl
    (by simp only [v, Arg.eval, e6, e5, env_get_insert, Nat.reduceEqDiff, ↓reduceIte, e4])
  refine ⟨m5, ?_, hbcap_fit, halloc5, hlive5⟩
  apply (runs_eval hinit).eq
  have hfull : Sem.Star (semStep (arrayProgram fnByteEmptyCap))
      (State.mk mem context [{ fn := fnByteEmptyCap, label := 0, pos := 0, env := e0 }]) 3
      (State.mk m5 context [{ fn := fnByteEmptyCap, label := 2, pos := 4, env := e6 }]) :=
    Sem.Star.free s01 (.free s10 (.free s12 (.charge s20
      (hstar_alloc.trans (.free (hret_alloc 4 rfl) (.free s21 (.free s22 (.free s23 (.refl _)))))))))
  exact Sem.Reaches.star hfull (k := clock) (.final sfin)

end IxCC.Rt.Rc.Array
