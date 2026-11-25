import IxCC.Rt.Rc.Array.Proof.OpsAlloc

/-! # The element copy (`Ops.copy`), specified

`copy_returns`: in any program holding `Ops.copy k` at `fn`, copying `n` elements of a source
range to a destination range (writable, without wrap, apart from the source) returns after `n`
charges (one per element), with the elements at the destination and memory changed only there.

The source is any run of elements in memory (`ElemsAt`): of a live cell, of a static cell, or a
prefix or suffix of either. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok)
open IxCC.Rt.Rc.Procs (v i to cellAddr)
open IxCC.X86 (Memory)
open Ops

/-- The elements `ys` at positions `off, off + 1, …` of the cell at `addr`. -/
def ElemsAt (mem : Memory) (addr : Word) (k : ElemKind) (off : Nat) (ys : List Word) : Prop :=
  ∀ (j : Nat) (hj : j < ys.length), ValAt mem (elemAddr addr k (off + j)) k.width ys[j]

/-- The bytes of positions `lo ..< hi` of the cell at `addr`. -/
def ElemRange (addr : Word) (k : ElemKind) (lo hi : Nat) : Nat → Prop :=
  fun x => addr.toNat + (arrayPayloadOffset + k.bytes * lo) ≤ x ∧
    x < addr.toNat + (arrayPayloadOffset + k.bytes * hi)

theorem Elems.elemsAt {mem : Memory} {addr : Word} {k : ElemKind} {xs : List Word}
    (h : Elems mem addr k xs) : ElemsAt mem addr k 0 xs := by
  intro j hj; rw [Nat.zero_add]; exact h j hj

theorem ElemsAt.elems {mem : Memory} {addr : Word} {k : ElemKind} {xs : List Word}
    (h : ElemsAt mem addr k 0 xs) : Elems mem addr k xs := by
  intro j hj; have := h j hj; rwa [Nat.zero_add] at this

/-- The elements from position `s` on. -/
theorem Elems.drop {mem : Memory} {addr : Word} {k : ElemKind} {xs : List Word}
    (h : Elems mem addr k xs) (s : Nat) : ElemsAt mem addr k s (xs.drop s) := by
  intro j hj
  rw [List.getElem_drop]
  exact h (s + j) (by simp at hj; omega)

/-- The bytes of element `p` lie in its range. -/
private theorem elem_bytes_in {addr : Word} {k : ElemKind} {p : Nat}
    (hfit : addr.toNat + (arrayPayloadOffset + k.bytes * (p + 1)) < 2 ^ 63) :
    (elemAddr addr k p).toNat = addr.toNat + (arrayPayloadOffset + k.bytes * p) ∧
      arrayPayloadOffset + k.bytes * p + k.bytes = arrayPayloadOffset + k.bytes * (p + 1) := by
  rw [Nat.mul_succ] at hfit ⊢
  exact ⟨addr_toNat (by omega), by omega⟩

/-- The registers of `copy` at its entry. -/
def copyEnv (src : Word) (srcOff : Nat) (dst : Word) (dstOff n : Nat) : Env :=
  (((((({} : Env).insert 0 src).insert 1 (UInt64.ofNat srcOff)).insert 2 dst).insert 3
    (UInt64.ofNat dstOff)).insert 4 (UInt64.ofNat n))

/-- The loop, from position `j` with the first `j` elements copied. -/
private theorem copy_loop {P : Program} {fn : FunId} {k : ElemKind}
    (hfn : P.funcs[fn]? = some (copy k)) {mem : Memory} {ctx src dst : Word} {xs : List Word}
    {srcOff dstOff n : Nat} (hfit : ElemsFit k xs) (hn : n ≤ xs.length)
    (hsb : src.toNat + (arrayPayloadOffset + k.bytes * (srcOff + n)) < 2 ^ 63)
    (hdb : dst.toNat + (arrayPayloadOffset + k.bytes * (dstOff + n)) < 2 ^ 63)
    (hsrc : ElemsAt mem src k srcOff xs)
    (hacc : ∀ j < n, ∀ b < k.bytes,
      mem.readable (elemAddr dst k (dstOff + j) + UInt64.ofNat b) = true ∧
        mem.writable (elemAddr dst k (dstOff + j) + UInt64.ofNat b) = true)
    (hapart : ∀ x, ElemRange dst k dstOff (dstOff + n) x → ¬ ElemRange src k srcOff (srcOff + n) x) :
    ∀ r j (m : Memory) (e : Env), j + r = n →
      e[0]? = some src → e[1]? = some (UInt64.ofNat srcOff) → e[2]? = some dst →
      e[3]? = some (UInt64.ofNat dstOff) → e[4]? = some (UInt64.ofNat n) →
      e[5]? = some (UInt64.ofNat j) →
      MemFrame mem m (ElemRange dst k dstOff (dstOff + j)) →
      ElemsAt m dst k dstOff (xs.take j) →
      ∃ m' e', MemFrame mem m' (ElemRange dst k dstOff (dstOff + n)) ∧
        ElemsAt m' dst k dstOff (xs.take n) ∧
        ∀ rest : List Frame, Sem.Star (semStep P) (State.mk m ctx ({ fn, label := 1, pos := 0, env := e } :: rest)) r
          (State.mk m' ctx ({ fn, label := 3, pos := 0, env := e' } :: rest)) := by
  have hb8 := k.bytes_le
  have hbp := k.bytes_pos
  have hbw : k.width.bytes = k.bytes := rfl
  have hn64 : n < 2 ^ 63 := by
    have : n ≤ k.bytes * (dstOff + n) := by
      calc n ≤ dstOff + n := by omega
        _ ≤ k.bytes * (dstOff + n) := Nat.le_mul_of_pos_left _ hbp
    unfold arrayPayloadOffset at hdb; omega
  intro r
  induction r with
  | zero =>
    intro j m e hj h0 h1 h2 h3 h4 h5 hfr hel
    have hjn : j = n := by omega
    subst hjn
    refine ⟨m, e, hfr, hel, fun rest => ?_⟩
    have hge : Cond.holds .ult .w64 (UInt64.ofNat j) (UInt64.ofNat j) = false := by
      rw [cond_ult_w64]; simp
    exact star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hge
      (evalArgs_nil _) rfl rfl (.refl _)
  | succ r ih =>
    intro j m e hj h0 h1 h2 h3 h4 h5 hfr hel
    have hjn : j < n := by omega
    have hjx : j < xs.length := by omega
    have hlt : Cond.holds .ult .w64 (UInt64.ofNat j) (UInt64.ofNat n) = true := by
      rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
      exact decide_eq_true hjn
    have hmono : ∀ {a c : Nat}, a ≤ c → k.bytes * a ≤ k.bytes * c := fun h => Nat.mul_le_mul_left _ h
    have hsucc : ∀ a, k.bytes * (a + 1) = k.bytes * a + k.bytes := fun a => Nat.mul_succ _ _
    have hsm := hmono (show srcOff + j + 1 ≤ srcOff + n by omega)
    have hdm := hmono (show dstOff + j + 1 ≤ dstOff + n by omega)
    have hsl := hmono (show srcOff ≤ srcOff + j by omega)
    have hdl := hmono (show dstOff ≤ dstOff + j by omega)
    have hdj1 : k.bytes * (dstOff + (j + 1)) = k.bytes * (dstOff + j) + k.bytes := by
      rw [show dstOff + (j + 1) = dstOff + j + 1 by omega, hsucc]
    rw [hsucc] at hsm hdm
    unfold arrayPayloadOffset at hsb hdb
    have hsle : srcOff + j ≤ k.bytes * (srcOff + j) := Nat.le_mul_of_pos_left _ hbp
    have hdle : dstOff + j ≤ k.bytes * (dstOff + j) := Nat.le_mul_of_pos_left _ hbp
    have hsa : (elemAddr src k (srcOff + j)).toNat = src.toNat + (24 + k.bytes * (srcOff + j)) :=
      addr_toNat (by first | (unfold arrayPayloadOffset; omega) | omega)
    have hda : (elemAddr dst k (dstOff + j)).toNat = dst.toNat + (24 + k.bytes * (dstOff + j)) :=
      addr_toNat (by first | (unfold arrayPayloadOffset; omega) | omega)
    -- the source element, untouched so far
    have hsrcm : ValAt m (elemAddr src k (srcOff + j)) k.width xs[j] :=
      hfr.valAt (hsrc j hjx) (by rw [hsa]; omega) (fun x x1 x2 hx => by
        rw [hsa] at x1 x2
        obtain ⟨hx1, hx2⟩ := hx
        unfold arrayPayloadOffset at hx1 hx2
        have hdjn := hmono (show dstOff + j ≤ dstOff + n by omega)
        exact hapart x ⟨by unfold arrayPayloadOffset; omega, by unfold arrayPayloadOffset; omega⟩
          ⟨by unfold arrayPayloadOffset; omega, by unfold arrayPayloadOffset; omega⟩)
    have hload : loadWord m k.width .zero (elemAddr src k (srcOff + j)) = some xs[j] :=
      hsrcm.load (hfit _ (List.getElem_mem hjx))
    have hwr : m.write? k.width (elemAddr dst k (dstOff + j)) xs[j] =
        .ok (m.write k.width (elemAddr dst k (dstOff + j)) xs[j]) :=
      write?_ok (fun b hb => by rw [hfr.writable]; exact (hacc j hjn b (by rw [← hbw]; exact hb)).2)
    let m' := m.write k.width (elemAddr dst k (dstOff + j)) xs[j]
    have hfw := MemFrame.write m k.width (elemAddr dst k (dstOff + j)) xs[j] (by rw [hda]; omega)
    have hfr' : MemFrame mem m' (ElemRange dst k dstOff (dstOff + (j + 1))) :=
      (hfr.mono (fun x hx => by
        obtain ⟨hx1, hx2⟩ := hx
        unfold arrayPayloadOffset at hx1 hx2
        unfold ElemRange arrayPayloadOffset; rw [hdj1]; omega)).trans
      (hfw.mono (fun x hx => by
        obtain ⟨hx1, hx2⟩ := hx; rw [hda] at hx1 hx2
        unfold ElemRange arrayPayloadOffset; rw [hdj1]; omega))
    have hel' : ElemsAt m' dst k dstOff (xs.take (j + 1)) := by
      intro p hp
      have hp' : p < j + 1 := by simp at hp; omega
      rw [List.getElem_take]
      by_cases hpj : p = j
      · subst hpj
        apply valAt_write
        intro b hb
        rw [hfr.readable]; exact (hacc p hjn b (by rw [← hbw]; exact hb)).1
      · have hpj' : p < j := by omega
        have hold := hel p (by simp; omega)
        rw [List.getElem_take] at hold
        have hpm := hmono (show dstOff + p + 1 ≤ dstOff + j by omega)
        rw [hsucc] at hpm
        have hdp : (elemAddr dst k (dstOff + p)).toNat = dst.toNat + (24 + k.bytes * (dstOff + p)) :=
          addr_toNat (by first | (unfold arrayPayloadOffset; omega) | omega)
        exact hfw.valAt hold (by rw [hdp]; omega) (fun x x1 x2 hx => by
          obtain ⟨hx1, hx2⟩ := hx; rw [hda] at hx1 hx2; rw [hdp] at x1 x2; omega)
    obtain ⟨mf, ef, hfrf, helf, hstar⟩ := ih (j + 1) m'
      (((((e.insert 6 (UInt64.ofNat (srcOff + j))).insert 7 xs[j]).insert 8
        (UInt64.ofNat (dstOff + j))).insert 9 (UInt64.ofNat (j + 1))).insert 5 (UInt64.ofNat (j + 1)))
      (by omega) (by env_lookup) (by env_lookup) (by env_lookup) (by env_lookup) (by env_lookup)
      (by env_lookup) hfr' hel'
    refine ⟨mf, ef, hfrf, helf, fun rest => ?_⟩
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hlt
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
      (binOp_add64 srcOff j (by omega))) ?_
    refine star_assign hfn rfl (by body_pos) rfl
      (rhs_load_eval (elemAt_eval (by env_lookup) (by env_lookup) (by unfold arrayPayloadOffset; omega)) hload) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
      (binOp_add64 dstOff j (by omega))) ?_
    refine star_store hfn rfl (by body_pos) rfl (elemAt_eval (by env_lookup) (by env_lookup) (by unfold arrayPayloadOffset; omega))
      (by arg_eval) hwr ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
      (binOp_add64 j 1 (by omega))) ?_
    refine star_jump_back hfn rfl rfl rfl rfl (evalArgs1 (by arg_eval)) rfl rfl ?_
    exact star_cast (hstar rest) (by omega)

/-- **The copy.** `n` elements from `src` at `srcOff` to `dst` at `dstOff`, in `n` charges. -/
theorem copy_returns {P : Program} {fn : FunId} {k : ElemKind}
    (hfn : P.funcs[fn]? = some (copy k)) {mem : Memory} {ctx src dst : Word} {xs : List Word}
    {srcOff dstOff n : Nat} (hfit : ElemsFit k xs) (hn : n ≤ xs.length)
    (hsb : src.toNat + (arrayPayloadOffset + k.bytes * (srcOff + n)) < 2 ^ 63)
    (hdb : dst.toNat + (arrayPayloadOffset + k.bytes * (dstOff + n)) < 2 ^ 63)
    (hsrc : ElemsAt mem src k srcOff xs)
    (hacc : ∀ j < n, ∀ b < k.bytes,
      mem.readable (elemAddr dst k (dstOff + j) + UInt64.ofNat b) = true ∧
        mem.writable (elemAddr dst k (dstOff + j) + UInt64.ofNat b) = true)
    (hapart : ∀ x, ElemRange dst k dstOff (dstOff + n) x → ¬ ElemRange src k srcOff (srcOff + n) x) :
    ∃ mem', Returns0 P fn (copyEnv src srcOff dst dstOff n) mem ctx n mem' ∧
      ElemsAt mem' dst k dstOff (xs.take n) ∧
      MemFrame mem mem' (ElemRange dst k dstOff (dstOff + n)) := by
  have h0 : MemFrame mem mem (ElemRange dst k dstOff (dstOff + 0)) := MemFrame.refl _ _
  have hel0 : ElemsAt mem dst k dstOff (xs.take 0) := fun j hj => by simp at hj
  obtain ⟨mf, ef, hfrf, helf, hstar⟩ := copy_loop hfn hfit hn hsb hdb hsrc hacc hapart
    n 0 mem ((copyEnv src srcOff dst dstOff n).insert 5 (UInt64.ofNat 0)) (by omega)
    (by unfold copyEnv; env_lookup) (by unfold copyEnv; env_lookup) (by unfold copyEnv; env_lookup)
    (by unfold copyEnv; env_lookup) (by unfold copyEnv; env_lookup) (by env_lookup) h0 hel0
  refine ⟨mf, fun caller callers hd => ?_, helf, hfrf⟩
  refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs1 (by arg_eval)) rfl rfl ?_
  exact star_cast ((hstar (caller :: callers)).trans (star_ret_zero hfn rfl rfl rfl hd)) (by omega)

end IxCC.Rt.Rc.Array
