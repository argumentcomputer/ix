import IxCC.Rt.Rc.Array.Proof.OpsExtract

/-! # The increments of the copying paths (`Ops.incs`), specified

`incs_returns`: in any program holding `Ops.incs t` at `fn` and the one increment `Procs.inc` at
`t.inc`, incrementing the boxed elements `ys` at positions `lo ..< hi` of the cell at `a` returns
after `2 · (hi − lo)` charges (a call and a back edge per element) with the memory the increments
make (`IncAll`), provided the increments never write the elements themselves (no element's count
word lies among the elements read). -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok)
open IxCC.Rt.Rc.Procs (v i to cellAddr)
open IxCC.X86 (Memory)
open Ops

/-- The registers of `incs` at its entry. -/
def incsEnv (a : Word) (lo hi : Nat) : Env :=
  ((({} : Env).insert 0 a).insert 1 (UInt64.ofNat lo)).insert 2 (UInt64.ofNat hi)

/-- The loop, over the elements still to increment. -/
private theorem incs_loop {P : Program} {fn : FunId} {t : Fns}
    (hfn : P.funcs[fn]? = some (incs t)) (hinc : P.funcs[t.inc]? = some IxCC.Rt.Rc.Procs.inc)
    {ctx a : Word} {hi : Nat} (hfit : a.toNat + (arrayPayloadOffset + 8 * hi) < 2 ^ 63) :
    ∀ (zs : List Word) (j : Nat) (m mf : Memory) (e : Env), j + zs.length = hi →
      e[0]? = some a → e[2]? = some (UInt64.ofNat hi) → e[3]? = some (UInt64.ofNat j) →
      ElemsAt m a .boxed j zs → IncAll m zs mf →
      (∀ z ∈ zs, Cond.holds .tnz .w64 z 1 = false → z.toNat + 8 ≤ 2 ^ 64) →
      (∀ x, CountWords zs x → ¬ ElemRange a .boxed j hi x) →
      ∃ e', ∀ rest : List Frame, Sem.Star (semStep P)
        (State.mk m ctx ({ fn, label := 1, pos := 0, env := e } :: rest)) (2 * zs.length)
        (State.mk mf ctx ({ fn, label := 3, pos := 0, env := e' } :: rest)) := by
  intro zs
  induction zs with
  | nil =>
    intro j m mf e hj h0 h2 h3 _ hall _ _
    cases hall
    have hjh : j = hi := by simpa using hj
    subst hjh
    refine ⟨e, fun rest => ?_⟩
    have hge : Cond.holds .ult .w64 (UInt64.ofNat j) (UInt64.ofNat j) = false := by
      rw [cond_ult_w64]; simp
    exact star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hge
      (evalArgs_nil _) rfl rfl (.refl _)
  | cons z zs ih =>
    intro j m mf e hj h0 h2 h3 hel hall hptr hcw
    cases hall with
    | cons hstep hrest =>
    rename_i m1
    simp only [List.length_cons] at hj
    have hjh : j < hi := by omega
    have hhi : hi < 2 ^ 60 := by unfold arrayPayloadOffset at hfit; omega
    have hlt : Cond.holds .ult .w64 (UInt64.ofNat j) (UInt64.ofNat hi) = true := by
      rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
      exact decide_eq_true hjh
    have hz : ValAt m (elemAddr a .boxed j) .w64 z := by
      have := hel 0 (by simp); simpa using this
    have hload : loadWord m .w64 .zero (elemAddr a .boxed j) = some z :=
      hz.load (ElemKind.boxed_fits z)
    -- the increment of `z` writes no element still to be read
    have hfr1 : MemFrame m m1 (CountWords [z]) :=
      (IncAll.cons hstep (IncAll.nil m1)).frame (fun y hy hp => hptr y (by simp at hy; simp [hy]) hp)
    have hel1 : ElemsAt m1 a .boxed (j + 1) zs := by
      intro p hp
      have hold := hel (p + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at hold
      rw [show j + (p + 1) = j + 1 + p by omega] at hold
      have hpa : (elemAddr a .boxed (j + 1 + p)).toNat =
          a.toNat + (arrayPayloadOffset + 8 * (j + 1 + p)) := by
        show (a + UInt64.ofNat (arrayPayloadOffset + 8 * (j + 1 + p))).toNat = _
        exact addr_toNat (by
        have := Nat.mul_le_mul_left 8 (show j + 1 + p ≤ hi by omega)
        unfold arrayPayloadOffset at hfit ⊢; omega)
      have hm8 := Nat.mul_le_mul_left 8 (show j + 1 + p + 1 ≤ hi by omega)
      have hwb : ElemKind.boxed.width.bytes = 8 := rfl
      have hwb2 : X86.Width.w64.bytes = 8 := rfl
      exact hfr1.valAt hold (by rw [hpa]; unfold arrayPayloadOffset at hfit ⊢; omega)
        (fun x x1 x2 hx => by
          rw [hpa] at x1 x2
          apply hcw x (by obtain ⟨y, hy, hp, h1, h2⟩ := hx; exact ⟨y, by simp at hy; simp [hy], hp, h1, h2⟩)
          unfold ElemRange; simp only [ElemKind.boxed_bytes]
          refine ⟨?_, ?_⟩
          · have := Nat.mul_le_mul_left 8 (show j ≤ j + 1 + p by omega)
            unfold arrayPayloadOffset at x1 ⊢; omega
          · unfold arrayPayloadOffset at x2 ⊢; omega)
    obtain ⟨e', hstar⟩ := ih (j + 1) m1 mf
      (((e.insert 4 z).insert 5 (UInt64.ofNat (j + 1))).insert 3 (UInt64.ofNat (j + 1)))
      (by omega) (by env_lookup) (by env_lookup) (by env_lookup) hel1 hrest
      (fun y hy hp => hptr y (by simp [hy]) hp)
      (fun x hx => by
        intro hr
        obtain ⟨y, hy, hp, h1, h2⟩ := hx
        apply hcw x ⟨y, by simp [hy], hp, h1, h2⟩
        unfold ElemRange at hr ⊢; simp only [ElemKind.boxed_bytes] at hr ⊢
        refine ⟨?_, hr.2⟩
        have := Nat.mul_le_mul_left 8 (show j ≤ j + 1 by omega)
        have := hr.1
        unfold arrayPayloadOffset at this ⊢; omega)
    refine ⟨e', fun rest => ?_⟩
    have hb : arrayPayloadOffset + ElemKind.boxed.bytes * j < 2 ^ 64 := by
      show arrayPayloadOffset + 8 * j < 2 ^ 64
      unfold arrayPayloadOffset at hfit ⊢; omega
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hlt
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by body_pos) rfl
      (rhs_load_eval (elemAt_eval (by env_lookup) (by env_lookup) hb) hload) ?_
    refine star_call0_eq (c' := 2 * zs.length + 1) hfn rfl (by body_pos) rfl
      (evalArgs1 (by arg_eval)) hinc rfl (inc_returns hinc hstep) ?_ (by simp; omega)
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
      (binOp_add64 j 1 (by omega))) ?_
    refine star_jump_back hfn rfl rfl rfl rfl (evalArgs1 (by arg_eval)) rfl rfl ?_
    exact hstar rest

/-- **The increments.** The elements `ys` at positions `lo ..< lo + |ys|`, incremented in order. -/
theorem incs_returns {P : Program} {fn : FunId} {t : Fns}
    (hfn : P.funcs[fn]? = some (incs t)) (hinc : P.funcs[t.inc]? = some IxCC.Rt.Rc.Procs.inc)
    {mem mem' : Memory} {ctx a : Word} {lo : Nat} {ys : List Word}
    (hfit : a.toNat + (arrayPayloadOffset + 8 * (lo + ys.length)) < 2 ^ 63)
    (hel : ElemsAt mem a .boxed lo ys) (hall : IncAll mem ys mem')
    (hptr : ∀ y ∈ ys, Cond.holds .tnz .w64 y 1 = false → y.toNat + 8 ≤ 2 ^ 64)
    (hcw : ∀ x, CountWords ys x → ¬ ElemRange a .boxed lo (lo + ys.length) x) :
    Returns0 P fn (incsEnv a lo (lo + ys.length)) mem ctx (2 * ys.length) mem' := by
  obtain ⟨e', hstar⟩ := incs_loop hfn hinc hfit ys lo mem mem'
    ((incsEnv a lo (lo + ys.length)).insert 3 (UInt64.ofNat lo)) rfl
    (by unfold incsEnv; env_lookup) (by unfold incsEnv; env_lookup) (by env_lookup) hel hall hptr hcw
  intro caller callers hd
  unfold incsEnv
  refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs1 (by arg_eval)) rfl rfl ?_
  exact star_cast ((hstar (caller :: callers)).trans (star_ret_zero hfn rfl rfl rfl hd)) (by omega)

end IxCC.Rt.Rc.Array
