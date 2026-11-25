import IxCC.Rt.Rc.Array.Proof.OpsCopying
import IxCC.Src.ArraySpec

/-! # `extract`, specified

`extract_packed`: in any program holding `Ops.extract t (.packed w)` at `fn` and its callees
(`FnsOk`), extracting `start ..< stop` of a live packed array returns a fresh array holding
`ArraySpec.extractList xs start stop`, in `n + 4` charges for `n` elements copied; the source is
read, not released, and keeps everything. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok wordAt_write64)
open IxCC.Rt.Rc (maxClass classBytes classWords maxCount)
open IxCC.Rt.Rc.Procs (v i to cellAddr)
open IxCC.X86 (Memory)
open Ops

/-- The elements `extract` copies: from `start'`, `len'` of them. -/
def extractStart (len start stop : Nat) : Nat := if start < min stop len then start else 0

def extractLen (len start stop : Nat) : Nat := if start < min stop len then min stop len - start else 0

theorem extractList_eq (xs : List Word) (start stop : Nat) :
    IxCC.Src.ArraySpec.extractList xs start stop =
      (xs.drop (extractStart xs.length start stop)).take (extractLen xs.length start stop) := by
  unfold IxCC.Src.ArraySpec.extractList extractStart extractLen
  by_cases h : start < min stop xs.length
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    have : min stop xs.length - start = 0 := by omega
    rw [this]; simp

/-- The registers of `extract` at its entry. -/
def extractEnv (a : Word) (start stop : Nat) : Env :=
  ((({} : Env).insert 0 a).insert 1 (UInt64.ofNat start)).insert 2 (UInt64.ofNat stop)

/-- **`extract`** of a live packed array: a fresh array of the run. -/
theorem extract_packed {P : Program} {fn : FunId} {t : Fns} {w : X86.Width}
    (hfn : P.funcs[fn]? = some (extract t (.packed w))) (hf : FnsOk P t (.packed w))
    {mem : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {a : Word} {refs cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a refs cls cap (.packed w) xs)
    (ha : Allocated base bump lists a (classBytes cls)) {start stop : Nat}
    (hs64 : start < 2 ^ 64) (ht64 : stop < 2 ^ 64)
    (hroom : AllocRoom bump limit lists (.packed w) (extractLen xs.length start stop)) :
    ∃ b mem' bump' lists',
      Returns1 P fn (extractEnv a start stop) mem ctx (extractLen xs.length start stop + 4) b mem' ∧
      ArrCell mem' b 1 (allocClass (.packed w) (extractLen xs.length start stop))
        ((ElemKind.packed w).capOfClass (allocClass (.packed w) (extractLen xs.length start stop)))
        (.packed w) (IxCC.Src.ArraySpec.extractList xs start stop) ∧
      ArrCell mem' a refs cls cap (.packed w) xs ∧
      ArrayAllocator mem' ctx base bump' limit lists' ∧
      Allocated base bump' lists' b (classBytes (allocClass (.packed w) (extractLen xs.length start stop))) ∧
      Allocated base bump' lists' a (classBytes cls) ∧
      (∀ c m, Allocated base bump lists c m → Allocated base bump' lists' c m) ∧
      MemFrame mem mem' (fun y => AllocBytes ctx lists y ∨
        CellBytes b (allocClass (.packed w) (extractLen xs.length start stop)) y) := by
  have hlen := h.arrRead.len_lt
  have hmaxc := h.len_le_maxCap
  have hle : extractStart xs.length start stop + extractLen xs.length start stop ≤ xs.length := by
    unfold extractStart extractLen; split <;> omega
  have hn : extractLen xs.length start stop ≤ (ElemKind.packed w).maxCap := by omega
  obtain ⟨hlo, hhi, hcap⟩ := allocClass_spec (.packed w) hn
  obtain ⟨b, m1, bump', lists', hret, hd⟩ := alloc_returns hf.alloc hf.classFor hf.classWords
    halloc hn hroom
  obtain ⟨hdrop, hsb, hdb, hsrc, hfit, hacc, hapart, hafter⟩ :=
    fresh_copy hd halloc hlo hhi h ha (off := extractStart xs.length start stop)
      (n := extractLen xs.length start stop) hle hcap
  obtain ⟨m2, hcopy, hel2, hfr2⟩ := copy_returns hf.copy hfit hdrop hsb hdb hsrc hacc hapart
  obtain ⟨hw3, hb3, ha3, hal3, hA3, hsep, hfr3⟩ := hafter m2 hel2 hfr2
  rw [← extractList_eq] at hb3
  refine ⟨b, _, bump', lists', ?_, hb3, ha3, hal3, hd.allocated, hA3,
    fun c m hc => (hd.keeps c m hc).1, hfr3⟩
  -- the arithmetic of block 0
  have hm : (if Cond.holds .ult .w64 (UInt64.ofNat stop) (UInt64.ofNat xs.length) then
      UInt64.ofNat stop else UInt64.ofNat xs.length) = UInt64.ofNat (min stop xs.length) := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt ht64, u64_toNat_ofNat_lt (by omega)]
    by_cases hc : stop < xs.length
    · simp only [decide_eq_true_eq, hc, ↓reduceIte, Nat.min_eq_left (Nat.le_of_lt hc)]
    · simp only [decide_eq_true_eq, hc, ↓reduceIte, Nat.min_eq_right (Nat.le_of_not_lt hc)]
  have hmlt : min stop xs.length < 2 ^ 64 := by omega
  have hsub : BinOp.eval .sub .w64 (UInt64.ofNat (min stop xs.length)) (UInt64.ofNat start) =
      some (UInt64.ofNat (min stop xs.length) - UInt64.ofNat start) := by
    simp only [BinOp.eval, w64_trunc]
  have hl : (if Cond.holds .ult .w64 (UInt64.ofNat start) (UInt64.ofNat (min stop xs.length)) then
      UInt64.ofNat (min stop xs.length) - UInt64.ofNat start else UInt64.ofNat 0) =
      UInt64.ofNat (extractLen xs.length start stop) := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt hs64, u64_toNat_ofNat_lt hmlt]
    unfold extractLen
    by_cases hc : start < min stop xs.length
    · simp only [decide_eq_true_eq, hc, ↓reduceIte, u64_sub_ofNat (Nat.le_of_lt hc) hmlt]
    · simp only [decide_eq_true_eq, hc, ↓reduceIte]
  have hst : (if Cond.holds .ult .w64 (UInt64.ofNat start) (UInt64.ofNat (min stop xs.length)) then
      UInt64.ofNat start else UInt64.ofNat 0) = UInt64.ofNat (extractStart xs.length start stop) := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt hs64, u64_toNat_ofNat_lt hmlt]
    unfold extractStart
    by_cases hc : start < min stop xs.length
    · simp only [decide_eq_true_eq, hc, ↓reduceIte]
    · simp only [decide_eq_true_eq, hc, ↓reduceIte]
  refine returns1_of_star (lbl := 2) (env' := ?env) hfn rfl rfl ?ha (fun rest => ?run)
  case run =>
    unfold extractEnv
    refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
      h.shell.size_load) ?_
    refine star_assign (val := UInt64.ofNat (min stop xs.length)) hfn rfl (by body_pos) rfl (by
      rw [rhs_select_eval (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval)]
      exact congrArg some hm) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval) hsub) ?_
    refine star_assign (val := UInt64.ofNat (extractLen xs.length start stop)) hfn rfl (by body_pos)
      rfl (by
      rw [rhs_select_eval (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval)]
      exact congrArg some hl) ?_
    refine star_assign (val := UInt64.ofNat (extractStart xs.length start stop)) hfn rfl
      (by body_pos) rfl (by
      rw [rhs_select_eval (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval)]
      exact congrArg some hst) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
      (binOp_add64 (extractStart xs.length start stop) (extractLen xs.length start stop)
        (by omega))) ?_
    refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs_nil _) rfl rfl ?_
    refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs_nil _) rfl rfl ?_
    refine star_call1_eq (c' := extractLen xs.length start stop + 1) hfn rfl (by body_pos) rfl
      (evalArgs1 (by arg_eval)) hf.alloc rfl hret ?_ (by omega)
    refine star_call0_eq (c' := 0) hfn rfl (by body_pos) rfl
      (evalArgs5 (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval) (by arg_eval)) hf.copy rfl
      hcopy ?_ (by omega)
    refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
      hw3 ?_
    exact .refl _
  case ha => arg_eval

end IxCC.Rt.Rc.Array
