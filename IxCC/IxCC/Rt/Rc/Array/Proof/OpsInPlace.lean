import IxCC.Rt.Rc.Array.Proof.OpsCopy

/-! # The array operations' paths that need no allocation, specified

In any program holding the procedure at `fn`:

| procedure | path | theorem |
| --- | --- | --- |
| `size` | a live or static array | `size_returns` |
| `get k` | in range | `get_returns` |
| `get k` | out of range: trap | `get_traps` |
| `set k` | out of range: trap | `set_traps` |
| `set k` | unique, packed / boxed | `set_unique_packed`, `set_unique_boxed` |
| `push k` | unique with room | `push_unique_room` |
| `pop k` | empty | `pop_empty_packed`, `pop_empty_boxed` |
| `pop k` | unique, packed / boxed | `pop_unique_packed`, `pop_unique_boxed` |

Reads are stated over the loads they make (`ArrRead`), which a live cell
(`ArrCell.arrRead`) and a static cell (`StaticArrCell.arrRead`) both provide. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok)
open IxCC.Rt.Rc (maxClass classBytes maxCount)
open IxCC.Rt.Rc.Procs (v i to cellAddr)
open IxCC.X86 (Memory)
open Ops

/-- `fn` returns two results to a caller awaiting two. -/
def Returns2 (P : Program) (fn : FunId) (env : Env) (mem : Memory) (ctx : Word) (c : Nat)
    (r₁ r₂ : Word) (mem' : Memory) : Prop :=
  ∀ (caller : Frame) (callers : List Frame) (d₁ d₂ : VReg), caller.dsts = [d₁, d₂] →
    Sem.Star (semStep P) (State.mk mem ctx ({ fn, label := 0, pos := 0, env } :: caller :: callers)) c
      (State.mk mem' ctx
        ({ caller with env := (caller.env.insert d₁ r₁).insert d₂ r₂, dsts := [] } :: callers))

theorem returns2_of_star {P : Program} {fn : FunId} {f : Func} {blk : Block} {lbl : Nat}
    {a b : Arg} {env env' : Env} {mem mem' : Memory} {ctx r₁ r₂ : Word} {c : Nat}
    (hf : P.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk) (ht : blk.term = .ret [a, b])
    (ha : a.eval env' = some r₁) (hb' : b.eval env' = some r₂)
    (hrun : ∀ rest : List Frame, Sem.Star (semStep P)
      (State.mk mem ctx ({ fn, label := 0, pos := 0, env } :: rest)) c
      (State.mk mem' ctx ({ fn, label := lbl, pos := blk.body.size, env := env' } :: rest))) :
    Returns2 P fn env mem ctx c r₁ r₂ mem' := by
  intro caller callers d₁ d₂ hd
  have h := (hrun (caller :: callers)).trans (star_ret_two (env := env') (mem := mem')
    (context := ctx) (callers := callers) hf hb rfl ht ha hb' hd)
  simpa using h

theorem star_trans0 {P : Program} {s s' s'' : State} {c : Nat} (h : Sem.Star (semStep P) s 0 s')
    (h' : Sem.Star (semStep P) s' c s'') : Sem.Star (semStep P) s c s'' := by
  simpa using h.trans h'

/-- What a read of an array uses: its size word, its elements, and that their addresses do not
wrap. -/
structure ArrRead (mem : Memory) (a : Word) (k : ElemKind) (xs : List Word) : Prop where
  ptr : Cond.holds .tnz .w64 a 1 = false
  size : loadWord mem .w64 .zero (a + 8) = some (UInt64.ofNat xs.length)
  elem : ∀ (j : Nat) (hj : j < xs.length), loadWord mem k.width .zero (elemAddr a k j) = some xs[j]
  fit : a.toNat + (arrayPayloadOffset + k.bytes * xs.length) < 2 ^ 63

theorem ArrCell.arrRead {mem : Memory} {a : Word} {refs cls cap : Nat} {k : ElemKind}
    {xs : List Word} (h : ArrCell mem a refs cls cap k xs) : ArrRead mem a k xs := by
  have hp := h.shell.payload_le
  have hfit := h.shell.fit
  have hm := Nat.mul_le_mul_left k.bytes h.shell.size_le
  exact ⟨h.shell.pointer_branch, h.shell.size_load, fun j hj => h.elem_load hj, by omega⟩

theorem StaticArrCell.arrRead {mem : Memory} {a : Word} {cap : Nat} {k : ElemKind}
    {xs : List Word} (h : StaticArrCell mem a cap k xs) : ArrRead mem a k xs := by
  have hfit := h.fit
  have hm := Nat.mul_le_mul_left k.bytes h.size_le
  exact ⟨h.pointer_branch, h.size_load, fun j hj => h.elem_load hj, by omega⟩

theorem ArrRead.len_lt {mem : Memory} {a : Word} {k : ElemKind} {xs : List Word}
    (h : ArrRead mem a k xs) : xs.length < 2 ^ 63 := by
  have := h.fit
  have := Nat.le_mul_of_pos_left xs.length k.bytes_pos
  omega

theorem ArrRead.elem_bound {mem : Memory} {a : Word} {k : ElemKind} {xs : List Word}
    (h : ArrRead mem a k xs) {j : Nat} (hj : j < xs.length) :
    arrayPayloadOffset + k.bytes * j < 2 ^ 64 := by
  have := h.fit
  have := Nat.mul_le_mul_left k.bytes (Nat.le_of_lt hj)
  omega

/-! ## Reads -/

/-- **`size`**: the size word, nothing written. -/
theorem size_returns {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some size)
    {mem : Memory} {ctx a : Word} {k : ElemKind} {xs : List Word} (h : ArrRead mem a k xs) :
    Returns1 P fn (({} : Env).insert 0 a) mem ctx 0 (UInt64.ofNat xs.length) mem := by
  refine returns1_of_star (lbl := 0) (env' := ?env) hfn rfl rfl ?ha (fun rest => ?run)
  case run =>
    refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
      h.size) ?_
    exact .refl _
  case ha => arg_eval

/-- **`get`** in range: the element, nothing written. -/
theorem get_returns {P : Program} {fn : FunId} {k : ElemKind} (hfn : P.funcs[fn]? = some (get k))
    {mem : Memory} {ctx a : Word} {xs : List Word} (h : ArrRead mem a k xs) {j : Nat}
    (hj : j < xs.length) :
    Returns1 P fn ((({} : Env).insert 0 a).insert 1 (UInt64.ofNat j)) mem ctx 0 xs[j] mem := by
  have hlen := h.len_lt
  have hlt : Cond.holds .ult .w64 (UInt64.ofNat j) (UInt64.ofNat xs.length) = true := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_true hj
  refine returns1_of_star (lbl := 1) (env' := ?env) hfn rfl rfl ?ha (fun rest => ?run)
  case run =>
    refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
      h.size) ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hlt
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (elemAt_eval (by env_lookup)
      (by env_lookup) (h.elem_bound hj)) (h.elem j hj)) ?_
    exact .refl _
  case ha => arg_eval

/-- The registers of `get` at its entry. -/
def getEnv (a : Word) (j : Nat) : Env := (({} : Env).insert 0 a).insert 1 (UInt64.ofNat j)

/-- **`get`** out of range traps. -/
theorem get_traps {P : Program} {fn : FunId} {k : ElemKind} (hfn : P.funcs[fn]? = some (get k))
    {mem : Memory} {ctx a : Word} {xs : List Word} (h : ArrRead mem a k xs) {j : Nat}
    (hj : xs.length ≤ j) (hj64 : j < 2 ^ 64) (rest : List Frame) (clock : Nat) :
    Sem.Reaches (semStep P) (State.mk mem ctx ({ fn, label := 0, pos := 0, env := getEnv a j } ::
      rest)) clock .trap := by
  unfold getEnv
  have hlen := h.len_lt
  have hge : Cond.holds .ult .w64 (UInt64.ofNat j) (UInt64.ofNat xs.length) = false := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt hj64, u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_false (by omega)
  refine Sem.Reaches.star (star_assign hfn rfl (by body_pos) rfl
    (rhs_load_eval (cellAddr_eval_8 (by env_lookup)) h.size)
    (star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hge
      (evalArgs_nil _) rfl rfl (.refl _))) ?_
  exact reaches_trap (lbl := 2) (pos := 0) (k := clock) hfn rfl rfl rfl

/-! ## Updates in place -/

/-- The registers of `set` at its entry. -/
def setEnv (a : Word) (j : Nat) (x : Word) : Env :=
  ((({} : Env).insert 0 a).insert 1 (UInt64.ofNat j)).insert 2 x

/-- **`set`** out of range traps. -/
theorem set_traps {P : Program} {fn : FunId} {t : Fns} {k : ElemKind}
    (hfn : P.funcs[fn]? = some (set t k)) {mem : Memory} {ctx a x : Word} {xs : List Word}
    (h : ArrRead mem a k xs) {j : Nat} (hj : xs.length ≤ j) (hj64 : j < 2 ^ 64)
    (rest : List Frame) (clock : Nat) :
    Sem.Reaches (semStep P) (State.mk mem ctx ({ fn, label := 0, pos := 0, env := setEnv a j x } ::
      rest)) clock .trap := by
  have hlen := h.len_lt
  have hge : Cond.holds .ult .w64 (UInt64.ofNat j) (UInt64.ofNat xs.length) = false := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt hj64, u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_false (by omega)
  unfold setEnv
  refine Sem.Reaches.star (star_assign hfn rfl (by body_pos) rfl
    (rhs_load_eval (cellAddr_eval_8 (by env_lookup)) h.size)
    (star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hge
      (evalArgs_nil _) rfl rfl (.refl _))) ?_
  exact reaches_trap (lbl := 5) (pos := 0) (k := clock) hfn rfl rfl rfl

/-- The path into the unique branch of `set`: the size, the bound, the count word `0`. -/
private theorem set_to_unique {P : Program} {fn : FunId} {t : Fns} {k : ElemKind}
    (hfn : P.funcs[fn]? = some (set t k)) {mem : Memory} {ctx a x : Word} {cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a 1 cls cap k xs) {j : Nat} (hj : j < xs.length)
 :
    ∃ e, e[0]? = some a ∧ e[1]? = some (UInt64.ofNat j) ∧ e[2]? = some x ∧
      ∀ rest : List Frame, Sem.Star (semStep P) (State.mk mem ctx ({ fn, label := 0, pos := 0, env := setEnv a j x } :: rest))
        0 (State.mk mem ctx ({ fn, label := 2, pos := 0, env := e } :: rest)) := by
  have hr := h.arrRead
  have hlen := hr.len_lt
  have hlt : Cond.holds .ult .w64 (UInt64.ofNat j) (UInt64.ofNat xs.length) = true := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_true hj
  unfold setEnv
  refine ⟨?e, ?h0, ?h1, ?h2, fun rest => ?hs⟩
  case hs =>
    refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
      hr.size) ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hlt
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_4 (by env_lookup))
      h.shell.count_load) ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) (by decide)
      (evalArgs_nil _) rfl rfl ?_
    exact .refl _
  case h0 => env_lookup
  case h1 => env_lookup
  case h2 => env_lookup

/-- The store of `set`'s unique branch. -/
private theorem set_store {mem : Memory} {a x : Word} {cls cap : Nat} {k : ElemKind}
    {xs : List Word} (h : ArrCell mem a 1 cls cap k xs) {j : Nat} (hj : j < xs.length) :
    mem.write? k.width (elemAddr a k j) x = .ok (mem.write k.width (elemAddr a k j) x) := by
  obtain ⟨hja, hjb⟩ := h.shell.elem_toNat (j := j) (by have := h.shell.size_le; omega)
  have hbw : k.width.bytes = k.bytes := rfl
  have hfit := h.shell.fit
  exact write?_ok (fun b hb => by
    have := h.shell.access (arrayPayloadOffset + k.bytes * j + b) (by omega)
    have hadd : elemAddr a k j + UInt64.ofNat b =
        a + UInt64.ofNat (arrayPayloadOffset + k.bytes * j + b) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [hja]; omega), hja, addr_toNat (by omega)]; omega
    rw [hadd]; exact this.2)

/-- **`set`** of a packed unique array, in range: the element stored in place. -/
theorem set_unique_packed {P : Program} {fn : FunId} {t : Fns} {w : X86.Width}
    (hfn : P.funcs[fn]? = some (set t (.packed w))) {mem : Memory} {ctx a x : Word}
    {cls cap : Nat} {xs : List Word} (h : ArrCell mem a 1 cls cap (.packed w) xs) {j : Nat}
    (hj : j < xs.length) (hx : (ElemKind.packed w).Fits x) :
    Returns1 P fn (setEnv a j x) mem ctx 0 a (mem.write w (elemAddr a (.packed w) j) x) ∧
      ArrCell (mem.write w (elemAddr a (.packed w) j) x) a 1 cls cap (.packed w) (xs.set j x) := by
  refine ⟨?_, h.setElem hj hx⟩
  obtain ⟨e, h0, h1, h2, hpre⟩ := set_to_unique (x := x) hfn h hj
  have hb := h.arrRead.elem_bound hj
  refine returns1_of_star (lbl := 2) (env' := e.insert 5 xs[j]) hfn rfl rfl (by arg_eval)
    (fun rest => ?_)
  refine star_trans0 (hpre rest) ?_
  refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (elemAt_eval (by env_lookup)
    (by env_lookup) hb) (h.elem_load hj)) ?_
  refine star_store hfn rfl (by body_pos) rfl (elemAt_eval (by env_lookup) (by env_lookup) hb)
    (by arg_eval) (set_store h hj) ?_
  exact .refl _

/-- **`set`** of a boxed unique array, in range: the element stored in place; the old one is
returned, to be released by the caller. -/
theorem set_unique_boxed {P : Program} {fn : FunId} {t : Fns}
    (hfn : P.funcs[fn]? = some (set t .boxed)) {mem : Memory} {ctx a x : Word}
    {cls cap : Nat} {xs : List Word} (h : ArrCell mem a 1 cls cap .boxed xs) {j : Nat}
    (hj : j < xs.length) :
    Returns2 P fn (setEnv a j x) mem ctx 0 a xs[j] (mem.write .w64 (elemAddr a .boxed j) x) ∧
      ArrCell (mem.write .w64 (elemAddr a .boxed j) x) a 1 cls cap .boxed (xs.set j x) := by
  refine ⟨?_, h.setElem hj (ElemKind.boxed_fits x)⟩
  obtain ⟨e, h0, h1, h2, hpre⟩ := set_to_unique (x := x) hfn h hj
  have hb := h.arrRead.elem_bound hj
  refine returns2_of_star (lbl := 2) (env' := e.insert 5 xs[j]) hfn rfl rfl (by arg_eval)
    (by arg_eval) (fun rest => ?_)
  refine star_trans0 (hpre rest) ?_
  refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (elemAt_eval (by env_lookup)
    (by env_lookup) hb) (h.elem_load hj)) ?_
  refine star_store hfn rfl (by body_pos) rfl (elemAt_eval (by env_lookup) (by env_lookup) hb)
    (by arg_eval) (set_store h hj) ?_
  exact .refl _

/-- The registers of `push` at its entry. -/
def pushEnv (a x : Word) : Env := (({} : Env).insert 0 a).insert 1 x

/-- **`push`** on a unique array with room: the element stored, the size raised, in place. -/
theorem push_unique_room {P : Program} {fn : FunId} {t : Fns} {k : ElemKind}
    (hfn : P.funcs[fn]? = some (push t k)) {mem : Memory} {ctx a x : Word} {cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a 1 cls cap k xs) (hroom : xs.length < cap) (hx : k.Fits x) :
    Returns1 P fn (pushEnv a x) mem ctx 0 a
        ((mem.write k.width (elemAddr a k xs.length) x).write .w64 (a + 8)
          (UInt64.ofNat (xs.length + 1))) ∧
      ArrCell ((mem.write k.width (elemAddr a k xs.length) x).write .w64 (a + 8)
          (UInt64.ofNat (xs.length + 1))) a 1 cls cap k (xs ++ [x]) := by
  refine ⟨?_, h.pushElem hroom hx⟩
  have hs := h.shell
  have hcap := hs.cap_lt
  have hp := hs.payload_le
  have hfit := hs.fit
  have h24 := hs.classBytes_ge_24
  have hbw : k.width.bytes = k.bytes := rfl
  obtain ⟨hja, hjb⟩ := hs.elem_toNat hroom
  have hlt : Cond.holds .ult .w64 (UInt64.ofNat xs.length) (UInt64.ofNat cap) = true := by
    rw [cond_ult_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_true hroom
  have hwr1 : mem.write? k.width (elemAddr a k xs.length) x =
      .ok (mem.write k.width (elemAddr a k xs.length) x) := write?_ok (fun b hb => by
    have := hs.access (arrayPayloadOffset + k.bytes * xs.length + b) (by omega)
    have hadd : elemAddr a k xs.length + UInt64.ofNat b =
        a + UInt64.ofNat (arrayPayloadOffset + k.bytes * xs.length + b) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [hja]; omega), hja, addr_toNat (by omega)]; omega
    rw [hadd]; exact this.2)
  have hwr2 : (mem.write k.width (elemAddr a k xs.length) x).write? .w64 (a + 8)
      (UInt64.ofNat (xs.length + 1)) = .ok ((mem.write k.width (elemAddr a k xs.length) x).write .w64
        (a + 8) (UInt64.ofNat (xs.length + 1))) :=
    (MemFrame.write mem k.width (elemAddr a k xs.length) x (by rw [hja]; omega)).write?_ok
      (hs.write_ok (off := 8) (w := .w64) (by simp [X86.Width.bytes]; omega) (UInt64.ofNat 0))
  have hb : arrayPayloadOffset + k.bytes * xs.length < 2 ^ 64 := by omega
  refine returns1_of_star (lbl := 2) (env' := ?env) hfn rfl rfl ?ha (fun rest => ?run)
  case run =>
    unfold pushEnv
    refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
      hs.size_load) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_16 (by env_lookup))
      hs.cap_load) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_4 (by env_lookup))
      hs.count_load) ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) (by decide)
      (evalArgs_nil _) rfl rfl ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hlt
      (evalArgs_nil _) rfl rfl ?_
    refine star_store hfn rfl (by body_pos) rfl (elemAt_eval (by env_lookup) (by env_lookup) hb)
      (by arg_eval) hwr1 ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
      (binOp_add64 xs.length 1 (by omega))) ?_
    refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
      hwr2 ?_
    exact .refl _
  case ha => arg_eval

/-- **`pop`** of an empty array (live or static, any count): returned as it is. -/
theorem pop_empty_packed {P : Program} {fn : FunId} {t : Fns} {w : X86.Width}
    (hfn : P.funcs[fn]? = some (pop t (.packed w))) {mem : Memory} {ctx a : Word}
    (hsize : loadWord mem .w64 .zero (a + 8) = some (UInt64.ofNat 0)) :
    Returns1 P fn (({} : Env).insert 0 a) mem ctx 0 a mem := by
  refine returns1_of_star (lbl := 1) (env' := (({} : Env).insert 0 a).insert 1 (UInt64.ofNat 0))
    hfn rfl rfl (by arg_eval) (fun rest => ?_)
  refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
    hsize) ?_
  refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) (by decide)
    (evalArgs_nil _) rfl rfl ?_
  exact .refl _

/-- **`pop`** of an empty boxed array: returned as it is, with nothing to drop (an immediate). -/
theorem pop_empty_boxed {P : Program} {fn : FunId} {t : Fns}
    (hfn : P.funcs[fn]? = some (pop t .boxed)) {mem : Memory} {ctx a : Word}
    (hsize : loadWord mem .w64 .zero (a + 8) = some (UInt64.ofNat 0)) :
    Returns2 P fn (({} : Env).insert 0 a) mem ctx 0 a 1 mem := by
  refine returns2_of_star (lbl := 1) (env' := (({} : Env).insert 0 a).insert 1 (UInt64.ofNat 0))
    hfn rfl rfl (by arg_eval) (by arg_eval) (fun rest => ?_)
  refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
    hsize) ?_
  refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) (by decide)
    (evalArgs_nil _) rfl rfl ?_
  exact .refl _

/-- The path into the unique branch of `pop`. -/
private theorem pop_to_unique {P : Program} {fn : FunId} {t : Fns} {k : ElemKind}
    (hfn : P.funcs[fn]? = some (pop t k)) {mem : Memory} {ctx a : Word} {cls cap : Nat}
    {xs : List Word} (h : ArrCell mem a 1 cls cap k xs) (hne : xs ≠ []) :
    ∃ e, e[0]? = some a ∧ e[2]? = some (UInt64.ofNat (xs.length - 1)) ∧
      ∀ rest : List Frame, Sem.Star (semStep P)
        (State.mk mem ctx ({ fn, label := 0, pos := 0, env := ({} : Env).insert 0 a } :: rest))
        0 (State.mk mem ctx ({ fn, label := 3, pos := 0, env := e } :: rest)) := by
  have hr := h.arrRead
  have hlen := hr.len_lt
  have hpos : 0 < xs.length := List.length_pos_iff.mpr hne
  have hne0 : Cond.holds .eq .w64 (UInt64.ofNat xs.length) (UInt64.ofNat 0) = false := by
    rw [cond_eq_w64]
    exact beq_false_of_ne (fun hq => by
      have := congrArg UInt64.toNat hq
      rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)] at this; omega)
  refine ⟨?e, ?h0, ?h2, fun rest => ?hs⟩
  case hs =>
    refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_8 (by env_lookup))
      hr.size) ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hne0
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval)
      (binOp_sub64 xs.length 1 (by omega) (by omega))) ?_
    refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (cellAddr_eval_4 (by env_lookup))
      h.shell.count_load) ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) (by decide)
      (evalArgs_nil _) rfl rfl ?_
    exact .refl _
  case h0 => env_lookup
  case h2 => env_lookup

/-- **`pop`** of a packed unique non-empty array: the size lowered in place. -/
theorem pop_unique_packed {P : Program} {fn : FunId} {t : Fns} {w : X86.Width}
    (hfn : P.funcs[fn]? = some (pop t (.packed w))) {mem : Memory} {ctx a : Word}
    {cls cap : Nat} {xs : List Word} (h : ArrCell mem a 1 cls cap (.packed w) xs) (hne : xs ≠ []) :
    Returns1 P fn (({} : Env).insert 0 a) mem ctx 0 a
        (mem.write .w64 (a + 8) (UInt64.ofNat (xs.length - 1))) ∧
      ArrCell (mem.write .w64 (a + 8) (UInt64.ofNat (xs.length - 1))) a 1 cls cap (.packed w)
        xs.dropLast := by
  rw [List.dropLast_eq_take]
  refine ⟨?_, h.truncate (by omega)⟩
  obtain ⟨e, h0, h2, hpre⟩ := pop_to_unique hfn h hne
  have hpos : 0 < xs.length := List.length_pos_iff.mpr hne
  have hj : xs.length - 1 < xs.length := by omega
  have hb := h.arrRead.elem_bound hj
  have h24 := h.shell.classBytes_ge_24
  refine returns1_of_star (lbl := 3) (env' := e.insert 4 xs[xs.length - 1]) hfn rfl rfl
    (by arg_eval) (fun rest => ?_)
  refine star_trans0 (hpre rest) ?_
  refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (elemAt_eval (by env_lookup)
    (by env_lookup) hb) (h.elem_load hj)) ?_
  refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
    (h.shell.write_ok (off := 8) (w := .w64) (by simp [X86.Width.bytes]; omega) _) ?_
  exact .refl _

/-- **`pop`** of a boxed unique non-empty array: the size lowered in place; the last element is
returned, to be released by the caller. -/
theorem pop_unique_boxed {P : Program} {fn : FunId} {t : Fns}
    (hfn : P.funcs[fn]? = some (pop t .boxed)) {mem : Memory} {ctx a : Word}
    {cls cap : Nat} {xs : List Word} (h : ArrCell mem a 1 cls cap .boxed xs) (hne : xs ≠ []) :
    Returns2 P fn (({} : Env).insert 0 a) mem ctx 0 a (xs.getLast hne)
        (mem.write .w64 (a + 8) (UInt64.ofNat (xs.length - 1))) ∧
      ArrCell (mem.write .w64 (a + 8) (UInt64.ofNat (xs.length - 1))) a 1 cls cap .boxed
        xs.dropLast := by
  rw [List.dropLast_eq_take, List.getLast_eq_getElem]
  refine ⟨?_, h.truncate (by omega)⟩
  obtain ⟨e, h0, h2, hpre⟩ := pop_to_unique hfn h hne
  have hpos : 0 < xs.length := List.length_pos_iff.mpr hne
  have hj : xs.length - 1 < xs.length := by omega
  have hb := h.arrRead.elem_bound hj
  have h24 := h.shell.classBytes_ge_24
  refine returns2_of_star (lbl := 3) (env' := e.insert 4 xs[xs.length - 1]) hfn rfl rfl
    (by arg_eval) (by arg_eval) (fun rest => ?_)
  refine star_trans0 (hpre rest) ?_
  refine star_assign hfn rfl (by body_pos) rfl (rhs_load_eval (elemAt_eval (by env_lookup)
    (by env_lookup) hb) (h.elem_load hj)) ?_
  refine star_store hfn rfl (by body_pos) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
    (h.shell.write_ok (off := 8) (w := .w64) (by simp [X86.Width.bytes]; omega) _) ?_
  exact .refl _

end IxCC.Rt.Rc.Array
