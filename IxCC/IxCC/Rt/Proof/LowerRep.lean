import IxCC.Rt.Proof.OpsWord
import IxCC.Rt.Proof.OpsAlloc
import IxCC.Rt.Readback

/-! # DR2 Stage W2 Proofs: Raw 64-bit `UInt64`, `box64` / `unbox64`, and Zero-Alloc Limb Pairs

Proves the Stage W2 runtime lowering (`Rt.LowerRep`):

* `PrimCoreRaw` & `wordRaw64_core`: every 64-bit `UInt64` and hardware limb-component operation
  in `LowerRep.wordRaw64` simulates `Lam.wordSem .w64` over FULL `[0, 2^64)` with ZERO
  `natOverflow` (no failure branch!) and memory unchanged.
* `limbPairRaw_mulWide`, `limbPairRaw_divWide`, `limbPairRaw_addCarry`, `limbPairRaw_subBorrow`:
  a single fused `Lir.Stmt.limb r1 r2 op` binds BOTH raw 64-bit results agreeing exactly with
  `IxCC.BigNat.{mulWide64, divWide64, addCarry64, subBorrow64}` with zero heap allocation.
* `box64_sound` & `unbox64_sound` & `box64_readback`: `box64` allocates a 1-scalar-word cell
  `⟨nobj = 0, nscalar = 1, tag = 0⟩` (`BoxedAt m' addr n`, never failing with `natOverflow`),
  preserves memory below `bump`, reads back via `Rt.readbackWord .boxedWord64`, and `unbox64`
  uniformly recovers the raw 64-bit word from BOTH odd tagged immediates `< 2^63` AND even
  boxed 1-scalar-word cells across all `[0, 2^64)`.
* `rawCmp_sound`: raw 64-bit unsigned comparisons agree with `Nat` comparisons across `[0, 2^64)`.

Zero `sorry`, strictly standard axioms `[propext, Classical.choice, Quot.sound]`. -/

set_option autoImplicit false

namespace IxCC.Rt.Proof.LowerRep

open IxCC.Lir (Word)
open IxCC.Rt
open IxCC.Rt.Lower
open IxCC.Rt.LowerRep
open IxCC.Rt.Proof
open IxCC.Src (NatMap Width WordOp LimbOp)

/-! ## Raw 64-bit Heap-Free Core (`PrimCoreRaw`, full `[0, 2^64)`, zero `natOverflow`) -/

/-- **Raw 64-bit heap-free core (Stage W2)**: from registers where `las` evaluate to raw 64-bit
words `ws` matching `ns` (`w.toNat = n`, full `[0, 2^64)`), Lir runs to `(L', p')` with memory
unchanged, binding `x` to the raw 64-bit word `w'` with `w'.toNat = n` and preserving all other
registers below `sup`. Never fails with `natOverflow`. -/
def PrimCoreRaw (lp : Lir.Program) (ctx : Word) (sup fn L p L' p' x : Nat) (op : Lam.Prim)
    (las : List Lir.Arg) : Prop :=
  ∀ (ρl : Lir.Env) (mem : X86.Memory) (rest : List Lir.Frame) (ns : List Nat) (ws : List Word) (n : Nat),
    Lir.evalArgs ρl las = some ws → ListRel (fun n w => w.toNat = n) ns ws →
    (∀ la ∈ las, ArgReads sup la) → op.sem ns = some (.nat n) →
    ∃ c ρl' w, Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn L p ρl rest) c
        (Lir.atState mem ctx fn L' p' ρl' rest) ∧ w.toNat = n ∧ ρl'[x]? = some w ∧
        ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?

private theorem raw_one {ρl : Lir.Env} {la : Lir.Arg} {ns : List Nat} {ws : List Word}
    (hws : Lir.evalArgs ρl [la] = some ws) (hrel : ListRel (fun n w => w.toNat = n) ns ws) :
    ∃ p wa, ns = [p] ∧ la.eval ρl = some wa ∧ wa.toNat = p := by
  simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, Option.bind_eq_bind] at hws
  cases ha : la.eval ρl with
  | none => simp [ha] at hws
  | some wa =>
    simp [ha] at hws; subst hws
    cases hrel with
    | @cons p _ _ _ hwa hnil => cases hnil; exact ⟨p, wa, rfl, rfl, hwa⟩

private theorem raw_two {ρl : Lir.Env} {la lb : Lir.Arg} {ns : List Nat} {ws : List Word}
    (hws : Lir.evalArgs ρl [la, lb] = some ws) (hrel : ListRel (fun n w => w.toNat = n) ns ws) :
    ∃ p q wa wb, ns = [p, q] ∧ la.eval ρl = some wa ∧ lb.eval ρl = some wb ∧
      wa.toNat = p ∧ wb.toNat = q := by
  simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, Option.bind_eq_bind] at hws
  cases ha : la.eval ρl with
  | none => simp [ha] at hws
  | some wa =>
    cases hb : lb.eval ρl with
    | none => simp [ha, hb] at hws
    | some wb =>
      simp [ha, hb] at hws; subst hws
      cases hrel with
      | @cons p _ _ _ hwa hrel1 =>
        cases hrel1 with
        | @cons q _ _ _ hwb hnil => cases hnil; exact ⟨p, q, wa, wb, rfl, rfl, rfl, hwa, hwb⟩

private theorem raw_three {ρl : Lir.Env} {la lb lc : Lir.Arg} {ns : List Nat} {ws : List Word}
    (hws : Lir.evalArgs ρl [la, lb, lc] = some ws) (hrel : ListRel (fun n w => w.toNat = n) ns ws) :
    ∃ a b c wa wb wc, ns = [a, b, c] ∧ la.eval ρl = some wa ∧ lb.eval ρl = some wb ∧
      lc.eval ρl = some wc ∧ wa.toNat = a ∧ wb.toNat = b ∧ wc.toNat = c := by
  simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, Option.bind_eq_bind] at hws
  cases ha : la.eval ρl with
  | none => simp [ha] at hws
  | some wa =>
    cases hb : lb.eval ρl with
    | none => simp [ha, hb] at hws
    | some wb =>
      cases hc : lc.eval ρl with
      | none => simp [ha, hb, hc] at hws
      | some wc =>
        simp [ha, hb, hc] at hws; subst hws
        cases hrel with
        | @cons a _ _ _ hwa h1 =>
          cases h1 with
          | @cons b _ _ _ hwb h2 =>
            cases h2 with
            | @cons c _ _ _ hwc hnil =>
              cases hnil; exact ⟨a, b, c, wa, wb, wc, rfl, rfl, rfl, rfl, hwa, hwb, hwc⟩

/-! ## Multi-block state shapes for `divModRaw64` and `unbox64` -/

/-- State left by `divModRaw64`. -/
def DivModRawSt (st : St) (x : Nat) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg)
    (a b : Lir.Arg) : St :=
  let n := st.next
  let curBlk : PBlock :=
    { params := st.params, body := st.acc.reverse,
      term := .br .eq b (.imm 0) (loc (n + 1)) (loc n) }
  { done := ((st.done.insert st.cur curBlk)
      |>.insert n { body := [.assign st.fresh (.bin o .w64 a b)], term := .jump ⟨.loc (n + 2), [.v st.fresh]⟩ })
      |>.insert (n + 1) { term := .jump ⟨.loc (n + 2), [zero a]⟩, cold := true },
    cur := n + 2, params := [x], acc := [], next := n + 3, fresh := st.fresh + 1 }

theorem divModRaw_code {f : Fir.FunId} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hH : Holds f F off starts C) {st : St} {x : Nat} {o : Lir.BinOp} {zero : Lir.Arg → Lir.Arg}
    {a b : Lir.Arg} (hC : Ext C (DivModRawSt st x o zero a b)) (hl : Labels st) (_ho : Open st) :
    let n := st.next
    (∃ lb, F.blocks[off + st.cur]? = some lb ∧ lb.body.toList = st.acc.reverse ∧
      lb.term = .br .eq .w64 b (.imm 0) ⟨off + (n + 1), []⟩ ⟨off + n, []⟩) ∧
    (∃ nzb, F.blocks[off + n]? = some nzb ∧ nzb.params = [] ∧
      nzb.body.toList = [.assign st.fresh (.bin o .w64 a b)] ∧
      nzb.term = .jump ⟨off + (n + 2), [.v st.fresh]⟩) ∧
    (∃ zb, F.blocks[off + (n + 1)]? = some zb ∧ zb.params = [] ∧ zb.body.toList = [] ∧
      zb.term = .jump ⟨off + (n + 2), [zero a]⟩) ∧
    (∃ jb, F.blocks[off + (n + 2)]? = some jb ∧ jb.params = [x]) := by
  have hcur := hl.cur
  let n := st.next
  refine ⟨?_, ?_, ?_, ?_⟩
  · let curBlk : PBlock :=
      { params := st.params, body := st.acc.reverse,
        term := .br .eq b (.imm 0) (loc (n + 1)) (loc n) }
    obtain ⟨lb, hres, hlb⟩ := hH (hC.done (j := st.cur) (b := curBlk) (by
      simp only [DivModRawSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [↓reduceIte, curBlk, n]))
    obtain ⟨-, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, curBlk] at hterm
    exact ⟨lb, hlb, hbody, hterm.symm⟩
  · obtain ⟨nzb, hres, hnzb⟩ := hH (hC.done (j := n)
      (b := { body := [.assign st.fresh (.bin o .w64 a b)], term := .jump ⟨.loc (n + 2), [.v st.fresh]⟩ }) (by
        simp only [DivModRawSt, NatMap.get?_insert]
        rw [ite_eq_right (by omega)]
        simp only [↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨nzb, hnzb, hp, hbody, hterm.symm⟩
  · obtain ⟨zb, hres, hzb⟩ := hH (hC.done (j := n + 1)
      (b := { term := .jump ⟨.loc (n + 2), [zero a]⟩, cold := true }) (by
        simp only [DivModRawSt, NatMap.get?_insert, ↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨zb, hzb, hp, hbody, hterm.symm⟩
  · have hopen : Open (DivModRawSt st x o zero a b) := by
      simp only [Open, DivModRawSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      cases hq : st.done.get? (n + 2) with
      | none => rfl
      | some bj => have := hl.done hq; omega
    obtain ⟨jb0, hjb0, hjp0, -⟩ := hC.cur hopen
    obtain ⟨jb, hres, hjb⟩ := hH hjb0
    obtain ⟨hjp, -, -⟩ := resolveBlock_ok hres
    exact ⟨jb, hjb, hjp.trans hjp0⟩

/-! ## Raw 64-bit Primitive Core (`wordRaw64_core`) -/

private theorem wordResult_val_word (w : Width) (n : Nat) : (Src.WordResult.word w n).val = n := rfl

/-- Evaluate `LowerRep.wordRaw64` into its final state. -/
macro "raw_run" " at " h:ident : tactic =>
  `(tactic| simp only [wordRaw64, divModRaw64, clz64Code, bin, temp, freshReg, assign, emit,
      newLabel, close, openAt, put, StateT.run, bind, StateT.bind, pure, StateT.pure, modify,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet, Except.bind,
      Except.pure, Except.ok.injEq, Prod.mk.injEq, true_and, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at $h:ident)

/-- **Every 64-bit `UInt64` and hardware limb-component op in `LowerRep.wordRaw64` simulates
`Lam.wordSem .w64` over full `[0, 2^64)` with zero `natOverflow`.** -/
theorem wordRaw64_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {sup fn : Nat} {F : Lir.Func}
    {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {op : WordOp} {las : List Lir.Arg}
    (hrun : (wordRaw64 f x op las).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st)
    (ho : Open st) (hsup : sup ≤ st.fresh) (hx : x < sup) :
    PrimCoreRaw lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word .w64 op) las := by
  cases op <;> (rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, _ | ⟨ld, las⟩⟩⟩⟩) <;>
    try (raw_run at hrun; cases hrun; done)
  case add =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := raw_two hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
    have hx' : Lir.execList ρl mem ctx [.assign x (.bin .add .w64 la lb)] =
        some (ρl.insert x (wa + wb), mem) := by simp [lir_eval, ha, hb]
    exact ⟨0, ρl.insert x (wa + wb), wa + wb,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      rawAdd_toNat hwa hwb, by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
  case sub =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := raw_two hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
    have hx' : Lir.execList ρl mem ctx [.assign x (.bin .sub .w64 la lb)] =
        some (ρl.insert x (wa - wb), mem) := by simp [lir_eval, ha, hb]
    exact ⟨0, ρl.insert x (wa - wb), wa - wb,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      rawSub_toNat hwa hwb, by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
  case mul =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := raw_two hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
    have hx' : Lir.execList ρl mem ctx [.assign x (.bin .mul .w64 la lb)] =
        some (ρl.insert x (wa * wb), mem) := by simp [lir_eval, ha, hb]
    exact ⟨0, ρl.insert x (wa * wb), wa * wb,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      rawMul_toNat hwa hwb, by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
  case div =>
    raw_run at hrun; subst hrun
    have hC' : Ext C (DivModRawSt st x .udiv (fun _ => .imm 0) la lb) := hC
    obtain ⟨⟨lbk, hlb, hbody, hterm⟩, ⟨nzb, hnzb, hnzp, hnzbody, hnzterm⟩,
      ⟨zb, hzb, hzp, hzbody, hzterm⟩, ⟨jb, hjb, hjp⟩⟩ := divModRaw_code hH hC' hl ho
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := raw_two hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
    have hpos : st.acc.length = lbk.body.size := by rw [← Array.length_toList, hbody]; simp
    by_cases hz : wb = 0
    · have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl)
        (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := 0) (vb := 0) hF hlb hpos hterm
        (by simpa [hz] using hb) rfl (by simp [Lir.Cond.holds]) rfl hzb (by simp [hzp, Lir.bindParams])
      have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl)
        (ρ' := ρl.insert x 0) (e := ⟨off + (st.next + 2), [.imm 0]⟩) (vals := [0]) hF hzb
        (by rw [← Array.length_toList, hzbody]) hzterm rfl hjb (by simp [hjp, Lir.bindParams])
      have hval : (0 : Word).toNat = (WordOp.eval .w64 .div p q).val := by
        have := rawDiv_toNat hwa hwb; simpa [hz] using this
      exact ⟨_, ρl.insert x 0, 0, (Lir.star_of_step hbr).trans (Lir.star_of_step hjmp),
        hval, by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
    · have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl)
        (e := ⟨off + st.next, []⟩) (vals := []) (va := wb) (vb := 0) hF hlb hpos hterm
        hb rfl (by simp [Lir.Cond.holds, hz]) rfl hnzb (by simp [hnzp, Lir.bindParams])
      have hbeq0 : (wb == 0) = false := beq_false_of_ne hz
      let qv : Word := wa / wb
      let ρ₁ := ρl.insert st.fresh qv
      have hx1 : Lir.execList ρl mem ctx [.assign st.fresh (.bin .udiv .w64 la lb)] =
          some (ρ₁, mem) := by
        simp only [Lir.execList, Lir.Stmt.exec, Lir.Rhs.eval, ha, hb, Option.bind_eq_bind,
          Option.bind_some, Lir.BinOp.eval, truncate_w64, hbeq0, Bool.false_eq_true, ↓reduceIte,
          qv, ρ₁]
      have h1 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
        hF hnzb (by simpa using hnzbody) (by simp [Lir.Stmt.isCall]) hx1
      have h1' : Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.next) 0 ρl rest) 0
          (Lir.atState mem ctx fn (off + st.next) 1 ρ₁ rest) := by simpa using h1
      have hnzpos : 1 = nzb.body.size := by rw [← Array.length_toList, hnzbody]; rfl
      have hqv : (Lir.Arg.v st.fresh).eval ρ₁ = some qv := by simp [ρ₁]
      have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁)
        (ρ' := ρ₁.insert x qv) (e := ⟨off + (st.next + 2), [.v st.fresh]⟩) (vals := [qv]) hF hnzb
        hnzpos hnzterm (by simp [Lir.evalArgs, hqv]) hjb (by simp [hjp, Lir.bindParams])
      have hval : qv.toNat = (WordOp.eval .w64 .div p q).val := by
        have := rawDiv_toNat hwa hwb; simpa [hbeq0, qv] using this
      exact ⟨_, ρ₁.insert x qv, qv,
        (Lir.star_of_step hbr).trans (h1'.trans (Lir.star_of_step hjmp)),
        hval, by simp, fun y hy hyx => by
          simp only [ρ₁]; rw [Lir.env_insert_ne _ _ (Ne.symm hyx)]; exact Lir.env_insert_ne _ _ (by omega)⟩
  case mod =>
    raw_run at hrun; subst hrun
    have hC' : Ext C (DivModRawSt st x .urem id la lb) := hC
    obtain ⟨⟨lbk, hlb, hbody, hterm⟩, ⟨nzb, hnzb, hnzp, hnzbody, hnzterm⟩,
      ⟨zb, hzb, hzp, hzbody, hzterm⟩, ⟨jb, hjb, hjp⟩⟩ := divModRaw_code hH hC' hl ho
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := raw_two hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
    have hpos : st.acc.length = lbk.body.size := by rw [← Array.length_toList, hbody]; simp
    by_cases hz : wb = 0
    · have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl)
        (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := 0) (vb := 0) hF hlb hpos hterm
        (by simpa [hz] using hb) rfl (by simp [Lir.Cond.holds]) rfl hzb (by simp [hzp, Lir.bindParams])
      have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl)
        (ρ' := ρl.insert x wa) (e := ⟨off + (st.next + 2), [la]⟩) (vals := [wa]) hF hzb
        (by rw [← Array.length_toList, hzbody]) hzterm (by simp [Lir.evalArgs, ha]) hjb
        (by simp [hjp, Lir.bindParams])
      have hval : wa.toNat = (WordOp.eval .w64 .mod p q).val := by
        have := rawMod_toNat hwa hwb; simpa [hz] using this
      exact ⟨_, ρl.insert x wa, wa, (Lir.star_of_step hbr).trans (Lir.star_of_step hjmp),
        hval, by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
    · have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl)
        (e := ⟨off + st.next, []⟩) (vals := []) (va := wb) (vb := 0) hF hlb hpos hterm
        hb rfl (by simp [Lir.Cond.holds, hz]) rfl hnzb (by simp [hnzp, Lir.bindParams])
      have hbeq0 : (wb == 0) = false := beq_false_of_ne hz
      let rv : Word := wa % wb
      let ρ₁ := ρl.insert st.fresh rv
      have hx1 : Lir.execList ρl mem ctx [.assign st.fresh (.bin .urem .w64 la lb)] =
          some (ρ₁, mem) := by
        simp only [Lir.execList, Lir.Stmt.exec, Lir.Rhs.eval, ha, hb, Option.bind_eq_bind,
          Option.bind_some, Lir.BinOp.eval, truncate_w64, hbeq0, Bool.false_eq_true, ↓reduceIte,
          rv, ρ₁]
      have h1 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
        hF hnzb (by simpa using hnzbody) (by simp [Lir.Stmt.isCall]) hx1
      have h1' : Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.next) 0 ρl rest) 0
          (Lir.atState mem ctx fn (off + st.next) 1 ρ₁ rest) := by simpa using h1
      have hnzpos : 1 = nzb.body.size := by rw [← Array.length_toList, hnzbody]; rfl
      have hrv : (Lir.Arg.v st.fresh).eval ρ₁ = some rv := by simp [ρ₁]
      have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁)
        (ρ' := ρ₁.insert x rv) (e := ⟨off + (st.next + 2), [.v st.fresh]⟩) (vals := [rv]) hF hnzb
        hnzpos hnzterm (by simp [Lir.evalArgs, hrv]) hjb (by simp [hjp, Lir.bindParams])
      have hval : rv.toNat = (WordOp.eval .w64 .mod p q).val := by
        have := rawMod_toNat hwa hwb; simpa [hbeq0, rv] using this
      exact ⟨_, ρ₁.insert x rv, rv,
        (Lir.star_of_step hbr).trans (h1'.trans (Lir.star_of_step hjmp)),
        hval, by simp, fun y hy hyx => by
          simp only [ρ₁]; rw [Lir.env_insert_ne _ _ (Ne.symm hyx)]; exact Lir.env_insert_ne _ _ (by omega)⟩
  case land =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := raw_two hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
    have hx' : Lir.execList ρl mem ctx [.assign x (.bin .and .w64 la lb)] =
        some (ρl.insert x (wa &&& wb), mem) := by simp [lir_eval, ha, hb]
    exact ⟨0, ρl.insert x (wa &&& wb), wa &&& wb,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      rawLand_toNat hwa hwb, by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
  case lor =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := raw_two hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
    have hx' : Lir.execList ρl mem ctx [.assign x (.bin .or .w64 la lb)] =
        some (ρl.insert x (wa ||| wb), mem) := by simp [lir_eval, ha, hb]
    exact ⟨0, ρl.insert x (wa ||| wb), wa ||| wb,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      rawLor_toNat hwa hwb, by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
  case xor =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := raw_two hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
    have hx' : Lir.execList ρl mem ctx [.assign x (.bin .xor .w64 la lb)] =
        some (ρl.insert x (wa ^^^ wb), mem) := by simp [lir_eval, ha, hb]
    exact ⟨0, ρl.insert x (wa ^^^ wb), wa ^^^ wb,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      rawXor_toNat hwa hwb, by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
  case shiftLeft =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel hreads hsem
    obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := raw_two hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
    have hra := hreads la (by simp)
    have ha1 : la.eval (ρl.insert st.fresh (wb &&& 63)) = some wa := by
      rw [arg_eval_temp hra hsup]; exact ha
    let r : Word := wa <<< ((wb &&& 63) &&& 63)
    have hx' : Lir.execList ρl mem ctx
        [.assign st.fresh (.bin .and .w64 lb (.imm 63)),
         .assign x (.bin .shl .w64 la (.v st.fresh))] =
        some ((ρl.insert st.fresh (wb &&& 63)).insert x r, mem) := by
      simp only [Lir.execList, Lir.Stmt.exec, Lir.Rhs.eval, hb, Lir.Arg.eval_imm, Option.bind_eq_bind,
        Option.bind_some, Lir.BinOp.eval, truncate_w64, shiftMask_w64, ha1, Lir.Arg.eval_v,
        Lir.env_insert_self, r]
    exact ⟨0, (ρl.insert st.fresh (wb &&& 63)).insert x r, r,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      rawShl_toNat hwa hwb, by simp, fun y hy hyx => by
        rw [Lir.env_insert_ne _ _ (Ne.symm hyx)]; exact Lir.env_insert_ne _ _ (by omega)⟩
  case shiftRight =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel hreads hsem
    obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := raw_two hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
    have hra := hreads la (by simp)
    have ha1 : la.eval (ρl.insert st.fresh (wb &&& 63)) = some wa := by
      rw [arg_eval_temp hra hsup]; exact ha
    let r : Word := wa >>> ((wb &&& 63) &&& 63)
    have hx' : Lir.execList ρl mem ctx
        [.assign st.fresh (.bin .and .w64 lb (.imm 63)),
         .assign x (.bin .shr .w64 la (.v st.fresh))] =
        some ((ρl.insert st.fresh (wb &&& 63)).insert x r, mem) := by
      simp only [Lir.execList, Lir.Stmt.exec, Lir.Rhs.eval, hb, Lir.Arg.eval_imm, Option.bind_eq_bind,
        Option.bind_some, Lir.BinOp.eval, truncate_w64, shiftMask_w64, ha1, Lir.Arg.eval_v,
        Lir.env_insert_self, r]
    exact ⟨0, (ρl.insert st.fresh (wb &&& 63)).insert x r, r,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      rawShr_toNat hwa hwb, by simp, fun y hy hyx => by
        rw [Lir.env_insert_ne _ _ (Ne.symm hyx)]; exact Lir.env_insert_ne _ _ (by omega)⟩
  case complement =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, wa, rfl, ha, hwa⟩ := raw_one hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, rfl⟩ := Lam.wordSem_one hsem
    have hx' : Lir.execList ρl mem ctx [.assign x (.bin .xor .w64 la (.imm 0xFFFFFFFFFFFFFFFF))] =
        some (ρl.insert x (wa ^^^ 0xFFFFFFFFFFFFFFFF), mem) := by simp [lir_eval, ha]
    exact ⟨0, ρl.insert x (wa ^^^ 0xFFFFFFFFFFFFFFFF), wa ^^^ 0xFFFFFFFFFFFFFFFF,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      rawComplement_toNat hwa, by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
  case neg =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, wa, rfl, ha, hwa⟩ := raw_one hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, rfl⟩ := Lam.wordSem_one hsem
    have hx' : Lir.execList ρl mem ctx [.assign x (.bin .sub .w64 (.imm 0) la)] =
        some (ρl.insert x (0 - wa), mem) := by simp [lir_eval, ha]
    exact ⟨0, ρl.insert x (0 - wa), 0 - wa,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      rawNeg_toNat hwa, by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
  case ofNat =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, wa, rfl, ha, hwa⟩ := raw_one hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, rfl⟩ := Lam.wordSem_one hsem
    have hlt := wa.toNat_lt_size; simp only [UInt64.size] at hlt
    have hx' : Lir.execList ρl mem ctx [.assign x (.arg la)] = some (ρl.insert x wa, mem) := by
      simp [lir_eval, ha]
    exact ⟨0, ρl.insert x wa, wa, straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      by simp [WordOp.eval, Src.WordResult.val, Width.size, Width.bits, ← hwa, Nat.mod_eq_of_lt hlt],
      by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
  case toNat =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, wa, rfl, ha, hwa⟩ := raw_one hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, rfl⟩ := Lam.wordSem_one hsem
    have hx' : Lir.execList ρl mem ctx [.assign x (.arg la)] = some (ρl.insert x wa, mem) := by
      simp [lir_eval, ha]
    exact ⟨0, ρl.insert x wa, wa, straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      hwa, by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
  case convert w' =>
    by_cases hw' : w' = .w64
    · subst hw'
      raw_run at hrun; subst hrun
      intro ρl mem rest ns ws n hws hrel _ hsem
      obtain ⟨p, wa, rfl, ha, hwa⟩ := raw_one hws hrel
      rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, rfl⟩ := Lam.wordSem_one hsem
      have hx' : Lir.execList ρl mem ctx [.assign x (.arg la)] = some (ρl.insert x wa, mem) := by
        simp [lir_eval, ha]
      exact ⟨0, ρl.insert x wa, wa, straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
        by simp [hwa], by simp,
        fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
    · have hgo : ∀ (w'' : Width), w'' ≠ .w64 →
          st' = { st with acc := .assign x (.bin .and .w64 la (.imm (UInt64.ofNat (w''.size - 1)))) :: st.acc } →
          PrimCoreRaw lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
            (.word .w64 (.convert w'')) [la] := by
        intro w'' hne hst
        subst hst
        intro ρl mem rest ns ws n hws hrel _ hsem
        obtain ⟨p, wa, rfl, ha, hwa⟩ := raw_one hws hrel
        rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, rfl⟩ := Lam.wordSem_one hsem
        have hx' : Lir.execList ρl mem ctx
            [.assign x (.bin .and .w64 la (.imm (UInt64.ofNat (w''.size - 1))))] =
            some (ρl.insert x (wa &&& UInt64.ofNat (w''.size - 1)), mem) := by simp [lir_eval, ha]
        exact ⟨0, ρl.insert x (wa &&& UInt64.ofNat (w''.size - 1)),
          wa &&& UInt64.ofNat (w''.size - 1),
          straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
          rawConvertNarrow_toNat hne hwa, by simp,
          fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
      cases w' with
      | w64 => exact absurd rfl hw'
      | w8 => raw_run at hrun; exact hgo .w8 (by decide) hrun.symm
      | w16 => raw_run at hrun; exact hgo .w16 (by decide) hrun.symm
      | w32 => raw_run at hrun; exact hgo .w32 (by decide) hrun.symm
  case clz64 =>
    raw_run at hrun; subst hrun
    let nzBody : List Lir.Stmt := [
      .assign st.fresh (.bsr64 la),
      .assign (st.fresh + 1) (.bin .sub .w64 (.imm 63) (.v st.fresh))]
    have hC' : Ext C (ClzSt st x [] la (.imm 64) nzBody (.v (st.fresh + 1)) (st.fresh + 1 + 1)) := by
      simpa [ClzSt] using hC
    obtain ⟨⟨lbk, hlb, hbody, hterm⟩, ⟨zb, hzb, hzp, hzbody, hzterm⟩,
      ⟨nzb, hnzb, hnzp, hnzbody, hnzterm⟩, ⟨jb, hjb, hjp⟩⟩ := clz_code hH hC' hl ho
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, wa, rfl, ha, hwa⟩ := raw_one hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, rfl⟩ := Lam.wordSem_one hsem
    have hpos : st.acc.length = lbk.body.size := by rw [← Array.length_toList, hbody]; simp
    by_cases hz : wa = 0
    · have hp0 : p = 0 := by rw [← hwa, hz]; rfl
      subst hp0
      have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl)
        (e := ⟨off + st.next, []⟩) (vals := []) (va := 0) (vb := 0) hF hlb hpos hterm
        (by simpa [hz] using ha) rfl (by simp [Lir.Cond.holds]) rfl hzb (by simp [hzp, Lir.bindParams])
      have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl)
        (ρ' := ρl.insert x 64) (e := ⟨off + (st.next + 2), [.imm 64]⟩) (vals := [64]) hF hzb
        (by rw [← Array.length_toList, hzbody]) hzterm rfl hjb (by simp [hjp, Lir.bindParams])
      exact ⟨_, ρl.insert x 64, 64, (Lir.star_of_step hbr).trans (Lir.star_of_step hjmp),
        rawClz64_zero, by simp, fun y _ hyx => Lir.env_insert_ne _ _ (Ne.symm hyx)⟩
    · have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl)
        (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := wa) (vb := 0) hF hlb hpos hterm
        ha rfl (by simp [Lir.Cond.holds, hz]) rfl hnzb (by simp [hnzp, Lir.bindParams])
      have hbeq0 : (wa == 0) = false := beq_false_of_ne hz
      let bval : Word := UInt64.ofNat wa.toNat.log2
      let rval : Word := 63 - bval
      let ρ₁ := ρl.insert st.fresh bval
      let ρ₂ := ρ₁.insert (st.fresh + 1) rval
      have hs1 : Lir.Stmt.exec ρl mem ctx (.assign st.fresh (.bsr64 la)) = some (ρ₁, mem) := by
        simp only [Lir.Stmt.exec, Lir.Rhs.eval, ha, Option.bind_eq_bind, Option.bind_some, hbeq0,
          Bool.false_eq_true, ↓reduceIte, bval, ρ₁]
      have hs2 : Lir.Stmt.exec ρ₁ mem ctx
          (.assign (st.fresh + 1) (.bin .sub .w64 (.imm 63) (.v st.fresh))) = some (ρ₂, mem) := by
        have hb1 : (Lir.Arg.v st.fresh).eval ρ₁ = some bval := by simp [ρ₁]
        simp only [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval_imm, hb1, Option.bind_eq_bind,
          Option.bind_some, Lir.BinOp.eval, truncate_w64, rval, ρ₂]
      have hx2 : Lir.execList ρl mem ctx nzBody = some (ρ₂, mem) := by
        simp only [nzBody, Lir.execList, hs1, hs2]
      have h2 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
        hF hnzb (by simpa using hnzbody) (by simp [nzBody, Lir.Stmt.isCall]) hx2
      have h2' : Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + (st.next + 1)) 0 ρl rest) 0
          (Lir.atState mem ctx fn (off + (st.next + 1)) nzBody.length ρ₂ rest) := by simpa using h2
      have hnzpos : nzBody.length = nzb.body.size := by rw [← Array.length_toList, hnzbody]
      have hrval : (Lir.Arg.v (st.fresh + 1)).eval ρ₂ = some rval := by simp [ρ₂]
      have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₂)
        (ρ' := ρ₂.insert x rval) (e := ⟨off + (st.next + 2), [.v (st.fresh + 1)]⟩)
        (vals := [rval]) hF hnzb hnzpos hnzterm (by simp [Lir.evalArgs, hrval]) hjb
        (by simp [hjp, Lir.bindParams])
      exact ⟨_, ρ₂.insert x rval, rval,
        (Lir.star_of_step hbr).trans (h2'.trans (Lir.star_of_step hjmp)),
        rawClz64_nz hwa hz, by simp, fun y hy hyx => by
          simp only [ρ₂, ρ₁]; rw [Lir.env_insert_ne _ _ (Ne.symm hyx)]; regs_ne⟩
  case mulWideLo =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := raw_two hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
    let lo : Word := wa * wb
    let hi : Word := UInt64.ofNat (wa.toNat * wb.toNat / 2 ^ 64)
    have hx' : Lir.execList ρl mem ctx [.limb x st.fresh (.mulWide64 la lb)] =
        some ((ρl.insert x lo).insert st.fresh hi, mem) := by
      simp only [Lir.execList, Lir.Stmt.exec, Lir.LimbOp.eval, ha, hb, Option.bind_eq_bind,
        Option.bind_some, lo, hi]
    exact ⟨0, (ρl.insert x lo).insert st.fresh hi, lo,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      rawMulWideLo_toNat hwa hwb,
      by rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_self],
      fun y hy hyx => by rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (Ne.symm hyx)]⟩
  case mulWideHi =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := raw_two hws hrel
    rw [Lam.Prim.sem_word] at hsem; obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
    let lo : Word := wa * wb
    let hi : Word := UInt64.ofNat (wa.toNat * wb.toNat / 2 ^ 64)
    have hx' : Lir.execList ρl mem ctx [.limb st.fresh x (.mulWide64 la lb)] =
        some ((ρl.insert st.fresh lo).insert x hi, mem) := by
      simp only [Lir.execList, Lir.Stmt.exec, Lir.LimbOp.eval, ha, hb, Option.bind_eq_bind,
        Option.bind_some, lo, hi]
    exact ⟨0, (ρl.insert st.fresh lo).insert x hi, hi,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      rawMulWideHi_toNat hwa hwb, by simp,
      fun y hy hyx => by rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega)]⟩
  case divWideQ =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨hi, lo, d, whi, wlo, wd, rfl, ha, hb, hc, hwa, hwb, hwc⟩ := raw_three hws hrel
    rw [Lam.Prim.sem_word] at hsem
    obtain ⟨-, -, -, -, -, res, hres, rfl⟩ := Lam.wordSem_three hsem
    simp only [WordOp.eval3] at hres
    split at hres
    · rename_i hlt; simp only [Option.some.injEq] at hres; subst hres
      have hcond : (wd.toNat == 0 || decide (wd.toNat ≤ whi.toNat)) = false := by
        simp only [hwa, hwc, Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]; omega
      let qv : Word := UInt64.ofNat ((whi.toNat * 2 ^ 64 + wlo.toNat) / wd.toNat)
      let rv : Word := UInt64.ofNat ((whi.toNat * 2 ^ 64 + wlo.toNat) % wd.toNat)
      have hx' : Lir.execList ρl mem ctx [.limb x st.fresh (.divWide64 la lb lc)] =
          some ((ρl.insert x qv).insert st.fresh rv, mem) := by
        simp only [Lir.execList, Lir.Stmt.exec, Lir.LimbOp.eval, ha, hb, hc, Option.bind_eq_bind,
          Option.bind_some, hcond, Bool.false_eq_true, ↓reduceIte, qv, rv]
      exact ⟨0, (ρl.insert x qv).insert st.fresh rv, qv,
        straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
        (rawDivWideQ_toNat hwa hwb hwc hlt).trans (wordResult_val_word .w64 _).symm,
        by rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_self],
        fun y hy hyx => by rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (Ne.symm hyx)]⟩
    · cases hres
  case divWideR =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨hi, lo, d, whi, wlo, wd, rfl, ha, hb, hc, hwa, hwb, hwc⟩ := raw_three hws hrel
    rw [Lam.Prim.sem_word] at hsem
    obtain ⟨-, -, -, -, -, res, hres, rfl⟩ := Lam.wordSem_three hsem
    simp only [WordOp.eval3] at hres
    split at hres
    · rename_i hlt; simp only [Option.some.injEq] at hres; subst hres
      have hcond : (wd.toNat == 0 || decide (wd.toNat ≤ whi.toNat)) = false := by
        simp only [hwa, hwc, Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]; omega
      let qv : Word := UInt64.ofNat ((whi.toNat * 2 ^ 64 + wlo.toNat) / wd.toNat)
      let rv : Word := UInt64.ofNat ((whi.toNat * 2 ^ 64 + wlo.toNat) % wd.toNat)
      have hx' : Lir.execList ρl mem ctx [.limb st.fresh x (.divWide64 la lb lc)] =
          some ((ρl.insert st.fresh qv).insert x rv, mem) := by
        simp only [Lir.execList, Lir.Stmt.exec, Lir.LimbOp.eval, ha, hb, hc, Option.bind_eq_bind,
          Option.bind_some, hcond, Bool.false_eq_true, ↓reduceIte, qv, rv]
      exact ⟨0, (ρl.insert st.fresh qv).insert x rv, rv,
        straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
        (rawDivWideR_toNat hwa hwb hwc hlt).trans (wordResult_val_word .w64 _).symm, by simp,
        fun y hy hyx => by rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega)]⟩
    · cases hres
  case addCarryLo =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨a, b, c, wa, wb, wc, rfl, ha, hb, hc, hwa, hwb, hwc⟩ := raw_three hws hrel
    rw [Lam.Prim.sem_word] at hsem
    obtain ⟨-, -, -, -, -, res, hres, rfl⟩ := Lam.wordSem_three hsem
    simp only [WordOp.eval3, Option.some.injEq] at hres; subst hres
    let cin : Nat := if wc == 0 then 0 else 1
    let sv : Word := wa + wb + UInt64.ofNat cin
    let co : Word := if wa.toNat + wb.toNat + cin ≥ 2 ^ 64 then 1 else 0
    have hx' : Lir.execList ρl mem ctx [.limb x st.fresh (.addCarry64 la lb lc)] =
        some ((ρl.insert x sv).insert st.fresh co, mem) := by
      simp only [Lir.execList, Lir.Stmt.exec, Lir.LimbOp.eval, ha, hb, hc, Option.bind_eq_bind,
        Option.bind_some, cin, sv, co]
    exact ⟨0, (ρl.insert x sv).insert st.fresh co, sv,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      (rawAddCarryLo_toNat hwa hwb hwc).trans (wordResult_val_word .w64 _).symm,
      by rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_self],
      fun y hy hyx => by rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (Ne.symm hyx)]⟩
  case addCarryOut =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨a, b, c, wa, wb, wc, rfl, ha, hb, hc, hwa, hwb, hwc⟩ := raw_three hws hrel
    rw [Lam.Prim.sem_word] at hsem
    obtain ⟨-, -, -, -, -, res, hres, rfl⟩ := Lam.wordSem_three hsem
    simp only [WordOp.eval3, Option.some.injEq] at hres; subst hres
    let cin : Nat := if wc == 0 then 0 else 1
    let sv : Word := wa + wb + UInt64.ofNat cin
    let co : Word := if wa.toNat + wb.toNat + cin ≥ 2 ^ 64 then 1 else 0
    have hx' : Lir.execList ρl mem ctx [.limb st.fresh x (.addCarry64 la lb lc)] =
        some ((ρl.insert st.fresh sv).insert x co, mem) := by
      simp only [Lir.execList, Lir.Stmt.exec, Lir.LimbOp.eval, ha, hb, hc, Option.bind_eq_bind,
        Option.bind_some, cin, sv, co]
    exact ⟨0, (ρl.insert st.fresh sv).insert x co, co,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      (rawAddCarryOut_toNat hwa hwb hwc).trans (wordResult_val_word .w64 _).symm, by simp,
      fun y hy hyx => by rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega)]⟩
  case subBorrowLo =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨a, b, c, wa, wb, wc, rfl, ha, hb, hc, hwa, hwb, hwc⟩ := raw_three hws hrel
    rw [Lam.Prim.sem_word] at hsem
    obtain ⟨-, -, -, -, -, res, hres, rfl⟩ := Lam.wordSem_three hsem
    simp only [WordOp.eval3, Option.some.injEq] at hres; subst hres
    let bin : Nat := if wc == 0 then 0 else 1
    let dv : Word := wa - wb - UInt64.ofNat bin
    let bo : Word := if wa.toNat < wb.toNat + bin then 1 else 0
    have hx' : Lir.execList ρl mem ctx [.limb x st.fresh (.subBorrow64 la lb lc)] =
        some ((ρl.insert x dv).insert st.fresh bo, mem) := by
      simp only [Lir.execList, Lir.Stmt.exec, Lir.LimbOp.eval, ha, hb, hc, Option.bind_eq_bind,
        Option.bind_some, bin, dv, bo]
    exact ⟨0, (ρl.insert x dv).insert st.fresh bo, dv,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      (rawSubBorrowLo_toNat hwa hwb hwc).trans (wordResult_val_word .w64 _).symm,
      by rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_self],
      fun y hy hyx => by rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (Ne.symm hyx)]⟩
  case subBorrowOut =>
    raw_run at hrun; subst hrun
    intro ρl mem rest ns ws n hws hrel _ hsem
    obtain ⟨a, b, c, wa, wb, wc, rfl, ha, hb, hc, hwa, hwb, hwc⟩ := raw_three hws hrel
    rw [Lam.Prim.sem_word] at hsem
    obtain ⟨-, -, -, -, -, res, hres, rfl⟩ := Lam.wordSem_three hsem
    simp only [WordOp.eval3, Option.some.injEq] at hres; subst hres
    let bin : Nat := if wc == 0 then 0 else 1
    let dv : Word := wa - wb - UInt64.ofNat bin
    let bo : Word := if wa.toNat < wb.toNat + bin then 1 else 0
    have hx' : Lir.execList ρl mem ctx [.limb st.fresh x (.subBorrow64 la lb lc)] =
        some ((ρl.insert st.fresh dv).insert x bo, mem) := by
      simp only [Lir.execList, Lir.Stmt.exec, Lir.LimbOp.eval, ha, hb, hc, Option.bind_eq_bind,
        Option.bind_some, bin, dv, bo]
    exact ⟨0, (ρl.insert st.fresh dv).insert x bo, bo,
      straight_star hF hH hC ho (by simp [Lir.Stmt.isCall]) hx',
      (rawSubBorrowOut_toNat hwa hwb hwc).trans (wordResult_val_word .w64 _).symm, by simp,
      fun y hy hyx => by rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega)]⟩

/-! ## Zero-Alloc Fused Limb Pairs (`Lir.Stmt.limb r1 r2 op`) -/

theorem limbPairRaw_mulWide {ρl : Lir.Env} {mem : X86.Memory} {ctx : Word} {r1 r2 : Lir.VReg}
    {la lb : Lir.Arg} {a b : UInt64} (hne : r1 ≠ r2)
    (ha : la.eval ρl = some a) (hb : lb.eval ρl = some b) :
    ∃ ρl', Lir.Stmt.exec ρl mem ctx (.limb r1 r2 (.mulWide64 la lb)) = some (ρl', mem) ∧
      ρl'[r1]? = some (IxCC.BigNat.mulWide64 a b).1 ∧
      ρl'[r2]? = some (IxCC.BigNat.mulWide64 a b).2 ∧
      ∀ y, y ≠ r1 → y ≠ r2 → ρl'[y]? = ρl[y]? := by
  let lo : Word := a * b
  let hi : Word := UInt64.ofNat (a.toNat * b.toNat / 2 ^ 64)
  have hlo : lo = (IxCC.BigNat.mulWide64 a b).1 :=
    UInt64.toNat_inj.mp ((rawMulWideLo_toNat (p := a.toNat) (q := b.toNat) rfl rfl).trans
      (LimbOp.mulWide64_lo_conservative a b))
  have hhi : hi = (IxCC.BigNat.mulWide64 a b).2 :=
    UInt64.toNat_inj.mp ((rawMulWideHi_toNat (p := a.toNat) (q := b.toNat) rfl rfl).trans
      (LimbOp.mulWide64_hi_conservative a b))
  refine ⟨(ρl.insert r1 lo).insert r2 hi, ?_, ?_, ?_, ?_⟩
  · simp only [Lir.Stmt.exec, Lir.LimbOp.eval, ha, hb, Option.bind_eq_bind, Option.bind_some, lo, hi]
  · rw [Lir.env_insert_ne _ _ hne.symm, Lir.env_insert_self, hlo]
  · rw [Lir.env_insert_self, hhi]
  · intro y hy1 hy2; rw [Lir.env_insert_ne _ _ (Ne.symm hy2), Lir.env_insert_ne _ _ (Ne.symm hy1)]

theorem limbPairRaw_divWide {ρl : Lir.Env} {mem : X86.Memory} {ctx : Word} {r1 r2 : Lir.VReg}
    {lhi llo ld : Lir.Arg} {hi lo d : UInt64} (hne : r1 ≠ r2) (hlt : hi < d)
    (hhi : lhi.eval ρl = some hi) (hlo : llo.eval ρl = some lo) (hd : ld.eval ρl = some d) :
    ∃ ρl', Lir.Stmt.exec ρl mem ctx (.limb r1 r2 (.divWide64 lhi llo ld)) = some (ρl', mem) ∧
      ρl'[r1]? = some (IxCC.BigNat.divWide64 hi lo d hlt).1 ∧
      ρl'[r2]? = some (IxCC.BigNat.divWide64 hi lo d hlt).2 ∧
      ∀ y, y ≠ r1 → y ≠ r2 → ρl'[y]? = ρl[y]? := by
  have hltNat : hi.toNat < d.toNat := UInt64.lt_iff_toNat_lt.mp hlt
  have hcond : (d.toNat == 0 || decide (d.toNat ≤ hi.toNat)) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]; omega
  let qv : Word := UInt64.ofNat ((hi.toNat * 2 ^ 64 + lo.toNat) / d.toNat)
  let rv : Word := UInt64.ofNat ((hi.toNat * 2 ^ 64 + lo.toNat) % d.toNat)
  have hq : qv = (IxCC.BigNat.divWide64 hi lo d hlt).1 :=
    UInt64.toNat_inj.mp (by rw [rawDivWideQ_toNat rfl rfl rfl hltNat, IxCC.BigNat.divWide64_fst]; rfl)
  have hr : rv = (IxCC.BigNat.divWide64 hi lo d hlt).2 :=
    UInt64.toNat_inj.mp (by rw [rawDivWideR_toNat rfl rfl rfl hltNat, IxCC.BigNat.divWide64_snd]; rfl)
  refine ⟨(ρl.insert r1 qv).insert r2 rv, ?_, ?_, ?_, ?_⟩
  · simp only [Lir.Stmt.exec, Lir.LimbOp.eval, hhi, hlo, hd, Option.bind_eq_bind, Option.bind_some,
      hcond, Bool.false_eq_true, ↓reduceIte, qv, rv]
  · rw [Lir.env_insert_ne _ _ hne.symm, Lir.env_insert_self, hq]
  · rw [Lir.env_insert_self, hr]
  · intro y hy1 hy2; rw [Lir.env_insert_ne _ _ (Ne.symm hy2), Lir.env_insert_ne _ _ (Ne.symm hy1)]

theorem limbPairRaw_addCarry {ρl : Lir.Env} {mem : X86.Memory} {ctx : Word} {r1 r2 : Lir.VReg}
    {la lb lc : Lir.Arg} {a b : UInt64} {c : Bool} (hne : r1 ≠ r2)
    (ha : la.eval ρl = some a) (hb : lb.eval ρl = some b)
    (hc : lc.eval ρl = some (UInt64.ofNat c.toNat)) :
    ∃ ρl', Lir.Stmt.exec ρl mem ctx (.limb r1 r2 (.addCarry64 la lb lc)) = some (ρl', mem) ∧
      ρl'[r1]? = some (IxCC.BigNat.addCarry64 a b c).1 ∧
      ρl'[r2]? = some (UInt64.ofNat (IxCC.BigNat.addCarry64 a b c).2.toNat) ∧
      ∀ y, y ≠ r1 → y ≠ r2 → ρl'[y]? = ρl[y]? := by
  let wc : Word := UInt64.ofNat c.toNat
  have hwc : wc.toNat = c.toNat := by cases c <;> decide
  let cin : Nat := if wc == 0 then 0 else 1
  let sv : Word := a + b + UInt64.ofNat cin
  let co : Word := if a.toNat + b.toNat + cin ≥ 2 ^ 64 then 1 else 0
  have h1 : sv = (IxCC.BigNat.addCarry64 a b c).1 := by
    apply UInt64.toNat_inj.mp
    have hlo := LimbOp.addCarry64_lo_conservative a b c
    simp only [WordOp.eval3, Option.some.injEq, Src.WordResult.word.injEq, true_and] at hlo
    rw [rawAddCarryLo_toNat (p := a.toNat) (q := b.toNat) (c := c.toNat) rfl rfl hwc, hlo]
  have h2 : co = UInt64.ofNat (IxCC.BigNat.addCarry64 a b c).2.toNat := by
    apply UInt64.toNat_inj.mp
    have hout := LimbOp.addCarry64_out_conservative a b c
    simp only [WordOp.eval3, Option.some.injEq, Src.WordResult.word.injEq, true_and] at hout
    have hlt : (IxCC.BigNat.addCarry64 a b c).2.toNat < 2 ^ 64 := by
      cases (IxCC.BigNat.addCarry64 a b c).2 <;> decide
    rw [rawAddCarryOut_toNat (p := a.toNat) (q := b.toNat) (c := c.toNat) rfl rfl hwc, hout,
      toNat_ofNat_lt hlt]
  refine ⟨(ρl.insert r1 sv).insert r2 co, ?_, ?_, ?_, ?_⟩
  · simp only [Lir.Stmt.exec, Lir.LimbOp.eval, ha, hb, hc, Option.bind_eq_bind, Option.bind_some,
      wc, cin, sv, co]
  · rw [Lir.env_insert_ne _ _ hne.symm, Lir.env_insert_self, h1]
  · rw [Lir.env_insert_self, h2]
  · intro y hy1 hy2; rw [Lir.env_insert_ne _ _ (Ne.symm hy2), Lir.env_insert_ne _ _ (Ne.symm hy1)]

theorem limbPairRaw_subBorrow {ρl : Lir.Env} {mem : X86.Memory} {ctx : Word} {r1 r2 : Lir.VReg}
    {la lb lc : Lir.Arg} {a b : UInt64} {bIn : Bool} (hne : r1 ≠ r2)
    (ha : la.eval ρl = some a) (hb : lb.eval ρl = some b)
    (hc : lc.eval ρl = some (UInt64.ofNat bIn.toNat)) :
    ∃ ρl', Lir.Stmt.exec ρl mem ctx (.limb r1 r2 (.subBorrow64 la lb lc)) = some (ρl', mem) ∧
      ρl'[r1]? = some (IxCC.BigNat.subBorrow64 a b bIn).1 ∧
      ρl'[r2]? = some (UInt64.ofNat (IxCC.BigNat.subBorrow64 a b bIn).2.toNat) ∧
      ∀ y, y ≠ r1 → y ≠ r2 → ρl'[y]? = ρl[y]? := by
  let wc : Word := UInt64.ofNat bIn.toNat
  have hwc : wc.toNat = bIn.toNat := by cases bIn <;> decide
  let bin : Nat := if wc == 0 then 0 else 1
  let dv : Word := a - b - UInt64.ofNat bin
  let bo : Word := if a.toNat < b.toNat + bin then 1 else 0
  have h1 : dv = (IxCC.BigNat.subBorrow64 a b bIn).1 := by
    apply UInt64.toNat_inj.mp
    have hlo := LimbOp.subBorrow64_lo_conservative a b bIn
    simp only [WordOp.eval3, Option.some.injEq, Src.WordResult.word.injEq, true_and] at hlo
    rw [rawSubBorrowLo_toNat (p := a.toNat) (q := b.toNat) (c := bIn.toNat) rfl rfl hwc, hlo]
  have h2 : bo = UInt64.ofNat (IxCC.BigNat.subBorrow64 a b bIn).2.toNat := by
    apply UInt64.toNat_inj.mp
    have hout := LimbOp.subBorrow64_out_conservative a b bIn
    simp only [WordOp.eval3, Option.some.injEq, Src.WordResult.word.injEq, true_and] at hout
    have hlt : (IxCC.BigNat.subBorrow64 a b bIn).2.toNat < 2 ^ 64 := by
      cases (IxCC.BigNat.subBorrow64 a b bIn).2 <;> decide
    rw [rawSubBorrowOut_toNat (p := a.toNat) (q := b.toNat) (c := bIn.toNat) rfl rfl hwc, hout,
      toNat_ofNat_lt hlt]
  refine ⟨(ρl.insert r1 dv).insert r2 bo, ?_, ?_, ?_, ?_⟩
  · simp only [Lir.Stmt.exec, Lir.LimbOp.eval, ha, hb, hc, Option.bind_eq_bind, Option.bind_some,
      wc, bin, dv, bo]
  · rw [Lir.env_insert_ne _ _ hne.symm, Lir.env_insert_self, h1]
  · rw [Lir.env_insert_self, h2]
  · intro y hy1 hy2; rw [Lir.env_insert_ne _ _ (Ne.symm hy2), Lir.env_insert_ne _ _ (Ne.symm hy1)]

/-! ## `box64` and `unbox64` Soundness & Readback -/

/-- A 1-scalar-word boxed `UInt64` cell (`nobj = 0, nscalar = 1, tag = 0`, 16 bytes, `scan = 0`,
raw 64-bit payload at `[w + 8]`) live in `m` at aligned even address `w`. -/
def BoxedAt (m : X86.Memory) (w : Word) (n : Nat) : Prop :=
  w &&& 1 = 0 ∧ WordAt m w (immortalHeader 0 0) ∧ WordAt m (w + 8) (UInt64.ofNat n) ∧ n < 2 ^ 64

/-- A uniform `.obj` word representing `n < 2^64`: either an odd tagged immediate `2n + 1`
(`n < 2^63`) or an even pointer to a 1-scalar-word boxed cell `BoxedAt m w n`. -/
def ObjWordRep (m : X86.Memory) (n : Nat) (w : Word) : Prop :=
  natWord n = some w ∨ BoxedAt m w n

/-- Any boxed 1-scalar-word cell reads back as `Obs.word (UInt64.ofNat n)`. -/
theorem box64_readback {sig : Sig} {fuel : Nat} {m : X86.Memory} {w : Word} {n : Nat}
    (hb : BoxedAt m w n) :
    readbackWord sig fuel m .boxedWord64 w = some (.word (UInt64.ofNat n)) := by
  obtain ⟨heven, hh, hv, _⟩ := hb
  exact readbackWord_boxed_cell (by rw [heven]; decide) hh.read64 hv.read64

/-- State left by `unbox64 x (.v y)`. -/
def UnboxSt (st : St) (x y : Nat) : St :=
  let n := st.next
  let curBlk : PBlock :=
    { params := st.params, body := st.acc.reverse,
      term := .br .tz (.v y) (.imm 1) (loc (n + 1)) (loc n) }
  { done := ((st.done.insert st.cur curBlk)
      |>.insert n { body := [.assign st.fresh (.bin .shr .w64 (.v y) (.imm 1))],
                    term := .jump ⟨.loc (n + 2), [.v st.fresh]⟩ })
      |>.insert (n + 1) { body := [.assign (st.fresh + 1) (.load .w64 .zero (mem y (fieldOffset 0)))],
                          term := .jump ⟨.loc (n + 2), [.v (st.fresh + 1)]⟩ },
    cur := n + 2, params := [x], acc := [], next := n + 3, fresh := st.fresh + 1 + 1 }

theorem unbox_code {f : Fir.FunId} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hH : Holds f F off starts C) {st : St} {x y : Nat}
    (hC : Ext C (UnboxSt st x y)) (hl : Labels st) (_ho : Open st) :
    let n := st.next
    (∃ lb, F.blocks[off + st.cur]? = some lb ∧ lb.body.toList = st.acc.reverse ∧
      lb.term = .br .tz .w64 (.v y) (.imm 1) ⟨off + (n + 1), []⟩ ⟨off + n, []⟩) ∧
    (∃ ib, F.blocks[off + n]? = some ib ∧ ib.params = [] ∧
      ib.body.toList = [.assign st.fresh (.bin .shr .w64 (.v y) (.imm 1))] ∧
      ib.term = .jump ⟨off + (n + 2), [.v st.fresh]⟩) ∧
    (∃ bb, F.blocks[off + (n + 1)]? = some bb ∧ bb.params = [] ∧
      bb.body.toList = [.assign (st.fresh + 1) (.load .w64 .zero (mem y (fieldOffset 0)))] ∧
      bb.term = .jump ⟨off + (n + 2), [.v (st.fresh + 1)]⟩) ∧
    (∃ jb, F.blocks[off + (n + 2)]? = some jb ∧ jb.params = [x]) := by
  have hcur := hl.cur
  let n := st.next
  refine ⟨?_, ?_, ?_, ?_⟩
  · let curBlk : PBlock :=
      { params := st.params, body := st.acc.reverse,
        term := .br .tz (.v y) (.imm 1) (loc (n + 1)) (loc n) }
    obtain ⟨lb, hres, hlb⟩ := hH (hC.done (j := st.cur) (b := curBlk) (by
      simp only [UnboxSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [↓reduceIte, curBlk, n]))
    obtain ⟨-, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, curBlk] at hterm
    exact ⟨lb, hlb, hbody, hterm.symm⟩
  · obtain ⟨ib, hres, hib⟩ := hH (hC.done (j := n)
      (b := { body := [.assign st.fresh (.bin .shr .w64 (.v y) (.imm 1))],
              term := .jump ⟨.loc (n + 2), [.v st.fresh]⟩ }) (by
        simp only [UnboxSt, NatMap.get?_insert]
        rw [ite_eq_right (by omega)]
        simp only [↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨ib, hib, hp, hbody, hterm.symm⟩
  · obtain ⟨bb, hres, hbb⟩ := hH (hC.done (j := n + 1)
      (b := { body := [.assign (st.fresh + 1) (.load .w64 .zero (mem y (fieldOffset 0)))],
              term := .jump ⟨.loc (n + 2), [.v (st.fresh + 1)]⟩ }) (by
        simp only [UnboxSt, NatMap.get?_insert, ↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨bb, hbb, hp, hbody, hterm.symm⟩
  · have hopen : Open (UnboxSt st x y) := by
      simp only [Open, UnboxSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      cases hq : st.done.get? (n + 2) with
      | none => rfl
      | some bj => have := hl.done hq; omega
    obtain ⟨jb0, hjb0, hjp0, -⟩ := hC.cur hopen
    obtain ⟨jb, hres, hjb⟩ := hH hjb0
    obtain ⟨hjp, -, -⟩ := resolveBlock_ok hres
    exact ⟨jb, hjb, hjp.trans hjp0⟩

/-- **`unbox64` soundness**: recovers the exact raw 64-bit word `UInt64.ofNat n` from ANY
`ObjWordRep m n w` (either odd tagged immediate `natWord n = some w` OR even 1-scalar-word
boxed cell `BoxedAt m w n`), leaving memory unchanged and never overflowing. -/
theorem unbox64_sound {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {sup fn : Nat} {F : Lir.Func}
    {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x y : Nat}
    (hrun : (unbox64 x (.v y)).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st)
    (ho : Open st) (hsup : sup ≤ st.fresh)
    {ρl : Lir.Env} {mem : X86.Memory} {rest : List Lir.Frame} {n : Nat} {w : Word}
    (hy : ρl[y]? = some w) (hrep : ObjWordRep mem n w) :
    ∃ c ρl', Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) c
        (Lir.atState mem ctx fn (off + st'.cur) st'.acc.length ρl' rest) ∧
      ρl'[x]? = some (UInt64.ofNat n) ∧ (UInt64.ofNat n).toNat = n ∧
      ∀ z, z < sup → z ≠ x → ρl'[z]? = ρl[z]? := by
  simp only [unbox64, newLabel, close, put, freshReg, openAt, StateT.run, bind, StateT.bind, pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet,
    Except.bind, Except.pure, Except.ok.injEq, Prod.mk.injEq, true_and] at hrun
  subst hrun
  have hC' : Ext C (UnboxSt st x y) := hC
  obtain ⟨⟨lbk, hlb, hbody, hterm⟩, ⟨ib, hib, hip, hibody, hiterm⟩,
    ⟨bb, hbb, hbp, hbbody, hbterm⟩, ⟨jb, hjb, hjp⟩⟩ := unbox_code hH hC' hl ho
  have hpos : st.acc.length = lbk.body.size := by rw [← Array.length_toList, hbody]; simp
  have hyv : (Lir.Arg.v y).eval ρl = some w := hy
  rcases hrep with hnat | ⟨heven, _, hv, hnlt⟩
  · -- Odd tagged immediate: `w &&& 1 = 1`, takes `immBlk`, shifts `w >>> 1 = UInt64.ofNat n`.
    have hw := natWord_toNat hnat
    have h1 : w &&& 1 = 1 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_and, show (UInt64.toNat 1) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, hw]
      omega
    have h2 : (w >>> 1).toNat = n := untag_toNat hnat
    have hlt := natWord_lt hnat
    have hshift : w >>> 1 = UInt64.ofNat n := by
      apply UInt64.toNat_inj.mp
      rw [h2, toNat_ofNat_lt (by omega)]
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl)
      (e := ⟨off + st.next, []⟩) (vals := []) (va := w) (vb := 1) hF hlb hpos hterm
      hyv rfl (by simp [Lir.Cond.holds, h1]) rfl hib (by simp [hip, Lir.bindParams])
    let ρ₁ := ρl.insert st.fresh (UInt64.ofNat n)
    have h1m : (1 : Word) &&& 63 = 1 := rfl
    have hx1 : Lir.execList ρl mem ctx [.assign st.fresh (.bin .shr .w64 (.v y) (.imm 1))] =
        some (ρ₁, mem) := by
      simp only [Lir.execList, Lir.Stmt.exec, Lir.Rhs.eval, hyv, Lir.Arg.eval_imm,
        Option.bind_eq_bind, Option.bind_some, Lir.BinOp.eval, truncate_w64, shiftMask_w64, h1m,
        hshift, ρ₁]
    have h1s := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
      hF hib (by simpa using hibody) (by simp [Lir.Stmt.isCall]) hx1
    have h1s' : Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.next) 0 ρl rest) 0
        (Lir.atState mem ctx fn (off + st.next) 1 ρ₁ rest) := by simpa using h1s
    have hipos : 1 = ib.body.size := by rw [← Array.length_toList, hibody]; rfl
    have hval : (Lir.Arg.v st.fresh).eval ρ₁ = some (UInt64.ofNat n) := by simp [ρ₁]
    have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁)
      (ρ' := ρ₁.insert x (UInt64.ofNat n)) (e := ⟨off + (st.next + 2), [.v st.fresh]⟩)
      (vals := [UInt64.ofNat n]) hF hib hipos hiterm (by simp [Lir.evalArgs, hval]) hjb
      (by simp [hjp, Lir.bindParams])
    exact ⟨_, ρ₁.insert x (UInt64.ofNat n),
      (Lir.star_of_step hbr).trans (h1s'.trans (Lir.star_of_step hjmp)),
      by simp, toNat_ofNat_lt (by omega),
      fun z hz hzx => by simp only [ρ₁]; rw [Lir.env_insert_ne _ _ (Ne.symm hzx)]; exact Lir.env_insert_ne _ _ (by omega)⟩
  · -- Even boxed 1-scalar-word cell: `w &&& 1 = 0`, takes `boxBlk`, loads `[w + 8] = UInt64.ofNat n`.
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl)
      (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := w) (vb := 1) hF hlb hpos hterm
      hyv rfl (by simp [Lir.Cond.holds, heven]) rfl hbb (by simp [hbp, Lir.bindParams])
    let ρ₁ := ρl.insert (st.fresh + 1) (UInt64.ofNat n)
    have haddr : Lir.Addr.eval ρl ctx (Lower.mem y (fieldOffset 0)) = some (w + 8) := by
      have := eval_mem (ctx := ctx) hy 8
      simpa [fieldOffset] using this
    have hx1 : Lir.execList ρl mem ctx
        [.assign (st.fresh + 1) (.load .w64 .zero (Lower.mem y (fieldOffset 0)))] = some (ρ₁, mem) := by
      simp only [Lir.execList, Lir.Stmt.exec, load_word haddr hv, Option.bind_eq_bind,
        Option.bind_some, ρ₁]
    have h1s := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
      hF hbb (by simpa using hbbody) (by simp [Lir.Stmt.isCall]) hx1
    have h1s' : Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + (st.next + 1)) 0 ρl rest) 0
        (Lir.atState mem ctx fn (off + (st.next + 1)) 1 ρ₁ rest) := by simpa using h1s
    have hbpos : 1 = bb.body.size := by rw [← Array.length_toList, hbbody]; rfl
    have hval : (Lir.Arg.v (st.fresh + 1)).eval ρ₁ = some (UInt64.ofNat n) := by simp [ρ₁]
    have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁)
      (ρ' := ρ₁.insert x (UInt64.ofNat n)) (e := ⟨off + (st.next + 2), [.v (st.fresh + 1)]⟩)
      (vals := [UInt64.ofNat n]) hF hbb hbpos hbterm (by simp [Lir.evalArgs, hval]) hjb
      (by simp [hjp, Lir.bindParams])
    exact ⟨_, ρ₁.insert x (UInt64.ofNat n),
      (Lir.star_of_step hbr).trans (h1s'.trans (Lir.star_of_step hjmp)),
      by simp, toNat_ofNat_lt hnlt,
      fun z hz hzx => by simp only [ρ₁]; rw [Lir.env_insert_ne _ _ (Ne.symm hzx)]; exact Lir.env_insert_ne _ _ (by omega)⟩

/-- **`box64` soundness**: allocates a 1-scalar-word cell `BoxedAt m' bump n` (`immortalHeader 0 0`
at `bump`, raw `UInt64.ofNat n` at `bump + 8`, advancing `bump` by 16) when `bump + 16 ≤ limit`,
preserving all prior heap words below `bump`. Never fails with `natOverflow` for any `n < 2^64`! -/
theorem box64_alloc_spec {T : Tables} {P : List Word} {H : Own.Heap} {m : X86.Memory}
    {ctx bump limit : Word} {n : Nat}
    (hheap : HeapAt T P H ctx m bump limit) (hn : n < 2 ^ 64)
    (hroom : bump.toNat + 16 ≤ limit.toNat) :
    let e : Word := bump + 16
    let m' := allocStores m ctx bump e (UInt64.ofNat (headerLow 0 0 0)) (UInt64.ofNat immortalRc)
      [UInt64.ofNat n]
    BoxedAt m' bump n ∧
    WordAt m' (ctx - 40) e ∧
    (∀ a v, a.toNat + 8 ≤ bump.toNat → ctx.toNat + 576 ≤ a.toNat → WordAt m a v → WordAt m' a v) := by
  intro e m'
  have halign := hheap.bumpAligned
  have hctx := hheap.ctxLo
  have hstart := hheap.start
  have hlim := hheap.limitLt
  have hfit : bump.toNat + 8 + 8 * ([UInt64.ofNat n] : List Word).length < 2 ^ 63 := by simp; omega
  have heven : bump &&& 1 = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, show (UInt64.toNat 1) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp; omega
  have hhead : WordAt m' bump (immortalHeader 0 0) :=
    allocStores_header (fun k hk hk' => (hheap.free k (by omega) (by omega)).1)
      hctx hfit hstart (by decide) (by decide)
  have hpay : WordAt m' (bump + 8) (UInt64.ofNat n) := by
    have hf := allocStores_field (m := m) (ctx := ctx) (a := bump) (e := e)
      (lo := UInt64.ofNat (headerLow 0 0 0)) (hi := UInt64.ofNat immortalRc)
      (ws := [UInt64.ofNat n])
      (fun k hk hk' => (hheap.free k (by omega) (by simp at hk'; omega)).1)
      hfit (i := 0) (w := UInt64.ofNat n) rfl
    simpa using hf
  have hbump' : WordAt m' (ctx - 40) e :=
    allocStores_bump hheap.bumpWord.readable hctx hfit hstart
  refine ⟨⟨heven, hhead, hpay, hn⟩, hbump', ?_⟩
  intro a v hbelow habove hwa
  exact allocStores_keep hwa hctx hfit hbelow (Or.inl (by omega))

/-- **Raw 64-bit unsigned comparison soundness**: `Lir.Cond.holds` on raw 64-bit words agrees
with `Nat.beq`, `Nat.ble`, `Nat.blt` across ALL `[0, 2^64)` with zero tagging and zero overflow. -/
theorem rawCmp_sound {p q : Nat} {a b : Word} (ha : a.toNat = p) (hb : b.toNat = q) :
    Lir.Cond.holds .eq .w64 a b = (p == q) ∧
    Lir.Cond.holds .ule .w64 a b = decide (p ≤ q) ∧
    Lir.Cond.holds .ult .w64 a b = decide (p < q) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Lir.Cond.holds, ← ha, ← hb]
    by_cases h : a = b
    · subst h; simp
    · have hne : a.toNat ≠ b.toNat := fun he => h (UInt64.toNat_inj.mp he)
      simp [beq_false_of_ne h, beq_false_of_ne hne]
  · simp only [Lir.Cond.holds, truncate_w64, UInt64.le_iff_toNat_le, ha, hb]
  · simp only [Lir.Cond.holds, truncate_w64, UInt64.lt_iff_toNat_lt, ha, hb]

end IxCC.Rt.Proof.LowerRep
