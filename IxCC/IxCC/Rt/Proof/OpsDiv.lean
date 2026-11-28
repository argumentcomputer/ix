import IxCC.Rt.Proof.Ops

/-!
# `natDiv` and `natMod`

`Rt.lower`'s `divMod` untags both operands, divides by a nonzero divisor
(`1` in place of a zero one), retags, and selects `n / 0 = 0`
(`n % 0 = n`) for a zero divisor; an immediate divisor folds (a zero one
gives the result directly). One lemma per operation covers every operand
shape.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

theorem untag_ne_zero {q : Nat} {wb : Word} (hb : natWord q = some wb) (hq : q ≠ 0) : wb >>> 1 ≠ 0 := by
  intro h
  have := untag_toNat hb
  rw [h] at this
  exact hq (by simpa using this.symm)

theorem word_one_ne_zero : (1 : Word) ≠ 0 := by decide

theorem mod_word0 {p : Nat} {wa : Word} (h : natWord p = some wa) :
    natWord (if (0 : Nat) = 0 then p else p % 0) = some wa := by
  simpa using h

theorem div_word0 {p : Nat} : natWord (if (0 : Nat) = 0 then 0 else p / 0) = some 1 := by
  simp; exact natWord_of_lt (by decide)

theorem div1_word {p : Nat} {wa : Word} (hwa : natWord p = some wa) :
    natWord (if (1 : Nat) = 0 then 0 else p / 1) = some wa := by
  simpa using hwa

theorem mod1_word {p : Nat} :
    natWord (if (1 : Nat) = 0 then p else p % 1) = some 1 := by
  simp [Nat.mod_one]; exact natWord_of_lt (by decide)

theorem div2_word {p : Nat} {wa : Word} (hwa : natWord p = some wa) :
    natWord (if (2 : Nat) = 0 then 0 else p / 2) = some ((wa >>> 1) ||| 1) := by
  simpa using natDiv2_word hwa

theorem mod2_word {p : Nat} {wa : Word} (hwa : natWord p = some wa) :
    natWord (if (2 : Nat) = 0 then p else p % 2) = some (wa &&& 3) := by
  simpa using natMod2_word hwa

theorem div4_word {p : Nat} {wa : Word} (hwa : natWord p = some wa) :
    natWord (if (4 : Nat) = 0 then 0 else p / 4) = some ((wa >>> 2) ||| 1) := by
  simpa using natDiv4_word hwa

theorem mod4_word {p : Nat} {wa : Word} (hwa : natWord p = some wa) :
    natWord (if (4 : Nat) = 0 then p else p % 4) = some (wa &&& 7) := by
  simpa using natMod4_word hwa

theorem div_word {p q : Nat} {wa wb : Word} (hwa : natWord p = some wa) (hwb : natWord q = some wb) (hq : q ≠ 0) :
    natWord (if q = 0 then 0 else p / q) = some ((wa >>> 1) / (wb >>> 1) + (wa >>> 1) / (wb >>> 1) + 1) := by
  simp only [hq, ↓reduceIte]; exact natDiv_word hwa hwb hq

theorem mod_word {p q : Nat} {wa wb : Word} (hwa : natWord p = some wa) (hwb : natWord q = some wb) (hq : q ≠ 0) :
    natWord (if q = 0 then p else p % q) = some ((wa >>> 1) % (wb >>> 1) + (wa >>> 1) % (wb >>> 1) + 1) := by
  simp only [hq, ↓reduceIte]; exact natMod_word hwa hwb hq

/-! ## Multi-block variable-divisor `divModVar` (32-bit fast path + cold zero/64-bit paths) -/

/-- Value produced by `divModVar` on untagged operands for `.udiv` vs `.urem`. -/
def divModVal (o : Lir.BinOp) (u y : Word) : Word :=
  match o with | .udiv => u / y | _ => u % y

/-- The state `divModVar` leaves: 5 blocks inserted (`cur`, `nz`, `fast32`, `slow64`, `zBlk`),
with `join` open at `st.next + 4` carrying parameter `[x]`. -/
def DivModVarSt (st : St) (x : Nat) (b : Lir.Arg) (nzBody : List Lir.Stmt) (nzTerm : PTerm)
    (fastBody slowBody : List Lir.Stmt) (fastArg slowArg zArg : Lir.Arg) (f' : Nat) : St :=
  let n := st.next
  let curBlk : PBlock :=
    { params := st.params, body := st.acc.reverse,
      term := .br .eq b (.imm 1) (loc (n + 3)) (loc n) }
  { done := ((((st.done.insert st.cur curBlk)
      |>.insert n { body := nzBody, term := nzTerm })
      |>.insert (n + 1) { body := fastBody, term := .jump ⟨.loc (n + 4), [fastArg]⟩ })
      |>.insert (n + 2) { body := slowBody, term := .jump ⟨.loc (n + 4), [slowArg]⟩, cold := true })
      |>.insert (n + 3) { term := .jump ⟨.loc (n + 4), [zArg]⟩, cold := true },
    cur := n + 4, params := [x], acc := [], next := n + 5, fresh := f' }

theorem divModVar_code {f : Fir.FunId} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hH : Holds f F off starts C) {st : St} {x : Nat} {b : Lir.Arg} {nzBody : List Lir.Stmt} {nzTerm : PTerm}
    {fastBody slowBody : List Lir.Stmt} {fastArg slowArg zArg : Lir.Arg} {f' : Nat}
    (hC : Ext C (DivModVarSt st x b nzBody nzTerm fastBody slowBody fastArg slowArg zArg f'))
    (hl : Labels st) (ho : Open st) :
    let n := st.next
    (∃ lb, F.blocks[off + st.cur]? = some lb ∧ lb.body.toList = st.acc.reverse ∧
      lb.term = .br .eq .w64 b (.imm 1) ⟨off + (n + 3), []⟩ ⟨off + n, []⟩) ∧
    (∃ nzb, F.blocks[off + n]? = some nzb ∧ nzb.params = [] ∧ nzb.body.toList = nzBody ∧
      resolveTerm f off starts nzTerm = .ok nzb.term) ∧
    (∃ fb, F.blocks[off + (n + 1)]? = some fb ∧ fb.params = [] ∧ fb.body.toList = fastBody ∧
      fb.term = .jump ⟨off + (n + 4), [fastArg]⟩) ∧
    (∃ sb, F.blocks[off + (n + 2)]? = some sb ∧ sb.params = [] ∧ sb.body.toList = slowBody ∧
      sb.term = .jump ⟨off + (n + 4), [slowArg]⟩) ∧
    (∃ zb, F.blocks[off + (n + 3)]? = some zb ∧ zb.params = [] ∧ zb.body.toList = [] ∧
      zb.term = .jump ⟨off + (n + 4), [zArg]⟩) ∧
    (∃ jb, F.blocks[off + (n + 4)]? = some jb ∧ jb.params = [x]) := by
  have hcur := hl.cur
  let n := st.next
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · let curBlk : PBlock :=
      { params := st.params, body := st.acc.reverse,
        term := .br .eq b (.imm 1) (loc (n + 3)) (loc n) }
    obtain ⟨lb, hres, hlb⟩ := hH (hC.done (j := st.cur) (b := curBlk) (by
      simp only [DivModVarSt, NatMap.get?_insert]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp only [↓reduceIte, curBlk, n]))
    obtain ⟨-, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      curBlk] at hterm
    exact ⟨lb, hlb, hbody, hterm.symm⟩
  · obtain ⟨nzb, hres, hnz⟩ := hH (hC.done (j := n) (b := { body := nzBody, term := nzTerm }) (by
      simp only [DivModVarSt, NatMap.get?_insert, n]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp only [↓reduceIte]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    exact ⟨nzb, hnz, hp, hbody, hterm⟩
  · obtain ⟨fb, hres, hfb⟩ := hH (hC.done (j := n + 1)
        (b := { body := fastBody, term := .jump ⟨.loc (n + 4), [fastArg]⟩ }) (by
      simp only [DivModVarSt, NatMap.get?_insert, n]
      rw [if_neg (by omega), if_neg (by omega)]
      simp only [↓reduceIte]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hterm
    exact ⟨fb, hfb, hp, hbody, hterm.symm⟩
  · obtain ⟨sb, hres, hsb⟩ := hH (hC.done (j := n + 2)
        (b := { body := slowBody, term := .jump ⟨.loc (n + 4), [slowArg]⟩, cold := true }) (by
      simp only [DivModVarSt, NatMap.get?_insert, n]
      rw [if_neg (by omega)]
      simp only [↓reduceIte]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hterm
    exact ⟨sb, hsb, hp, hbody, hterm.symm⟩
  · obtain ⟨zb, hres, hzb⟩ := hH (hC.done (j := n + 3)
        (b := { term := .jump ⟨.loc (n + 4), [zArg]⟩, cold := true }) (by
      simp only [DivModVarSt, NatMap.get?_insert, n, ↓reduceIte]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hterm
    exact ⟨zb, hzb, hp, hbody, hterm.symm⟩
  · have hopen : Open (DivModVarSt st x b nzBody nzTerm fastBody slowBody fastArg slowArg zArg f') := by
      simp only [Open, DivModVarSt, NatMap.get?_insert]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      cases hq : st.done.get? (n + 4) with
      | none => rfl
      | some bj => have := hl.done hq; omega
    obtain ⟨jb0, hjb0, hjp0, -⟩ := hC.cur hopen
    obtain ⟨jb, hres, hjb⟩ := hH hjb0
    obtain ⟨hjp, -, -⟩ := resolveBlock_ok hres
    exact ⟨jb, hjb, hjp.trans hjp0⟩

/-- Shared simulation core for `divModVar` (handles both `natDiv`/`natMod`, both `la` shapes,
and both immortal and plain-RC routes). -/
theorem divModVar_star {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {sup fn : Nat} {F : Lir.Func}
    {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x yb : Nat} {o : Lir.BinOp} {zero : Lir.Arg → Lir.Arg}
    {la : Lir.Arg} (ho_op : o = .udiv ∨ o = .urem)
    (hrun : (divModVar x o zero la (.v yb)).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (ho : Open st) (hsup : sup ≤ st.fresh)
    {ρl : Lir.Env} {mem : X86.Memory} {rest : List Lir.Frame} {p q : Nat} {wa wb wz : Word}
    (ha : la.eval ρl = some wa) (hb : ρl[yb]? = some wb) (hwa : natWord p = some wa) (hwb : natWord q = some wb)
    (hra : ∀ y, la = .v y → y < sup) (hyb : yb < sup)
    (hz : (zero la).eval ρl = some wz) :
    ∃ c ρl', Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) c
        (Lir.atState mem ctx fn (off + st'.cur) st'.acc.length ρl' rest) ∧
      ρl'[x]? = some (if q = 0 then wz else
        let v := divModVal o (wa >>> 1) (wb >>> 1)
        v + v + 1) ∧
      ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]? := by
  have hop_eval : ∀ (w : X86.Width) (u y : Word), w.truncate u = u → w.truncate y = y → y ≠ 0 →
      Lir.BinOp.eval o w u y = some (divModVal o u y) := by
    intro w u y hu hy hne
    rcases ho_op with rfl | rfl <;> simp [Lir.BinOp.eval, divModVal, hu, hy, hne]
  have htrunc64 : ∀ v : Word, X86.Width.w64.truncate v = v := by
    intro v
    apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro i hi
    change (v &&& (0xffffffffffffffff : Word)).toBitVec.getLsbD i = v.toBitVec.getLsbD i
    rw [UInt64.toBitVec_and, BitVec.getLsbD_and]
    have hm : (0xffffffffffffffff : Word).toBitVec = BitVec.ofNat 64 (2 ^ 64 - 1) := rfl
    rw [hm, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]; simp [hi]
  have hdisp1 : Lir.dispWord 1 = 1 := rfl
  have hscale1 : X86.Scale.one.word = 1 := rfl
  -- Factor the common multi-block execution once `st'` has the `DivModVarSt` shape.
  have run_blocks : ∀ (nzBody : List Lir.Stmt) (hiReg : Nat) (uArg yArg : Lir.Arg)
      (q32 r32 q64 r64 f' : Nat),
      st' = DivModVarSt st x (.v yb) nzBody
        (.br .ne (.v hiReg) (.imm 0) (loc (st.next + 2)) (loc (st.next + 1)))
        [.assign q32 (.bin o .w32 uArg yArg), .assign r32 (retag (.v q32))]
        [.assign q64 (.bin o .w64 uArg yArg), .assign r64 (retag (.v q64))]
        (.v r32) (.v r64) (zero la) f' →
      (∀ s ∈ nzBody, s.isCall = false) →
      sup ≤ q32 → sup ≤ r32 → sup ≤ q64 → sup ≤ r64 → q32 ≠ r32 → q64 ≠ r64 →
      (∃ ρl₁, Lir.execList ρl mem ctx nzBody = some (ρl₁, mem) ∧
        uArg.eval ρl₁ = some (wa >>> 1) ∧ yArg.eval ρl₁ = some (wb >>> 1) ∧
        ρl₁[hiReg]? = some (((wa >>> 1) ||| (wb >>> 1)) >>> 32) ∧
        ∀ y, y < sup → ρl₁[y]? = ρl[y]?) →
      ∃ c ρl', Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) c
          (Lir.atState mem ctx fn (off + st'.cur) st'.acc.length ρl' rest) ∧
        ρl'[x]? = some (if q = 0 then wz else
          let v := divModVal o (wa >>> 1) (wb >>> 1)
          v + v + 1) ∧
        ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]? := by
    intro nzBody hiReg uArg yArg q32 r32 q64 r64 f' hst hnc hq32 hr32 hq64 hr64 hne32 hne64 hnzExec
    subst hst
    obtain ⟨⟨lb, hlb, hbody, hterm⟩, ⟨nzb, hnzb, hnzp, hnzbody, hnzterm⟩,
      ⟨fb, hfb, hfp, hfbody, hfterm⟩, ⟨sb, hsb, hsp, hsbody, hsterm⟩,
      ⟨zb, hzb, hzp, hzbody, hzterm⟩, ⟨jb, hjb, hjp⟩⟩ := divModVar_code hH hC hl ho
    simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hnzterm
    have hpos : st.acc.length = lb.body.size := by rw [← Array.length_toList, hbody]; simp
    dsimp only [DivModVarSt, List.length_nil]
    by_cases hq : q = 0
    · subst hq
      have hw1 : wb = 1 := (natWord_eq_one hwb).2 rfl
      have h1 := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl)
        (e := ⟨off + (st.next + 3), []⟩) (vals := []) (va := wb) (vb := 1) hF hlb hpos hterm hb rfl
        (by simp [Lir.Cond.holds, hw1]) rfl hzb (by simp [hzp, Lir.bindParams])
      have hzpos : 0 = zb.body.size := by rw [← Array.length_toList, hzbody]; rfl
      have h2 := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl.insert x wz)
        (e := ⟨off + (st.next + 4), [zero la]⟩) (vals := [wz]) hF hzb hzpos hzterm
        (by simp [Lir.evalArgs, hz]) hjb (by simp [hjp, Lir.bindParams])
      refine ⟨_, ρl.insert x wz, (Lir.star_of_step h1).trans (Lir.star_of_step h2), by simp, ?_⟩
      intro y _ hyx; exact Lir.env_insert_ne _ _ (Ne.symm hyx)
    · have hw1 : wb ≠ 1 := fun h => hq ((natWord_eq_one hwb).1 h)
      have hne0 : wb >>> 1 ≠ 0 := untag_ne_zero hwb hq
      have h1 := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl)
        (e := ⟨off + st.next, []⟩) (vals := []) (va := wb) (vb := 1) hF hlb hpos hterm hb rfl
        (by simp [Lir.Cond.holds, hw1]) rfl hnzb (by simp [hnzp, Lir.bindParams])
      obtain ⟨ρl₁, hxnz, hu₁, hy₁, hhi₁, hfr₁⟩ := hnzExec
      have h2 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := []) hF hnzb
        (by simpa using hnzbody) hnc hxnz
      have hnzpos : nzBody.length = nzb.body.size := by rw [← Array.length_toList, hnzbody]
      simp only [List.length_nil, Nat.zero_add] at h2
      let v := divModVal o (wa >>> 1) (wb >>> 1)
      by_cases hhi0 : ((wa >>> 1) ||| (wb >>> 1)) >>> (32 : Word) = 0
      · -- 32-bit fast path
        obtain ⟨hu32, hy32⟩ := untag_or_shr32_eq_zero hhi0
        have h3 := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl₁) (ρ' := ρl₁)
          (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := ((wa >>> 1) ||| (wb >>> 1)) >>> 32) (vb := 0)
          hF hnzb hnzpos hnzterm.symm hhi₁ rfl (by simp [Lir.Cond.holds, hhi0]) rfl hfb
          (by simp [hfp, Lir.bindParams])
        have hxf : Lir.execList ρl₁ mem ctx [.assign q32 (.bin o .w32 uArg yArg), .assign r32 (retag (.v q32))] =
            some ((ρl₁.insert q32 v).insert r32 (v + v + 1), mem) := by
          simp only [lir_eval, hu₁, hy₁, hop_eval .w32 _ _ hu32 hy32 hne0, retag, UInt64.mul_one, ↓reduceIte, v]
        have h4 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := []) hF hfb
          (by simpa using hfbody) (by simp [Lir.Stmt.isCall]) hxf
        have hfpos : 2 = fb.body.size := by rw [← Array.length_toList, hfbody]; rfl
        simp only [List.length_nil, Nat.zero_add, List.length_cons] at h4
        have h5 := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest)
          (ρ := (ρl₁.insert q32 v).insert r32 (v + v + 1))
          (ρ' := ((ρl₁.insert q32 v).insert r32 (v + v + 1)).insert x (v + v + 1))
          (e := ⟨off + (st.next + 4), [.v r32]⟩) (vals := [v + v + 1]) hF hfb hfpos hfterm
          (by simp [Lir.evalArgs, Lir.Arg.eval]) hjb (by simp [hjp, Lir.bindParams])
        refine ⟨_, _, (Lir.star_of_step h1).trans (h2.trans ((Lir.star_of_step h3).trans (h4.trans (Lir.star_of_step h5)))),
          by simp [hq, v], ?_⟩
        intro y hy hyx
        rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega),
          Lir.env_insert_ne _ _ (by omega), hfr₁ y hy]
      · -- 64-bit slow path
        have h3 := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl₁) (ρ' := ρl₁)
          (e := ⟨off + (st.next + 2), []⟩) (vals := []) (va := ((wa >>> 1) ||| (wb >>> 1)) >>> 32) (vb := 0)
          hF hnzb hnzpos hnzterm.symm hhi₁ rfl (by simp [Lir.Cond.holds, hhi0]) rfl hsb
          (by simp [hsp, Lir.bindParams])
        have hxs : Lir.execList ρl₁ mem ctx [.assign q64 (.bin o .w64 uArg yArg), .assign r64 (retag (.v q64))] =
            some ((ρl₁.insert q64 v).insert r64 (v + v + 1), mem) := by
          simp only [lir_eval, hu₁, hy₁, hop_eval .w64 _ _ (htrunc64 _) (htrunc64 _) hne0, retag, UInt64.mul_one,
            ↓reduceIte, v]
        have h4 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := []) hF hsb
          (by simpa using hsbody) (by simp [Lir.Stmt.isCall]) hxs
        have hspos : 2 = sb.body.size := by rw [← Array.length_toList, hsbody]; rfl
        simp only [List.length_nil, Nat.zero_add, List.length_cons] at h4
        have h5 := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest)
          (ρ := (ρl₁.insert q64 v).insert r64 (v + v + 1))
          (ρ' := ((ρl₁.insert q64 v).insert r64 (v + v + 1)).insert x (v + v + 1))
          (e := ⟨off + (st.next + 4), [.v r64]⟩) (vals := [v + v + 1]) hF hsb hspos hsterm
          (by simp [Lir.evalArgs, Lir.Arg.eval]) hjb (by simp [hjp, Lir.bindParams])
        refine ⟨_, _, (Lir.star_of_step h1).trans (h2.trans ((Lir.star_of_step h3).trans (h4.trans (Lir.star_of_step h5)))),
          by simp [hq, v], ?_⟩
        intro y hy hyx
        rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega),
          Lir.env_insert_ne _ _ (by omega), hfr₁ y hy]
  -- Instantiate for `la = .v ya` and `la = .imm wai`.
  cases la with
  | v ya =>
    have hya : ya < sup := hra ya rfl
    have ha' : ρl[ya]? = some wa := ha
    simp only [divModVar, newLabel, close, openAt, untag, bin, temp, freshReg, assign, emit, put, retag,
      StateT.run, bind, StateT.bind, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, MonadState.modifyGet, Except.bind, Except.pure, Except.ok.injEq, Prod.mk.injEq,
      true_and, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hrun
    let f0 := st.fresh
    refine run_blocks
      [.assign f0 (.bin .shr .w64 (.v ya) (.imm 1)),
       .assign (f0 + 1) (.bin .shr .w64 (.v yb) (.imm 1)),
       .assign (f0 + 2) (.bin .or .w64 (.v f0) (.v (f0 + 1))),
       .assign (f0 + 3) (.bin .shr .w64 (.v (f0 + 2)) (.imm 32))]
      (f0 + 3) (.v f0) (.v (f0 + 1)) (f0 + 4) (f0 + 5) (f0 + 6) (f0 + 7) (f0 + 8)
      (by subst hrun; rfl) (by simp [Lir.Stmt.isCall]) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) ?_
    let ρl₁ := (((ρl.insert f0 (wa >>> 1)).insert (f0 + 1) (wb >>> 1)).insert
      (f0 + 2) ((wa >>> 1) ||| (wb >>> 1))).insert (f0 + 3) (((wa >>> 1) ||| (wb >>> 1)) >>> 32)
    refine ⟨ρl₁, by simp (disch := omega) only [lir_eval, ha', hb, show (32 &&& 63 : Word) = 32 from rfl,
        ↓reduceIte, if_neg, f0, ρl₁],
      by simp only [Lir.Arg.eval_v, ρl₁]
         rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega),
           Lir.env_insert_ne _ _ (by omega), Lir.env_insert_self],
      by simp only [Lir.Arg.eval_v, ρl₁]
         rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega), Lir.env_insert_self],
      by simp only [ρl₁, Lir.env_insert_self],
      fun y hy => by
        simp only [ρl₁]
        rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega),
          Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega)]⟩
  | imm wai =>
    simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha
    subst ha
    simp only [divModVar, newLabel, close, openAt, untag, bin, temp, freshReg, assign, emit, put, retag,
      StateT.run, bind, StateT.bind, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, MonadState.modifyGet, Except.bind, Except.pure, Except.ok.injEq, Prod.mk.injEq,
      true_and, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hrun
    let f0 := st.fresh
    refine run_blocks
      [.assign f0 (.bin .shr .w64 (.v yb) (.imm 1)),
       .assign (f0 + 1) (.bin .or .w64 (.imm (wai >>> 1)) (.v f0)),
       .assign (f0 + 2) (.bin .shr .w64 (.v (f0 + 1)) (.imm 32))]
      (f0 + 2) (.imm (wai >>> 1)) (.v f0) (f0 + 3) (f0 + 4) (f0 + 5) (f0 + 6) (f0 + 7)
      (by subst hrun; rfl) (by simp [Lir.Stmt.isCall]) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) ?_
    let ρl₁ := ((ρl.insert f0 (wb >>> 1)).insert
      (f0 + 1) ((wai >>> 1) ||| (wb >>> 1))).insert (f0 + 2) (((wai >>> 1) ||| (wb >>> 1)) >>> 32)
    refine ⟨ρl₁, by simp (disch := omega) only [lir_eval, hb, show (32 &&& 63 : Word) = 32 from rfl,
        ↓reduceIte, if_neg, f0, ρl₁],
      rfl,
      by simp only [Lir.Arg.eval_v, ρl₁]
         rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega), Lir.env_insert_self],
      by simp only [ρl₁, Lir.env_insert_self],
      fun y hy => by
        simp only [ρl₁]
        rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega),
          Lir.env_insert_ne _ _ (by omega)]⟩

theorem prim_natDiv {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natDiv [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st) (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natDiv as)) := by
  have hsem := sem_nat2 .natDiv (by decide)
  cases lb with
  | imm wbi =>
    by_cases hw : wbi = 1
    · subst hw
      lower_run at hrun
      simp only [beq_self_eq_true, ↓reduceIte] at hrun
      lower_run at hrun
      subst hrun
      refine prim2_sim (ss := [.assign x (.arg (.imm 1))]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
        hlive (by decide) (fun p q => if q = 0 then 0 else p / q) hsem ?_
      intro ρl mem p q wa wb ha hb hwa hwb hra _
      simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
      subst hb
      have hq0 : q = 0 := (natWord_eq_one hwb).1 rfl
      subst hq0
      exact ⟨_, _, by (simp only [lir_eval]; try rfl), div_word0, by simp, fun y hy hyx => by regs_ne⟩
    · have hw' : (wbi == 1) = false := by simpa using hw
      by_cases hw3 : wbi = 3
      · subst hw3
        lower_run at hrun
        simp only [hw', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
        lower_run at hrun
        subst hrun
        refine prim2_sim (ss := [.assign x (.arg la)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
          hlive (by decide) (fun p q => if q = 0 then 0 else p / q) hsem ?_
        intro ρl mem p q wa wb ha hb hwa hwb hra _
        simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
        subst hb
        have hq1 : q = 1 := (natWord_eq_three hwb).1 rfl
        subst hq1
        exact ⟨_, _, by (simp only [lir_eval, ha]; try rfl), div1_word hwa, by simp, fun y hy hyx => by regs_ne⟩
      · have hw3' : (wbi == 3) = false := by simpa using hw3
        by_cases hw5 : wbi = 5
        · subst hw5
          cases la with
          | v ya =>
            lower_run at hrun
            simp only [hw', hw3', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
            lower_run at hrun
            subst hrun
            refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 (.v ya) (.imm 1)),
                .assign x (.bin .or .w64 (.v st.fresh) (.imm 1))])
              hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
              (fun p q => if q = 0 then 0 else p / q) hsem ?_
            intro ρl mem p q wa wb ha hb hwa hwb hra _
            simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
            subst hb
            have hq2 : q = 2 := (natWord_eq_five hwb).1 rfl
            subst hq2
            have ha' : ρl[ya]? = some wa := ha
            have hya := hra ya rfl
            exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ha', ↓reduceIte, if_neg]; try rfl),
              div2_word hwa, by simp, fun y hy hyx => by regs_ne⟩
          | imm wai =>
            lower_run at hrun
            simp only [hw', hw3', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
            lower_run at hrun
            subst hrun
            refine prim2_sim (ss := [.assign x (.bin .or .w64 (.imm (wai >>> 1)) (.imm 1))])
              hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
              (fun p q => if q = 0 then 0 else p / q) hsem ?_
            intro ρl mem p q wa wb ha hb hwa hwb _ _
            simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha hb
            subst ha hb
            have hq2 : q = 2 := (natWord_eq_five hwb).1 rfl
            subst hq2
            exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ↓reduceIte, if_neg]; try rfl),
              div2_word hwa, by simp, fun y hy hyx => by regs_ne⟩
        · have hw5' : (wbi == 5) = false := by simpa using hw5
          by_cases hw9 : wbi = 9
          · subst hw9
            lower_run at hrun
            simp only [hw', hw3', hw5', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
            lower_run at hrun
            subst hrun
            refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 la (.imm 2)),
                .assign x (.bin .or .w64 (.v st.fresh) (.imm 1))])
              hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
              (fun p q => if q = 0 then 0 else p / q) hsem ?_
            intro ρl mem p q wa wb ha hb hwa hwb hra _
            simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
            subst hb
            have hq4 : q = 4 := (natWord_eq_nine hwb).1 rfl
            subst hq4
            exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ha, show (2 &&& 63 : Word) = 2 from rfl, ↓reduceIte]; try rfl),
              div4_word hwa, by simp, fun y hy hyx => by regs_ne⟩
          · have hw9' : (wbi == 9) = false := by simpa using hw9
            cases la with
            | v ya =>
              lower_run at hrun
              simp only [hw', hw3', hw5', hw9', Bool.false_eq_true, ↓reduceIte] at hrun
              lower_run at hrun
              subst hrun
              refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 (.v ya) (.imm 1)),
                  .assign (st.fresh + 1) (.bin .udiv .w64 (.v st.fresh) (.imm (wbi >>> 1))),
                  .assign x (.addr { base := some (.v (st.fresh + 1)), index := some (st.fresh + 1, .one), disp := 1 })])
                hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
                (fun p q => if q = 0 then 0 else p / q) hsem ?_
              intro ρl mem p q wa wb ha hb hwa hwb hra _
              simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
              subst hb
              have hq : q ≠ 0 := fun h => hw ((natWord_eq_one hwb).2 h)
              have ha' : ρl[ya]? = some wa := ha
              have hya := hra ya rfl
              exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ha', untag_ne_zero hwb hq, ↓reduceIte, if_neg,
                UInt64.mul_one]; try rfl), div_word hwa hwb hq, by simp, fun y hy hyx => by regs_ne⟩
            | imm wai =>
              lower_run at hrun
              simp only [hw', hw3', hw5', hw9', Bool.false_eq_true, ↓reduceIte] at hrun
              lower_run at hrun
              subst hrun
              refine prim2_sim (ss := [.assign st.fresh (.bin .udiv .w64 (.imm (wai >>> 1)) (.imm (wbi >>> 1))),
                  .assign x (.addr { base := some (.v st.fresh), index := some (st.fresh, .one), disp := 1 })])
                hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
                (fun p q => if q = 0 then 0 else p / q) hsem ?_
              intro ρl mem p q wa wb ha hb hwa hwb _ _
              simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha hb
              subst ha hb
              have hq : q ≠ 0 := fun h => hw ((natWord_eq_one hwb).2 h)
              exact ⟨_, _, by (simp (disch := omega) only [lir_eval, untag_ne_zero hwb hq, ↓reduceIte, if_neg,
                UInt64.mul_one]; try rfl), div_word hwa hwb hq, by simp, fun y hy hyx => by regs_ne⟩
  | v yb =>
    have hrun' : (divModVar x .udiv (fun _ => .imm 1) la (.v yb)).run st = .ok ((), st') := hrun
    intro P H ρ ρl mem rest v H' hheap hρ hr
    obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, hra, hrb⟩⟩ :=
      bin2_of hρ hops hlive (sem_not_bool .natDiv (by decide)) hr
    rw [hsem] at hs; cases hs
    obtain ⟨c, ρl', hstar, hx', hfr⟩ := divModVar_star hF hH (.inl rfl) hrun' hC hl ho hsup ha hb hwa hwb hra
      (hrb yb rfl) (wz := 1) rfl
    refine .inl ⟨c, ρl', mem, P, hstar, hheap, List.prefix_refl _, ?_⟩
    have hwn : natWord (if q = 0 then 0 else p / q) = some (if q = 0 then (1 : Word) else
        (wa >>> 1) / (wb >>> 1) + (wa >>> 1) / (wb >>> 1) + 1) := by
      by_cases hq : q = 0
      · subst hq; exact div_word0
      · simp only [hq, ↓reduceIte]; exact natDiv_word hwa hwb hq
    refine ⟨?_, ?_⟩
    · intro y v' hy
      rw [Src.NatMap.get?_insert] at hy
      split at hy
      · omega
      · exact hρ.dom hy
    · intro y v' hy hD
      rw [Src.NatMap.get?_insert] at hy
      split at hy
      · rename_i hyx; subst hyx; cases hy; exact ⟨_, hx', hwn⟩
      · rename_i hyx
        obtain ⟨w', hw', hv'⟩ := hρ.val hy hD
        exact ⟨w', by rw [hfr y (hρ.dom hy) hyx]; exact hw', hv'⟩

theorem prim_natMod {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natMod [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st) (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natMod as)) := by
  have hsem := sem_nat2 .natMod (by decide)
  cases lb with
  | imm wbi =>
    by_cases hw : wbi = 1
    · subst hw
      lower_run at hrun
      simp only [beq_self_eq_true, ↓reduceIte] at hrun
      lower_run at hrun
      subst hrun
      refine prim2_sim (ss := [.assign x (.arg la)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
        hlive (by decide) (fun p q => if q = 0 then p else p % q) hsem ?_
      intro ρl mem p q wa wb ha hb hwa hwb hra _
      simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
      subst hb
      have hq0 : q = 0 := (natWord_eq_one hwb).1 rfl
      subst hq0
      exact ⟨_, _, by (simp only [lir_eval, ha]; try rfl), mod_word0 hwa, by simp, fun y hy hyx => by regs_ne⟩
    · have hw' : (wbi == 1) = false := by simpa using hw
      by_cases hw3 : wbi = 3
      · subst hw3
        lower_run at hrun
        simp only [hw', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
        lower_run at hrun
        subst hrun
        refine prim2_sim (ss := [.assign x (.arg (.imm 1))]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
          hlive (by decide) (fun p q => if q = 0 then p else p % q) hsem ?_
        intro ρl mem p q wa wb ha hb hwa hwb hra _
        simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
        subst hb
        have hq1 : q = 1 := (natWord_eq_three hwb).1 rfl
        subst hq1
        exact ⟨_, _, by (simp only [lir_eval]; try rfl), mod1_word, by simp, fun y hy hyx => by regs_ne⟩
      · have hw3' : (wbi == 3) = false := by simpa using hw3
        by_cases hw5 : wbi = 5
        · subst hw5
          lower_run at hrun
          simp only [hw', hw3', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
          lower_run at hrun
          subst hrun
          refine prim2_sim (ss := [.assign x (.bin .and .w64 la (.imm 3))]) hF hH hC ho (by simp [Lir.Stmt.isCall])
            hsup hx hops hlive (by decide) (fun p q => if q = 0 then p else p % q) hsem ?_
          intro ρl mem p q wa wb ha hb hwa hwb hra _
          simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
          subst hb
          have hq2 : q = 2 := (natWord_eq_five hwb).1 rfl
          subst hq2
          exact ⟨_, _, by (simp only [lir_eval, ha]; try rfl), mod2_word hwa, by simp, fun y hy hyx => by regs_ne⟩
        · have hw5' : (wbi == 5) = false := by simpa using hw5
          by_cases hw9 : wbi = 9
          · subst hw9
            lower_run at hrun
            simp only [hw', hw3', hw5', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
            lower_run at hrun
            subst hrun
            refine prim2_sim (ss := [.assign x (.bin .and .w64 la (.imm 7))]) hF hH hC ho (by simp [Lir.Stmt.isCall])
              hsup hx hops hlive (by decide) (fun p q => if q = 0 then p else p % q) hsem ?_
            intro ρl mem p q wa wb ha hb hwa hwb hra _
            simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
            subst hb
            have hq4 : q = 4 := (natWord_eq_nine hwb).1 rfl
            subst hq4
            exact ⟨_, _, by (simp only [lir_eval, ha]; try rfl), mod4_word hwa, by simp, fun y hy hyx => by regs_ne⟩
          · have hw9' : (wbi == 9) = false := by simpa using hw9
            cases la with
            | v ya =>
              lower_run at hrun
              simp only [hw', hw3', hw5', hw9', Bool.false_eq_true, ↓reduceIte] at hrun
              lower_run at hrun
              subst hrun
              refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 (.v ya) (.imm 1)),
                  .assign (st.fresh + 1) (.bin .urem .w64 (.v st.fresh) (.imm (wbi >>> 1))),
                  .assign x (.addr { base := some (.v (st.fresh + 1)), index := some (st.fresh + 1, .one), disp := 1 })])
                hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
                (fun p q => if q = 0 then p else p % q) hsem ?_
              intro ρl mem p q wa wb ha hb hwa hwb hra _
              simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
              subst hb
              have hq : q ≠ 0 := fun h => hw ((natWord_eq_one hwb).2 h)
              have ha' : ρl[ya]? = some wa := ha
              have hya := hra ya rfl
              exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ha', untag_ne_zero hwb hq, ↓reduceIte, if_neg,
                UInt64.mul_one]; try rfl), mod_word hwa hwb hq, by simp, fun y hy hyx => by regs_ne⟩
            | imm wai =>
              lower_run at hrun
              simp only [hw', hw3', hw5', hw9', Bool.false_eq_true, ↓reduceIte] at hrun
              lower_run at hrun
              subst hrun
              refine prim2_sim (ss := [.assign st.fresh (.bin .urem .w64 (.imm (wai >>> 1)) (.imm (wbi >>> 1))),
                  .assign x (.addr { base := some (.v st.fresh), index := some (st.fresh, .one), disp := 1 })])
                hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
                (fun p q => if q = 0 then p else p % q) hsem ?_
              intro ρl mem p q wa wb ha hb hwa hwb _ _
              simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha hb
              subst ha hb
              have hq : q ≠ 0 := fun h => hw ((natWord_eq_one hwb).2 h)
              exact ⟨_, _, by (simp (disch := omega) only [lir_eval, untag_ne_zero hwb hq, ↓reduceIte, if_neg,
                UInt64.mul_one]; try rfl), mod_word hwa hwb hq, by simp, fun y hy hyx => by regs_ne⟩
  | v yb =>
    have hrun' : (divModVar x .urem id la (.v yb)).run st = .ok ((), st') := hrun
    intro P H ρ ρl mem rest v H' hheap hρ hr
    obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, hra, hrb⟩⟩ :=
      bin2_of hρ hops hlive (sem_not_bool .natMod (by decide)) hr
    rw [hsem] at hs; cases hs
    obtain ⟨c, ρl', hstar, hx', hfr⟩ := divModVar_star hF hH (.inr rfl) hrun' hC hl ho hsup ha hb hwa hwb hra
      (hrb yb rfl) (wz := wa) ha
    refine .inl ⟨c, ρl', mem, P, hstar, hheap, List.prefix_refl _, ?_⟩
    have hwn : natWord (if q = 0 then p else p % q) = some (if q = 0 then wa else
        (wa >>> 1) % (wb >>> 1) + (wa >>> 1) % (wb >>> 1) + 1) := by
      by_cases hq : q = 0
      · subst hq; exact mod_word0 hwa
      · simp only [hq, ↓reduceIte]; exact natMod_word hwa hwb hq
    refine ⟨?_, ?_⟩
    · intro y v' hy
      rw [Src.NatMap.get?_insert] at hy
      split at hy
      · omega
      · exact hρ.dom hy
    · intro y v' hy hD
      rw [Src.NatMap.get?_insert] at hy
      split at hy
      · rename_i hyx; subst hyx; cases hy; exact ⟨_, hx', hwn⟩
      · rename_i hyx
        obtain ⟨w', hw', hv'⟩ := hρ.val hy hD
        exact ⟨w', by rw [hfr y (hρ.dom hy) hyx]; exact hw', hv'⟩

end IxCC.Rt.Proof
