import IxCC.Rt.BigNat.Dispatch
import IxCC.Rt.BigNat.ProofProcs
import IxCC.Rt.Proof.OpsWord

/-! # Phase 4 Arbitrary-Precision `Nat` `PrimCoreBig` Simulation Proofs (`IxCC.Rt.BigNat.Proof`)

Proves `PrimCore`-style simulation theorems for every `Nat` primitive emitted by
`IxCC.Rt.BigNat.Dispatch`, parameterized by the linked `BigNat` slow-path contract
`SlowPathEnv` — with **ZERO `.natOverflow` failure disjunct** (only `FailsNoOvf`,
i.e. genuine `.heap` or `.stack` exhaustion):

* `natAddBig_core` (`.natAdd`)
* `natSubBig_core` (`.natSub`)
* `natPredBig_core` (`.natPred`) and `natSuccPeelBig_core` (`Nat.succ` projection peel)
* `natMulBig_core` (`.natMul`)
* `natDivBig_core` (`.natDiv`)
* `natModBig_core` (`.natMod`)
* `natBeqBig_core`, `natBleBig_core`, `natBltBig_core`, and `natCmpBig_core`
* `natLandBig_core`, `natLorBig_core`, `natXorBig_core`, and `natBitBig_core`
* `natShlBig_core`, `natShrBig_core`, and `natShiftBig_core`
* `natPowBig_core` (`.natPow`, via `Rt.Procs.natPowBig`)
* `natGcdBig_core` (`.natGcd`, via `Rt.Procs.natGcdBig`)
* `primitiveBig_core` (unified theorem over `Dispatch.primitiveBig` for all 16 `Nat` ops)

Ready to drop into `Rt/Lower.lean` and `Rt/Proof/Ops*.lean` in Wave 3b in one clean pass.
Strictly standard axioms `[propext, Classical.choice, Quot.sound]`; zero `sorry`. -/

set_option autoImplicit false

namespace IxCC.Rt.BigNat

open IxCC.Lir (Word)
open IxCC.Rt
open IxCC.Rt.Lower
open IxCC.Rt.Proof
open IxCC.Src (NatMap)

/-! ## Core Arbitrary-Precision Simulation Predicates (ZERO `.natOverflow`) -/

/-- **Arbitrary-precision `Nat`-valued primitive core (Phase 4, ZERO `natOverflow`)**:
From registers where `las` evaluate to `NatVal` words representing arbitrary `Nat`s `ns`
(small `< 2^63` OR canonical big `LimbArray` cells `≥ 2^63`) on which `op.sem ns = some (.nat n)`,
LIR runs from `(L, p)` to `(L', p')` of function `fn`, either:
* reaching `(L', p')` with `MemStep mem mem'`, `NatVal mem' n w`, `ρl'[x]? = some w`, and
  every other register `< sup` unchanged, OR
* failing with `FailsNoOvf` (STRICTLY NO `.natOverflow`). -/
def PrimCoreBig (lp : Lir.Program) (ctx : Word) (MemStep : X86.Memory → X86.Memory → Prop)
    (sup fn L p L' p' x : Nat) (op : Lam.Prim) (las : List Lir.Arg) : Prop :=
  ∀ (ρl : Lir.Env) (mem : X86.Memory) (rest : List Lir.Frame)
    (ns : List Nat) (ws : List Word) (n : Nat),
    Lir.evalArgs ρl las = some ws →
    ListRel (NatVal mem) ns ws →
    (∀ la ∈ las, ArgReads sup la) →
    op.sem ns = some (.nat n) →
    (∃ c ρl' mem' w,
        Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn L p ρl rest) c
          (Lir.atState mem' ctx fn L' p' ρl' rest) ∧
        MemStep mem mem' ∧ NatVal mem' n w ∧ ρl'[x]? = some w ∧
        ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) ∨
    FailsNoOvf lp (Lir.atState mem ctx fn L p ρl rest)

/-- **Arbitrary-precision `Bool`-valued `Nat` comparison core (Phase 4, ZERO `natOverflow`)**:
Same as `PrimCoreBig`, for `Bool`-returning `Nat` comparisons (`natBeq`, `natBle`, `natBlt`). -/
def PrimCoreBigBool (lp : Lir.Program) (ctx : Word) (MemStep : X86.Memory → X86.Memory → Prop)
    (tWord fWord : Word) (sup fn L p L' p' x : Nat) (op : Lam.Prim) (las : List Lir.Arg) : Prop :=
  ∀ (ρl : Lir.Env) (mem : X86.Memory) (rest : List Lir.Frame)
    (ns : List Nat) (ws : List Word) (b : Bool),
    Lir.evalArgs ρl las = some ws →
    ListRel (NatVal mem) ns ws →
    (∀ la ∈ las, ArgReads sup la) →
    op.sem ns = some (.bool b) →
    (∃ c ρl' mem' w,
        Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn L p ρl rest) c
          (Lir.atState mem' ctx fn L' p' ρl' rest) ∧
        MemStep mem mem' ∧ BoolVal tWord fWord b w ∧ ρl'[x]? = some w ∧
        ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) ∨
    FailsNoOvf lp (Lir.atState mem ctx fn L p ρl rest)

/-- Bundled linked slow-path contracts for all 16 arbitrary-precision `Nat` primitives. -/
structure SlowPathEnv (lp : Lir.Program) (ctx : Word)
    (MemStep : X86.Memory → X86.Memory → Prop) (procs : BigNatProcs)
    (tWord fWord : Word) : Prop where
  mem_refl : ∀ m, MemStep m m
  add : SlowNatBinSpec lp ctx MemStep procs.add (· + ·)
  sub : SlowNatBinSpec lp ctx MemStep procs.sub (· - ·)
  pred : SlowNatUnSpec lp ctx MemStep procs.pred (· - 1)
  mul : SlowNatBinSpec lp ctx MemStep procs.mul (· * ·)
  div : SlowNatBinSpec lp ctx MemStep procs.div (fun a b => if b = 0 then 0 else a / b)
  mod : SlowNatBinSpec lp ctx MemStep procs.mod (fun a b => if b = 0 then a else a % b)
  pow : SlowNatBinSpec lp ctx MemStep procs.pow (· ^ ·)
  gcd : SlowNatBinSpec lp ctx MemStep procs.gcd Nat.gcd
  beq : SlowNatCmpSpec lp ctx MemStep tWord fWord procs.beq (fun a b => a == b)
  ble : SlowNatCmpSpec lp ctx MemStep tWord fWord procs.ble (fun a b => decide (a ≤ b))
  blt : SlowNatCmpSpec lp ctx MemStep tWord fWord procs.blt (fun a b => decide (a < b))
  land : SlowNatBinSpec lp ctx MemStep procs.land (· &&& ·)
  lor : SlowNatBinSpec lp ctx MemStep procs.lor (· ||| ·)
  xor : SlowNatBinSpec lp ctx MemStep procs.xor (· ^^^ ·)
  shl : SlowNatBinSpec lp ctx MemStep procs.shl (fun a b => a * 2 ^ b)
  shr : SlowNatBinSpec lp ctx MemStep procs.shr (fun a b => a / 2 ^ b)

/-! ## Argument Evaluation & Lowering Helpers -/

private theorem natval_one {mem : X86.Memory} {ρl : Lir.Env} {la : Lir.Arg}
    {ns : List Nat} {ws : List Word}
    (hws : Lir.evalArgs ρl [la] = some ws) (hrel : ListRel (NatVal mem) ns ws) :
    ∃ p wa, ns = [p] ∧ la.eval ρl = some wa ∧ NatVal mem p wa := by
  simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, Option.bind_eq_bind] at hws
  cases ha : la.eval ρl with
  | none => simp [ha] at hws
  | some wa =>
    simp [ha] at hws
    subst hws
    cases hrel with
    | @cons p _ _ _ hpa hnil => cases hnil; exact ⟨p, wa, rfl, rfl, hpa⟩

private theorem natval_two {mem : X86.Memory} {ρl : Lir.Env} {la lb : Lir.Arg}
    {ns : List Nat} {ws : List Word}
    (hws : Lir.evalArgs ρl [la, lb] = some ws) (hrel : ListRel (NatVal mem) ns ws) :
    ∃ p q wa wb, ns = [p, q] ∧ la.eval ρl = some wa ∧ lb.eval ρl = some wb ∧
      NatVal mem p wa ∧ NatVal mem q wb := by
  simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, Option.bind_eq_bind] at hws
  cases ha : la.eval ρl with
  | none => simp [ha] at hws
  | some wa =>
    cases hb : lb.eval ρl with
    | none => simp [ha, hb] at hws
    | some wb =>
      simp [ha, hb] at hws
      subst hws
      cases hrel with
      | @cons p _ _ _ hpa hrel1 =>
        cases hrel1 with
        | @cons q _ _ _ hqb hnil => cases hnil; exact ⟨p, q, wa, wb, rfl, rfl, rfl, hpa, hqb⟩

private theorem arg_eval_of_frame {ρ ρ' : Lir.Env} {sup : Nat} {a : Lir.Arg} {w : Word}
    (hr : ArgReads sup a) (hfr : ∀ z, z < sup → ρ'[z]? = ρ[z]?) (he : a.eval ρ = some w) :
    a.eval ρ' = some w := by
  cases a with
  | imm _ => exact he
  | v y => simp only [Lir.Arg.eval] at he ⊢; rw [hfr y (hr y rfl)]; exact he

private theorem evalArgs_two_of {ρl : Lir.Env} {la lb : Lir.Arg} {wa wb : Word}
    (ha : la.eval ρl = some wa) (hb : lb.eval ρl = some wb) :
    Lir.evalArgs ρl [la, lb] = some [wa, wb] := by
  simp [Lir.evalArgs, ha, hb]

private theorem evalArgs_one_of {ρl : Lir.Env} {la : Lir.Arg} {wa : Word}
    (ha : la.eval ρl = some wa) :
    Lir.evalArgs ρl [la] = some [wa] := by
  simp [Lir.evalArgs, ha]

private theorem env_frame_temp {ρl : Lir.Env} {sup t : Nat} (ht : sup ≤ t) (v : Word) :
    ∀ y, y < sup → (ρl.insert t v)[y]? = ρl[y]? := by
  intro y hy
  exact Lir.env_insert_ne _ _ (by omega)

/-- Evaluate a `Dispatch` lowering run into its final `Lower.St`. -/
macro "big_run" " at " h:ident : tactic =>
  `(tactic| simp only [primitiveBig, natAddBig, natSubBig, natPredBig, natSuccPeelBig,
      natMulBig, natDivBig, natModBig, natDivModBig, natCmpBig, natBeqBig, natBleBig, natBltBig,
      natLandBig, natLorBig, natXorBig, natShrBig, natShlBig, natPowBig, natGcdBig, binFastSlow,
      bin, temp, freshReg, assign, emit, newLabel, close, openAt, put, retag, loc,
      StateT.run, bind, StateT.bind, pure, StateT.pure, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet, Except.bind, Except.pure,
      Except.ok.injEq, Prod.mk.injEq, true_and, throw, throwThe, MonadExceptOf.throw,
      StateT.lift] at $h:ident)

/-! ## Schema 1: Binary Fast-Only + Cold Slow Call (`BinFastSlowSt`) -/

/-- Chunk state produced by `binFastSlow` (possibly after allocating `k` fresh regs). -/
def BinFastSlowSt (st : St) (k : Nat) (slowFn : Lir.FunId) (x : Nat) (a b : Lir.Arg)
    (fastBody : List Lir.Stmt) (fastRes : Lir.Arg) : St :=
  let tagReg := st.fresh + k
  let rSlow := tagReg + 1
  let n := st.next
  let curBlk : PBlock :=
    { params := st.params
    , body := (.assign tagReg (.bin .and .w64 a b) :: st.acc).reverse
    , term := .br .tz (.v tagReg) (.imm 1) (loc (n + 1)) (loc n) }
  { done := ((st.done.insert st.cur curBlk)
      |>.insert n { body := fastBody, term := .jump ⟨.loc (n + 2), [fastRes]⟩ })
      |>.insert (n + 1) {
          body := [.call [rSlow] slowFn [a, b]]
          term := .jump ⟨.loc (n + 2), [.v rSlow]⟩
          cold := true }
  , cur := n + 2
  , params := [x]
  , acc := []
  , next := n + 3
  , fresh := rSlow + 1 }

private theorem binFastSlow_code {f : Fir.FunId} {F : Lir.Func} {off : Nat} {starts : NatMap Nat}
    {C : List PBlock} (hH : Holds f F off starts C) {st : St} {k : Nat} {slowFn : Lir.FunId}
    {x : Nat} {a b : Lir.Arg} {fastBody : List Lir.Stmt} {fastRes : Lir.Arg}
    (hC : Ext C (BinFastSlowSt st k slowFn x a b fastBody fastRes)) (hl : Labels st) :
    let tagReg := st.fresh + k
    let rSlow := tagReg + 1
    let n := st.next
    (∃ lb, F.blocks[off + st.cur]? = some lb ∧
      lb.body.toList = st.acc.reverse ++ [.assign tagReg (.bin .and .w64 a b)] ∧
      lb.term = .br .tz .w64 (.v tagReg) (.imm 1) ⟨off + (n + 1), []⟩ ⟨off + n, []⟩) ∧
    (∃ fb, F.blocks[off + n]? = some fb ∧ fb.params = [] ∧ fb.body.toList = fastBody ∧
      fb.term = .jump ⟨off + (n + 2), [fastRes]⟩) ∧
    (∃ sb, F.blocks[off + (n + 1)]? = some sb ∧ sb.params = [] ∧
      sb.body.toList = [.call [rSlow] slowFn [a, b]] ∧
      sb.term = .jump ⟨off + (n + 2), [.v rSlow]⟩) ∧
    (∃ jb, F.blocks[off + (n + 2)]? = some jb ∧ jb.params = [x]) := by
  have hcur := hl.cur
  let tagReg := st.fresh + k
  let rSlow := tagReg + 1
  let n := st.next
  refine ⟨?_, ?_, ?_, ?_⟩
  · let curBlk : PBlock :=
      { params := st.params
      , body := (.assign tagReg (.bin .and .w64 a b) :: st.acc).reverse
      , term := .br .tz (.v tagReg) (.imm 1) (loc (n + 1)) (loc n) }
    obtain ⟨lb, hres, hlb⟩ := hH (hC.done (j := st.cur) (b := curBlk) (by
      simp only [BinFastSlowSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [↓reduceIte, curBlk, tagReg, n]))
    obtain ⟨-, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, curBlk] at hterm
    exact ⟨lb, hlb, by rw [hbody]; simp [curBlk, tagReg], hterm.symm⟩
  · obtain ⟨fb, hres, hfb⟩ := hH (hC.done (j := n)
      (b := { body := fastBody, term := .jump ⟨.loc (n + 2), [fastRes]⟩ }) (by
        simp only [BinFastSlowSt, NatMap.get?_insert]
        rw [ite_eq_right (by omega)]
        simp only [↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨fb, hfb, hp, hbody, hterm.symm⟩
  · obtain ⟨sb, hres, hsb⟩ := hH (hC.done (j := n + 1)
      (b := { body := [.call [rSlow] slowFn [a, b]], term := .jump ⟨.loc (n + 2), [.v rSlow]⟩, cold := true }) (by
        simp only [BinFastSlowSt, NatMap.get?_insert, ↓reduceIte, n, rSlow, tagReg]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨sb, hsb, hp, hbody, hterm.symm⟩
  · have hopen : Open (BinFastSlowSt st k slowFn x a b fastBody fastRes) := by
      simp only [Open, BinFastSlowSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      cases hq : st.done.get? (n + 2) with
      | none => rfl
      | some bj => have := hl.done hq; omega
    obtain ⟨jb0, hjb0, hjp0, -⟩ := hC.cur hopen
    obtain ⟨jb, hres, hjb⟩ := hH hjb0
    obtain ⟨hjp, -, -⟩ := resolveBlock_ok hres
    exact ⟨jb, hjb, hjp.trans hjp0⟩

/-- Generic simulation for `BinFastSlowSt`: runs the 1-instruction tag test;
on both-small runs `fastBody` (no memory change), otherwise calls `slowFn [a, b]`. -/
private theorem binFastSlow_run {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st : St} {k : Nat} {slowFn : Lir.FunId} {x : Nat} {la lb : Lir.Arg}
    {fastBody : List Lir.Stmt} {fastRes : Lir.Arg}
    (hC : Ext C (BinFastSlowSt st k slowFn x la lb fastBody fastRes))
    (hl : Labels st) (hsup : sup ≤ st.fresh)
    (hnc : ∀ s ∈ fastBody, s.isCall = false)
    {ρl : Lir.Env} {mem : X86.Memory} {rest : List Lir.Frame}
    {p q : Nat} {wa wb : Word} {Post : X86.Memory → Word → Prop}
    (ha : la.eval ρl = some wa) (hb : lb.eval ρl = some wb)
    (hra : ArgReads sup la) (hrb : ArgReads sup lb)
    (hpa : NatVal mem p wa) (hqb : NatVal mem q wb)
    (hfast : Rt.natWord p = some wa → Rt.natWord q = some wb →
      ∃ ρf w,
        Lir.execList (ρl.insert (st.fresh + k) (wa &&& wb)) mem ctx fastBody = some (ρf, mem) ∧
        fastRes.eval ρf = some w ∧ Post mem w ∧
        ∀ y, y < sup → ρf[y]? = ρl[y]?)
    (hslow : ProcSpec lp slowFn ctx [wa, wb] mem (fun mem' w => MemStep mem mem' ∧ Post mem' w)) :
    (∃ c ρl' mem' w,
        Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) c
          (Lir.atState mem' ctx fn (off + (st.next + 2)) 0 ρl' rest) ∧
        MemStep mem mem' ∧ Post mem' w ∧ ρl'[x]? = some w ∧
        ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) ∨
    FailsNoOvf lp (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) := by
  obtain ⟨⟨lbk, hlb, hlbody, hlterm⟩, ⟨fb, hfb, hfp, hfbody, hfterm⟩,
    ⟨sb, hsb, hsp, hsbody, hsterm⟩, ⟨jb, hjb, hjp⟩⟩ := binFastSlow_code hH hC hl
  let tagReg := st.fresh + k
  let rSlow := tagReg + 1
  let ρ₁ := ρl.insert tagReg (wa &&& wb)
  have hx1 : Lir.execList ρl mem ctx [.assign tagReg (.bin .and .w64 la lb)] = some (ρ₁, mem) := by
    simp [lir_eval, ha, hb, ρ₁]
  have hstar1 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := st.acc.reverse) (post := [])
    hF hlb (by simpa using hlbody) (by simp [Lir.Stmt.isCall]) hx1
  simp only [List.length_reverse] at hstar1
  have hlpos : st.acc.length + 1 = lbk.body.size := by
    rw [← Array.length_toList, hlbody]; simp
  cases htz : Lir.Cond.holds .tz .w64 (wa &&& wb) 1 with
  | false =>
    obtain ⟨hwa, hwb⟩ := (NatVal.and_tz_one_false_iff hpa hqb).mp htz
    obtain ⟨ρf, w, hxf, hres, hpost, hframe⟩ := hfast hwa hwb
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁) (ρ' := ρ₁)
      (e := ⟨off + st.next, []⟩) (vals := []) (va := wa &&& wb) (vb := 1)
      hF hlb hlpos hlterm (by simp [Lir.Arg.eval, ρ₁, tagReg]) rfl
      (by simp [htz]) rfl hfb (by simp [hfp, Lir.bindParams])
    have hstarf := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
      hF hfb (by simpa using hfbody) hnc hxf
    simp only [List.length_nil, Nat.zero_add] at hstarf
    have hfpos : fastBody.length = fb.body.size := by rw [← Array.length_toList, hfbody]
    have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest)
      (pos := fastBody.length) (ρ := ρf) (e := ⟨off + (st.next + 2), [fastRes]⟩)
      (vals := [w]) (ρ' := ρf.insert x w) hF hfb hfpos hfterm
      (evalArgs_one_of hres) hjb (by simp [hjp, Lir.bindParams])
    left
    refine ⟨_, ρf.insert x w, mem, w,
      hstar1.trans ((Lir.star_of_step hbr).trans (hstarf.trans (Lir.star_of_step hjmp))),
      hrefl mem, hpost, by simp, ?_⟩
    intro y hy hyx
    rw [Lir.env_insert_ne _ _ (Ne.symm hyx)]
    exact hframe y hy
  | true =>
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁) (ρ' := ρ₁)
      (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := wa &&& wb) (vb := 1)
      hF hlb hlpos hlterm (by simp [Lir.Arg.eval, ρ₁, tagReg]) rfl
      (by simp [htz]) rfl hsb (by simp [hsp, Lir.bindParams])
    have hpre := hstar1.trans (Lir.star_of_step hbr)
    have hsb_pos : 0 < sb.body.size := by rw [← Array.length_toList, hsbody]; simp
    have hsb_call : sb.body[0] = .call [rSlow] slowFn [la, lb] := by
      rw [← Array.getElem_toList (h := hsb_pos)]
      simp [hsbody, rSlow, tagReg]
    have ha1 : la.eval ρ₁ = some wa := by rw [arg_eval_temp hra (t := tagReg) (by omega)]; exact ha
    have hb1 : lb.eval ρ₁ = some wb := by rw [arg_eval_temp hrb (t := tagReg) (by omega)]; exact hb
    rcases call_procSpec (rest := rest) hF hsb hsb_pos hsb_call (evalArgs_two_of ha1 hb1) hslow with
      ⟨c, mem', w, hcall, hmstep, hpost⟩ | hfail
    · have hspos : 1 = sb.body.size := by rw [← Array.length_toList, hsbody]; simp
      have hjmp := Lir.jump_at (p := lp) (mem := mem') (ctx := ctx) (rest := rest) (pos := 1)
        (ρ := ρ₁.insert rSlow w) (e := ⟨off + (st.next + 2), [.v rSlow]⟩)
        (vals := [w]) (ρ' := (ρ₁.insert rSlow w).insert x w) hF hsb hspos hsterm
        (by simp [Lir.evalArgs, Lir.Arg.eval]) hjb (by simp [hjp, Lir.bindParams])
      left
      refine ⟨_, (ρ₁.insert rSlow w).insert x w, mem', w,
        hpre.trans (hcall.trans (Lir.star_of_step hjmp)),
        hmstep, hpost, by simp, ?_⟩
      intro y hy hyx
      rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega),
        Lir.env_insert_ne _ _ (by omega)]
    · right
      exact hfail.prepend hpre

/-! ## Schema 2: Unary Fast-Only + Cold Slow Call (`UnFastSlowSt`) -/

/-- Chunk state produced by `natPredBig` / `natSuccPeelBig`. -/
def UnFastSlowSt (st : St) (slowFn : Lir.FunId) (x : Nat) (a : Lir.Arg)
    (fastBody : List Lir.Stmt) (fastRes : Lir.Arg) (rSlow f' : Nat) : St :=
  let n := st.next
  let curBlk : PBlock :=
    { params := st.params
    , body := st.acc.reverse
    , term := .br .tz a (.imm 1) (loc (n + 1)) (loc n) }
  { done := ((st.done.insert st.cur curBlk)
      |>.insert n { body := fastBody, term := .jump ⟨.loc (n + 2), [fastRes]⟩ })
      |>.insert (n + 1) {
          body := [.call [rSlow] slowFn [a]]
          term := .jump ⟨.loc (n + 2), [.v rSlow]⟩
          cold := true }
  , cur := n + 2
  , params := [x]
  , acc := []
  , next := n + 3
  , fresh := f' }

private theorem unFastSlow_code {f : Fir.FunId} {F : Lir.Func} {off : Nat} {starts : NatMap Nat}
    {C : List PBlock} (hH : Holds f F off starts C) {st : St} {slowFn : Lir.FunId}
    {x : Nat} {a : Lir.Arg} {fastBody : List Lir.Stmt} {fastRes : Lir.Arg} {rSlow f' : Nat}
    (hC : Ext C (UnFastSlowSt st slowFn x a fastBody fastRes rSlow f')) (hl : Labels st) :
    let n := st.next
    (∃ lb, F.blocks[off + st.cur]? = some lb ∧ lb.body.toList = st.acc.reverse ∧
      lb.term = .br .tz .w64 a (.imm 1) ⟨off + (n + 1), []⟩ ⟨off + n, []⟩) ∧
    (∃ fb, F.blocks[off + n]? = some fb ∧ fb.params = [] ∧ fb.body.toList = fastBody ∧
      fb.term = .jump ⟨off + (n + 2), [fastRes]⟩) ∧
    (∃ sb, F.blocks[off + (n + 1)]? = some sb ∧ sb.params = [] ∧
      sb.body.toList = [.call [rSlow] slowFn [a]] ∧
      sb.term = .jump ⟨off + (n + 2), [.v rSlow]⟩) ∧
    (∃ jb, F.blocks[off + (n + 2)]? = some jb ∧ jb.params = [x]) := by
  have hcur := hl.cur
  let n := st.next
  refine ⟨?_, ?_, ?_, ?_⟩
  · let curBlk : PBlock :=
      { params := st.params, body := st.acc.reverse, term := .br .tz a (.imm 1) (loc (n + 1)) (loc n) }
    obtain ⟨lb, hres, hlb⟩ := hH (hC.done (j := st.cur) (b := curBlk) (by
      simp only [UnFastSlowSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [↓reduceIte, curBlk, n]))
    obtain ⟨-, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, curBlk] at hterm
    exact ⟨lb, hlb, hbody, hterm.symm⟩
  · obtain ⟨fb, hres, hfb⟩ := hH (hC.done (j := n)
      (b := { body := fastBody, term := .jump ⟨.loc (n + 2), [fastRes]⟩ }) (by
        simp only [UnFastSlowSt, NatMap.get?_insert]
        rw [ite_eq_right (by omega)]
        simp only [↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨fb, hfb, hp, hbody, hterm.symm⟩
  · obtain ⟨sb, hres, hsb⟩ := hH (hC.done (j := n + 1)
      (b := { body := [.call [rSlow] slowFn [a]], term := .jump ⟨.loc (n + 2), [.v rSlow]⟩, cold := true }) (by
        simp only [UnFastSlowSt, NatMap.get?_insert, ↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨sb, hsb, hp, hbody, hterm.symm⟩
  · have hopen : Open (UnFastSlowSt st slowFn x a fastBody fastRes rSlow f') := by
      simp only [Open, UnFastSlowSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      cases hq : st.done.get? (n + 2) with
      | none => rfl
      | some bj => have := hl.done hq; omega
    obtain ⟨jb0, hjb0, hjp0, -⟩ := hC.cur hopen
    obtain ⟨jb, hres, hjb⟩ := hH hjb0
    obtain ⟨hjp, -, -⟩ := resolveBlock_ok hres
    exact ⟨jb, hjb, hjp.trans hjp0⟩

/-! ## Schema 3: Binary Fast-With-Overflow + Two Cold Slow Calls (`BinOvfSlowSt`) -/

/-- Chunk state produced by `natAddBig`, `natMulBig`, and `natShlBig`. -/
def BinOvfSlowSt (st : St) (slowFn : Lir.FunId) (x : Nat) (a b : Lir.Arg)
    (fastBody : List Lir.Stmt) (fastTerm : PTerm) (fastOkBody : List Lir.Stmt)
    (fastRes : Lir.Arg) (rSlow1 rSlow2 f' : Nat) : St :=
  let tagReg := st.fresh
  let n := st.next
  let curBlk : PBlock :=
    { params := st.params
    , body := (.assign tagReg (.bin .and .w64 a b) :: st.acc).reverse
    , term := .br .tz (.v tagReg) (.imm 1) (loc (n + 2)) (loc n) }
  { done := ((((st.done.insert st.cur curBlk)
      |>.insert n { body := fastBody, term := fastTerm })
      |>.insert (n + 1) { body := fastOkBody, term := .jump ⟨.loc (n + 4), [fastRes]⟩ })
      |>.insert (n + 2) {
          body := [.call [rSlow1] slowFn [a, b]]
          term := .jump ⟨.loc (n + 4), [.v rSlow1]⟩
          cold := true })
      |>.insert (n + 3) {
          body := [.call [rSlow2] slowFn [a, b]]
          term := .jump ⟨.loc (n + 4), [.v rSlow2]⟩
          cold := true }
  , cur := n + 4
  , params := [x]
  , acc := []
  , next := n + 5
  , fresh := f' }

private theorem binOvfSlow_code {f : Fir.FunId} {F : Lir.Func} {off : Nat} {starts : NatMap Nat}
    {C : List PBlock} (hH : Holds f F off starts C) {st : St} {slowFn : Lir.FunId}
    {x : Nat} {a b : Lir.Arg} {fastBody : List Lir.Stmt} {fastTerm : PTerm}
    {fastOkBody : List Lir.Stmt} {fastRes : Lir.Arg} {rSlow1 rSlow2 f' : Nat}
    (hC : Ext C (BinOvfSlowSt st slowFn x a b fastBody fastTerm fastOkBody fastRes rSlow1 rSlow2 f'))
    (hl : Labels st) :
    let tagReg := st.fresh
    let n := st.next
    (∃ lb, F.blocks[off + st.cur]? = some lb ∧
      lb.body.toList = st.acc.reverse ++ [.assign tagReg (.bin .and .w64 a b)] ∧
      lb.term = .br .tz .w64 (.v tagReg) (.imm 1) ⟨off + (n + 2), []⟩ ⟨off + n, []⟩) ∧
    (∃ fb, F.blocks[off + n]? = some fb ∧ fb.params = [] ∧ fb.body.toList = fastBody ∧
      resolveTerm f off starts fastTerm = .ok fb.term) ∧
    (∃ okb, F.blocks[off + (n + 1)]? = some okb ∧ okb.params = [] ∧ okb.body.toList = fastOkBody ∧
      okb.term = .jump ⟨off + (n + 4), [fastRes]⟩) ∧
    (∃ st1, F.blocks[off + (n + 2)]? = some st1 ∧ st1.params = [] ∧
      st1.body.toList = [.call [rSlow1] slowFn [a, b]] ∧
      st1.term = .jump ⟨off + (n + 4), [.v rSlow1]⟩) ∧
    (∃ st2, F.blocks[off + (n + 3)]? = some st2 ∧ st2.params = [] ∧
      st2.body.toList = [.call [rSlow2] slowFn [a, b]] ∧
      st2.term = .jump ⟨off + (n + 4), [.v rSlow2]⟩) ∧
    (∃ jb, F.blocks[off + (n + 4)]? = some jb ∧ jb.params = [x]) := by
  have hcur := hl.cur
  let tagReg := st.fresh
  let n := st.next
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · let curBlk : PBlock :=
      { params := st.params
      , body := (.assign tagReg (.bin .and .w64 a b) :: st.acc).reverse
      , term := .br .tz (.v tagReg) (.imm 1) (loc (n + 2)) (loc n) }
    obtain ⟨lb, hres, hlb⟩ := hH (hC.done (j := st.cur) (b := curBlk) (by
      simp only [BinOvfSlowSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [↓reduceIte, curBlk, tagReg, n]))
    obtain ⟨-, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, curBlk] at hterm
    exact ⟨lb, hlb, by rw [hbody]; simp [curBlk, tagReg], hterm.symm⟩
  · obtain ⟨fb, hres, hfb⟩ := hH (hC.done (j := n) (b := { body := fastBody, term := fastTerm }) (by
      simp only [BinOvfSlowSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    exact ⟨fb, hfb, hp, hbody, hterm⟩
  · obtain ⟨okb, hres, hokb⟩ := hH (hC.done (j := n + 1)
      (b := { body := fastOkBody, term := .jump ⟨.loc (n + 4), [fastRes]⟩ }) (by
        simp only [BinOvfSlowSt, NatMap.get?_insert]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨okb, hokb, hp, hbody, hterm.symm⟩
  · obtain ⟨st1, hres, hst1⟩ := hH (hC.done (j := n + 2)
      (b := { body := [.call [rSlow1] slowFn [a, b]], term := .jump ⟨.loc (n + 4), [.v rSlow1]⟩, cold := true }) (by
        simp only [BinOvfSlowSt, NatMap.get?_insert]
        rw [ite_eq_right (by omega)]
        simp only [↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨st1, hst1, hp, hbody, hterm.symm⟩
  · obtain ⟨st2, hres, hst2⟩ := hH (hC.done (j := n + 3)
      (b := { body := [.call [rSlow2] slowFn [a, b]], term := .jump ⟨.loc (n + 4), [.v rSlow2]⟩, cold := true }) (by
        simp only [BinOvfSlowSt, NatMap.get?_insert, ↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨st2, hst2, hp, hbody, hterm.symm⟩
  · have hopen : Open (BinOvfSlowSt st slowFn x a b fastBody fastTerm fastOkBody fastRes rSlow1 rSlow2 f') := by
      simp only [Open, BinOvfSlowSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      cases hq : st.done.get? (n + 4) with
      | none => rfl
      | some bj => have := hl.done hq; omega
    obtain ⟨jb0, hjb0, hjp0, -⟩ := hC.cur hopen
    obtain ⟨jb, hres, hjb⟩ := hH hjb0
    obtain ⟨hjp, -, -⟩ := resolveBlock_ok hres
    exact ⟨jb, hjb, hjp.trans hjp0⟩

/-- Helper executing a single-call slow block `[call [rSlow] slowFn [la, lb]]; jump join [rSlow]`. -/
private theorem exec_slow_block {lp : Lir.Program} {ctx : Word} {mem : X86.Memory}
    {MemStep : X86.Memory → X86.Memory → Prop}
    {sup fn Lslow Ljoin x rSlow : Nat} {F : Lir.Func} {sb jb : Lir.Block}
    {slowFn : Lir.FunId} {la lb : Lir.Arg} {ρ0 ρs : Lir.Env} {rest : List Lir.Frame}
    {wa wb : Word} {Post : X86.Memory → Word → Prop}
    (hF : lp.funcs[fn]? = some F) (hsb : F.blocks[Lslow]? = some sb)
    (hsbody : sb.body.toList = [.call [rSlow] slowFn [la, lb]])
    (hsterm : sb.term = .jump ⟨Ljoin, [.v rSlow]⟩)
    (hjb : F.blocks[Ljoin]? = some jb) (hjp : jb.params = [x])
    (hrs : sup ≤ rSlow) (hframe : ∀ y, y < sup → ρs[y]? = ρ0[y]?)
    (ha : la.eval ρs = some wa) (hb : lb.eval ρs = some wb)
    (hslow : ProcSpec lp slowFn ctx [wa, wb] mem (fun mem' w => MemStep mem mem' ∧ Post mem' w)) :
    (∃ c ρl' mem' w,
        Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn Lslow 0 ρs rest) c
          (Lir.atState mem' ctx fn Ljoin 0 ρl' rest) ∧
        MemStep mem mem' ∧ Post mem' w ∧ ρl'[x]? = some w ∧
        ∀ y, y < sup → y ≠ x → ρl'[y]? = ρ0[y]?) ∨
    FailsNoOvf lp (Lir.atState mem ctx fn Lslow 0 ρs rest) := by
  have hsb_pos : 0 < sb.body.size := by rw [← Array.length_toList, hsbody]; simp
  have hsb_call : sb.body[0] = .call [rSlow] slowFn [la, lb] := by
    rw [← Array.getElem_toList (h := hsb_pos)]; simp [hsbody]
  rcases call_procSpec (rest := rest) hF hsb hsb_pos hsb_call (evalArgs_two_of ha hb) hslow with
    ⟨c, mem', w, hcall, hmstep, hpost⟩ | hfail
  · have hspos : 1 = sb.body.size := by rw [← Array.length_toList, hsbody]; simp
    have hjmp := Lir.jump_at (p := lp) (mem := mem') (ctx := ctx) (rest := rest) (pos := 1)
      (ρ := ρs.insert rSlow w) (e := ⟨Ljoin, [.v rSlow]⟩)
      (vals := [w]) (ρ' := (ρs.insert rSlow w).insert x w) hF hsb hspos hsterm
      (by simp [Lir.evalArgs, Lir.Arg.eval]) hjb (by simp [hjp, Lir.bindParams])
    left
    refine ⟨_, (ρs.insert rSlow w).insert x w, mem', w,
      hcall.trans (Lir.star_of_step hjmp), hmstep, hpost, by simp, ?_⟩
    intro y hy hyx
    rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega)]
    exact hframe y hy
  · exact Or.inr hfail

/-! ## Schema 4: Binary Division/Modulo with Zero Guard + Slow Call (`BinDivModSlowSt`) -/

/-- Chunk state produced by `natDivModBig` (`natDivBig` and `natModBig`). -/
def BinDivModSlowSt (st : St) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg)
    (slowFn : Lir.FunId) (x : Nat) (a b : Lir.Arg) : St :=
  let tagReg := st.fresh
  let u := tagReg + 1
  let y := tagReg + 2
  let q := tagReg + 3
  let rFast := tagReg + 4
  let rSlow := tagReg + 5
  let n := st.next
  let curBlk : PBlock :=
    { params := st.params
    , body := (.assign tagReg (.bin .and .w64 a b) :: st.acc).reverse
    , term := .br .tz (.v tagReg) (.imm 1) (loc (n + 3)) (loc n) }
  { done := ((((st.done.insert st.cur curBlk)
      |>.insert n { term := .br .eq b (.imm 1) (loc (n + 1)) (loc (n + 2)) })
      |>.insert (n + 1) { term := .jump ⟨.loc (n + 4), [zero a]⟩, cold := true })
      |>.insert (n + 2) {
          body :=
            [ .assign u (.bin .shr .w64 a (.imm 1))
            , .assign y (.bin .shr .w64 b (.imm 1))
            , .assign q (.bin o .w64 (.v u) (.v y))
            , .assign rFast (retag (.v q)) ]
          term := .jump ⟨.loc (n + 4), [.v rFast]⟩ })
      |>.insert (n + 3) {
          body := [.call [rSlow] slowFn [a, b]]
          term := .jump ⟨.loc (n + 4), [.v rSlow]⟩
          cold := true }
  , cur := n + 4
  , params := [x]
  , acc := []
  , next := n + 5
  , fresh := rSlow + 1 }

private theorem binDivModSlow_code {f : Fir.FunId} {F : Lir.Func} {off : Nat} {starts : NatMap Nat}
    {C : List PBlock} (hH : Holds f F off starts C) {st : St} {o : Lir.BinOp}
    {zero : Lir.Arg → Lir.Arg} {slowFn : Lir.FunId} {x : Nat} {a b : Lir.Arg}
    (hC : Ext C (BinDivModSlowSt st o zero slowFn x a b)) (hl : Labels st) :
    let tagReg := st.fresh
    let u := tagReg + 1
    let y := tagReg + 2
    let q := tagReg + 3
    let rFast := tagReg + 4
    let rSlow := tagReg + 5
    let n := st.next
    (∃ lb, F.blocks[off + st.cur]? = some lb ∧
      lb.body.toList = st.acc.reverse ++ [.assign tagReg (.bin .and .w64 a b)] ∧
      lb.term = .br .tz .w64 (.v tagReg) (.imm 1) ⟨off + (n + 3), []⟩ ⟨off + n, []⟩) ∧
    (∃ cz, F.blocks[off + n]? = some cz ∧ cz.params = [] ∧ cz.body.toList = [] ∧
      cz.term = .br .eq .w64 b (.imm 1) ⟨off + (n + 1), []⟩ ⟨off + (n + 2), []⟩) ∧
    (∃ zb, F.blocks[off + (n + 1)]? = some zb ∧ zb.params = [] ∧ zb.body.toList = [] ∧
      zb.term = .jump ⟨off + (n + 4), [zero a]⟩) ∧
    (∃ nzb, F.blocks[off + (n + 2)]? = some nzb ∧ nzb.params = [] ∧
      nzb.body.toList =
        [ .assign u (.bin .shr .w64 a (.imm 1))
        , .assign y (.bin .shr .w64 b (.imm 1))
        , .assign q (.bin o .w64 (.v u) (.v y))
        , .assign rFast (retag (.v q)) ] ∧
      nzb.term = .jump ⟨off + (n + 4), [.v rFast]⟩) ∧
    (∃ sb, F.blocks[off + (n + 3)]? = some sb ∧ sb.params = [] ∧
      sb.body.toList = [.call [rSlow] slowFn [a, b]] ∧
      sb.term = .jump ⟨off + (n + 4), [.v rSlow]⟩) ∧
    (∃ jb, F.blocks[off + (n + 4)]? = some jb ∧ jb.params = [x]) := by
  have hcur := hl.cur
  let tagReg := st.fresh
  let u := tagReg + 1
  let y := tagReg + 2
  let q := tagReg + 3
  let rFast := tagReg + 4
  let rSlow := tagReg + 5
  let n := st.next
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · let curBlk : PBlock :=
      { params := st.params
      , body := (.assign tagReg (.bin .and .w64 a b) :: st.acc).reverse
      , term := .br .tz (.v tagReg) (.imm 1) (loc (n + 3)) (loc n) }
    obtain ⟨lb, hres, hlb⟩ := hH (hC.done (j := st.cur) (b := curBlk) (by
      simp only [BinDivModSlowSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [↓reduceIte, curBlk, tagReg, n]))
    obtain ⟨-, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, curBlk] at hterm
    exact ⟨lb, hlb, by rw [hbody]; simp [curBlk, tagReg], hterm.symm⟩
  · obtain ⟨cz, hres, hcz⟩ := hH (hC.done (j := n)
      (b := { term := .br .eq b (.imm 1) (loc (n + 1)) (loc (n + 2)) }) (by
        simp only [BinDivModSlowSt, NatMap.get?_insert]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨cz, hcz, hp, hbody, hterm.symm⟩
  · obtain ⟨zb, hres, hzb⟩ := hH (hC.done (j := n + 1)
      (b := { term := .jump ⟨.loc (n + 4), [zero a]⟩, cold := true }) (by
        simp only [BinDivModSlowSt, NatMap.get?_insert]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [↓reduceIte, n]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨zb, hzb, hp, hbody, hterm.symm⟩
  · obtain ⟨nzb, hres, hnzb⟩ := hH (hC.done (j := n + 2)
      (b := {
        body :=
          [ .assign u (.bin .shr .w64 a (.imm 1))
          , .assign y (.bin .shr .w64 b (.imm 1))
          , .assign q (.bin o .w64 (.v u) (.v y))
          , .assign rFast (retag (.v q)) ]
        term := .jump ⟨.loc (n + 4), [.v rFast]⟩ }) (by
          simp only [BinDivModSlowSt, NatMap.get?_insert]
          rw [ite_eq_right (by omega)]
          simp only [↓reduceIte, n, u, y, q, rFast, tagReg]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨nzb, hnzb, hp, hbody, hterm.symm⟩
  · obtain ⟨sb, hres, hsb⟩ := hH (hC.done (j := n + 3)
      (b := { body := [.call [rSlow] slowFn [a, b]], term := .jump ⟨.loc (n + 4), [.v rSlow]⟩, cold := true }) (by
        simp only [BinDivModSlowSt, NatMap.get?_insert, ↓reduceIte, n, rSlow, tagReg]))
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
    simp only [resolveTerm, resolveEdge, resolveTgt, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    exact ⟨sb, hsb, hp, hbody, hterm.symm⟩
  · have hopen : Open (BinDivModSlowSt st o zero slowFn x a b) := by
      simp only [Open, BinDivModSlowSt, NatMap.get?_insert]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      cases hq : st.done.get? (n + 4) with
      | none => rfl
      | some bj => have := hl.done hq; omega
    obtain ⟨jb0, hjb0, hjp0, -⟩ := hC.cur hopen
    obtain ⟨jb, hres, hjb⟩ := hH hjb0
    obtain ⟨hjp, -, -⟩ := resolveBlock_ok hres
    exact ⟨jb, hjb, hjp.trans hjp0⟩

/-! ## Individual Primitive `PrimCoreBig` Simulation Proofs -/

/-- **`natAddBig_core`:** Arbitrary-precision `Nat.add` with ZERO `.natOverflow`. -/
theorem natAddBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} (hslow : SlowNatBinSpec lp ctx MemStep procs.add (· + ·))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natAddBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natAdd [la, lb] := by
  big_run at hrun
  subst hrun
  let f0 : Nat := st.fresh
  have hstEq : Ext C (BinOvfSlowSt st procs.add x la lb
      [.assign (f0 + 1) (.bin .sub .w64 lb (.imm 1))]
      (.brOvf .addC (f0 + 2) la (.v (f0 + 1)) (loc (st.next + 1)) (loc (st.next + 3)))
      [] (.v (f0 + 2)) (f0 + 3) (f0 + 4) (f0 + 5)) := hC
  obtain ⟨⟨lbk, hlb, hlbody, hlterm⟩, ⟨fb, hfb, hfp, hfbody, hfterm⟩,
    ⟨okb, hokb, hokp, hokbody, hokterm⟩, ⟨st1, hst1, hst1p, hst1body, hst1term⟩,
    ⟨st2, hst2, hst2p, hst2body, hst2term⟩, ⟨jb, hjb, hjp⟩⟩ := binOvfSlow_code hH hstEq hl
  simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hfterm
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hpa, hqb⟩ := natval_two hws hrel
  have hra : ArgReads sup la := hreads la (by simp)
  have hrb : ArgReads sup lb := hreads lb (by simp)
  have hns : n = p + q := by
    have := sem_nat2 .natAdd (by decide) p q
    rw [this] at hsem; cases hsem; rfl
  subst hns
  let ρ₁ := ρl.insert f0 (wa &&& wb)
  have hx1 : Lir.execList ρl mem ctx [.assign f0 (.bin .and .w64 la lb)] = some (ρ₁, mem) := by
    simp [lir_eval, ha, hb, ρ₁]
  have hstar1 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := st.acc.reverse) (post := [])
    hF hlb (by simpa using hlbody) (by simp [Lir.Stmt.isCall]) hx1
  simp only [List.length_reverse] at hstar1
  have hlpos : st.acc.length + 1 = lbk.body.size := by rw [← Array.length_toList, hlbody]; simp
  have ha1 : la.eval ρ₁ = some wa := by rw [arg_eval_temp hra (t := f0) hsup]; exact ha
  have hb1 : lb.eval ρ₁ = some wb := by rw [arg_eval_temp hrb (t := f0) hsup]; exact hb
  cases htz : Lir.Cond.holds .tz .w64 (wa &&& wb) 1 with
  | true =>
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁) (ρ' := ρ₁)
      (e := ⟨off + (st.next + 2), []⟩) (vals := []) (va := wa &&& wb) (vb := 1)
      hF hlb hlpos hlterm (by simp [Lir.Arg.eval, ρ₁, f0]) rfl (by simp [htz]) rfl
      hst1 (by simp [hst1p, Lir.bindParams])
    have hpre := hstar1.trans (Lir.star_of_step hbr)
    rcases exec_slow_block hF hst1 hst1body hst1term hjb hjp (by omega)
        (env_frame_temp (t := f0) hsup _) ha1 hb1 (hslow mem p q wa wb hpa hqb) with
      ⟨c, ρl', mem', w, hrunS, hm, hnv, hrx, hfr⟩ | hfail
    · exact Or.inl ⟨_, ρl', mem', w, hpre.trans hrunS, hm, hnv, hrx, hfr⟩
    · exact Or.inr (hfail.prepend hpre)
  | false =>
    obtain ⟨hwa, hwb⟩ := (NatVal.and_tz_one_false_iff hpa hqb).mp htz
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁) (ρ' := ρ₁)
      (e := ⟨off + st.next, []⟩) (vals := []) (va := wa &&& wb) (vb := 1)
      hF hlb hlpos hlterm (by simp [Lir.Arg.eval, ρ₁, f0]) rfl (by simp [htz]) rfl
      hfb (by simp [hfp, Lir.bindParams])
    let ρ₂ := ρ₁.insert (f0 + 1) (wb - 1)
    have hx2 : Lir.execList ρ₁ mem ctx [.assign (f0 + 1) (.bin .sub .w64 lb (.imm 1))] =
        some (ρ₂, mem) := by simp [lir_eval, hb1, ρ₂]
    have hstar2 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
      hF hfb (by simpa using hfbody) (by simp [Lir.Stmt.isCall]) hx2
    simp only [List.length_nil, Nat.zero_add, List.length_singleton] at hstar2
    have hfpos : 1 = fb.body.size := by rw [← Array.length_toList, hfbody]; simp
    have ha2 : la.eval ρ₂ = some wa := by rw [arg_eval_temp hra (t := f0 + 1) (by omega)]; exact ha1
    have hb2 : lb.eval ρ₂ = some wb := by rw [arg_eval_temp hrb (t := f0 + 1) (by omega)]; exact hb1
    let ρ₃ := ρ₂.insert (f0 + 2) (wa + (wb - 1))
    by_cases hcar : wa + (wb - 1) < wa
    · have hovf := Lir.brOvf_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 1)
        (ρ := ρ₂) (ρ' := ρ₃) (e := ⟨off + (st.next + 3), []⟩) (vals := [])
        (va := wa) (vb := wb - 1) hF hfb hfpos hfterm.symm ha2 (by simp [Lir.Arg.eval, ρ₂])
        (by simp [Lir.Ovf.eval, hcar]) rfl hst2 (by simp [Lir.Ovf.eval, hst2p, Lir.bindParams, ρ₃])
      have hpre := hstar1.trans ((Lir.star_of_step hbr).trans (hstar2.trans (Lir.star_of_step hovf)))
      have ha3 : la.eval ρ₃ = some wa := by rw [arg_eval_temp hra (t := f0 + 2) (by omega)]; exact ha2
      have hb3 : lb.eval ρ₃ = some wb := by rw [arg_eval_temp hrb (t := f0 + 2) (by omega)]; exact hb2
      have hfr3 : ∀ y, y < sup → ρ₃[y]? = ρl[y]? := by
        intro y hy
        rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega),
          Lir.env_insert_ne _ _ (by omega)]
      rcases exec_slow_block hF hst2 hst2body hst2term hjb hjp (by omega)
          hfr3 ha3 hb3 (hslow mem p q wa wb hpa hqb) with
        ⟨c, ρl', mem', w, hrunS, hm, hnv, hrx, hfr⟩ | hfail
      · exact Or.inl ⟨_, ρl', mem', w, hpre.trans hrunS, hm, hnv, hrx, hfr⟩
      · exact Or.inr (hfail.prepend hpre)
    · have hok := Lir.brOvf_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 1)
        (ρ := ρ₂) (ρ' := ρ₃) (e := ⟨off + (st.next + 1), []⟩) (vals := [])
        (va := wa) (vb := wb - 1) hF hfb hfpos hfterm.symm ha2 (by simp [Lir.Arg.eval, ρ₂])
        (by simp [Lir.Ovf.eval, hcar]) rfl hokb (by simp [Lir.Ovf.eval, hokp, Lir.bindParams, ρ₃])
      have hokpos : 0 = okb.body.size := by rw [← Array.length_toList, hokbody]; rfl
      have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0)
        (ρ := ρ₃) (e := ⟨off + (st.next + 4), [.v (f0 + 2)]⟩)
        (vals := [wa + (wb - 1)]) (ρ' := ρ₃.insert x (wa + (wb - 1))) hF hokb hokpos hokterm
        (by simp [Lir.evalArgs, Lir.Arg.eval, ρ₃]) hjb (by simp [hjp, Lir.bindParams])
      left
      refine ⟨_, ρ₃.insert x (wa + (wb - 1)), mem, wa + (wb - 1),
        hstar1.trans ((Lir.star_of_step hbr).trans (hstar2.trans
          ((Lir.star_of_step hok).trans (Lir.star_of_step hjmp)))),
        hrefl mem, .small (natAdd_word (natAdd_operands hwa hwb).2 hcar), by simp, ?_⟩
      intro y hy hyx
      rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega),
        Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega)]

/-- **`natSubBig_core`:** Arbitrary-precision `Nat.sub` with ZERO `.natOverflow`. -/
theorem natSubBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} (hslow : SlowNatBinSpec lp ctx MemStep procs.sub (· - ·))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natSubBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natSub [la, lb] := by
  big_run at hrun
  subst hrun
  let f0 : Nat := st.fresh
  have hstEq : Ext C (BinFastSlowSt st 3 procs.sub x la lb
      [ .assign f0 (.bin .sub .w64 la lb)
      , .assign (f0 + 1) (.bin .or .w64 (.v f0) (.imm 1))
      , .assign (f0 + 2) (.select .ult .w64 la lb (.imm 1) (.v (f0 + 1))) ]
      (.v (f0 + 2))) := hC
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hpa, hqb⟩ := natval_two hws hrel
  have hra := hreads la (by simp)
  have hrb := hreads lb (by simp)
  have hns : n = p - q := by
    have := sem_nat2 .natSub (by decide) p q
    rw [this] at hsem; cases hsem; rfl
  subst hns
  refine binFastSlow_run hrefl hF hH hstEq hl hsup (by simp [Lir.Stmt.isCall]) ha hb hra hrb hpa hqb
    ?_ (hslow mem p q wa wb hpa hqb)
  intro hwa hwb
  let ρ₁ := ρl.insert (f0 + 3) (wa &&& wb)
  let w := if wa < wb then (1 : Word) else (wa - wb) ||| 1
  let ρf := ((ρ₁.insert f0 (wa - wb)).insert (f0 + 1) ((wa - wb) ||| 1)).insert (f0 + 2) w
  have ha1 : la.eval ρ₁ = some wa := by rw [arg_eval_temp hra (t := f0 + 3) (by omega)]; exact ha
  have hb1 : lb.eval ρ₁ = some wb := by rw [arg_eval_temp hrb (t := f0 + 3) (by omega)]; exact hb
  have ha2 : la.eval ((ρ₁.insert f0 (wa - wb)).insert (f0 + 1) ((wa - wb) ||| 1)) = some wa := by
    rw [arg_eval_temp hra (t := f0 + 1) (by omega), arg_eval_temp hra (t := f0) hsup]; exact ha1
  have hb2 : lb.eval ((ρ₁.insert f0 (wa - wb)).insert (f0 + 1) ((wa - wb) ||| 1)) = some wb := by
    rw [arg_eval_temp hrb (t := f0 + 1) (by omega), arg_eval_temp hrb (t := f0) hsup]; exact hb1
  refine ⟨ρf, w, ?_, by simp [Lir.Arg.eval, ρf], .small (natSub_word hwa hwb), ?_⟩
  · change Lir.execList ρ₁ mem ctx _ = _
    simp only [lir_eval, ha1, hb1, ha2, hb2, ↓reduceIte, ρf, w]
  · intro y hy
    rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega),
      Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega)]

/-- **`natPredBig_core`:** Arbitrary-precision `Nat.pred` with ZERO `.natOverflow`. -/
theorem natPredBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} (hslow : SlowNatUnSpec lp ctx MemStep procs.pred (· - 1))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la : Lir.Arg}
    (hrun : (natPredBig procs x la).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natPred [la] := by
  big_run at hrun
  subst hrun
  let f0 : Nat := st.fresh
  have hstEq : Ext C (UnFastSlowSt st procs.pred x la
      [ .assign f0 (.bin .sub .w64 la (.imm 2))
      , .assign (f0 + 1) (.select .eq .w64 la (.imm 1) (.imm 1) (.v f0)) ]
      (.v (f0 + 1)) (f0 + 2) (f0 + 3)) := hC
  obtain ⟨⟨lbk, hlb, hlbody, hlterm⟩, ⟨fb, hfb, hfp, hfbody, hfterm⟩,
    ⟨sb, hsb, hsp, hsbody, hsterm⟩, ⟨jb, hjb, hjp⟩⟩ := unFastSlow_code hH hstEq hl
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, wa, rfl, ha, hpa⟩ := natval_one hws hrel
  have hra := hreads la (by simp)
  have hns : n = p - 1 := by
    simp [Lam.Prim.sem, Src.PrimOp.eval2] at hsem; exact hsem.symm
  subst hns
  have hlpos : st.acc.length = lbk.body.size := by rw [← Array.length_toList, hlbody]; simp
  cases htz : Lir.Cond.holds .tz .w64 wa 1 with
  | false =>
    have hwa : Rt.natWord p = some wa := (NatVal.tz_one_false_iff hpa).mp htz
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl)
      (e := ⟨off + st.next, []⟩) (vals := []) (va := wa) (vb := 1)
      hF hlb hlpos hlterm ha rfl (by simp [htz]) rfl hfb (by simp [hfp, Lir.bindParams])
    let w := if wa = 1 then (1 : Word) else wa - 2
    let ρf := (ρl.insert f0 (wa - 2)).insert (f0 + 1) w
    have ha1 : la.eval (ρl.insert f0 (wa - 2)) = some wa := by
      rw [arg_eval_temp hra (t := f0) hsup]; exact ha
    have hxf : Lir.execList ρl mem ctx
        [ .assign f0 (.bin .sub .w64 la (.imm 2))
        , .assign (f0 + 1) (.select .eq .w64 la (.imm 1) (.imm 1) (.v f0)) ] = some (ρf, mem) := by
      simp [lir_eval, ha, ha1, ρf, w]
    have hstarf := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
      hF hfb (by simpa using hfbody) (by simp [Lir.Stmt.isCall]) hxf
    simp only [List.length_nil, Nat.zero_add, List.length_cons, Nat.reduceAdd] at hstarf
    have hfpos : 2 = fb.body.size := by rw [← Array.length_toList, hfbody]; simp
    have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 2)
      (ρ := ρf) (e := ⟨off + (st.next + 2), [.v (f0 + 1)]⟩) (vals := [w]) (ρ' := ρf.insert x w)
      hF hfb hfpos hfterm (by simp [Lir.evalArgs, Lir.Arg.eval, ρf]) hjb (by simp [hjp, Lir.bindParams])
    left
    refine ⟨_, ρf.insert x w, mem, w,
      (Lir.star_of_step hbr).trans (hstarf.trans (Lir.star_of_step hjmp)),
      hrefl mem, .small (natPred_word hwa), by simp, ?_⟩
    intro y hy hyx
    rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega),
      Lir.env_insert_ne _ _ (by omega)]
  | true =>
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl) (ρ' := ρl)
      (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := wa) (vb := 1)
      hF hlb hlpos hlterm ha rfl (by simp [htz]) rfl hsb (by simp [hsp, Lir.bindParams])
    have hsb_pos : 0 < sb.body.size := by rw [← Array.length_toList, hsbody]; simp
    have hsb_call : sb.body[0] = .call [f0 + 2] procs.pred [la] := by
      rw [← Array.getElem_toList (h := hsb_pos)]; simp [hsbody]
    rcases call_procSpec (rest := rest) hF hsb hsb_pos hsb_call (evalArgs_one_of ha)
        (hslow mem p wa hpa) with
      ⟨c, mem', w, hcall, hm, hnv⟩ | hfail
    · have hspos : 1 = sb.body.size := by rw [← Array.length_toList, hsbody]; simp
      have hjmp := Lir.jump_at (p := lp) (mem := mem') (ctx := ctx) (rest := rest) (pos := 1)
        (ρ := ρl.insert (f0 + 2) w) (e := ⟨off + (st.next + 2), [.v (f0 + 2)]⟩)
        (vals := [w]) (ρ' := (ρl.insert (f0 + 2) w).insert x w)
        hF hsb hspos hsterm (by simp [Lir.evalArgs, Lir.Arg.eval]) hjb (by simp [hjp, Lir.bindParams])
      left
      refine ⟨_, (ρl.insert (f0 + 2) w).insert x w, mem', w,
        (Lir.star_of_step hbr).trans (hcall.trans (Lir.star_of_step hjmp)),
        hm, hnv, by simp, ?_⟩
      intro y hy hyx
      rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega)]
    · exact Or.inr (hfail.prepend (Lir.star_of_step hbr))

/-- **`natSuccPeelBig_core`:** `Nat.succ` projection peel (for `Cfg.Instr.proj` on `natSucc`)
computes `p - 1` (demoting `2^63` cleanly) with ZERO `.natOverflow`. -/
theorem natSuccPeelBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} (hslow : SlowNatUnSpec lp ctx MemStep procs.pred (· - 1))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x y : Nat}
    (hrun : (natSuccPeelBig procs x y).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natPred [.v y] :=
  natPredBig_core hrefl hslow hF hH hrun hC hl hsup

/-- **`natMulBig_core`:** Arbitrary-precision `Nat.mul` with ZERO `.natOverflow`. -/
theorem natMulBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} (hslow : SlowNatBinSpec lp ctx MemStep procs.mul (· * ·))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natMulBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natMul [la, lb] := by
  big_run at hrun
  subst hrun
  let f0 : Nat := st.fresh
  have hstEq : Ext C (BinOvfSlowSt st procs.mul x la lb
      [ .assign (f0 + 1) (.bin .shr .w64 la (.imm 1))
      , .assign (f0 + 2) (.bin .sub .w64 lb (.imm 1)) ]
      (.brOvf .mulOvf (f0 + 3) (.v (f0 + 1)) (.v (f0 + 2)) (loc (st.next + 1)) (loc (st.next + 3)))
      [.assign (f0 + 4) (.bin .or .w64 (.v (f0 + 3)) (.imm 1))]
      (.v (f0 + 4)) (f0 + 5) (f0 + 6) (f0 + 7)) := hC
  obtain ⟨⟨lbk, hlb, hlbody, hlterm⟩, ⟨fb, hfb, hfp, hfbody, hfterm⟩,
    ⟨okb, hokb, hokp, hokbody, hokterm⟩, ⟨st1, hst1, hst1p, hst1body, hst1term⟩,
    ⟨st2, hst2, hst2p, hst2body, hst2term⟩, ⟨jb, hjb, hjp⟩⟩ := binOvfSlow_code hH hstEq hl
  simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hfterm
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hpa, hqb⟩ := natval_two hws hrel
  have hra := hreads la (by simp)
  have hrb := hreads lb (by simp)
  have hns : n = p * q := by
    have := sem_nat2 .natMul (by decide) p q
    rw [this] at hsem; cases hsem; rfl
  subst hns
  let ρ₁ := ρl.insert f0 (wa &&& wb)
  have hx1 : Lir.execList ρl mem ctx [.assign f0 (.bin .and .w64 la lb)] = some (ρ₁, mem) := by
    simp [lir_eval, ha, hb, ρ₁]
  have hstar1 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := st.acc.reverse) (post := [])
    hF hlb (by simpa using hlbody) (by simp [Lir.Stmt.isCall]) hx1
  simp only [List.length_reverse] at hstar1
  have hlpos : st.acc.length + 1 = lbk.body.size := by rw [← Array.length_toList, hlbody]; simp
  have ha1 : la.eval ρ₁ = some wa := by rw [arg_eval_temp hra (t := f0) hsup]; exact ha
  have hb1 : lb.eval ρ₁ = some wb := by rw [arg_eval_temp hrb (t := f0) hsup]; exact hb
  cases htz : Lir.Cond.holds .tz .w64 (wa &&& wb) 1 with
  | true =>
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁) (ρ' := ρ₁)
      (e := ⟨off + (st.next + 2), []⟩) (vals := []) (va := wa &&& wb) (vb := 1)
      hF hlb hlpos hlterm (by simp [Lir.Arg.eval, ρ₁, f0]) rfl (by simp [htz]) rfl
      hst1 (by simp [hst1p, Lir.bindParams])
    have hpre := hstar1.trans (Lir.star_of_step hbr)
    rcases exec_slow_block hF hst1 hst1body hst1term hjb hjp (by omega)
        (env_frame_temp (t := f0) hsup _) ha1 hb1 (hslow mem p q wa wb hpa hqb) with
      ⟨c, ρl', mem', w, hrunS, hm, hnv, hrx, hfr⟩ | hfail
    · exact Or.inl ⟨_, ρl', mem', w, hpre.trans hrunS, hm, hnv, hrx, hfr⟩
    · exact Or.inr (hfail.prepend hpre)
  | false =>
    obtain ⟨hwa, hwb⟩ := (NatVal.and_tz_one_false_iff hpa hqb).mp htz
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁) (ρ' := ρ₁)
      (e := ⟨off + st.next, []⟩) (vals := []) (va := wa &&& wb) (vb := 1)
      hF hlb hlpos hlterm (by simp [Lir.Arg.eval, ρ₁, f0]) rfl (by simp [htz]) rfl
      hfb (by simp [hfp, Lir.bindParams])
    let u := wa >>> (1 : Word)
    let t := wb - 1
    let ρ₂ := (ρ₁.insert (f0 + 1) u).insert (f0 + 2) t
    have hb_ins : lb.eval (ρ₁.insert (f0 + 1) u) = some wb := by
      rw [arg_eval_temp hrb (t := f0 + 1) (by omega)]; exact hb1
    have hx2 : Lir.execList ρ₁ mem ctx
        [ .assign (f0 + 1) (.bin .shr .w64 la (.imm 1))
        , .assign (f0 + 2) (.bin .sub .w64 lb (.imm 1)) ] = some (ρ₂, mem) := by
      simp [lir_eval, ha1, hb_ins, ρ₂, u, t]
    have hstar2 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
      hF hfb (by simpa using hfbody) (by simp [Lir.Stmt.isCall]) hx2
    simp only [List.length_nil, Nat.zero_add, List.length_cons, Nat.reduceAdd] at hstar2
    have hfpos : 2 = fb.body.size := by rw [← Array.length_toList, hfbody]; simp
    have hu2 : (Lir.Arg.v (f0 + 1)).eval ρ₂ = some u := by
      simp only [Lir.Arg.eval, ρ₂, Lir.env_insert_get]
      rw [ite_eq_right (by omega)]
      simp
    let ρ₃ := ρ₂.insert (f0 + 3) (u * t)
    by_cases hovf : 2 ^ 64 ≤ u.toNat * t.toNat
    · have hbrO := Lir.brOvf_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 2)
        (ρ := ρ₂) (ρ' := ρ₃) (e := ⟨off + (st.next + 3), []⟩) (vals := [])
        (va := u) (vb := t) hF hfb hfpos hfterm.symm hu2 (by simp [Lir.Arg.eval, ρ₂])
        (by simp [Lir.Ovf.eval, hovf]) rfl hst2 (by simp [Lir.Ovf.eval, hst2p, Lir.bindParams, ρ₃])
      have hpre := hstar1.trans ((Lir.star_of_step hbr).trans (hstar2.trans (Lir.star_of_step hbrO)))
      have ha3 : la.eval ρ₃ = some wa := by
        rw [arg_eval_temp hra (t := f0 + 3) (by omega), arg_eval_temp hra (t := f0 + 2) (by omega),
          arg_eval_temp hra (t := f0 + 1) (by omega)]; exact ha1
      have hb3 : lb.eval ρ₃ = some wb := by
        rw [arg_eval_temp hrb (t := f0 + 3) (by omega), arg_eval_temp hrb (t := f0 + 2) (by omega),
          arg_eval_temp hrb (t := f0 + 1) (by omega)]; exact hb1
      have hfr3 : ∀ y, y < sup → ρ₃[y]? = ρl[y]? := by
        intro y hy
        rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega),
          Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega)]
      rcases exec_slow_block hF hst2 hst2body hst2term hjb hjp (by omega)
          hfr3 ha3 hb3 (hslow mem p q wa wb hpa hqb) with
        ⟨c, ρl', mem', w, hrunS, hm, hnv, hrx, hfr⟩ | hfail
      · exact Or.inl ⟨_, ρl', mem', w, hpre.trans hrunS, hm, hnv, hrx, hfr⟩
      · exact Or.inr (hfail.prepend hpre)
    · have hbrO := Lir.brOvf_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 2)
        (ρ := ρ₂) (ρ' := ρ₃) (e := ⟨off + (st.next + 1), []⟩) (vals := [])
        (va := u) (vb := t) hF hfb hfpos hfterm.symm hu2 (by simp [Lir.Arg.eval, ρ₂])
        (by simp [Lir.Ovf.eval, hovf]) rfl hokb (by simp [Lir.Ovf.eval, hokp, Lir.bindParams, ρ₃])
      let w := (u * t) ||| 1
      let ρ₄ := ρ₃.insert (f0 + 4) w
      have hxok : Lir.execList ρ₃ mem ctx [.assign (f0 + 4) (.bin .or .w64 (.v (f0 + 3)) (.imm 1))] =
          some (ρ₄, mem) := by simp [lir_eval, ρ₃, ρ₄, w]
      have hstarOk := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
        hF hokb (by simpa using hokbody) (by simp [Lir.Stmt.isCall]) hxok
      simp only [List.length_nil, Nat.zero_add, List.length_singleton] at hstarOk
      have hokpos : 1 = okb.body.size := by rw [← Array.length_toList, hokbody]; simp
      have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 1)
        (ρ := ρ₄) (e := ⟨off + (st.next + 4), [.v (f0 + 4)]⟩) (vals := [w]) (ρ' := ρ₄.insert x w)
        hF hokb hokpos hokterm (by simp [Lir.evalArgs, Lir.Arg.eval, ρ₄]) hjb (by simp [hjp, Lir.bindParams])
      left
      refine ⟨_, ρ₄.insert x w, mem, w,
        hstar1.trans ((Lir.star_of_step hbr).trans (hstar2.trans
          ((Lir.star_of_step hbrO).trans (hstarOk.trans (Lir.star_of_step hjmp))))),
        hrefl mem, .small (natMul_ovf_word hwa hwb hovf), by simp, ?_⟩
      intro y hy hyx
      rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega),
        Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega),
        Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega)]

private def divModWord (o : Lir.BinOp) (u y : Word) : Word :=
  match o with
  | .udiv => u / y
  | _ => u % y

/-- Shared proof for `natDivBig_core` and `natModBig_core`. -/
private theorem natDivModBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {o : Lir.BinOp} {zero : Lir.Arg → Lir.Arg} {slowFn : Lir.FunId} {op : Lam.Prim}
    {fnSpec : Nat → Nat → Nat}
    (ho : o = .udiv ∨ o = .urem)
    (hsemEq : ∀ p q, op.sem [p, q] = some (.nat (fnSpec p q)))
    (hzero : ∀ {p : Nat} {la : Lir.Arg} {ρ : Lir.Env} {wa : Word},
      la.eval ρ = some wa → Rt.natWord p = some wa →
      ∃ wz, (zero la).eval ρ = some wz ∧ Rt.natWord (fnSpec p 0) = some wz)
    (hnz : ∀ {p q : Nat} {wa wb : Word},
      Rt.natWord p = some wa → Rt.natWord q = some wb → q ≠ 0 →
      let qv := divModWord o (wa >>> 1) (wb >>> 1)
      Rt.natWord (fnSpec p q) = some (qv + qv + 1))
    (hslow : SlowNatBinSpec lp ctx MemStep slowFn fnSpec)
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natDivModBig o zero slowFn x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x op [la, lb] := by
  big_run at hrun
  subst hrun
  let f0 : Nat := st.fresh
  have hstEq : Ext C (BinDivModSlowSt st o zero slowFn x la lb) := hC
  obtain ⟨⟨lbk, hlb, hlbody, hlterm⟩, ⟨cz, hcz, hczp, hczbody, hczterm⟩,
    ⟨zb, hzb, hzbp, hzbbody, hzbterm⟩, ⟨nzb, hnzb, hnzbp, hnzbbody, hnzbterm⟩,
    ⟨sb, hsb, hsp, hsbody, hsterm⟩, ⟨jb, hjb, hjp⟩⟩ := binDivModSlow_code hH hstEq hl
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hpa, hqb⟩ := natval_two hws hrel
  have hra := hreads la (by simp)
  have hrb := hreads lb (by simp)
  rw [hsemEq] at hsem
  cases hsem
  let ρ₁ := ρl.insert f0 (wa &&& wb)
  have hx1 : Lir.execList ρl mem ctx [.assign f0 (.bin .and .w64 la lb)] = some (ρ₁, mem) := by
    simp [lir_eval, ha, hb, ρ₁]
  have hstar1 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := st.acc.reverse) (post := [])
    hF hlb (by simpa using hlbody) (by simp [Lir.Stmt.isCall]) hx1
  simp only [List.length_reverse] at hstar1
  have hlpos : st.acc.length + 1 = lbk.body.size := by rw [← Array.length_toList, hlbody]; simp
  have ha1 : la.eval ρ₁ = some wa := by rw [arg_eval_temp hra (t := f0) hsup]; exact ha
  have hb1 : lb.eval ρ₁ = some wb := by rw [arg_eval_temp hrb (t := f0) hsup]; exact hb
  cases htz : Lir.Cond.holds .tz .w64 (wa &&& wb) 1 with
  | true =>
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁) (ρ' := ρ₁)
      (e := ⟨off + (st.next + 3), []⟩) (vals := []) (va := wa &&& wb) (vb := 1)
      hF hlb hlpos hlterm (by simp [Lir.Arg.eval, ρ₁, f0]) rfl (by simp [htz]) rfl
      hsb (by simp [hsp, Lir.bindParams])
    have hpre := hstar1.trans (Lir.star_of_step hbr)
    rcases exec_slow_block hF hsb hsbody hsterm hjb hjp (by omega)
        (env_frame_temp (t := f0) hsup _) ha1 hb1 (hslow mem p q wa wb hpa hqb) with
      ⟨c, ρl', mem', w, hrunS, hm, hnv, hrx, hfr⟩ | hfail
    · exact Or.inl ⟨_, ρl', mem', w, hpre.trans hrunS, hm, hnv, hrx, hfr⟩
    · exact Or.inr (hfail.prepend hpre)
  | false =>
    obtain ⟨hwa, hwb⟩ := (NatVal.and_tz_one_false_iff hpa hqb).mp htz
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁) (ρ' := ρ₁)
      (e := ⟨off + st.next, []⟩) (vals := []) (va := wa &&& wb) (vb := 1)
      hF hlb hlpos hlterm (by simp [Lir.Arg.eval, ρ₁, f0]) rfl (by simp [htz]) rfl
      hcz (by simp [hczp, Lir.bindParams])
    have hczpos : 0 = cz.body.size := by rw [← Array.length_toList, hczbody]; rfl
    by_cases hq0 : q = 0
    · subst hq0
      have hwb1 : wb = 1 := (natWord_eq_one hwb).2 rfl
      have hbrz := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0)
        (ρ := ρ₁) (ρ' := ρ₁) (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := wb) (vb := 1)
        hF hcz hczpos hczterm hb1 rfl (by simp [lir_eval, hwb1]) rfl hzb (by simp [hzbp, Lir.bindParams])
      obtain ⟨wz, hwz, hnwz⟩ := hzero ha1 hwa
      have hzbpos : 0 = zb.body.size := by rw [← Array.length_toList, hzbbody]; rfl
      have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0)
        (ρ := ρ₁) (e := ⟨off + (st.next + 4), [zero la]⟩) (vals := [wz]) (ρ' := ρ₁.insert x wz)
        hF hzb hzbpos hzbterm (evalArgs_one_of hwz) hjb (by simp [hjp, Lir.bindParams])
      left
      refine ⟨_, ρ₁.insert x wz, mem, wz,
        hstar1.trans ((Lir.star_of_step hbr).trans ((Lir.star_of_step hbrz).trans (Lir.star_of_step hjmp))),
        hrefl mem, .small hnwz, by simp, ?_⟩
      intro y hy hyx
      rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega)]
    · have hwbne : wb ≠ 1 := fun h => hq0 ((natWord_eq_one hwb).1 h)
      have hbrz := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0)
        (ρ := ρ₁) (ρ' := ρ₁) (e := ⟨off + (st.next + 2), []⟩) (vals := []) (va := wb) (vb := 1)
        hF hcz hczpos hczterm hb1 rfl (by simp [lir_eval, hwbne]) rfl hnzb (by simp [hnzbp, Lir.bindParams])
      have hy0 : wb >>> (1 : Word) ≠ 0 := untag_ne_zero hwb hq0
      let u := wa >>> (1 : Word)
      let yv := wb >>> (1 : Word)
      let qv : Word := divModWord o u yv
      let rF := qv + qv + 1
      let ρ₂ := (((ρ₁.insert (f0 + 1) u).insert (f0 + 2) yv).insert (f0 + 3) qv).insert (f0 + 4) rF
      have hb_ins : lb.eval (ρ₁.insert (f0 + 1) u) = some wb := by
        rw [arg_eval_temp hrb (t := f0 + 1) (by omega)]; exact hb1
      have hxnz : Lir.execList ρ₁ mem ctx
          [ .assign (f0 + 1) (.bin .shr .w64 la (.imm 1))
          , .assign (f0 + 2) (.bin .shr .w64 lb (.imm 1))
          , .assign (f0 + 3) (.bin o .w64 (.v (f0 + 1)) (.v (f0 + 2)))
          , .assign (f0 + 4) (retag (.v (f0 + 3))) ] = some (ρ₂, mem) := by
        rcases ho with rfl | rfl <;>
        · have h12 : f0 + 2 ≠ f0 + 1 := by omega
          simp only [divModWord, retag, lir_eval, ha1, hb_ins, hy0, h12, ↓reduceIte, UInt64.mul_one, u, yv, qv, rF, ρ₂]
      have hstarnz := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
        hF hnzb (by simpa using hnzbbody) (by simp [Lir.Stmt.isCall]) hxnz
      simp only [List.length_nil, Nat.zero_add, List.length_cons, Nat.reduceAdd] at hstarnz
      have hnzpos : 4 = nzb.body.size := by rw [← Array.length_toList, hnzbbody]; simp
      have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 4)
        (ρ := ρ₂) (e := ⟨off + (st.next + 4), [.v (f0 + 4)]⟩) (vals := [rF]) (ρ' := ρ₂.insert x rF)
        hF hnzb hnzpos hnzbterm (by simp [Lir.evalArgs, Lir.Arg.eval, ρ₂]) hjb (by simp [hjp, Lir.bindParams])
      left
      refine ⟨_, ρ₂.insert x rF, mem, rF,
        hstar1.trans ((Lir.star_of_step hbr).trans ((Lir.star_of_step hbrz).trans
          (hstarnz.trans (Lir.star_of_step hjmp)))),
        hrefl mem, .small (hnz hwa hwb hq0), by simp, ?_⟩
      intro y hy hyx
      rw [Lir.env_insert_ne _ _ (Ne.symm hyx), Lir.env_insert_ne _ _ (by omega),
        Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega),
        Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega)]

/-- **`natDivBig_core`:** Arbitrary-precision `Nat.div` (`n / 0 = 0`) with ZERO `.natOverflow`. -/
theorem natDivBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs}
    (hslow : SlowNatBinSpec lp ctx MemStep procs.div (fun a b => if b = 0 then 0 else a / b))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natDivBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natDiv [la, lb] :=
  natDivModBig_core hrefl (Or.inl rfl) (sem_nat2 .natDiv (by decide))
    (fun _ _ => ⟨1, rfl, div_word0⟩)
    (fun hwa hwb hq => div_word hwa hwb hq)
    hslow hF hH hrun hC hl hsup

/-- **`natModBig_core`:** Arbitrary-precision `Nat.mod` (`n % 0 = n`) with ZERO `.natOverflow`. -/
theorem natModBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs}
    (hslow : SlowNatBinSpec lp ctx MemStep procs.mod (fun a b => if b = 0 then a else a % b))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natModBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natMod [la, lb] :=
  natDivModBig_core hrefl (Or.inr rfl) (sem_nat2 .natMod (by decide))
    (fun ha hwa => ⟨_, ha, mod_word0 hwa⟩)
    (fun hwa hwb hq => mod_word hwa hwb hq)
    hslow hF hH hrun hC hl hsup

/-! ## Comparisons (`natBeqBig_core`, `natBleBig_core`, `natBltBig_core`, `natCmpBig_core`) -/

private theorem natCmpBig_aux {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {cond : Lir.Cond} {slowFn : Lir.FunId} {tWord fWord : Word}
    {op : Lam.Prim} {cmpSpec : Nat → Nat → Bool}
    (hsemEq : ∀ p q, op.sem [p, q] = some (.bool (cmpSpec p q)))
    (hcond : ∀ {p q : Nat} {wa wb : Word},
      Rt.natWord p = some wa → Rt.natWord q = some wb →
      cond.holds .w64 wa wb = cmpSpec p q)
    (hslow : SlowNatCmpSpec lp ctx MemStep tWord fWord slowFn cmpSpec)
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natCmpBig cond slowFn tWord fWord x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBigBool lp ctx MemStep tWord fWord sup fn (off + st.cur) st.acc.length
      (off + st'.cur) st'.acc.length x op [la, lb] := by
  big_run at hrun
  subst hrun
  let f0 : Nat := st.fresh
  have hstEq : Ext C (BinFastSlowSt st 1 slowFn x la lb
      [.assign f0 (.select cond .w64 la lb (.imm tWord) (.imm fWord))] (.v f0)) := hC
  intro ρl mem rest ns ws b hws hrel hreads hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hpa, hqb⟩ := natval_two hws hrel
  have hra := hreads la (by simp)
  have hrb := hreads lb (by simp)
  rw [hsemEq] at hsem
  cases hsem
  refine binFastSlow_run hrefl hF hH hstEq hl hsup (by simp [Lir.Stmt.isCall]) ha hb hra hrb hpa hqb
    ?_ (hslow mem p q wa wb hpa hqb)
  intro hwa hwb
  let ρ₁ := ρl.insert (f0 + 1) (wa &&& wb)
  let w := if cmpSpec p q then tWord else fWord
  let ρf := ρ₁.insert f0 w
  have ha1 : la.eval ρ₁ = some wa := by rw [arg_eval_temp hra (t := f0 + 1) (by omega)]; exact ha
  have hb1 : lb.eval ρ₁ = some wb := by rw [arg_eval_temp hrb (t := f0 + 1) (by omega)]; exact hb
  refine ⟨ρf, w, ?_, by simp [Lir.Arg.eval, ρf], rfl, ?_⟩
  · change Lir.execList ρ₁ mem ctx _ = _
    simp [lir_eval, ha1, hb1, hcond hwa hwb, ρf, w]
  · intro y hy
    rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega)]

/-- **`natBeqBig_core`:** Arbitrary-precision `Nat.beq` with ZERO `.natOverflow`. -/
theorem natBeqBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} {tWord fWord : Word}
    (hslow : SlowNatCmpSpec lp ctx MemStep tWord fWord procs.beq (fun a b => a == b))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natBeqBig procs tWord fWord x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBigBool lp ctx MemStep tWord fWord sup fn (off + st.cur) st.acc.length
      (off + st'.cur) st'.acc.length x .natBeq [la, lb] :=
  natCmpBig_aux hrefl (fun p q => by simp [Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2])
    (fun hwa hwb => by
      rw [Lir.holds_eq]
      apply Bool.eq_iff_iff.mpr
      simp [natWord_eq_iff hwa hwb])
    hslow hF hH hrun hC hl hsup

/-- **`natBleBig_core`:** Arbitrary-precision `Nat.ble` with ZERO `.natOverflow`. -/
theorem natBleBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} {tWord fWord : Word}
    (hslow : SlowNatCmpSpec lp ctx MemStep tWord fWord procs.ble (fun a b => decide (a ≤ b)))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natBleBig procs tWord fWord x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBigBool lp ctx MemStep tWord fWord sup fn (off + st.cur) st.acc.length
      (off + st'.cur) st'.acc.length x .natBle [la, lb] :=
  natCmpBig_aux hrefl (fun p q => by simp [Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2])
    (fun hwa hwb => by rw [Lir.holds_ule]; simp [natWord_le_iff hwa hwb])
    hslow hF hH hrun hC hl hsup

/-- **`natBltBig_core`:** Arbitrary-precision `Nat.blt` with ZERO `.natOverflow`. -/
theorem natBltBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} {tWord fWord : Word}
    (hslow : SlowNatCmpSpec lp ctx MemStep tWord fWord procs.blt (fun a b => decide (a < b)))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natBltBig procs tWord fWord x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBigBool lp ctx MemStep tWord fWord sup fn (off + st.cur) st.acc.length
      (off + st'.cur) st'.acc.length x .natBlt [la, lb] :=
  natCmpBig_aux hrefl (fun p q => by simp [Lam.Prim.sem])
    (fun hwa hwb => by rw [Lir.holds_ult]; simp [natWord_lt_iff hwa hwb])
    hslow hF hH hrun hC hl hsup

/-- **`natCmpBig_core`:** Unified arbitrary-precision comparison theorem covering
`natBeq`, `natBle`, and `natBlt` with ZERO `.natOverflow`. -/
theorem natCmpBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop}
    {procs : BigNatProcs} {tWord fWord : Word}
    (henv : SlowPathEnv lp ctx MemStep procs tWord fWord)
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {op : Lam.Prim} {la lb : Lir.Arg}
    (hop : op = .natBeq ∨ op = .natBle ∨ op = .natBlt)
    (hrun : (primitiveBig f { bools := some (tWord, fWord), procs } x op [la, lb]).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBigBool lp ctx MemStep tWord fWord sup fn (off + st.cur) st.acc.length
      (off + st'.cur) st'.acc.length x op [la, lb] := by
  rcases hop with rfl | rfl | rfl
  · exact natBeqBig_core henv.mem_refl henv.beq hF hH hrun hC hl hsup
  · exact natBleBig_core henv.mem_refl henv.ble hF hH hrun hC hl hsup
  · exact natBltBig_core henv.mem_refl henv.blt hF hH hrun hC hl hsup

/-! ## Bitwise Operations (`natLandBig_core`, `natLorBig_core`, `natXorBig_core`, `natBitBig_core`) -/

/-- **`natLandBig_core`:** Arbitrary-precision `Nat.land` (zero extra fast-path ALU ops!)
with ZERO `.natOverflow`. -/
theorem natLandBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} (hslow : SlowNatBinSpec lp ctx MemStep procs.land (· &&& ·))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natLandBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natLand [la, lb] := by
  big_run at hrun
  subst hrun
  have hstEq : Ext C (BinFastSlowSt st 0 procs.land x la lb [] (.v st.fresh)) := hC
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hpa, hqb⟩ := natval_two hws hrel
  have hra := hreads la (by simp)
  have hrb := hreads lb (by simp)
  have hns : n = p &&& q := by
    have := sem_nat2 .natLand (by decide) p q
    rw [this] at hsem; cases hsem; rfl
  subst hns
  refine binFastSlow_run hrefl hF hH hstEq hl hsup (by simp) ha hb hra hrb hpa hqb
    ?_ (hslow mem p q wa wb hpa hqb)
  intro hwa hwb
  refine ⟨ρl.insert (st.fresh + 0) (wa &&& wb), wa &&& wb, rfl,
    by simp [Lir.Arg.eval], .small (natLand_word hwa hwb), env_frame_temp (by omega) _⟩

/-- **`natLorBig_core`:** Arbitrary-precision `Nat.lor` with ZERO `.natOverflow`. -/
theorem natLorBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} (hslow : SlowNatBinSpec lp ctx MemStep procs.lor (· ||| ·))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natLorBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natLor [la, lb] := by
  big_run at hrun
  subst hrun
  let f0 : Nat := st.fresh
  have hstEq : Ext C (BinFastSlowSt st 1 procs.lor x la lb
      [.assign f0 (.bin .or .w64 la lb)] (.v f0)) := hC
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hpa, hqb⟩ := natval_two hws hrel
  have hra := hreads la (by simp)
  have hrb := hreads lb (by simp)
  have hns : n = p ||| q := by
    have := sem_nat2 .natLor (by decide) p q
    rw [this] at hsem; cases hsem; rfl
  subst hns
  refine binFastSlow_run hrefl hF hH hstEq hl hsup (by simp [Lir.Stmt.isCall]) ha hb hra hrb hpa hqb
    ?_ (hslow mem p q wa wb hpa hqb)
  intro hwa hwb
  let ρ₁ := ρl.insert (f0 + 1) (wa &&& wb)
  have ha1 : la.eval ρ₁ = some wa := by rw [arg_eval_temp hra (t := f0 + 1) (by omega)]; exact ha
  have hb1 : lb.eval ρ₁ = some wb := by rw [arg_eval_temp hrb (t := f0 + 1) (by omega)]; exact hb
  refine ⟨ρ₁.insert f0 (wa ||| wb), wa ||| wb, ?_,
    by simp [Lir.Arg.eval], .small (natLor_word hwa hwb), ?_⟩
  · change Lir.execList ρ₁ mem ctx _ = _
    simp [lir_eval, ha1, hb1]
  · intro y hy
    rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega)]

/-- **`natXorBig_core`:** Arbitrary-precision `Nat.xor` with ZERO `.natOverflow`. -/
theorem natXorBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} (hslow : SlowNatBinSpec lp ctx MemStep procs.xor (· ^^^ ·))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natXorBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natXor [la, lb] := by
  big_run at hrun
  subst hrun
  let f0 : Nat := st.fresh
  have hstEq : Ext C (BinFastSlowSt st 2 procs.xor x la lb
      [ .assign f0 (.bin .xor .w64 la lb)
      , .assign (f0 + 1) (.bin .or .w64 (.v f0) (.imm 1)) ] (.v (f0 + 1))) := hC
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hpa, hqb⟩ := natval_two hws hrel
  have hra := hreads la (by simp)
  have hrb := hreads lb (by simp)
  have hns : n = p ^^^ q := by
    have := sem_nat2 .natXor (by decide) p q
    rw [this] at hsem; cases hsem; rfl
  subst hns
  refine binFastSlow_run hrefl hF hH hstEq hl hsup (by simp [Lir.Stmt.isCall]) ha hb hra hrb hpa hqb
    ?_ (hslow mem p q wa wb hpa hqb)
  intro hwa hwb
  let ρ₁ := ρl.insert (f0 + 2) (wa &&& wb)
  let ρf := (ρ₁.insert f0 (wa ^^^ wb)).insert (f0 + 1) ((wa ^^^ wb) ||| 1)
  have ha1 : la.eval ρ₁ = some wa := by rw [arg_eval_temp hra (t := f0 + 2) (by omega)]; exact ha
  have hb1 : lb.eval ρ₁ = some wb := by rw [arg_eval_temp hrb (t := f0 + 2) (by omega)]; exact hb
  refine ⟨ρf, (wa ^^^ wb) ||| 1, ?_,
    by simp [Lir.Arg.eval, ρf], .small (natXor_word hwa hwb), ?_⟩
  · change Lir.execList ρ₁ mem ctx _ = _
    simp [lir_eval, ha1, hb1, ρf]
  · intro y hy
    rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega),
      Lir.env_insert_ne _ _ (by omega)]

/-- **`natBitBig_core`:** Unified arbitrary-precision bitwise theorem covering
`natLand`, `natLor`, and `natXor` with ZERO `.natOverflow`. -/
theorem natBitBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop}
    {procs : BigNatProcs} {tWord fWord : Word}
    (henv : SlowPathEnv lp ctx MemStep procs tWord fWord)
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {op : Lam.Prim} {la lb : Lir.Arg}
    (hop : op = .natLand ∨ op = .natLor ∨ op = .natXor)
    (hrun : (primitiveBig f { bools := some (tWord, fWord), procs } x op [la, lb]).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x op [la, lb] := by
  rcases hop with rfl | rfl | rfl
  · exact natLandBig_core henv.mem_refl henv.land hF hH hrun hC hl hsup
  · exact natLorBig_core henv.mem_refl henv.lor hF hH hrun hC hl hsup
  · exact natXorBig_core henv.mem_refl henv.xor hF hH hrun hC hl hsup

/-! ## Shifts (`natShrBig_core`, `natShlBig_core`, `natShiftBig_core`) -/

/-- **`natShrBig_core`:** Arbitrary-precision `Nat.shiftRight` with ZERO `.natOverflow`. -/
theorem natShrBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} (hslow : SlowNatBinSpec lp ctx MemStep procs.shr (fun a b => a / 2 ^ b))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natShrBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natShr [la, lb] := by
  big_run at hrun
  subst hrun
  let f0 : Nat := st.fresh
  have hstEq : Ext C (BinFastSlowSt st 4 procs.shr x la lb
      [ .assign f0 (.bin .shr .w64 lb (.imm 1))
      , .assign (f0 + 1) (.bin .shr .w64 la (.v f0))
      , .assign (f0 + 2) (.bin .or .w64 (.v (f0 + 1)) (.imm 1))
      , .assign (f0 + 3) (.select .ugt .w64 (.v f0) (.imm 63) (.imm 1) (.v (f0 + 2))) ]
      (.v (f0 + 3))) := hC
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hpa, hqb⟩ := natval_two hws hrel
  have hra := hreads la (by simp)
  have hrb := hreads lb (by simp)
  have hns : n = p / 2 ^ q := by
    have := sem_nat2 .natShr (by decide) p q
    rw [this] at hsem; cases hsem; rfl
  subst hns
  refine binFastSlow_run hrefl hF hH hstEq hl hsup (by simp [Lir.Stmt.isCall]) ha hb hra hrb hpa hqb
    ?_ (hslow mem p q wa wb hpa hqb)
  intro hwa hwb
  let ρ₁ := ρl.insert (f0 + 4) (wa &&& wb)
  let y := wb >>> (1 : Word)
  let s := wa >>> (y &&& 63)
  let r := s ||| 1
  let w := if (63 : Word) < y then (1 : Word) else r
  let ρf := (((ρ₁.insert f0 y).insert (f0 + 1) s).insert (f0 + 2) r).insert (f0 + 3) w
  have ha1 : la.eval ρ₁ = some wa := by rw [arg_eval_temp hra (t := f0 + 4) (by omega)]; exact ha
  have hb1 : lb.eval ρ₁ = some wb := by rw [arg_eval_temp hrb (t := f0 + 4) (by omega)]; exact hb
  have ha2 : la.eval (ρ₁.insert f0 y) = some wa := by
    rw [arg_eval_temp hra (t := f0) hsup]; exact ha1
  refine ⟨ρf, w, ?_, by simp [Lir.Arg.eval, ρf], .small (natShr_word hwa hwb), ?_⟩
  · change Lir.execList ρ₁ mem ctx _ = _
    have h1 : f0 + 2 ≠ f0 := by omega
    have h2 : f0 + 1 ≠ f0 := by omega
    simp only [lir_eval, hb1, ha2, h1, h2, ↓reduceIte, ρf, w, r, s, y]
  · intro z hz
    rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega),
      Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega),
      Lir.env_insert_ne _ _ (by omega)]

private theorem shl_check_zero {back t y : Word}
    (h : (((if back ≠ t then (1 : Word) else 0) ||| (if (63 : Word) < y then (1 : Word) else 0)) &&&
          (if t ≠ 0 then (1 : Word) else 0)) = 0) :
    (back = t ∧ ¬ (y > 63)) ∨ t = 0 := by
  by_cases ht : t = 0
  · exact Or.inr ht
  · left
    by_cases h1 : back = t <;> by_cases h2 : (63 : Word) < y <;>
      simp [ht, h1, h2] at h ⊢

/-- **`natShlBig_core`:** Arbitrary-precision `Nat.shiftLeft` with ZERO `.natOverflow`. -/
theorem natShlBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} (hslow : SlowNatBinSpec lp ctx MemStep procs.shl (fun a b => a * 2 ^ b))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natShlBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natShl [la, lb] := by
  big_run at hrun
  subst hrun
  let f0 : Nat := st.fresh
  let fastBody : List Lir.Stmt :=
    [ .assign (f0 + 1) (.bin .shr .w64 lb (.imm 1))
    , .assign (f0 + 2) (.bin .sub .w64 la (.imm 1))
    , .assign (f0 + 3) (.bin .shl .w64 (.v (f0 + 2)) (.v (f0 + 1)))
    , .assign (f0 + 4) (.bin .shr .w64 (.v (f0 + 3)) (.v (f0 + 1)))
    , .assign (f0 + 5) (.test .ne .w64 (.v (f0 + 4)) (.v (f0 + 2)))
    , .assign (f0 + 6) (.test .ugt .w64 (.v (f0 + 1)) (.imm 63))
    , .assign (f0 + 7) (.bin .or .w64 (.v (f0 + 5)) (.v (f0 + 6)))
    , .assign (f0 + 8) (.test .ne .w64 (.v (f0 + 2)) (.imm 0))
    , .assign (f0 + 9) (.bin .and .w64 (.v (f0 + 7)) (.v (f0 + 8))) ]
  have hstEq : Ext C (BinOvfSlowSt st procs.shl x la lb
      fastBody (.br .ne (.v (f0 + 9)) (.imm 0) (loc (st.next + 3)) (loc (st.next + 1)))
      [.assign (f0 + 10) (.bin .or .w64 (.v (f0 + 3)) (.imm 1))]
      (.v (f0 + 10)) (f0 + 11) (f0 + 12) (f0 + 13)) := hC
  obtain ⟨⟨lbk, hlb, hlbody, hlterm⟩, ⟨fb, hfb, hfp, hfbody, hfterm⟩,
    ⟨okb, hokb, hokp, hokbody, hokterm⟩, ⟨st1, hst1, hst1p, hst1body, hst1term⟩,
    ⟨st2, hst2, hst2p, hst2body, hst2term⟩, ⟨jb, hjb, hjp⟩⟩ := binOvfSlow_code hH hstEq hl
  simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hfterm
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hpa, hqb⟩ := natval_two hws hrel
  have hra := hreads la (by simp)
  have hrb := hreads lb (by simp)
  have hns : n = p * 2 ^ q := by
    have := sem_nat2 .natShl (by decide) p q
    rw [this] at hsem; cases hsem; rfl
  subst hns
  let ρ₁ := ρl.insert f0 (wa &&& wb)
  have hx1 : Lir.execList ρl mem ctx [.assign f0 (.bin .and .w64 la lb)] = some (ρ₁, mem) := by
    simp [lir_eval, ha, hb, ρ₁]
  have hstar1 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := st.acc.reverse) (post := [])
    hF hlb (by simpa using hlbody) (by simp [Lir.Stmt.isCall]) hx1
  simp only [List.length_reverse] at hstar1
  have hlpos : st.acc.length + 1 = lbk.body.size := by rw [← Array.length_toList, hlbody]; simp
  have ha1 : la.eval ρ₁ = some wa := by rw [arg_eval_temp hra (t := f0) hsup]; exact ha
  have hb1 : lb.eval ρ₁ = some wb := by rw [arg_eval_temp hrb (t := f0) hsup]; exact hb
  cases htz : Lir.Cond.holds .tz .w64 (wa &&& wb) 1 with
  | true =>
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁) (ρ' := ρ₁)
      (e := ⟨off + (st.next + 2), []⟩) (vals := []) (va := wa &&& wb) (vb := 1)
      hF hlb hlpos hlterm (by simp [Lir.Arg.eval, ρ₁, f0]) rfl (by simp [htz]) rfl
      hst1 (by simp [hst1p, Lir.bindParams])
    have hpre := hstar1.trans (Lir.star_of_step hbr)
    rcases exec_slow_block hF hst1 hst1body hst1term hjb hjp (by omega)
        (env_frame_temp (t := f0) hsup _) ha1 hb1 (hslow mem p q wa wb hpa hqb) with
      ⟨c, ρl', mem', w, hrunS, hm, hnv, hrx, hfr⟩ | hfail
    · exact Or.inl ⟨_, ρl', mem', w, hpre.trans hrunS, hm, hnv, hrx, hfr⟩
    · exact Or.inr (hfail.prepend hpre)
  | false =>
    obtain ⟨hwa, hwb⟩ := (NatVal.and_tz_one_false_iff hpa hqb).mp htz
    have hbr := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρ₁) (ρ' := ρ₁)
      (e := ⟨off + st.next, []⟩) (vals := []) (va := wa &&& wb) (vb := 1)
      hF hlb hlpos hlterm (by simp [Lir.Arg.eval, ρ₁, f0]) rfl (by simp [htz]) rfl
      hfb (by simp [hfp, Lir.bindParams])
    let yv := wb >>> (1 : Word)
    let tv := wa - 1
    let sv := tv <<< (yv &&& 63)
    let backv := sv >>> (yv &&& 63)
    let c1v : Word := if backv ≠ tv then 1 else 0
    let c2v : Word := if (63 : Word) < yv then 1 else 0
    let c3v := c1v ||| c2v
    let c4v : Word := if tv ≠ 0 then 1 else 0
    let cv := c3v &&& c4v
    let ρ₂ :=
      ((((((((ρ₁.insert (f0 + 1) yv).insert (f0 + 2) tv).insert (f0 + 3) sv).insert (f0 + 4) backv).insert
        (f0 + 5) c1v).insert (f0 + 6) c2v).insert (f0 + 7) c3v).insert (f0 + 8) c4v).insert (f0 + 9) cv
    have ha_ins : la.eval (ρ₁.insert (f0 + 1) yv) = some wa := by
      rw [arg_eval_temp hra (t := f0 + 1) (by omega)]; exact ha1
    have hx2 : Lir.execList ρ₁ mem ctx fastBody = some (ρ₂, mem) := by
      simp (disch := omega) only [fastBody, lir_eval, hb1, ha_ins, ite_eq_right, ↓reduceIte,
        ρ₂, yv, tv, sv, backv, c1v, c2v, c3v, c4v, cv]
    have hstar2 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
      hF hfb (by simpa using hfbody) (by simp [fastBody, Lir.Stmt.isCall]) hx2
    simp only [fastBody, List.length_nil, Nat.zero_add, List.length_cons, Nat.reduceAdd] at hstar2
    have hfpos : 9 = fb.body.size := by rw [← Array.length_toList, hfbody]; rfl
    have hfr2 : ∀ z, z < sup → ρ₂[z]? = ρl[z]? := by
      intro z hz
      simp only [ρ₂, ρ₁]
      repeat rw [Lir.env_insert_ne _ _ (by omega)]
    by_cases hcv : cv = 0
    · have hbrO := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 9)
        (ρ := ρ₂) (ρ' := ρ₂) (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := cv) (vb := 0)
        hF hfb hfpos hfterm.symm (by simp [Lir.Arg.eval, ρ₂]) rfl
        (by simp [lir_eval, hcv]) rfl hokb (by simp [hokp, Lir.bindParams])
      have hs3 : (Lir.Arg.v (f0 + 3)).eval ρ₂ = some sv := by
        simp (disch := omega) only [Lir.Arg.eval, ρ₂, Lir.env_insert_get, ite_eq_right, ↓reduceIte]
      let w := sv ||| 1
      let ρ₃ := ρ₂.insert (f0 + 10) w
      have hxok : Lir.execList ρ₂ mem ctx [.assign (f0 + 10) (.bin .or .w64 (.v (f0 + 3)) (.imm 1))] =
          some (ρ₃, mem) := by simp [lir_eval, hs3, ρ₃, w]
      have hstarOk := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
        hF hokb (by simpa using hokbody) (by simp [Lir.Stmt.isCall]) hxok
      simp only [List.length_nil, Nat.zero_add, List.length_singleton] at hstarOk
      have hokpos : 1 = okb.body.size := by rw [← Array.length_toList, hokbody]; simp
      have hjmp := Lir.jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 1)
        (ρ := ρ₃) (e := ⟨off + (st.next + 4), [.v (f0 + 10)]⟩) (vals := [w]) (ρ' := ρ₃.insert x w)
        hF hokb hokpos hokterm (by simp [Lir.evalArgs, Lir.Arg.eval, ρ₃]) hjb (by simp [hjp, Lir.bindParams])
      have hok := shl_check_zero hcv
      left
      refine ⟨_, ρ₃.insert x w, mem, w,
        hstar1.trans ((Lir.star_of_step hbr).trans (hstar2.trans
          ((Lir.star_of_step hbrO).trans (hstarOk.trans (Lir.star_of_step hjmp))))),
        hrefl mem, .small (natShl_word hwa hwb hok), by simp, ?_⟩
      intro z hz hzx
      rw [Lir.env_insert_ne _ _ (Ne.symm hzx), Lir.env_insert_ne _ _ (by omega)]
      exact hfr2 z hz
    · have hbrO := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 9)
        (ρ := ρ₂) (ρ' := ρ₂) (e := ⟨off + (st.next + 3), []⟩) (vals := []) (va := cv) (vb := 0)
        hF hfb hfpos hfterm.symm (by simp [Lir.Arg.eval, ρ₂]) rfl
        (by simp [lir_eval, hcv]) rfl hst2 (by simp [hst2p, Lir.bindParams])
      have hpre := hstar1.trans ((Lir.star_of_step hbr).trans (hstar2.trans (Lir.star_of_step hbrO)))
      have ha2 : la.eval ρ₂ = some wa := arg_eval_of_frame hra hfr2 ha
      have hb2 : lb.eval ρ₂ = some wb := arg_eval_of_frame hrb hfr2 hb
      rcases exec_slow_block hF hst2 hst2body hst2term hjb hjp (by omega)
          hfr2 ha2 hb2 (hslow mem p q wa wb hpa hqb) with
        ⟨c, ρl', mem', w, hrunS, hm, hnv, hrx, hfr⟩ | hfail
      · exact Or.inl ⟨_, ρl', mem', w, hpre.trans hrunS, hm, hnv, hrx, hfr⟩
      · exact Or.inr (hfail.prepend hpre)

/-- **`natShiftBig_core`:** Unified arbitrary-precision shift theorem covering
`natShl` and `natShr` with ZERO `.natOverflow`. -/
theorem natShiftBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop}
    {procs : BigNatProcs} {tWord fWord : Word}
    (henv : SlowPathEnv lp ctx MemStep procs tWord fWord)
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {op : Lam.Prim} {la lb : Lir.Arg}
    (hop : op = .natShl ∨ op = .natShr)
    (hrun : (primitiveBig f { bools := some (tWord, fWord), procs } x op [la, lb]).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x op [la, lb] := by
  rcases hop with rfl | rfl
  · exact natShlBig_core henv.mem_refl henv.shl hF hH hrun hC hl hsup
  · exact natShrBig_core henv.mem_refl henv.shr hF hH hrun hC hl hsup

/-! ## Procedure Calls (`natPowBig_core`, `natGcdBig_core`) -/

private theorem natProcCall_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop}
    {g : Lir.FunId} {op : Lam.Prim} {fnSpec : Nat → Nat → Nat}
    (hsemEq : ∀ p q, op.sem [p, q] = some (.nat (fnSpec p q)))
    (hspec : SlowNatBinSpec lp ctx MemStep g fnSpec)
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st : St} {x : Nat} {la lb : Lir.Arg}
    (hC : Ext C { st with acc := .call [x] g [la, lb] :: st.acc })
    (ho : Open st) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st.cur)
      (.call [x] g [la, lb] :: st.acc).length x op [la, lb] := by
  intro ρl mem rest ns ws n hws hrel _ hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hpa, hqb⟩ := natval_two hws hrel
  rw [hsemEq] at hsem
  cases hsem
  obtain ⟨lbk, post, hlb, -, hbody⟩ := holds_open hH [.call [x] g [la, lb]] st.fresh hC ho
  have hpos : st.acc.length < lbk.body.size := by rw [← Array.length_toList, hbody]; simp
  have hcall : lbk.body[st.acc.length] = .call [x] g [la, lb] := by
    rw [← Array.getElem_toList (h := hpos)]
    simp only [hbody]
    rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
    simp
  rcases call_procSpec (rest := rest) hF hlb hpos hcall (evalArgs_two_of ha hb)
      (hspec mem p q wa wb hpa hqb) with
    ⟨c, mem', w, hstar, hm, hnv⟩ | hfail
  · left
    refine ⟨c, ρl.insert x w, mem', w, hstar, hm, hnv, by simp, ?_⟩
    intro y _ hyx
    exact Lir.env_insert_ne _ _ (Ne.symm hyx)
  · exact Or.inr hfail

/-- **`natPowBig_core`:** Arbitrary-precision `Nat.pow` (calling `rt_nat_pow_big`,
proved via `natPowBig_proc_spec`) with ZERO `.natOverflow`. -/
theorem natPowBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop}
    {procs : BigNatProcs} (hspec : SlowNatBinSpec lp ctx MemStep procs.pow (· ^ ·))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natPowBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (ho : Open st) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natPow [la, lb] := by
  big_run at hrun
  subst hrun
  exact natProcCall_core (sem_nat2 .natPow (by decide)) hspec hF hH hC ho

/-- **`natPowBig_core` instantiated directly from `Rt.Procs.natPowBig slowPow`.** -/
theorem natPowBig_core_of_proc {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} {slowPow : Lir.FunId}
    (hpow : lp.funcs[procs.pow]? = some (Procs.natPowBig slowPow))
    (hslow : SlowNatBinSpec lp ctx MemStep slowPow (· ^ ·))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natPowBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (ho : Open st) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natPow [la, lb] :=
  natPowBig_core (natPowBig_proc_spec hrefl hpow hslow) hF hH hrun hC ho

/-- **`natGcdBig_core`:** Arbitrary-precision `Nat.gcd` (calling `rt_nat_gcd_big`,
proved via `natGcdBig_proc_spec`) with ZERO `.natOverflow`. -/
theorem natGcdBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop}
    {procs : BigNatProcs} (hspec : SlowNatBinSpec lp ctx MemStep procs.gcd Nat.gcd)
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natGcdBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (ho : Open st) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natGcd [la, lb] := by
  big_run at hrun
  subst hrun
  exact natProcCall_core (sem_nat2 .natGcd (by decide)) hspec hF hH hC ho

/-- **`natGcdBig_core` instantiated directly from `Rt.Procs.natGcdBig slowGcd`.** -/
theorem natGcdBig_core_of_proc {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {procs : BigNatProcs} {slowGcd : Lir.FunId}
    (hgcd : lp.funcs[procs.gcd]? = some (Procs.natGcdBig slowGcd))
    (hslow : SlowNatBinSpec lp ctx MemStep slowGcd Nat.gcd)
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {la lb : Lir.Arg}
    (hrun : (natGcdBig procs x la lb).run st = .ok ((), st'))
    (hC : Ext C st') (ho : Open st) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x .natGcd [la, lb] :=
  natGcdBig_core (natGcdBig_proc_spec hrefl hgcd hslow) hF hH hrun hC ho

/-! ## Top-Level Combined Theorem (`primitiveBig_core`) -/

/-- **Complete Phase 4 `Nat` primitive simulation (`primitiveBig_core`)**:
Every `Nat` primitive lowered by `Dispatch.primitiveBig` simulates exact arbitrary-precision
`Lam.Prim.sem` over unified `NatVal` / `BoolVal` words with **ZERO `.natOverflow`**! -/
theorem primitiveBig_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop}
    {procs : BigNatProcs} {tWord fWord : Word}
    (henv : SlowPathEnv lp ctx MemStep procs tWord fWord)
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {op : Lam.Prim} {las : List Lir.Arg}
    (hrun : (primitiveBig f { bools := some (tWord, fWord), procs } x op las).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (ho : Open st) (hsup : sup ≤ st.fresh) :
    PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
      x op las ∧
    PrimCoreBigBool lp ctx MemStep tWord fWord sup fn (off + st.cur) st.acc.length
      (off + st'.cur) st'.acc.length x op las := by
  have noBool : ∀ (hnb : ∀ ns b, op.sem ns ≠ some (.bool b)),
      PrimCoreBigBool lp ctx MemStep tWord fWord sup fn (off + st.cur) st.acc.length
        (off + st'.cur) st'.acc.length x op las := fun hnb _ _ _ ns _ b _ _ _ hs =>
    absurd hs (hnb ns b)
  have noNat : ∀ (hnn : ∀ ns n, op.sem ns ≠ some (.nat n)),
      PrimCoreBig lp ctx MemStep sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length
        x op las := fun hnn _ _ _ ns _ n _ _ _ hs =>
    absurd hs (hnn ns n)
  cases op <;> (rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩) <;>
    try (simp only [primitiveBig, throw, throwThe, MonadExceptOf.throw, StateT.run] at hrun; cases hrun; done)
  case natAdd =>
    exact ⟨natAddBig_core henv.mem_refl henv.add hF hH hrun hC hl hsup,
      noBool (sem_not_bool .natAdd (by decide))⟩
  case natSub =>
    exact ⟨natSubBig_core henv.mem_refl henv.sub hF hH hrun hC hl hsup,
      noBool (sem_not_bool .natSub (by decide))⟩
  case natPred =>
    exact ⟨natPredBig_core henv.mem_refl henv.pred hF hH hrun hC hl hsup,
      noBool (sem_not_bool .natPred (by decide))⟩
  case natMul =>
    exact ⟨natMulBig_core henv.mem_refl henv.mul hF hH hrun hC hl hsup,
      noBool (sem_not_bool .natMul (by decide))⟩
  case natDiv =>
    exact ⟨natDivBig_core henv.mem_refl henv.div hF hH hrun hC hl hsup,
      noBool (sem_not_bool .natDiv (by decide))⟩
  case natMod =>
    exact ⟨natModBig_core henv.mem_refl henv.mod hF hH hrun hC hl hsup,
      noBool (sem_not_bool .natMod (by decide))⟩
  case natPow =>
    exact ⟨natPowBig_core henv.pow hF hH hrun hC ho,
      noBool (sem_not_bool .natPow (by decide))⟩
  case natGcd =>
    exact ⟨natGcdBig_core henv.gcd hF hH hrun hC ho,
      noBool (sem_not_bool .natGcd (by decide))⟩
  case natBeq =>
    exact ⟨noNat (fun ns n h => by
        cases ns with
        | nil => simp [Lam.Prim.sem] at h
        | cons a ns => cases ns with
          | nil => simp [Lam.Prim.sem] at h
          | cons b ns => cases ns <;> simp [Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2] at h),
      natBeqBig_core henv.mem_refl henv.beq hF hH hrun hC hl hsup⟩
  case natBle =>
    exact ⟨noNat (fun ns n h => by
        cases ns with
        | nil => simp [Lam.Prim.sem] at h
        | cons a ns => cases ns with
          | nil => simp [Lam.Prim.sem] at h
          | cons b ns => cases ns <;> simp [Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2] at h),
      natBleBig_core henv.mem_refl henv.ble hF hH hrun hC hl hsup⟩
  case natBlt =>
    exact ⟨noNat (fun ns n h => by
        cases ns with
        | nil => simp [Lam.Prim.sem] at h
        | cons a ns => cases ns with
          | nil => simp [Lam.Prim.sem] at h
          | cons b ns => cases ns <;> simp [Lam.Prim.sem] at h),
      natBltBig_core henv.mem_refl henv.blt hF hH hrun hC hl hsup⟩
  case natLand =>
    exact ⟨natLandBig_core henv.mem_refl henv.land hF hH hrun hC hl hsup,
      noBool (sem_not_bool .natLand (by decide))⟩
  case natLor =>
    exact ⟨natLorBig_core henv.mem_refl henv.lor hF hH hrun hC hl hsup,
      noBool (sem_not_bool .natLor (by decide))⟩
  case natXor =>
    exact ⟨natXorBig_core henv.mem_refl henv.xor hF hH hrun hC hl hsup,
      noBool (sem_not_bool .natXor (by decide))⟩
  case natShl =>
    exact ⟨natShlBig_core henv.mem_refl henv.shl hF hH hrun hC hl hsup,
      noBool (sem_not_bool .natShl (by decide))⟩
  case natShr =>
    exact ⟨natShrBig_core henv.mem_refl henv.shr hF hH hrun hC hl hsup,
      noBool (sem_not_bool .natShr (by decide))⟩

end IxCC.Rt.BigNat
