import Compilatrix.Rt.Proof.Env
import Compilatrix.Rt.Proof.Alloc
import Compilatrix.Rt.Proof.Pow

/-!
# One lemma per instruction expansion

`RhsSim … L p L' p' x r`: the Lir code of a function between positions
`(L, p)` and `(L', p')` implements the Cfg instruction `x := r` (not a
call): from registers and memory related to a Cfg environment and heap, if
Cfg evaluates `r` to `v` (and heap `H'`), Lir runs from `(L, p)` to
`(L', p')` with `x` bound to a related word, the heap invariant kept for a
longer placement, and every other related register intact; or Lir fails
for a resource (`natOverflow`, `heap`).

The lemmas below establish `RhsSim` for the code `Rt.lower` emits:
`straight_sim` for statements emitted into the open block, `check_code`
for an expansion that ends its block with a check (a cold `fail` block and
a continuation), and per expansion the arithmetic of `Rt.Proof.Words`.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Lower
open Compilatrix.Src (NatMap)

/-- Cfg's tables, as `Rt.lower` reads them. -/
def ownTables (T : Tables) : Own.Tables := { ctors := T.ctors, known := T.known }

/-- The Lir code between `(L, p)` and `(L', p')` of function `fn`
implements `x := r`. -/
def RhsSim (T : Tables) (lp : Lir.Program) (ctx : Word) (D : Nat → Prop) (sup : Nat) (fn L p L' p' : Nat)
    (x : Nat) (r : Own.Rhs) : Prop :=
  ∀ (P : List Word) (H : Own.Heap) (ρ : Own.Env) (ρl : Lir.Env) (mem : X86.Memory) (rest : List Lir.Frame)
    (v : Own.RVal) (H' : Own.Heap),
    HeapInv T P H ctx mem → EnvRel T P D sup ρ ρl →
    Own.evalRhs .immortal (ownTables T) ρ H r = .ok (v, H') →
    (∃ c ρl' mem' P', Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn L p ρl rest) c
        (Lir.atState mem' ctx fn L' p' ρl' rest) ∧
      HeapInv T P' H' ctx mem' ∧ P <+: P' ∧ EnvRel T P' D sup (ρ.insert x v) ρl') ∨
    Sem.Fails (Lir.semStep lp) (Lir.atState mem ctx fn L p ρl rest)

/-! ## Running the lowering monad -/

theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

/-- Evaluate a run of the lowering monad to its final state. -/
macro "lower_run" " at " h:ident : tactic =>
  `(tactic| simp only [primitive, bin, temp, freshReg, assign, emit, untag, check, coldBlock, newLabel, close,
      openAt, put, retag, divMod, Lower.alloc, Lower.proj, StateT.run, bind, StateT.bind, pure, StateT.pure, modify,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet, Except.bind, Except.pure,
      Except.ok.injEq, Prod.mk.injEq, true_and, throw, throwThe, MonadExceptOf.throw, StateT.lift] at $h:ident)

/-! ## Cfg's side: inversions -/

theorem natArgs_two {va vb : Own.RVal} {ns : List Nat} (h : Own.natArgs [va, vb] = some ns) :
    ∃ p q, va = .lit (.nat p) ∧ vb = .lit (.nat q) ∧ ns = [p, q] := by
  cases va with
  | lit l =>
    cases l with
    | nat p =>
      cases vb with
      | lit l' =>
        cases l' with
        | nat q => simp [Own.natArgs] at h; exact ⟨p, q, rfl, rfl, h.symm⟩
        | str _ => simp [Own.natArgs] at h
      | _ => simp [Own.natArgs] at h
    | str _ => simp [Own.natArgs] at h
  | _ => simp [Own.natArgs] at h

theorem natArgs_one {va : Own.RVal} {ns : List Nat} (h : Own.natArgs [va] = some ns) :
    ∃ p, va = .lit (.nat p) ∧ ns = [p] := by
  cases va with
  | lit l =>
    cases l with
    | nat p => simp [Own.natArgs] at h; exact ⟨p, rfl, h.symm⟩
    | str _ => simp [Own.natArgs] at h
  | _ => simp [Own.natArgs] at h

/-- A primitive that Cfg evaluates: its arguments' values, and the
result. -/
theorem evalRhs_prim {T : Own.Tables} {ρ : Own.Env} {H H' : Own.Heap} {op : Lam.Prim} {as : List Fir.Arg}
    {v : Own.RVal} (h : Own.evalRhs .immortal T ρ H (.fir (.prim op as)) = .ok (v, H')) :
    H' = H ∧ ∃ vs, Own.evalArgs ρ as = some vs ∧ Own.primResult T op vs = .ok v := by
  simp only [Own.evalRhs] at h
  cases hv : Own.evalArgs ρ as with
  | none => simp [hv] at h
  | some vs =>
    simp only [hv] at h
    cases hr : Own.primResult T op vs with
    | ok w =>
      simp only [hr, Sem.Result.map, Sem.Result.bind, Sem.Result.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.2.symm, vs, rfl, by rw [hr, h.1]⟩
    | _ => simp [hr, Sem.Result.map, Sem.Result.bind] at h

/-- A binary primitive with a `Nat` result. -/
theorem primResult_nat2 {T : Own.Tables} {op : Lam.Prim} {va vb v : Own.RVal}
    (h : Own.primResult T op [va, vb] = .ok v) (hop : ∀ ns b, op.sem ns ≠ some (.bool b)) :
    ∃ p q n, va = .lit (.nat p) ∧ vb = .lit (.nat q) ∧ op.sem [p, q] = some (.nat n) ∧ v = .lit (.nat n) := by
  simp only [Own.primResult] at h
  cases hn : Own.natArgs [va, vb] with
  | none => simp [hn] at h
  | some ns =>
    obtain ⟨p, q, rfl, rfl, rfl⟩ := natArgs_two hn
    simp only [hn] at h
    cases hs : op.sem [p, q] with
    | none => simp [hs] at h
    | some r =>
      cases r with
      | nat n =>
        simp only [hs, Sem.Result.ok.injEq] at h
        exact ⟨p, q, n, rfl, rfl, hs, h.symm⟩
      | bool b => exact absurd hs (hop _ b)

/-! ## Code in the open block -/

/-- Statements emitted into the open block run as a `Star` with no charge. -/
theorem straight_star {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st : St} {ss : List Lir.Stmt} {f' : Nat} (hC : Ext C { st with acc := ss.reverse ++ st.acc, fresh := f' })
    (ho : Open st) (hnc : ∀ s ∈ ss, s.isCall = false) {ctx : Word} {mem : X86.Memory} {ρl ρl' : Lir.Env}
    {rest : List Lir.Frame} (hx : Lir.execList ρl mem ctx ss = some (ρl', mem)) :
    Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) 0
      (Lir.atState mem ctx fn (off + st.cur) (ss.reverse ++ st.acc).length ρl' rest) := by
  obtain ⟨lb, post, hlb, -, hbody⟩ := holds_open hH ss f' hC ho
  have := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := st.acc.reverse) (post := post) hF hlb
    hbody hnc hx
  simpa [Nat.add_comm] using this

/-- An expansion of local statements that keep the heap and memory. -/
theorem straight_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss : List Lir.Stmt} {f' : Nat}
    (hC : Ext C { st with acc := ss.reverse ++ st.acc, fresh := f' }) (ho : Open st)
    (hnc : ∀ s ∈ ss, s.isCall = false) {x : Nat} {r : Own.Rhs}
    (hsem : ∀ (P : List Word) (H : Own.Heap) (ρ : Own.Env) (ρl : Lir.Env) (mem : X86.Memory) (v : Own.RVal)
        (H' : Own.Heap), EnvRel T P D sup ρ ρl → Own.evalRhs .immortal (ownTables T) ρ H r = .ok (v, H') →
        H' = H ∧ ∃ ρl', Lir.execList ρl mem ctx ss = some (ρl', mem) ∧ EnvRel T P D sup (ρ.insert x v) ρl') :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st.cur) (ss.reverse ++ st.acc).length x r := by
  intro P H ρ ρl mem rest v H' hheap hρ hr
  obtain ⟨rfl, ρl', hx, hρ'⟩ := hsem P H ρ ρl mem v H' hρ hr
  exact .inl ⟨0, ρl', mem, P, straight_star hF hH hC ho hnc hx, hheap, List.prefix_refl _, hρ'⟩

/-! ## Binary primitives: the operands -/

/-- What a binary `Nat` primitive's expansion starts from: Cfg's values are
`Nat` literals `p`, `q`, the result `n`, and the lowered operands evaluate
to their words. -/
structure Bin2 (T : Tables) (P : List Word) (sup : Nat) (ρl : Lir.Env) (op : Lam.Prim) (la lb : Lir.Arg)
    (v : Own.RVal) : Prop where
  ex : ∃ p q n wa wb, la.eval ρl = some wa ∧ lb.eval ρl = some wb ∧ natWord p = some wa ∧ natWord q = some wb ∧
    op.sem [p, q] = some (.nat n) ∧ v = .lit (.nat n) ∧ ArgReads sup la ∧ ArgReads sup lb

theorem bin2_of {T : Tables} {P : List Word} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
    (hρ : EnvRel T P D sup ρ ρl) {f : Fir.FunId} {as : List Fir.Arg} {la lb : Lir.Arg}
    (hops : operands f as = .ok (some [la, lb])) (hlive : ∀ a ∈ as, LiveArg D a) {op : Lam.Prim}
    (hop : ∀ ns b, op.sem ns ≠ some (.bool b)) {H H' : Own.Heap} {v : Own.RVal}
    (hr : Own.evalRhs .immortal (ownTables T) ρ H (.fir (.prim op as)) = .ok (v, H')) :
    H' = H ∧ Bin2 T P sup ρl op la lb v := by
  obtain ⟨rfl, vs, hvs, hres⟩ := evalRhs_prim hr
  obtain ⟨ws, hws, hrel, hreads⟩ := operands_rel hρ hops hlive hvs
  simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, Option.bind_eq_bind] at hws
  cases ha : la.eval ρl with
  | none => simp [ha] at hws
  | some wa =>
    cases hb : lb.eval ρl with
    | none => simp [ha, hb] at hws
    | some wb =>
      simp [ha, hb] at hws
      subst hws
      rcases hrel with _ | ⟨hva, hrel'⟩
      rcases hrel' with _ | ⟨hvb, hnil⟩
      rcases hnil
      obtain ⟨p, q, n, rfl, rfl, hsem, rfl⟩ := primResult_nat2 hres hop
      exact ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hva, hvb, hsem, rfl, hreads la (by simp),
        hreads lb (by simp)⟩⟩

theorem sem_not_bool_sub (ns : List Nat) (b : Bool) : Lam.Prim.sem .natSub ns ≠ some (.bool b) := by
  intro h
  match ns with
  | [_, _] => simp [Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2] at h
  | [] | [_] | _ :: _ :: _ :: _ => simp [Lam.Prim.sem] at h

/-! ## `natSub` -/

theorem prim_natSub {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natSub [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natSub as)) := by
  lower_run at hrun
  subst hrun
  apply straight_sim (ss := [.assign st.fresh (.bin .sub .w64 la lb),
      .assign (st.fresh + 1) (.bin .or .w64 (.v st.fresh) (.imm 1)),
      .assign x (.select .ult .w64 la lb (.imm 1) (.v (st.fresh + 1)))]) hF hH hC ho (by simp [Lir.Stmt.isCall])
  intro P H ρ ρl mem v H' hρ hr
  obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hsem, rfl, hra, hrb⟩⟩ :=
    bin2_of hρ hops hlive (sem_not_bool_sub) hr
  have hn : n = p - q := by
    simp [Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2] at hsem; omega
  subst hn
  refine ⟨rfl, ((ρl.insert st.fresh (wa - wb)).insert (st.fresh + 1) ((wa - wb) ||| 1)).insert x
    (if wa < wb then 1 else (wa - wb) ||| 1), ?_, ?_⟩
  · simp only [lir_eval, ha, hb, arg_eval_temp hra (t := st.fresh) hsup, arg_eval_temp hrb (t := st.fresh) hsup,
      arg_eval_temp hra (t := st.fresh + 1) (by omega), arg_eval_temp hrb (t := st.fresh + 1) (by omega),
      ↓reduceIte, Nat.add_one_ne_zero]
  · exact ((hρ.temp hsup _).temp (by omega) _).insert hx (by
      show natWord (p - q) = some _
      rw [natSub_word hwa hwb])

/-- The `Nat`-valued binary primitives' meanings. -/
theorem sem_nat2 (op : Lam.Prim) (hop : op ≠ .natBeq ∧ op ≠ .natBle ∧ op ≠ .natBlt ∧ op ≠ .natPred) (p q : Nat) :
    op.sem [p, q] = some (.nat (match op with
      | .natAdd => p + q | .natSub => p - q | .natMul => p * q
      | .natDiv => if q = 0 then 0 else p / q | .natMod => if q = 0 then p else p % q
      | .natPow => p ^ q | .natGcd => Nat.gcd p q | .natLand => p &&& q | .natLor => p ||| q
      | .natXor => p ^^^ q | .natShl => p * 2 ^ q | .natShr => p / 2 ^ q
      | _ => 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hop
  cases op <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 |
    simp [Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2, shiftRight_eval]

theorem sem_not_bool (op : Lam.Prim) (hop : op ≠ .natBeq ∧ op ≠ .natBle ∧ op ≠ .natBlt) (ns : List Nat)
    (b : Bool) : op.sem ns ≠ some (.bool b) := by
  obtain ⟨h1, h2, h3⟩ := hop
  intro h
  match ns with
  | [] => cases op <;> simp [Lam.Prim.sem] at h
  | [_] => cases op <;> simp [Lam.Prim.sem, Src.PrimOp.eval2] at h
  | [_, _] => cases op <;> simp_all [Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2]
  | _ :: _ :: _ :: _ => cases op <;> simp [Lam.Prim.sem] at h

/-- The common shape of a binary primitive's simulation: given the
expansion's statements and final register file, `RhsSim` follows from the
word of the result. -/
theorem prim2_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss : List Lir.Stmt} {f' : Nat}
    (hC : Ext C { st with acc := ss.reverse ++ st.acc, fresh := f' }) (ho : Open st)
    (hnc : ∀ s ∈ ss, s.isCall = false) (hsup : sup ≤ st.fresh) {x : Nat} (hx : x < sup) {la lb : Lir.Arg}
    {as : List Fir.Arg} (hops : operands f as = .ok (some [la, lb])) (hlive : ∀ a ∈ as, LiveArg D a)
    {op : Lam.Prim} (hop : op ≠ .natBeq ∧ op ≠ .natBle ∧ op ≠ .natBlt ∧ op ≠ .natPred) (g : Nat → Nat → Nat)
    (hg : ∀ p q, op.sem [p, q] = some (.nat (g p q)))
    (hexec : ∀ (ρl : Lir.Env) (mem : X86.Memory) (p q : Nat) (wa wb : Word), la.eval ρl = some wa →
      lb.eval ρl = some wb → natWord p = some wa → natWord q = some wb → ArgReads sup la → ArgReads sup lb →
      ∃ ρl' w, Lir.execList ρl mem ctx ss = some (ρl', mem) ∧ natWord (g p q) = some w ∧ ρl'[x]? = some w ∧
        ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st.cur) (ss.reverse ++ st.acc).length x
      (.fir (.prim op as)) := by
  apply straight_sim hF hH hC ho hnc
  intro P H ρ ρl mem v H' hρ hr
  obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hsem, rfl, hra, hrb⟩⟩ :=
    bin2_of hρ hops hlive (sem_not_bool op ⟨hop.1, hop.2.1, hop.2.2.1⟩) hr
  rw [hg] at hsem
  cases hsem
  obtain ⟨ρl', w, hx', hw, hρx, hρy⟩ := hexec ρl mem p q wa wb ha hb hwa hwb hra hrb
  refine ⟨rfl, ρl', hx', ?_, ?_⟩
  · intro y v' hy
    rw [Src.NatMap.get?_insert] at hy
    split at hy
    · omega
    · exact hρ.dom hy
  · intro y v' hy hD
    rw [Src.NatMap.get?_insert] at hy
    split at hy
    · rename_i hyx
      subst hyx
      cases hy
      exact ⟨w, hρx, hw⟩
    · rename_i hyx
      obtain ⟨w', hw', hv'⟩ := hρ.val hy hD
      exact ⟨w', by rw [hρy y (hρ.dom hy) hyx]; exact hw', hv'⟩

/-- Lookups of registers below the supply through temporaries and `x`. -/
macro "regs_ne" : tactic =>
  `(tactic| ((simp only [Lir.env_insert_get]; repeat' split) <;> first | rfl | (exfalso; omega)))

/-! ## `natLand`, `natLor`, `natXor` -/

theorem prim_natLand {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natLand [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natLand as)) := by
  lower_run at hrun
  subst hrun
  refine prim2_sim (ss := [.assign x (.bin .and .w64 la lb)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
    hlive (by decide) (· &&& ·) (sem_nat2 _ (by decide)) ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ _
  exact ⟨ρl.insert x (wa &&& wb), wa &&& wb, by simp only [lir_eval, ha, hb], natLand_word hwa hwb, by simp,
    fun y hy hyx => by regs_ne⟩

theorem prim_natLor {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natLor [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natLor as)) := by
  lower_run at hrun
  subst hrun
  refine prim2_sim (ss := [.assign x (.bin .or .w64 la lb)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
    hlive (by decide) (· ||| ·) (sem_nat2 _ (by decide)) ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ _
  exact ⟨ρl.insert x (wa ||| wb), wa ||| wb, by simp only [lir_eval, ha, hb], natLor_word hwa hwb, by simp,
    fun y hy hyx => by regs_ne⟩

theorem prim_natXor {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natXor [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natXor as)) := by
  lower_run at hrun
  subst hrun
  refine prim2_sim (ss := [.assign st.fresh (.bin .xor .w64 la lb),
      .assign x (.bin .or .w64 (.v st.fresh) (.imm 1))]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
    hlive (by decide) (· ^^^ ·) (sem_nat2 _ (by decide)) ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ _
  exact ⟨(ρl.insert st.fresh (wa ^^^ wb)).insert x ((wa ^^^ wb) ||| 1), (wa ^^^ wb) ||| 1,
    by simp only [lir_eval, ha, hb, ↓reduceIte], natXor_word hwa hwb, by simp, fun y hy hyx => by regs_ne⟩

/-! ## Comparisons -/

/-- `Rt.lower`'s `Bool` words are those of the pinned constructors, as the
table has them, outside `Nat`'s keys and within the tag limit
(`Lower.tables`). -/
def BoolsOk (T : Tables) : Prop :=
  ∀ t e, T.bools = some (t, e) →
    (∃ k c, T.known.boolTrue = some k ∧ Fir.CtorInfo.ofKey T.ctors k = some c ∧ isNatKey T k = false ∧
      c.tag ≤ maxTag ∧ t = ctor0Word c.tag) ∧
    (∃ k c, T.known.boolFalse = some k ∧ Fir.CtorInfo.ofKey T.ctors k = some c ∧ isNatKey T k = false ∧
      c.tag ≤ maxTag ∧ e = ctor0Word c.tag)

theorem ofKey_key {table : List Lam.CtorInfo} {k : Key.CtorKey} {c : Fir.CtorInfo}
    (h : Fir.CtorInfo.ofKey table k = some c) : c.key = k := by
  unfold Fir.CtorInfo.ofKey at h
  cases hf : table.find? (·.key == k) with
  | none => simp [hf] at h
  | some r => simp only [hf, Option.map_some, Option.some.injEq] at h; subst h; rfl

theorem tables_boolsOk (P : Cfg.Program) : BoolsOk (tables P) := by
  intro t e h
  simp only [tables] at h
  split at h
  · rename_i t' e' ht he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have word : ∀ (k : Option Key.CtorKey) (w : Word),
        (k.bind fun k => if P.known.natZero == some k || P.known.natSucc == some k then none
          else (Fir.CtorInfo.ofKey P.ctors k).bind fun c => if c.tag ≤ maxTag then some (ctor0Word c.tag) else none) =
          some w →
        ∃ k' c, k = some k' ∧ Fir.CtorInfo.ofKey P.ctors k' = some c ∧ isNatKey (tables P) k' = false ∧
          c.tag ≤ maxTag ∧ w = ctor0Word c.tag := by
      intro k w hw
      cases k with
      | none => simp at hw
      | some k =>
        simp only [Option.bind_some] at hw
        split at hw
        · simp at hw
        · rename_i hnat
          cases hc : Fir.CtorInfo.ofKey P.ctors k with
          | none => simp [hc] at hw
          | some c =>
            simp only [hc, Option.bind_some] at hw
            split at hw
            · rename_i htag
              simp only [Option.some.injEq] at hw
              exact ⟨k, c, rfl, hc, by simpa [isNatKey, tables] using hnat, htag, hw.symm⟩
            · simp at hw
    exact ⟨word _ _ ht, word _ _ he⟩
  · simp at h

theorem compareOf_cases {op : Lam.Prim} {c : Lir.Cond} (h : compareOf op = some c) :
    (op = .natBeq ∧ c = .eq) ∨ (op = .natBle ∧ c = .ule) ∨ (op = .natBlt ∧ c = .ult) := by
  cases op <;> simp [compareOf] at h <;> subst h <;> simp

/-- A comparison's meaning, and the Lir condition that decides it. -/
theorem cmp_sem {op : Lam.Prim} {c : Lir.Cond} (h : compareOf op = some c) {p q : Nat} {wa wb : Word}
    (hwa : natWord p = some wa) (hwb : natWord q = some wb) :
    op.sem [p, q] = some (.bool (c.holds .w64 wa wb)) := by
  rcases compareOf_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2, Lir.holds_eq, natWord_eq_iff hwa hwb]
    cases hpq : (p == q) <;> simp_all
  · simp only [Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2, Lir.holds_ule, natWord_le_iff hwa hwb]
  · simp only [Lam.Prim.sem, Lir.holds_ult, natWord_lt_iff hwa hwb]

/-- A comparison's `Bool` result relates to the word `Rt.lower` selects. -/
theorem bool_rel {T : Tables} (hT : BoolsOk T) {t e : Word} (hte : T.bools = some (t, e)) {P : List Word}
    {b : Bool} {v : Own.RVal}
    (hv : (match (if b then T.known.boolTrue else T.known.boolFalse) with
      | some c => Sem.Result.ofOption (Own.ctor0Of (ownTables T) c)
      | none => .stuck) = .ok v) :
    ValRel T P v (if b then t else e) := by
  obtain ⟨⟨kt, ct, hkt, hct, hnt, htt, rfl⟩, ⟨kf, cf, hkf, hcf, hnf, htf, rfl⟩⟩ := hT t e hte
  cases b with
  | true =>
    simp only [↓reduceIte, hkt, Own.ctor0Of, ownTables, hct] at hv
    split at hv
    · rename_i hfl
      simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hv
      subst hv
      exact ⟨rfl, ⟨by rw [ofKey_key hct]; exact hct, by rw [ofKey_key hct]; exact hnt, htt⟩, hfl⟩
    · simp [Sem.Result.ofOption] at hv
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, hkf, Own.ctor0Of, ownTables, hcf] at hv
    split at hv
    · rename_i hfl
      simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hv
      subst hv
      exact ⟨rfl, ⟨by rw [ofKey_key hcf]; exact hcf, by rw [ofKey_key hcf]; exact hnf, htf⟩, hfl⟩
    · simp [Sem.Result.ofOption] at hv

theorem prim_cmp {T : Tables} (hT : BoolsOk T) {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop}
    {sup : Nat} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg}
    {as : List Fir.Arg} {op : Lam.Prim} {c : Lir.Cond} (hc : compareOf op = some c)
    (hrun : (primitive f T x op [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hx : x < sup) (hops : operands f as = .ok (some [la, lb])) (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim op as)) := by
  cases hte : T.bools with
  | none =>
    rcases compareOf_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · lower_run at hrun
      simp [hte, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, Functor.map, Except.map] at hrun
  | some te =>
    obtain ⟨t, e⟩ := te
    have hrun' : st' = { st with
        acc := [.assign x (.select c .w64 la lb (.imm t) (.imm e))].reverse ++ st.acc, fresh := st.fresh } := by
      rcases compareOf_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · lower_run at hrun
        simp only [hte] at hrun
        lower_run at hrun
        exact hrun.symm
    subst hrun'
    apply straight_sim hF hH hC ho (by simp [Lir.Stmt.isCall])
    intro P H ρ ρl mem v H' hρ hr
    obtain ⟨rfl, vs, hvs, hres⟩ := evalRhs_prim hr
    obtain ⟨ws, hws, hrel, hreads⟩ := operands_rel hρ hops hlive hvs
    simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, Option.bind_eq_bind] at hws
    cases ha : la.eval ρl with
    | none => simp [ha] at hws
    | some wa =>
      cases hb : lb.eval ρl with
      | none => simp [ha, hb] at hws
      | some wb =>
        simp [ha, hb] at hws
        subst hws
        rcases hrel with _ | ⟨hva, hrel'⟩
        rcases hrel' with _ | ⟨hvb, hnil⟩
        rcases hnil
        rename_i va vb
        simp only [Own.primResult] at hres
        cases hn : Own.natArgs [va, vb] with
        | none => simp [hn] at hres
        | some ns =>
          obtain ⟨p, q, rfl, rfl, rfl⟩ := natArgs_two hn
          simp only [hn] at hres
          rw [cmp_sem hc hva hvb] at hres
          refine ⟨rfl, ρl.insert x (if c.holds .w64 wa wb then t else e), ?_, ?_⟩
          · rcases compareOf_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              simp only [lir_eval, ha, hb, ↓reduceIte]
          · exact hρ.insert hx (bool_rel hT hte hres)

/-! ## `natPred` -/

theorem prim_natPred {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natPred [la]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natPred as)) := by
  lower_run at hrun
  subst hrun
  apply straight_sim (ss := [.assign st.fresh (.bin .sub .w64 la (.imm 2)),
      .assign x (.select .eq .w64 la (.imm 1) (.imm 1) (.v st.fresh))]) hF hH hC ho (by simp [Lir.Stmt.isCall])
  intro P H ρ ρl mem v H' hρ hr
  obtain ⟨rfl, vs, hvs, hres⟩ := evalRhs_prim hr
  obtain ⟨ws, hws, hrel, hreads⟩ := operands_rel hρ hops hlive hvs
  simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, Option.bind_eq_bind] at hws
  cases ha : la.eval ρl with
  | none => simp [ha] at hws
  | some wa =>
    simp [ha] at hws
    subst hws
    rcases hrel with _ | ⟨hva, hnil⟩
    rcases hnil
    rename_i va
    simp only [Own.primResult] at hres
    cases hn : Own.natArgs [va] with
    | none => simp [hn] at hres
    | some ns =>
      obtain ⟨p, rfl, rfl⟩ := natArgs_one hn
      simp only [hn, Lam.Prim.sem, Src.PrimOp.eval2, Sem.Result.ok.injEq] at hres
      subst hres
      have hra := hreads la (by simp)
      refine ⟨rfl, (ρl.insert st.fresh (wa - 2)).insert x (if wa = 1 then 1 else wa - 2), ?_, ?_⟩
      · simp only [lir_eval, ha, arg_eval_temp hra (t := st.fresh) hsup, ↓reduceIte]
      · exact (hρ.temp hsup _).insert hx (natPred_word hva)

/-! ## `natShr` -/

theorem prim_natShr {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natShr [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natShr as)) := by
  cases lb with
  | v yb =>
    lower_run at hrun
    subst hrun
    refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 (.v yb) (.imm 1)),
        .assign (st.fresh + 1) (.bin .shr .w64 la (.v st.fresh)),
        .assign (st.fresh + 1 + 1) (.bin .or .w64 (.v (st.fresh + 1)) (.imm 1)),
        .assign x (.select .ugt .w64 (.v st.fresh) (.imm 63) (.imm 1) (.v (st.fresh + 1 + 1)))])
      hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide) (fun p q => p / 2 ^ q)
      (sem_nat2 _ (by decide)) ?_
    intro ρl mem p q wa wb ha hb hwa hwb hra _
    have hb' : ρl[yb]? = some wb := hb
    refine ⟨(((ρl.insert st.fresh (wb >>> 1)).insert (st.fresh + 1) (wa >>> ((wb >>> 1) &&& 63))).insert
        (st.fresh + 1 + 1) ((wa >>> ((wb >>> 1) &&& 63)) ||| 1)).insert x
        (if (63 : Word) < wb >>> 1 then (1 : Word) else (wa >>> ((wb >>> 1) &&& 63)) ||| 1),
      (if (63 : Word) < wb >>> 1 then (1 : Word) else (wa >>> ((wb >>> 1) &&& 63)) ||| 1), ?_, natShr_word hwa hwb, by simp,
      fun y hy hyx => by regs_ne⟩
    simp (disch := omega) only [lir_eval, hb', ha, arg_eval_temp hra (t := st.fresh) hsup, ↓reduceIte, if_neg]
  | imm wbi =>
    lower_run at hrun
    subst hrun
    refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 la (.imm (wbi >>> 1))),
        .assign (st.fresh + 1) (.bin .or .w64 (.v st.fresh) (.imm 1)),
        .assign x (.select .ugt .w64 (.imm (wbi >>> 1)) (.imm 63) (.imm 1) (.v (st.fresh + 1)))])
      hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide) (fun p q => p / 2 ^ q)
      (sem_nat2 _ (by decide)) ?_
    intro ρl mem p q wa wb ha hb hwa hwb hra _
    simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
    subst hb
    refine ⟨((ρl.insert st.fresh (wa >>> ((wbi >>> 1) &&& 63))).insert
        (st.fresh + 1) ((wa >>> ((wbi >>> 1) &&& 63)) ||| 1)).insert x
        (if (63 : Word) < wbi >>> 1 then (1 : Word) else (wa >>> ((wbi >>> 1) &&& 63)) ||| 1),
      (if (63 : Word) < wbi >>> 1 then (1 : Word) else (wa >>> ((wbi >>> 1) &&& 63)) ||| 1), ?_, natShr_word hwa hwb, by simp,
      fun y hy hyx => by regs_ne⟩
    simp (disch := omega) only [lir_eval, ha, ↓reduceIte, if_neg]

end Compilatrix.Rt.Proof
