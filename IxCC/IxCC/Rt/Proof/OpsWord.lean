import IxCC.Rt.Proof.Check
import IxCC.Rt.Proof.OpsDiv
import IxCC.Rt.Proof.WordArith
import IxCC.Lam.WordSem

/-!
# The fixed-width word primitives' expansions (stage W1)

`prim_word`: the code `Rt.Lower.word` emits for `Lam.Prim.word w op` implements Cfg's primitive
(`RhsSim`), or fails with `natOverflow` (width 64, a result at or above `2^63`).

* `div`, `mod`, `land`, `lor`, `xor` emit the `Nat` primitives' code, and wherever the word
  primitive returns a number the `Nat` primitive returns the same one, so their simulations
  transfer (`rhsSim_of_nat`).
* Every other operation: its statements run straight (`word2_sim`, `word1_sim`), or, at width
  64, up to a check on the untagged result (`word2_checked_sim`, `word1_checked_sim`); the
  arithmetic is `Rt.Proof.WordArith`'s.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap Width WordOp)

/-- Evaluate a run of a word expansion to its final state. -/
macro "word_run" " at " h:ident : tactic =>
  `(tactic| simp only [primitive, Lower.word, word64, wordNarrow, wordCount, checked64, bin, temp, freshReg, assign,
      emit, untag, check, coldBlock, newLabel, close, openAt, put, retag, divMod, StateT.run, bind, StateT.bind, pure,
      StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet, Except.bind,
      Except.pure, Except.ok.injEq, Prod.mk.injEq, true_and, throw, throwThe, MonadExceptOf.throw, StateT.lift,
      ↓reduceIte, eq_self_iff_true, if_true, if_false] at $h:ident)

/-- A word primitive with no expansion (a decision, an arity mismatch) never runs to a state. -/
macro "word_bad" : tactic =>
  `(tactic| (simp only [primitive, Lower.word, word64, wordNarrow] at *; (try split at *) <;>
      simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.bind, StateT.run] at *))

theorem envRel_frame {T : Tables} {P : List Word} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env}
    {ρl ρl' : Lir.Env} (h : EnvRel T P D sup ρ ρl) (hf : ∀ y, y < sup → ρl'[y]? = ρl[y]?) :
    EnvRel T P D sup ρ ρl' where
  dom := h.dom
  val := by
    intro y v hy hD
    obtain ⟨w, hw, hv⟩ := h.val hy hD
    exact ⟨w, by rw [hf y (h.dom hy)]; exact hw, hv⟩

/-- The relation after an expansion: `x` bound to the word of the new value, every other register
below the supply as before. -/
theorem envRel_insert_frame {T : Tables} {P : List Word} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env}
    {ρl ρl' : Lir.Env} (h : EnvRel T P D sup ρ ρl) {x : Nat} (hx : x < sup) {w : Word} {n : Nat}
    (hρx : ρl'[x]? = some w) (hw : natWord n = some w) (hρy : ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) :
    EnvRel T P D sup (ρ.insert x (.lit (.nat n))) ρl' where
  dom := by
    intro y v' hy
    rw [Src.NatMap.get?_insert] at hy
    split at hy
    · omega
    · exact h.dom hy
  val := by
    intro y v' hy hD
    rw [Src.NatMap.get?_insert] at hy
    split at hy
    · rename_i hyx
      subst hyx
      cases hy
      exact ⟨w, hρx, hw⟩
    · rename_i hyx
      obtain ⟨w', hw', hv'⟩ := h.val hy hD
      exact ⟨w', by rw [hρy y (h.dom hy) hyx]; exact hw', hv'⟩

theorem retag_val (u : Word) : u + u * X86.Scale.one.word + Lir.dispWord 1 = u + u + 1 := by
  rw [show X86.Scale.one.word = 1 from rfl, show Lir.dispWord 1 = 1 from rfl, UInt64.mul_one]

/-! ## Cfg's side -/

/-- A binary word primitive that Cfg evaluates: tagged operands of numbers in range, and
`eval`'s number. -/
theorem word2_of {T : Tables} {P : List Word} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
    (hρ : EnvRel T P D sup ρ ρl) {f : Fir.FunId} {as : List Fir.Arg} {la lb : Lir.Arg}
    (hops : operands f as = .ok (some [la, lb])) (hlive : ∀ a ∈ as, LiveArg D a) {w : Width} {op : WordOp}
    {H H' : Own.Heap} {v : Own.RVal}
    (hr : Own.evalRhs .immortal (ownTables T) ρ H (.fir (.prim (.word w op) as)) = .ok (v, H')) :
    H' = H ∧ ∃ p q wa wb, la.eval ρl = some wa ∧ lb.eval ρl = some wb ∧ natWord p = some wa ∧
      natWord q = some wb ∧ p < w.size ∧ q < w.size ∧ v = .lit (.nat (op.eval w p q).val) ∧
      ArgReads sup la ∧ ArgReads sup lb := by
  obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, hra, hrb⟩⟩ :=
    bin2_of (op := .word w op) hρ hops hlive (fun ns b => Lam.wordSem_ne_bool w op ns b) hr
  rw [Lam.Prim.sem_word] at hs
  obtain ⟨-, -, hp, hq, rfl⟩ := Lam.wordSem_two hs
  exact ⟨rfl, p, q, wa, wb, ha, hb, hwa, hwb, hp, hq, rfl, hra, hrb⟩

/-- A unary word primitive that Cfg evaluates. -/
theorem word1_of {T : Tables} {P : List Word} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
    (hρ : EnvRel T P D sup ρ ρl) {f : Fir.FunId} {as : List Fir.Arg} {la : Lir.Arg}
    (hops : operands f as = .ok (some [la])) (hlive : ∀ a ∈ as, LiveArg D a) {w : Width} {op : WordOp}
    {H H' : Own.Heap} {v : Own.RVal}
    (hr : Own.evalRhs .immortal (ownTables T) ρ H (.fir (.prim (.word w op) as)) = .ok (v, H')) :
    H' = H ∧ ∃ p wa, la.eval ρl = some wa ∧ natWord p = some wa ∧ (op = .ofNat ∨ p < w.size) ∧
      v = .lit (.nat (op.eval w p 0).val) ∧ ArgReads sup la := by
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
      simp only [hn] at hres
      cases hs : (Lam.Prim.word w op).sem [p] with
      | none => simp [hs] at hres
      | some r =>
        cases r with
        | nat n =>
          simp only [hs, Sem.Result.ok.injEq] at hres
          rw [Lam.Prim.sem_word] at hs
          obtain ⟨-, -, hp, rfl⟩ := Lam.wordSem_one hs
          exact ⟨rfl, p, wa, rfl, hva, hp, hres.symm, hreads la (by simp)⟩
        | bool b => exact absurd hs (Lam.wordSem_ne_bool w op [p] b)

/-! ## Generic simulations -/

/-- **The `Nat` code transfers**: where the word primitive returns a number, the `Nat`
primitive `nop` returns the same one, so the code of `nop` implements the word primitive. -/
theorem rhsSim_of_nat {T : Tables} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup fn L p L' p' x : Nat}
    {as : List Fir.Arg} {w : Width} {op : WordOp} {nop : Lam.Prim}
    (himp : ∀ (ns : List Nat) (n : Nat), Lam.wordSem w op ns = some (.nat n) → nop.sem ns = some (.nat n))
    (h : RhsSim T lp ctx D sup fn L p L' p' x (.fir (.prim nop as))) :
    RhsSim T lp ctx D sup fn L p L' p' x (.fir (.prim (.word w op) as)) := by
  intro P H ρ ρl mem rest v H' hheap hρ hr
  apply h P H ρ ρl mem rest v H' hheap hρ
  obtain ⟨rfl, vs, hvs, hres⟩ := evalRhs_prim hr
  have hres' : Own.primResult (ownTables T) nop vs = .ok v := by
    simp only [Own.primResult] at hres ⊢
    cases hn : Own.natArgs vs with
    | none => simp [hn] at hres
    | some ns =>
      simp only [hn] at hres ⊢
      cases hs : (Lam.Prim.word w op).sem ns with
      | none => simp [hs] at hres
      | some r =>
        cases r with
        | nat n =>
          simp only [hs] at hres
          rw [Lam.Prim.sem_word] at hs
          rw [himp ns n hs]
          exact hres
        | bool b => exact absurd hs (Lam.wordSem_ne_bool w op ns b)
  simp only [Own.evalRhs, hvs, hres', Sem.Result.map, Sem.Result.bind]

/-- A binary word primitive's straight expansion. -/
theorem word2_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss : List Lir.Stmt} {f' : Nat}
    (hC : Ext C { st with acc := ss.reverse ++ st.acc, fresh := f' }) (ho : Open st)
    (hnc : ∀ s ∈ ss, s.isCall = false) {x : Nat} (hx : x < sup) {la lb : Lir.Arg}
    {as : List Fir.Arg} (hops : operands f as = .ok (some [la, lb])) (hlive : ∀ a ∈ as, LiveArg D a)
    {w : Width} {op : WordOp}
    (hexec : ∀ (ρl : Lir.Env) (mem : X86.Memory) (p q : Nat) (wa wb : Word), la.eval ρl = some wa →
      lb.eval ρl = some wb → natWord p = some wa → natWord q = some wb → p < w.size → q < w.size →
      ArgReads sup la → ArgReads sup lb →
      ∃ ρl' w', Lir.execList ρl mem ctx ss = some (ρl', mem) ∧ natWord (op.eval w p q).val = some w' ∧
        ρl'[x]? = some w' ∧ ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st.cur) (ss.reverse ++ st.acc).length x
      (.fir (.prim (.word w op) as)) := by
  apply straight_sim hF hH hC ho hnc
  intro P H ρ ρl mem v H' hρ hr
  obtain ⟨rfl, p, q, wa, wb, ha, hb, hwa, hwb, hp, hq, rfl, hra, hrb⟩ := word2_of hρ hops hlive hr
  obtain ⟨ρl', w', hx', hw, hρx, hρy⟩ := hexec ρl mem p q wa wb ha hb hwa hwb hp hq hra hrb
  exact ⟨rfl, ρl', hx', envRel_insert_frame hρ hx hρx hw hρy⟩

/-- A unary word primitive's straight expansion. -/
theorem word1_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss : List Lir.Stmt} {f' : Nat}
    (hC : Ext C { st with acc := ss.reverse ++ st.acc, fresh := f' }) (ho : Open st)
    (hnc : ∀ s ∈ ss, s.isCall = false) {x : Nat} (hx : x < sup) {la : Lir.Arg}
    {as : List Fir.Arg} (hops : operands f as = .ok (some [la])) (hlive : ∀ a ∈ as, LiveArg D a)
    {w : Width} {op : WordOp}
    (hexec : ∀ (ρl : Lir.Env) (mem : X86.Memory) (p : Nat) (wa : Word), la.eval ρl = some wa →
      natWord p = some wa → (op = .ofNat ∨ p < w.size) → ArgReads sup la →
      ∃ ρl' w', Lir.execList ρl mem ctx ss = some (ρl', mem) ∧ natWord (op.eval w p 0).val = some w' ∧
        ρl'[x]? = some w' ∧ ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st.cur) (ss.reverse ++ st.acc).length x
      (.fir (.prim (.word w op) as)) := by
  apply straight_sim hF hH hC ho hnc
  intro P H ρ ρl mem v H' hρ hr
  obtain ⟨rfl, p, wa, ha, hwa, hp, rfl, hra⟩ := word1_of hρ hops hlive hr
  obtain ⟨ρl', w', hx', hw, hρx, hρy⟩ := hexec ρl mem p wa ha hwa hp hra
  exact ⟨rfl, ρl', hx', envRel_insert_frame hρ hx hρx hw hρy⟩

/-- The end of a width-64 expansion: the check on the untagged result `u` in register `r`,
then `x := 2u + 1`. -/
theorem checked_tail {T : Tables} {P : List Word} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env}
    {ρl ρl₁ : Lir.Env} {ctx : Word} {mem : X86.Memory} {H : Own.Heap} (hheap : HeapInv T P H ctx mem)
    (hρ : EnvRel T P D sup ρ ρl) {x r : Nat} (hx : x < sup) {u : Word} {n : Nat} (hr1 : ρl₁[r]? = some u)
    (hu : u.toNat = n) (hf : ∀ y, y < sup → ρl₁[y]? = ρl[y]?)
    (hfalse : Lir.Cond.holds .ugt .w64 u 0x7fffffffffffffff = false) :
    ∃ ρl' mem' P', Lir.execList ρl₁ mem ctx [.assign x (retag (.v r))] = some (ρl', mem') ∧
      HeapInv T P' H ctx mem' ∧ P <+: P' ∧ EnvRel T P' D sup (ρ.insert x (.lit (.nat n))) ρl' := by
  have hle : ¬ u > 0x7fffffffffffffff := by
    intro hgt
    simp [Lir.Cond.holds, hgt] at hfalse
  have hw := (wide_word hu).1 hle
  refine ⟨ρl₁.insert x (u + u + 1), mem, P, ?_, hheap, List.prefix_refl _, ?_⟩
  · simp only [lir_eval, retag, hr1, retag_val, UInt64.mul_one]
  · exact (envRel_frame hρ hf).insert hx hw

/-- A binary width-64 expansion: its statements compute the untagged result, then the check. -/
theorem word2_checked_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop}
    {sup : Nat} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C) {st : St} {ss1 : List Lir.Stmt} {r x : Nat}
    {f' : Nat}
    (hC : Ext C (CheckSt st .natOverflow ss1 [.assign x (retag (.v r))]
      (.br .ugt (.v r) (.imm 0x7fffffffffffffff) (loc st.next) (loc (st.next + 1))) f'))
    (hl : Labels st) (ho : Open st) (hnc : ∀ s ∈ ss1, s.isCall = false) (hx : x < sup) {la lb : Lir.Arg}
    {as : List Fir.Arg} (hops : operands f as = .ok (some [la, lb])) (hlive : ∀ a ∈ as, LiveArg D a)
    {op : WordOp}
    (hexec : ∀ (ρl : Lir.Env) (mem : X86.Memory) (p q : Nat) (wa wb : Word), la.eval ρl = some wa →
      lb.eval ρl = some wb → natWord p = some wa → natWord q = some wb → ArgReads sup la → ArgReads sup lb →
      ∃ ρl₁ u, Lir.execList ρl mem ctx ss1 = some (ρl₁, mem) ∧ ρl₁[r]? = some u ∧
        u.toNat = (op.eval .w64 p q).val ∧ ∀ y, y < sup → ρl₁[y]? = ρl[y]?) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + (st.next + 1))
      [Lir.Stmt.assign x (retag (.v r))].length x (.fir (.prim (.word .w64 op) as)) := by
  refine check_br_sim hF hH hC hl ho hnc (by simp [Lir.Stmt.isCall]) ?_
  intro P H ρ ρl mem v H' hheap hρ hr
  obtain ⟨rfl, p, q, wa, wb, ha, hb, hwa, hwb, -, -, rfl, hra, hrb⟩ := word2_of hρ hops hlive hr
  obtain ⟨ρl₁, u, hx1, hr1, hu, hf⟩ := hexec ρl mem p q wa wb ha hb hwa hwb hra hrb
  exact ⟨ρl₁, mem, u, 0x7fffffffffffffff, hx1, hr1, rfl, checked_tail hheap hρ hx hr1 hu hf⟩

/-- A unary width-64 expansion. -/
theorem word1_checked_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop}
    {sup : Nat} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C) {st : St} {ss1 : List Lir.Stmt} {r x : Nat}
    {f' : Nat}
    (hC : Ext C (CheckSt st .natOverflow ss1 [.assign x (retag (.v r))]
      (.br .ugt (.v r) (.imm 0x7fffffffffffffff) (loc st.next) (loc (st.next + 1))) f'))
    (hl : Labels st) (ho : Open st) (hnc : ∀ s ∈ ss1, s.isCall = false) (hx : x < sup) {la : Lir.Arg}
    {as : List Fir.Arg} (hops : operands f as = .ok (some [la])) (hlive : ∀ a ∈ as, LiveArg D a)
    {op : WordOp}
    (hexec : ∀ (ρl : Lir.Env) (mem : X86.Memory) (p : Nat) (wa : Word), la.eval ρl = some wa →
      natWord p = some wa → ArgReads sup la →
      ∃ ρl₁ u, Lir.execList ρl mem ctx ss1 = some (ρl₁, mem) ∧ ρl₁[r]? = some u ∧
        u.toNat = (op.eval .w64 p 0).val ∧ ∀ y, y < sup → ρl₁[y]? = ρl[y]?) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + (st.next + 1))
      [Lir.Stmt.assign x (retag (.v r))].length x (.fir (.prim (.word .w64 op) as)) := by
  refine check_br_sim hF hH hC hl ho hnc (by simp [Lir.Stmt.isCall]) ?_
  intro P H ρ ρl mem v H' hheap hρ hr
  obtain ⟨rfl, p, wa, ha, hwa, -, rfl, hra⟩ := word1_of hρ hops hlive hr
  obtain ⟨ρl₁, u, hx1, hr1, hu, hf⟩ := hexec ρl mem p wa ha hwa hra
  exact ⟨ρl₁, mem, u, 0x7fffffffffffffff, hx1, hr1, rfl, checked_tail hheap hρ hx hr1 hu hf⟩

/-- Where a binary word operation's number is the `Nat` primitive's on the same arguments, the
`Nat` primitive returns the same number. -/
theorem wordSem_nat_of {w : Width} {op : WordOp} {nop : Lam.Prim} (harity : op.arity = 2)
    (h2 : ∀ p q, nop.sem [p, q] = some (.nat (op.eval w p q).val)) :
    ∀ (ns : List Nat) (n : Nat), Lam.wordSem w op ns = some (.nat n) → nop.sem ns = some (.nat n) := by
  intro ns n h
  match ns with
  | [] => simp [Lam.wordSem] at h
  | [p] =>
    have := (Lam.wordSem_one h).1
    omega
  | [p, q] =>
    obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two h
    exact h2 p q
  | _ :: _ :: _ :: _ => simp [Lam.wordSem] at h

/-! ## Each operation -/

/-- Evaluate a run of a word expansion below width 64 (`hw`). -/
macro "word_run_n" " at " h:ident " using " hw:term : tactic =>
  `(tactic| simp only [primitive, Lower.word, word64, wordNarrow, wordCount, checked64, bin, temp, freshReg,
      assign, emit, untag, check, coldBlock, newLabel, close, openAt, put, retag, StateT.run, bind, StateT.bind, pure,
      StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet, Except.bind,
      Except.pure, Except.ok.injEq, Prod.mk.injEq, true_and, throw, throwThe, MonadExceptOf.throw, StateT.lift,
      $hw:term, ↓reduceIte, if_false, if_true] at $h:ident)

section ops

variable {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
  {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
  (hH : Holds f F off starts C) {st st' : St} {x : Nat} {as : List Fir.Arg} (hC : Ext C st') (ho : Open st)
  (hsup : sup ≤ st.fresh) (hx : x < sup) (hlive : ∀ a ∈ as, LiveArg D a)

/-! ### The `Nat` codes: `div`, `mod`, `land`, `lor`, `xor` -/

include hF hH hC ho hsup hx hlive in
theorem prim_wordDiv {w : Width} {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .div) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .div) as)) := by
  have hrun' : (primitive f T x .natDiv [la, lb]).run st = .ok ((), st') := hrun
  refine rhsSim_of_nat (nop := .natDiv) (wordSem_nat_of rfl fun p q => ?_)
    (prim_natDiv hF hH hrun' hC ho hsup hx hops hlive)
  rw [sem_nat2 .natDiv (by decide)]
  by_cases hq : q = 0 <;> simp [hq, WordOp.eval, Src.WordResult.val]

include hF hH hC ho hsup hx hlive in
theorem prim_wordMod {w : Width} {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .mod) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .mod) as)) := by
  have hrun' : (primitive f T x .natMod [la, lb]).run st = .ok ((), st') := hrun
  refine rhsSim_of_nat (nop := .natMod) (wordSem_nat_of rfl fun p q => ?_)
    (prim_natMod hF hH hrun' hC ho hsup hx hops hlive)
  rw [sem_nat2 .natMod (by decide)]
  by_cases hq : q = 0 <;> simp [hq, WordOp.eval, Src.WordResult.val]

include hF hH hC ho hsup hx hlive in
theorem prim_wordLand {w : Width} {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .land) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .land) as)) := by
  have hrun' : (primitive f T x .natLand [la, lb]).run st = .ok ((), st') := hrun
  exact rhsSim_of_nat (nop := .natLand) (wordSem_nat_of rfl fun p q => by
      rw [sem_nat2 .natLand (by decide)]; rfl)
    (prim_natLand hF hH hrun' hC ho hsup hx hops hlive)

include hF hH hC ho hsup hx hlive in
theorem prim_wordLor {w : Width} {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .lor) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .lor) as)) := by
  have hrun' : (primitive f T x .natLor [la, lb]).run st = .ok ((), st') := hrun
  exact rhsSim_of_nat (nop := .natLor) (wordSem_nat_of rfl fun p q => by
      rw [sem_nat2 .natLor (by decide)]; rfl)
    (prim_natLor hF hH hrun' hC ho hsup hx hops hlive)

include hF hH hC ho hsup hx hlive in
theorem prim_wordXor {w : Width} {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .xor) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .xor) as)) := by
  have hrun' : (primitive f T x .natXor [la, lb]).run st = .ok ((), st') := hrun
  exact rhsSim_of_nat (nop := .natXor) (wordSem_nat_of rfl fun p q => by
      rw [sem_nat2 .natXor (by decide)]; rfl)
    (prim_natXor hF hH hrun' hC ho hsup hx hops hlive)

/-! ### Every width: `shiftRight`, `toNat`, `convert` -/

include hF hH hC ho hsup hx hlive in
theorem prim_wordShr {w : Width} {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .shiftRight) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .shiftRight) as)) := by
  word_run at hrun
  subst hrun
  refine word2_sim (ss := [.assign st.fresh (.bin .shr .w64 lb (.imm 1)),
      .assign (st.fresh + 1) (.bin .and .w64 (.v st.fresh) (.imm (UInt64.ofNat (w.bits - 1)))),
      .assign (st.fresh + 1 + 1) (.bin .shr .w64 la (.v (st.fresh + 1))),
      .assign x (.bin .or .w64 (.v (st.fresh + 1 + 1)) (.imm 1))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ _ hra _
  refine ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hra (t := st.fresh) hsup,
        arg_eval_temp hra (t := st.fresh + 1) (by omega), ↓reduceIte, if_neg]; try rfl,
    wordShr_word w hwa hwb, by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordToNat {w : Width} {la : Lir.Arg}
    (hrun : (primitive f T x (.word w .toNat) [la]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .toNat) as)) := by
  word_run at hrun
  subst hrun
  refine word1_sim (ss := [.assign x (.arg la)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p wa ha hwa _ _
  exact ⟨_, _, by simp only [lir_eval, ha]; try rfl, toNat_word hwa, by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordConvert {w w' : Width} {la : Lir.Arg}
    (hrun : (primitive f T x (.word w (.convert w')) [la]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w (.convert w')) as)) := by
  by_cases hww : w.bits ≤ w'.bits
  · word_run_n at hrun using hww
    subst hrun
    refine word1_sim (ss := [.assign x (.arg la)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
    intro ρl mem p wa ha hwa _ _
    exact ⟨_, _, by simp only [lir_eval, ha]; try rfl, convertWide_word hww hwa, by simp,
      fun y hy hyx => by regs_ne⟩
  · word_run_n at hrun using hww
    subst hrun
    refine word1_sim (ss := [.assign x (.bin .and .w64 la (.imm (tagMask w')))]) hF hH hC ho
      (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
    intro ρl mem p wa ha hwa _ _
    exact ⟨_, _, by simp only [lir_eval, ha]; try rfl, convertNarrow_word hww hwa, by simp,
      fun y hy hyx => by regs_ne⟩

/-! ### Below width 64 -/

include hF hH hC ho hsup hx hlive in
theorem prim_wordAddN {w : Width} (hw : w ≠ .w64) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .add) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .add) as)) := by
  word_run_n at hrun using hw
  subst hrun
  refine word2_sim (ss := [.assign st.fresh (.bin .add .w64 la lb),
      .assign (st.fresh + 1) (.bin .sub .w64 (.v st.fresh) (.imm 1)),
      .assign x (.bin .and .w64 (.v (st.fresh + 1)) (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p q wa wb ha hb hwa hwb hp hq _ _
  exact ⟨_, _, by simp (disch := omega) only [lir_eval, ha, hb, ↓reduceIte, if_neg]; try rfl,
    narrowAdd_word hw hwa hwb hp hq, by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordSubN {w : Width} (hw : w ≠ .w64) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .sub) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .sub) as)) := by
  word_run_n at hrun using hw
  subst hrun
  refine word2_sim (ss := [.assign st.fresh (.bin .sub .w64 la lb),
      .assign (st.fresh + 1) (.bin .or .w64 (.v st.fresh) (.imm 1)),
      .assign x (.bin .and .w64 (.v (st.fresh + 1)) (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p q wa wb ha hb hwa hwb hp hq _ _
  exact ⟨_, _, by simp (disch := omega) only [lir_eval, ha, hb, ↓reduceIte, if_neg]; try rfl,
    narrowSub_word hw hwa hwb hp hq, by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordMulN {w : Width} (hw : w ≠ .w64) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .mul) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .mul) as)) := by
  word_run_n at hrun using hw
  subst hrun
  refine word2_sim (ss := [.assign st.fresh (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1) (.bin .sub .w64 lb (.imm 1)),
      .assign (st.fresh + 1 + 1) (.bin .mul .w64 (.v st.fresh) (.v (st.fresh + 1))),
      .assign (st.fresh + 1 + 1 + 1) (.bin .or .w64 (.v (st.fresh + 1 + 1)) (.imm 1)),
      .assign x (.bin .and .w64 (.v (st.fresh + 1 + 1 + 1)) (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p q wa wb ha hb hwa hwb hp hq _ hrb
  exact ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hrb (t := st.fresh) hsup, ↓reduceIte,
        if_neg]; try rfl,
    narrowMul_word hw hwa hwb hp hq, by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordShlN {w : Width} (hw : w ≠ .w64) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .shiftLeft) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .shiftLeft) as)) := by
  word_run_n at hrun using hw
  subst hrun
  refine word2_sim (ss := [.assign st.fresh (.bin .shr .w64 lb (.imm 1)),
      .assign (st.fresh + 1) (.bin .and .w64 (.v st.fresh) (.imm (UInt64.ofNat (w.bits - 1)))),
      .assign (st.fresh + 1 + 1) (.bin .sub .w64 la (.imm 1)),
      .assign (st.fresh + 1 + 1 + 1) (.bin .shl .w64 (.v (st.fresh + 1 + 1)) (.v (st.fresh + 1))),
      .assign (st.fresh + 1 + 1 + 1 + 1) (.bin .or .w64 (.v (st.fresh + 1 + 1 + 1)) (.imm 1)),
      .assign x (.bin .and .w64 (.v (st.fresh + 1 + 1 + 1 + 1)) (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p q wa wb ha hb hwa hwb hp hq hra _
  exact ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hra (t := st.fresh) hsup,
        arg_eval_temp hra (t := st.fresh + 1) (by omega), ↓reduceIte, if_neg]; try rfl,
    narrowShl_word hw hwa hwb hp hq, by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordComplementN {w : Width} (hw : w ≠ .w64) {la : Lir.Arg}
    (hrun : (primitive f T x (.word w .complement) [la]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .complement) as)) := by
  word_run_n at hrun using hw
  subst hrun
  refine word1_sim (ss := [.assign st.fresh (.bin .xor .w64 la (.imm (tagMask w - 1))),
      .assign x (.bin .and .w64 (.v st.fresh) (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p wa ha hwa hp _
  have hp' : p < w.size := hp.resolve_left (by simp)
  exact ⟨_, _, by simp (disch := omega) only [lir_eval, ha, ↓reduceIte, if_neg]; try rfl,
    narrowComplement_word hw hwa hp', by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordNegN {w : Width} (hw : w ≠ .w64) {la : Lir.Arg}
    (hrun : (primitive f T x (.word w .neg) [la]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .neg) as)) := by
  word_run_n at hrun using hw
  subst hrun
  refine word1_sim (ss := [.assign st.fresh (.bin .sub .w64 (.imm 2) la),
      .assign x (.bin .and .w64 (.v st.fresh) (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p wa ha hwa hp _
  have hp' : p < w.size := hp.resolve_left (by simp)
  exact ⟨_, _, by simp (disch := omega) only [lir_eval, ha, ↓reduceIte, if_neg]; try rfl,
    narrowNeg_word hw hwa hp', by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordOfNatN {w : Width} (hw : w ≠ .w64) {la : Lir.Arg}
    (hrun : (primitive f T x (.word w .ofNat) [la]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w .ofNat) as)) := by
  word_run_n at hrun using hw
  subst hrun
  refine word1_sim (ss := [.assign x (.bin .and .w64 la (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p wa ha hwa _ _
  exact ⟨_, _, by simp only [lir_eval, ha]; try rfl, narrowOfNat_word hw hwa, by simp,
    fun y hy hyx => by regs_ne⟩

/-! ### Width 64 -/

include hF hH hC ho hsup hx hlive in
theorem prim_wordOfNat64 {la : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .ofNat) [la]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word .w64 .ofNat) as)) := by
  word_run at hrun
  subst hrun
  refine word1_sim (ss := [.assign x (.arg la)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p wa ha hwa _ _
  exact ⟨_, _, by simp only [lir_eval, ha]; try rfl, wideOfNat_word hwa, by simp, fun y hy hyx => by regs_ne⟩


include hF hH hC ho hsup hx hlive in
theorem prim_wordAdd64 (hl : Labels st) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .add) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word .w64 .add) as)) := by
  word_run at hrun
  subst hrun
  refine word2_checked_sim (ss1 := [.assign st.fresh (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1) (.bin .shr .w64 lb (.imm 1)),
      .assign (st.fresh + 1 + 1) (.bin .add .w64 (.v st.fresh) (.v (st.fresh + 1)))])
    (r := st.fresh + 1 + 1) hF hH hC hl ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ hrb
  exact ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hrb (t := st.fresh) hsup, ↓reduceIte,
        if_neg]; try rfl,
    by simp, wideAdd_toNat hwa hwb, fun y hy => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordSub64 (hl : Labels st) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .sub) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word .w64 .sub) as)) := by
  word_run at hrun
  subst hrun
  refine word2_checked_sim (ss1 := [.assign st.fresh (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1) (.bin .shr .w64 lb (.imm 1)),
      .assign (st.fresh + 1 + 1) (.bin .sub .w64 (.v st.fresh) (.v (st.fresh + 1)))])
    (r := st.fresh + 1 + 1) hF hH hC hl ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ hrb
  exact ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hrb (t := st.fresh) hsup, ↓reduceIte,
        if_neg]; try rfl,
    by simp, wideSub_toNat hwa hwb, fun y hy => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordMul64 (hl : Labels st) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .mul) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word .w64 .mul) as)) := by
  word_run at hrun
  subst hrun
  refine word2_checked_sim (ss1 := [.assign st.fresh (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1) (.bin .shr .w64 lb (.imm 1)),
      .assign (st.fresh + 1 + 1) (.bin .mul .w64 (.v st.fresh) (.v (st.fresh + 1)))])
    (r := st.fresh + 1 + 1) hF hH hC hl ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ hrb
  exact ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hrb (t := st.fresh) hsup, ↓reduceIte,
        if_neg]; try rfl,
    by simp, wideMul_toNat hwa hwb, fun y hy => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordShl64 (hl : Labels st) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .shiftLeft) [la, lb]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la, lb])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word .w64 .shiftLeft) as)) := by
  word_run at hrun
  subst hrun
  refine word2_checked_sim (ss1 := [.assign st.fresh (.bin .shr .w64 lb (.imm 1)),
      .assign (st.fresh + 1) (.bin .and .w64 (.v st.fresh) (.imm (UInt64.ofNat (Width.bits .w64 - 1)))),
      .assign (st.fresh + 1 + 1) (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1 + 1 + 1) (.bin .shl .w64 (.v (st.fresh + 1 + 1)) (.v (st.fresh + 1)))])
    (r := st.fresh + 1 + 1 + 1) hF hH hC hl ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p q wa wb ha hb hwa hwb hra _
  exact ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hra (t := st.fresh) hsup,
        arg_eval_temp hra (t := st.fresh + 1) (by omega), ↓reduceIte, if_neg]; try rfl,
    by simp, wideShl_toNat hwa hwb, fun y hy => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordComplement64 (hl : Labels st) {la : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .complement) [la]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word .w64 .complement) as)) := by
  word_run at hrun
  subst hrun
  refine word1_checked_sim (ss1 := [.assign st.fresh (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1) (.bin .xor .w64 (.v st.fresh) (.imm 0xFFFFFFFFFFFFFFFF))])
    (r := st.fresh + 1) hF hH hC hl ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p wa ha hwa _
  exact ⟨_, _, by simp (disch := omega) only [lir_eval, ha, ↓reduceIte, if_neg]; try rfl,
    by simp, wideComplement_toNat hwa, fun y hy => by regs_ne⟩

include hF hH hC ho hsup hx hlive in
theorem prim_wordNeg64 (hl : Labels st) {la : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .neg) [la]).run st = .ok ((), st'))
    (hops : operands f as = .ok (some [la])) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word .w64 .neg) as)) := by
  word_run at hrun
  subst hrun
  refine word1_checked_sim (ss1 := [.assign st.fresh (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1) (.bin .sub .w64 (.imm 0) (.v st.fresh))])
    (r := st.fresh + 1) hF hH hC hl ho (by simp [Lir.Stmt.isCall]) hx hops hlive ?_
  intro ρl mem p wa ha hwa _
  exact ⟨_, _, by simp (disch := omega) only [lir_eval, ha, ↓reduceIte, if_neg]; try rfl,
    by simp, wideNeg_toNat hwa, fun y hy => by regs_ne⟩

end ops

/-! ## The dispatch -/

/-- **Every word primitive's expansion simulates Cfg's primitive** (the case of `primitive_sim`
for `Lam.Prim.word`). -/
theorem prim_word {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop}
    {sup : Nat} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C) {st st' : St} {x : Nat} {w : Width}
    {o : WordOp} {las : List Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x (.word w o) las).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st)
    (ho : Open st) (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some las))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w o) as)) := by
  rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩
  · exfalso
    cases o <;> word_bad
  · cases o
    case complement =>
      by_cases hw : w = .w64
      · subst hw; exact prim_wordComplement64 hF hH hC ho hsup hx hlive hl hrun hops
      · exact prim_wordComplementN hF hH hC ho hsup hx hlive hw hrun hops
    case neg =>
      by_cases hw : w = .w64
      · subst hw; exact prim_wordNeg64 hF hH hC ho hsup hx hlive hl hrun hops
      · exact prim_wordNegN hF hH hC ho hsup hx hlive hw hrun hops
    case ofNat =>
      by_cases hw : w = .w64
      · subst hw; exact prim_wordOfNat64 hF hH hC ho hsup hx hlive hrun hops
      · exact prim_wordOfNatN hF hH hC ho hsup hx hlive hw hrun hops
    case toNat => exact prim_wordToNat hF hH hC ho hsup hx hlive hrun hops
    case convert w' => exact prim_wordConvert hF hH hC ho hsup hx hlive hrun hops
    all_goals exfalso; word_bad
  · cases o
    case add =>
      by_cases hw : w = .w64
      · subst hw; exact prim_wordAdd64 hF hH hC ho hsup hx hlive hl hrun hops
      · exact prim_wordAddN hF hH hC ho hsup hx hlive hw hrun hops
    case sub =>
      by_cases hw : w = .w64
      · subst hw; exact prim_wordSub64 hF hH hC ho hsup hx hlive hl hrun hops
      · exact prim_wordSubN hF hH hC ho hsup hx hlive hw hrun hops
    case mul =>
      by_cases hw : w = .w64
      · subst hw; exact prim_wordMul64 hF hH hC ho hsup hx hlive hl hrun hops
      · exact prim_wordMulN hF hH hC ho hsup hx hlive hw hrun hops
    case shiftLeft =>
      by_cases hw : w = .w64
      · subst hw; exact prim_wordShl64 hF hH hC ho hsup hx hlive hl hrun hops
      · exact prim_wordShlN hF hH hC ho hsup hx hlive hw hrun hops
    case div => exact prim_wordDiv hF hH hC ho hsup hx hlive hrun hops
    case mod => exact prim_wordMod hF hH hC ho hsup hx hlive hrun hops
    case land => exact prim_wordLand hF hH hC ho hsup hx hlive hrun hops
    case lor => exact prim_wordLor hF hH hC ho hsup hx hlive hrun hops
    case xor => exact prim_wordXor hF hH hC ho hsup hx hlive hrun hops
    case shiftRight => exact prim_wordShr hF hH hC ho hsup hx hlive hrun hops
    all_goals exfalso; word_bad
  · exfalso
    cases o <;> word_bad

end IxCC.Rt.Proof
