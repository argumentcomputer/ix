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
      ↓reduceIte, eq_self_iff_true, ite_true, ite_false] at $h:ident)

/-- A word primitive with no expansion (a decision, an arity mismatch) never runs to a state. -/
macro "word_bad" : tactic =>
  `(tactic| (simp only [primitive, Lower.word, word64, wordNarrow] at *; (try split at *) <;>
      simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.bind, StateT.run] at *))

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


/-! ## The heap-free core

A primitive's expansion touches no memory and no heap: it reads its operands' words and binds
`x`. `PrimCore` states exactly that, without a heap invariant or an environment relation, so a
word operation's expansion is proved once (`word_core`) and each route's simulation relation
follows from it by one lemma (`rhsSim_of_core` here; the plain-RC bridge's own). -/

/-- **The heap-free core of a primitive's expansion**: from registers in which the lowered
operands `las` evaluate to the tagged words of numbers `ns` on which `op` returns the number `n`,
Lir runs from `(L, p)` to `(L', p')` of function `fn` with the memory unchanged, binding `x` to the
word of `n` and keeping every register below `sup` but `x`; or it fails. -/
def PrimCore (lp : Lir.Program) (ctx : Word) (sup fn L p L' p' x : Nat) (op : Lam.Prim)
    (las : List Lir.Arg) : Prop :=
  ∀ (ρl : Lir.Env) (mem : X86.Memory) (rest : List Lir.Frame) (ns : List Nat) (ws : List Word) (n : Nat),
    Lir.evalArgs ρl las = some ws → ListRel (fun n w => natWord n = some w) ns ws →
    (∀ la ∈ las, ArgReads sup la) → op.sem ns = some (.nat n) →
    (∃ c ρl' w, Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn L p ρl rest) c
        (Lir.atState mem ctx fn L' p' ρl' rest) ∧ natWord n = some w ∧ ρl'[x]? = some w ∧
        ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) ∨
    Sem.Fails (Lir.semStep lp) (Lir.atState mem ctx fn L p ρl rest)

/-- The numbers of related literal arguments have the related words. -/
theorem natArgs_words {R : Own.RVal → Word → Prop}
    (hR : ∀ {n : Nat} {w : Word}, R (.lit (.nat n)) w → natWord n = some w)
    {vs : List Own.RVal} {ws : List Word} (h : ListRel R vs ws) :
    ∀ {ns : List Nat}, Own.natArgs vs = some ns → ListRel (fun n w => natWord n = some w) ns ws := by
  induction h with
  | nil =>
    intro ns hn
    simp only [Own.natArgs, Option.some.injEq] at hn
    subst hn
    exact .nil
  | @cons v w vs ws hvw _ ih =>
    intro ns hn
    match v, hvw, hn with
    | .lit (.nat n), hvw, hn =>
      simp only [Own.natArgs] at hn
      cases hm : Own.natArgs vs with
      | none => simp [hm] at hn
      | some ns' =>
        simp only [hm, Option.map, Option.some.injEq] at hn
        subst hn
        exact .cons (hR hvw) (ih hm)
    | .lit (.str _), _, hn => simp [Own.natArgs] at hn
    | .ctor0 _, _, hn => simp [Own.natArgs] at hn
    | .erased, _, hn => simp [Own.natArgs] at hn
    | .loc _, _, hn => simp [Own.natArgs] at hn

/-- **The immortal route's simulation from the core.** -/
theorem rhsSim_of_core {T : Tables} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup fn L p L' p' x : Nat}
    {f : Fir.FunId} {op : Lam.Prim} {las : List Lir.Arg} {as : List Fir.Arg}
    (hops : operands f as = .ok (some las)) (hlive : ∀ a ∈ as, LiveArg D a) (hx : x < sup)
    (hnb : ∀ ns b, op.sem ns ≠ some (.bool b)) (hc : PrimCore lp ctx sup fn L p L' p' x op las) :
    RhsSim T lp ctx D sup fn L p L' p' x (.fir (.prim op as)) := by
  intro P H ρ ρl mem rest v H' hheap hρ hr
  obtain ⟨rfl, vs, hvs, hres⟩ := evalRhs_prim hr
  obtain ⟨ws, hws, hrel, hreads⟩ := operands_rel hρ hops hlive hvs
  simp only [Own.primResult] at hres
  cases hn : Own.natArgs vs with
  | none => simp [hn] at hres
  | some ns =>
    simp only [hn] at hres
    cases hs : op.sem ns with
    | none => simp [hs] at hres
    | some r =>
      cases r with
      | bool b => exact absurd hs (hnb ns b)
      | nat n =>
        simp only [hs, Sem.Result.ok.injEq] at hres
        subst hres
        rcases hc ρl mem rest ns ws n hws (natArgs_words (fun h => h) hrel hn) hreads hs with
          ⟨c, ρl', w, hstar, hw, hρx, hρy⟩ | hfail
        · exact .inl ⟨c, ρl', mem, P, hstar, hheap, List.prefix_refl _, envRel_insert_frame hρ hx hρx hw hρy⟩
        · exact .inr hfail

/-- The operands of a binary word primitive in the core. -/
theorem core_two {ρl : Lir.Env} {la lb : Lir.Arg} {ns : List Nat} {ws : List Word}
    (hws : Lir.evalArgs ρl [la, lb] = some ws) (hrel : ListRel (fun n w => natWord n = some w) ns ws) :
    ∃ p q wa wb, ns = [p, q] ∧ la.eval ρl = some wa ∧ lb.eval ρl = some wb ∧ natWord p = some wa ∧
      natWord q = some wb := by
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
      | @cons p _ _ _ hwa hrel' =>
        cases hrel' with
        | @cons q _ _ _ hwb hnil =>
          cases hnil
          exact ⟨p, q, wa, wb, rfl, rfl, rfl, hwa, hwb⟩

/-- The operand of a unary word primitive in the core. -/
theorem core_one {ρl : Lir.Env} {la : Lir.Arg} {ns : List Nat} {ws : List Word}
    (hws : Lir.evalArgs ρl [la] = some ws) (hrel : ListRel (fun n w => natWord n = some w) ns ws) :
    ∃ p wa, ns = [p] ∧ la.eval ρl = some wa ∧ natWord p = some wa := by
  simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, Option.bind_eq_bind] at hws
  cases ha : la.eval ρl with
  | none => simp [ha] at hws
  | some wa =>
    simp [ha] at hws
    subst hws
    cases hrel with
    | @cons p _ _ _ hwa hnil =>
      cases hnil
      exact ⟨p, wa, rfl, rfl, hwa⟩

/-- A binary word primitive's straight expansion, in the core. -/
theorem word2_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {sup : Nat} {fn : Nat} {F : Lir.Func}
    {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss : List Lir.Stmt} {f' : Nat}
    (hC : Ext C { st with acc := ss.reverse ++ st.acc, fresh := f' }) (ho : Open st)
    (hnc : ∀ s ∈ ss, s.isCall = false) {x : Nat} {la lb : Lir.Arg} {w : Width} {op : WordOp}
    (hexec : ∀ (ρl : Lir.Env) (mem : X86.Memory) (p q : Nat) (wa wb : Word), la.eval ρl = some wa →
      lb.eval ρl = some wb → natWord p = some wa → natWord q = some wb → p < w.size → q < w.size →
      ArgReads sup la → ArgReads sup lb →
      ∃ ρl' w', Lir.execList ρl mem ctx ss = some (ρl', mem) ∧ natWord (op.eval w p q).val = some w' ∧
        ρl'[x]? = some w' ∧ ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st.cur) (ss.reverse ++ st.acc).length x
      (.word w op) [la, lb] := by
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := core_two hws hrel
  rw [Lam.Prim.sem_word] at hsem
  obtain ⟨-, -, hp, hq, rfl⟩ := Lam.wordSem_two hsem
  obtain ⟨ρl', w', hx', hw, hρx, hρy⟩ :=
    hexec ρl mem p q wa wb ha hb hwa hwb hp hq (hreads la (by simp)) (hreads lb (by simp))
  exact .inl ⟨0, ρl', w', straight_star hF hH hC ho hnc hx', hw, hρx, hρy⟩

/-- A unary word primitive's straight expansion, in the core. -/
theorem word1_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {sup : Nat} {fn : Nat} {F : Lir.Func}
    {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss : List Lir.Stmt} {f' : Nat}
    (hC : Ext C { st with acc := ss.reverse ++ st.acc, fresh := f' }) (ho : Open st)
    (hnc : ∀ s ∈ ss, s.isCall = false) {x : Nat} {la : Lir.Arg} {w : Width} {op : WordOp}
    (hexec : ∀ (ρl : Lir.Env) (mem : X86.Memory) (p : Nat) (wa : Word), la.eval ρl = some wa →
      natWord p = some wa → (op = .ofNat ∨ p < w.size) → ArgReads sup la →
      ∃ ρl' w', Lir.execList ρl mem ctx ss = some (ρl', mem) ∧ natWord (op.eval w p 0).val = some w' ∧
        ρl'[x]? = some w' ∧ ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st.cur) (ss.reverse ++ st.acc).length x
      (.word w op) [la] := by
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, wa, rfl, ha, hwa⟩ := core_one hws hrel
  rw [Lam.Prim.sem_word] at hsem
  obtain ⟨-, -, hp, rfl⟩ := Lam.wordSem_one hsem
  obtain ⟨ρl', w', hx', hw, hρx, hρy⟩ := hexec ρl mem p wa ha hwa hp (hreads la (by simp))
  exact .inl ⟨0, ρl', w', straight_star hF hH hC ho hnc hx', hw, hρx, hρy⟩

/-- A check on the untagged result `u` in register `r`, then `x := 2u + 1`: the run up to the
continuation, or the failure. -/
theorem checked_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {sup : Nat} {fn : Nat} {F : Lir.Func}
    {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss1 : List Lir.Stmt} {r x : Nat} {f' : Nat}
    (hC : Ext C (CheckSt st .natOverflow ss1 [.assign x (retag (.v r))]
      (.br .ugt (.v r) (.imm 0x7fffffffffffffff) (loc st.next) (loc (st.next + 1))) f'))
    (hl : Labels st) (ho : Open st) (hnc : ∀ s ∈ ss1, s.isCall = false) {ρl ρl₁ : Lir.Env}
    {mem : X86.Memory} {rest : List Lir.Frame} {u : Word} {n : Nat}
    (hx1 : Lir.execList ρl mem ctx ss1 = some (ρl₁, mem)) (hr1 : ρl₁[r]? = some u) (hu : u.toNat = n)
    (hf : ∀ y, y < sup → ρl₁[y]? = ρl[y]?) :
    (∃ c ρl' w, Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) c
        (Lir.atState mem ctx fn (off + (st.next + 1)) [Lir.Stmt.assign x (retag (.v r))].length ρl' rest) ∧
        natWord n = some w ∧ ρl'[x]? = some w ∧ ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) ∨
    Sem.Fails (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) := by
  obtain ⟨⟨lb, hlb, hbody, hterm⟩, hbad, ⟨cbk, post, hcb, hcp, hcbody⟩⟩ := check_code hH hC hl ho
  simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hterm
  have h1 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := st.acc.reverse) (post := []) hF hlb
    (by simpa using hbody) hnc hx1
  simp only [List.length_reverse] at h1
  have hpos : st.acc.length + ss1.length = lb.body.size := by
    rw [← Array.length_toList, hbody]; simp
  have hca : (Lir.Arg.v r).eval ρl₁ = some u := hr1
  have hcbv : (Lir.Arg.imm 0x7fffffffffffffff).eval ρl₁ = some 0x7fffffffffffffff := rfl
  cases hz : Lir.Cond.holds .ugt .w64 u 0x7fffffffffffffff with
  | false =>
    have hle : ¬ u > 0x7fffffffffffffff := by
      intro hgt
      simp [Lir.Cond.holds, hgt] at hz
    have hw := (wide_word hu).1 hle
    have hx2 : Lir.execList ρl₁ mem ctx [Lir.Stmt.assign x (retag (.v r))] =
        some (ρl₁.insert x (u + u + 1), mem) := by
      simp only [lir_eval, retag, hr1, retag_val, UInt64.mul_one]
    have h2 := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl₁) (ρ' := ρl₁)
      (e := ⟨off + (st.next + 1), []⟩) (vals := []) (va := u) (vb := 0x7fffffffffffffff) hF hlb hpos hterm.symm hca
      hcbv (by simp [hz]) rfl hcb (by simp [hcp, Lir.bindParams])
    have h3 := Lir.stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := post) hF hcb
      (by simpa using hcbody) (by simp [Lir.Stmt.isCall]) hx2
    refine .inl ⟨_, ρl₁.insert x (u + u + 1), u + u + 1, h1.trans ((Lir.star_of_step h2).trans (by simpa using h3)),
      hw, by simp, fun y hy hyx => ?_⟩
    rw [Lir.env_insert_ne _ _ (Ne.symm hyx), hf y hy]
  | true =>
    have h2 := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl₁) (ρ' := ρl₁)
      (e := ⟨off + st.next, []⟩) (vals := []) (va := u) (vb := 0x7fffffffffffffff) hF hlb hpos hterm.symm hca hcbv
      (by simp [hz]) rfl hbad rfl
    have h3 := Lir.fail_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρl₁) hF hbad rfl rfl
    exact .inr (Lir.fails_of_star (h1.trans (Lir.star_of_step h2)) h3)

/-- A binary width-64 expansion, in the core: its statements compute the untagged result, then
the check. -/
theorem word2_checked_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {sup : Nat} {fn : Nat}
    {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss1 : List Lir.Stmt} {r x : Nat} {f' : Nat}
    (hC : Ext C (CheckSt st .natOverflow ss1 [.assign x (retag (.v r))]
      (.br .ugt (.v r) (.imm 0x7fffffffffffffff) (loc st.next) (loc (st.next + 1))) f'))
    (hl : Labels st) (ho : Open st) (hnc : ∀ s ∈ ss1, s.isCall = false) {la lb : Lir.Arg} {op : WordOp}
    (hexec : ∀ (ρl : Lir.Env) (mem : X86.Memory) (p q : Nat) (wa wb : Word), la.eval ρl = some wa →
      lb.eval ρl = some wb → natWord p = some wa → natWord q = some wb → ArgReads sup la → ArgReads sup lb →
      ∃ ρl₁ u, Lir.execList ρl mem ctx ss1 = some (ρl₁, mem) ∧ ρl₁[r]? = some u ∧
        u.toNat = (op.eval .w64 p q).val ∧ ∀ y, y < sup → ρl₁[y]? = ρl[y]?) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + (st.next + 1))
      [Lir.Stmt.assign x (retag (.v r))].length x (.word .w64 op) [la, lb] := by
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, q, wa, wb, rfl, ha, hb, hwa, hwb⟩ := core_two hws hrel
  rw [Lam.Prim.sem_word] at hsem
  obtain ⟨-, -, -, -, rfl⟩ := Lam.wordSem_two hsem
  obtain ⟨ρl₁, u, hx1, hr1, hu, hf⟩ := hexec ρl mem p q wa wb ha hb hwa hwb (hreads la (by simp)) (hreads lb (by simp))
  exact checked_core hF hH hC hl ho hnc hx1 hr1 hu hf

/-- A unary width-64 expansion, in the core. -/
theorem word1_checked_core {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {sup : Nat} {fn : Nat}
    {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss1 : List Lir.Stmt} {r x : Nat} {f' : Nat}
    (hC : Ext C (CheckSt st .natOverflow ss1 [.assign x (retag (.v r))]
      (.br .ugt (.v r) (.imm 0x7fffffffffffffff) (loc st.next) (loc (st.next + 1))) f'))
    (hl : Labels st) (ho : Open st) (hnc : ∀ s ∈ ss1, s.isCall = false) {la : Lir.Arg} {op : WordOp}
    (hexec : ∀ (ρl : Lir.Env) (mem : X86.Memory) (p : Nat) (wa : Word), la.eval ρl = some wa →
      natWord p = some wa → ArgReads sup la →
      ∃ ρl₁ u, Lir.execList ρl mem ctx ss1 = some (ρl₁, mem) ∧ ρl₁[r]? = some u ∧
        u.toNat = (op.eval .w64 p 0).val ∧ ∀ y, y < sup → ρl₁[y]? = ρl[y]?) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + (st.next + 1))
      [Lir.Stmt.assign x (retag (.v r))].length x (.word .w64 op) [la] := by
  intro ρl mem rest ns ws n hws hrel hreads hsem
  obtain ⟨p, wa, rfl, ha, hwa⟩ := core_one hws hrel
  rw [Lam.Prim.sem_word] at hsem
  obtain ⟨-, -, -, rfl⟩ := Lam.wordSem_one hsem
  obtain ⟨ρl₁, u, hx1, hr1, hu, hf⟩ := hexec ρl mem p wa ha hwa (hreads la (by simp))
  exact checked_core hF hH hC hl ho hnc hx1 hr1 hu hf

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
      $hw:term, ↓reduceIte, ite_false, ite_true] at $h:ident)

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

include hF hH hC ho hsup in
theorem core_wordShr {w : Width} {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .shiftRight) [la, lb]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word w .shiftRight) [la, lb] := by
  word_run at hrun
  subst hrun
  refine word2_core (ss := [.assign st.fresh (.bin .shr .w64 lb (.imm 1)),
      .assign (st.fresh + 1) (.bin .and .w64 (.v st.fresh) (.imm (UInt64.ofNat (w.bits - 1)))),
      .assign (st.fresh + 1 + 1) (.bin .shr .w64 la (.v (st.fresh + 1))),
      .assign x (.bin .or .w64 (.v (st.fresh + 1 + 1)) (.imm 1))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ _ hra _
  refine ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hra (t := st.fresh) hsup,
        arg_eval_temp hra (t := st.fresh + 1) (by omega), ↓reduceIte, ite_eq_right]; try rfl,
    wordShr_word w hwa hwb, by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho in
theorem core_wordToNat {w : Width} {la : Lir.Arg}
    (hrun : (primitive f T x (.word w .toNat) [la]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word w .toNat) [la] := by
  word_run at hrun
  subst hrun
  refine word1_core (ss := [.assign x (.arg la)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p wa ha hwa _ _
  exact ⟨_, _, by simp only [lir_eval, ha]; try rfl, toNat_word hwa, by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho in
theorem core_wordConvert {w w' : Width} {la : Lir.Arg}
    (hrun : (primitive f T x (.word w (.convert w')) [la]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word w (.convert w')) [la] := by
  by_cases hww : w.bits ≤ w'.bits
  · word_run_n at hrun using hww
    subst hrun
    refine word1_core (ss := [.assign x (.arg la)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) ?_
    intro ρl mem p wa ha hwa _ _
    exact ⟨_, _, by simp only [lir_eval, ha]; try rfl, convertWide_word hww hwa, by simp,
      fun y hy hyx => by regs_ne⟩
  · word_run_n at hrun using hww
    subst hrun
    refine word1_core (ss := [.assign x (.bin .and .w64 la (.imm (tagMask w')))]) hF hH hC ho
      (by simp [Lir.Stmt.isCall]) ?_
    intro ρl mem p wa ha hwa _ _
    exact ⟨_, _, by simp only [lir_eval, ha]; try rfl, convertNarrow_word hww hwa, by simp,
      fun y hy hyx => by regs_ne⟩

/-! ### Below width 64 -/

include hF hH hC ho hsup in
theorem core_wordAddN {w : Width} (hw : w ≠ .w64) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .add) [la, lb]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word w .add) [la, lb] := by
  word_run_n at hrun using hw
  subst hrun
  refine word2_core (ss := [.assign st.fresh (.bin .add .w64 la lb),
      .assign (st.fresh + 1) (.bin .sub .w64 (.v st.fresh) (.imm 1)),
      .assign x (.bin .and .w64 (.v (st.fresh + 1)) (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p q wa wb ha hb hwa hwb hp hq _ _
  exact ⟨_, _, by simp (disch := omega) only [lir_eval, ha, hb, ↓reduceIte, ite_eq_right]; try rfl,
    narrowAdd_word hw hwa hwb hp hq, by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup in
theorem core_wordSubN {w : Width} (hw : w ≠ .w64) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .sub) [la, lb]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word w .sub) [la, lb] := by
  word_run_n at hrun using hw
  subst hrun
  refine word2_core (ss := [.assign st.fresh (.bin .sub .w64 la lb),
      .assign (st.fresh + 1) (.bin .or .w64 (.v st.fresh) (.imm 1)),
      .assign x (.bin .and .w64 (.v (st.fresh + 1)) (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p q wa wb ha hb hwa hwb hp hq _ _
  exact ⟨_, _, by simp (disch := omega) only [lir_eval, ha, hb, ↓reduceIte, ite_eq_right]; try rfl,
    narrowSub_word hw hwa hwb hp hq, by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup in
theorem core_wordMulN {w : Width} (hw : w ≠ .w64) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .mul) [la, lb]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word w .mul) [la, lb] := by
  word_run_n at hrun using hw
  subst hrun
  refine word2_core (ss := [.assign st.fresh (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1) (.bin .sub .w64 lb (.imm 1)),
      .assign (st.fresh + 1 + 1) (.bin .mul .w64 (.v st.fresh) (.v (st.fresh + 1))),
      .assign (st.fresh + 1 + 1 + 1) (.bin .or .w64 (.v (st.fresh + 1 + 1)) (.imm 1)),
      .assign x (.bin .and .w64 (.v (st.fresh + 1 + 1 + 1)) (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p q wa wb ha hb hwa hwb hp hq _ hrb
  exact ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hrb (t := st.fresh) hsup, ↓reduceIte,
        ite_eq_right]; try rfl,
    narrowMul_word hw hwa hwb hp hq, by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup in
theorem core_wordShlN {w : Width} (hw : w ≠ .w64) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word w .shiftLeft) [la, lb]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word w .shiftLeft) [la, lb] := by
  word_run_n at hrun using hw
  subst hrun
  refine word2_core (ss := [.assign st.fresh (.bin .shr .w64 lb (.imm 1)),
      .assign (st.fresh + 1) (.bin .and .w64 (.v st.fresh) (.imm (UInt64.ofNat (w.bits - 1)))),
      .assign (st.fresh + 1 + 1) (.bin .sub .w64 la (.imm 1)),
      .assign (st.fresh + 1 + 1 + 1) (.bin .shl .w64 (.v (st.fresh + 1 + 1)) (.v (st.fresh + 1))),
      .assign (st.fresh + 1 + 1 + 1 + 1) (.bin .or .w64 (.v (st.fresh + 1 + 1 + 1)) (.imm 1)),
      .assign x (.bin .and .w64 (.v (st.fresh + 1 + 1 + 1 + 1)) (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p q wa wb ha hb hwa hwb hp hq hra _
  exact ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hra (t := st.fresh) hsup,
        arg_eval_temp hra (t := st.fresh + 1) (by omega), ↓reduceIte, ite_eq_right]; try rfl,
    narrowShl_word hw hwa hwb hp hq, by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup in
theorem core_wordComplementN {w : Width} (hw : w ≠ .w64) {la : Lir.Arg}
    (hrun : (primitive f T x (.word w .complement) [la]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word w .complement) [la] := by
  word_run_n at hrun using hw
  subst hrun
  refine word1_core (ss := [.assign st.fresh (.bin .xor .w64 la (.imm (tagMask w - 1))),
      .assign x (.bin .and .w64 (.v st.fresh) (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p wa ha hwa hp _
  have hp' : p < w.size := hp.resolve_left (by simp)
  exact ⟨_, _, by simp (disch := omega) only [lir_eval, ha, ↓reduceIte, ite_eq_right]; try rfl,
    narrowComplement_word hw hwa hp', by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho hsup in
theorem core_wordNegN {w : Width} (hw : w ≠ .w64) {la : Lir.Arg}
    (hrun : (primitive f T x (.word w .neg) [la]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word w .neg) [la] := by
  word_run_n at hrun using hw
  subst hrun
  refine word1_core (ss := [.assign st.fresh (.bin .sub .w64 (.imm 2) la),
      .assign x (.bin .and .w64 (.v st.fresh) (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p wa ha hwa hp _
  have hp' : p < w.size := hp.resolve_left (by simp)
  exact ⟨_, _, by simp (disch := omega) only [lir_eval, ha, ↓reduceIte, ite_eq_right]; try rfl,
    narrowNeg_word hw hwa hp', by simp, fun y hy hyx => by regs_ne⟩

include hF hH hC ho in
theorem core_wordOfNatN {w : Width} (hw : w ≠ .w64) {la : Lir.Arg}
    (hrun : (primitive f T x (.word w .ofNat) [la]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word w .ofNat) [la] := by
  word_run_n at hrun using hw
  subst hrun
  refine word1_core (ss := [.assign x (.bin .and .w64 la (.imm (tagMask w)))])
    hF hH hC ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p wa ha hwa _ _
  exact ⟨_, _, by simp only [lir_eval, ha]; try rfl, narrowOfNat_word hw hwa, by simp,
    fun y hy hyx => by regs_ne⟩

/-! ### Width 64 -/

include hF hH hC ho in
theorem core_wordOfNat64 {la : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .ofNat) [la]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word .w64 .ofNat) [la] := by
  word_run at hrun
  subst hrun
  refine word1_core (ss := [.assign x (.arg la)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p wa ha hwa _ _
  exact ⟨_, _, by simp only [lir_eval, ha]; try rfl, wideOfNat_word hwa, by simp, fun y hy hyx => by regs_ne⟩


include hF hH hC ho hsup in
theorem core_wordAdd64 (hl : Labels st) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .add) [la, lb]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word .w64 .add) [la, lb] := by
  word_run at hrun
  subst hrun
  refine word2_checked_core (ss1 := [.assign st.fresh (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1) (.bin .shr .w64 lb (.imm 1)),
      .assign (st.fresh + 1 + 1) (.bin .add .w64 (.v st.fresh) (.v (st.fresh + 1)))])
    (r := st.fresh + 1 + 1) hF hH hC hl ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ hrb
  exact ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hrb (t := st.fresh) hsup, ↓reduceIte,
        ite_eq_right]; try rfl,
    by simp, wideAdd_toNat hwa hwb, fun y hy => by regs_ne⟩

include hF hH hC ho hsup in
theorem core_wordSub64 (hl : Labels st) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .sub) [la, lb]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word .w64 .sub) [la, lb] := by
  word_run at hrun
  subst hrun
  refine word2_checked_core (ss1 := [.assign st.fresh (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1) (.bin .shr .w64 lb (.imm 1)),
      .assign (st.fresh + 1 + 1) (.bin .sub .w64 (.v st.fresh) (.v (st.fresh + 1)))])
    (r := st.fresh + 1 + 1) hF hH hC hl ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ hrb
  exact ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hrb (t := st.fresh) hsup, ↓reduceIte,
        ite_eq_right]; try rfl,
    by simp, wideSub_toNat hwa hwb, fun y hy => by regs_ne⟩

include hF hH hC ho hsup in
theorem core_wordMul64 (hl : Labels st) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .mul) [la, lb]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word .w64 .mul) [la, lb] := by
  word_run at hrun
  subst hrun
  refine word2_checked_core (ss1 := [.assign st.fresh (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1) (.bin .shr .w64 lb (.imm 1)),
      .assign (st.fresh + 1 + 1) (.bin .mul .w64 (.v st.fresh) (.v (st.fresh + 1)))])
    (r := st.fresh + 1 + 1) hF hH hC hl ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ hrb
  exact ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hrb (t := st.fresh) hsup, ↓reduceIte,
        ite_eq_right]; try rfl,
    by simp, wideMul_toNat hwa hwb, fun y hy => by regs_ne⟩

include hF hH hC ho hsup in
theorem core_wordShl64 (hl : Labels st) {la lb : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .shiftLeft) [la, lb]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word .w64 .shiftLeft) [la, lb] := by
  word_run at hrun
  subst hrun
  refine word2_checked_core (ss1 := [.assign st.fresh (.bin .shr .w64 lb (.imm 1)),
      .assign (st.fresh + 1) (.bin .and .w64 (.v st.fresh) (.imm (UInt64.ofNat (Width.bits .w64 - 1)))),
      .assign (st.fresh + 1 + 1) (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1 + 1 + 1) (.bin .shl .w64 (.v (st.fresh + 1 + 1)) (.v (st.fresh + 1)))])
    (r := st.fresh + 1 + 1 + 1) hF hH hC hl ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p q wa wb ha hb hwa hwb hra _
  exact ⟨_, _, by
      simp (disch := omega) only [lir_eval, ha, hb, arg_eval_temp hra (t := st.fresh) hsup,
        arg_eval_temp hra (t := st.fresh + 1) (by omega), ↓reduceIte, ite_eq_right]; try rfl,
    by simp, wideShl_toNat hwa hwb, fun y hy => by regs_ne⟩

include hF hH hC ho hsup in
theorem core_wordComplement64 (hl : Labels st) {la : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .complement) [la]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word .w64 .complement) [la] := by
  word_run at hrun
  subst hrun
  refine word1_checked_core (ss1 := [.assign st.fresh (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1) (.bin .xor .w64 (.v st.fresh) (.imm 0xFFFFFFFFFFFFFFFF))])
    (r := st.fresh + 1) hF hH hC hl ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p wa ha hwa _
  exact ⟨_, _, by simp (disch := omega) only [lir_eval, ha, ↓reduceIte, ite_eq_right]; try rfl,
    by simp, wideComplement_toNat hwa, fun y hy => by regs_ne⟩

include hF hH hC ho hsup in
theorem core_wordNeg64 (hl : Labels st) {la : Lir.Arg}
    (hrun : (primitive f T x (.word .w64 .neg) [la]).run st = .ok ((), st')) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.word .w64 .neg) [la] := by
  word_run at hrun
  subst hrun
  refine word1_checked_core (ss1 := [.assign st.fresh (.bin .shr .w64 la (.imm 1)),
      .assign (st.fresh + 1) (.bin .sub .w64 (.imm 0) (.v st.fresh))])
    (r := st.fresh + 1) hF hH hC hl ho (by simp [Lir.Stmt.isCall]) ?_
  intro ρl mem p wa ha hwa _
  exact ⟨_, _, by simp (disch := omega) only [lir_eval, ha, ↓reduceIte, ite_eq_right]; try rfl,
    by simp, wideNeg_toNat hwa, fun y hy => by regs_ne⟩

end ops

/-! ## The dispatch -/

/-- The operations whose code is a `Nat` primitive's (`div`, `mod`, `land`, `lor`, `xor`): their
simulations transfer from the `Nat` primitives' in each route (`rhsSim_of_nat`). -/
def natCodeOp : WordOp → Bool
  | .div | .mod | .land | .lor | .xor => true
  | _ => false

theorem word_not_bool (w : Width) (o : WordOp) : ∀ ns b, (Lam.Prim.word w o).sem ns ≠ some (.bool b) :=
  fun ns b => by rw [Lam.Prim.sem_word]; exact Lam.wordSem_ne_bool w o ns b

/-- **The core of every other word operation's expansion.** -/
theorem word_core {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {sup : Nat} {fn : Nat}
    {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {w : Width} {o : WordOp} {las : List Lir.Arg}
    (hrun : (primitive f T x (.word w o) las).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st)
    (ho : Open st) (hsup : sup ≤ st.fresh) (hcode : natCodeOp o = false) :
    PrimCore lp ctx sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x (.word w o) las := by
  rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩
  · exfalso
    cases o <;> word_bad
  · cases o
    case complement =>
      by_cases hw : w = .w64
      · subst hw; exact core_wordComplement64 hF hH hC ho hsup hl hrun
      · exact core_wordComplementN hF hH hC ho hsup hw hrun
    case neg =>
      by_cases hw : w = .w64
      · subst hw; exact core_wordNeg64 hF hH hC ho hsup hl hrun
      · exact core_wordNegN hF hH hC ho hsup hw hrun
    case ofNat =>
      by_cases hw : w = .w64
      · subst hw; exact core_wordOfNat64 hF hH hC ho hrun
      · exact core_wordOfNatN hF hH hC ho hw hrun
    case toNat => exact core_wordToNat hF hH hC ho hrun
    case convert w' => exact core_wordConvert hF hH hC ho hrun
    all_goals exfalso; word_bad
  · cases o
    case add =>
      by_cases hw : w = .w64
      · subst hw; exact core_wordAdd64 hF hH hC ho hsup hl hrun
      · exact core_wordAddN hF hH hC ho hsup hw hrun
    case sub =>
      by_cases hw : w = .w64
      · subst hw; exact core_wordSub64 hF hH hC ho hsup hl hrun
      · exact core_wordSubN hF hH hC ho hsup hw hrun
    case mul =>
      by_cases hw : w = .w64
      · subst hw; exact core_wordMul64 hF hH hC ho hsup hl hrun
      · exact core_wordMulN hF hH hC ho hsup hw hrun
    case shiftLeft =>
      by_cases hw : w = .w64
      · subst hw; exact core_wordShl64 hF hH hC ho hsup hl hrun
      · exact core_wordShlN hF hH hC ho hsup hw hrun
    case shiftRight => exact core_wordShr hF hH hC ho hsup hrun
    case div => simp [natCodeOp] at hcode
    case mod => simp [natCodeOp] at hcode
    case land => simp [natCodeOp] at hcode
    case lor => simp [natCodeOp] at hcode
    case xor => simp [natCodeOp] at hcode
    all_goals exfalso; word_bad
  · exfalso
    cases o <;> word_bad

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
  cases o
  case div =>
    rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩ <;>
      first | exact prim_wordDiv hF hH hC ho hsup hx hlive hrun hops | (exfalso; word_bad)
  case mod =>
    rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩ <;>
      first | exact prim_wordMod hF hH hC ho hsup hx hlive hrun hops | (exfalso; word_bad)
  case land =>
    rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩ <;>
      first | exact prim_wordLand hF hH hC ho hsup hx hlive hrun hops | (exfalso; word_bad)
  case lor =>
    rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩ <;>
      first | exact prim_wordLor hF hH hC ho hsup hx hlive hrun hops | (exfalso; word_bad)
  case xor =>
    rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩ <;>
      first | exact prim_wordXor hF hH hC ho hsup hx hlive hrun hops | (exfalso; word_bad)
  all_goals exact rhsSim_of_core hops hlive hx (word_not_bool _ _) (word_core hF hH hrun hC hl ho hsup rfl)

end IxCC.Rt.Proof
