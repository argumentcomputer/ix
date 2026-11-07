import IxCC.Rt.Procs.Nat
import IxCC.Rt.Proof.Words
import IxCC.Lir.Proof.Eval

/-!
# The `Nat` runtime procedures

`rt_nat_gcd` and `rt_nat_pow` (`Rt.Procs.Nat`) are Lir functions that
`Rt.lower` calls for `natGcd` and `natPow`. From their entry with the words
of `x` and `y`, each reaches its `ret` with the word of the exact result
(`Nat.gcd x y`, `x ^ y`), or `rt_nat_pow` fails with `natOverflow`; their
loops charge the clock at their back edges.

* `natGcd_spec`: Euclid over `urem` on the untagged values, by strong
  induction on the second argument.
* `natPow_spec`: square-and-multiply; the loop keeps `acc · base^n = x^y`,
  `acc ≥ 1`, `base ≥ 2`, `n ≥ 1`, everything below `2^63`, and halves `n`
  each round. Each product it needs is checked by division and against
  `2^63`, so a passing check is exact.

`call_proc` turns a procedure's run into one step of its caller.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir
open IxCC.Rt.Procs

variable {p : Program} {mem : X86.Memory} {ctx : Word}

@[simp] theorem dispWord_one : dispWord 1 = 1 := by decide

@[simp] theorem Scale.word_one : X86.Scale.one.word = 1 := rfl

/-- `lea [q + q·1 + 1]`. -/
theorem retag_eval (ρ : Env) (ctx : Word) {q : VReg} {wq : Word} (h : ρ[q]? = some wq) :
    Addr.eval ρ ctx { base := some (.v q), index := some (q, .one), disp := 1 } = some (wq + wq + 1) := by
  simp [Addr.eval, h, UInt64.mul_one]

/-- A call into a procedure that returns `w`: the caller moves past the
call with its result register bound. -/
theorem call_proc {cf callee frEnd : Frame} {rest : List Frame} {x : VReg} {w : Word} {c : Nat}
    {F : Func} {B : Block} {as : List Arg}
    (hstep : step p { mem, ctx, stack := cf :: rest } =
      .next { mem, ctx, stack := callee :: { cf with pos := cf.pos + 1, dsts := [x] } :: rest } true)
    (hrun : Sem.Star (semStep p) { mem, ctx, stack := callee :: { cf with pos := cf.pos + 1, dsts := [x] } :: rest } c
      { mem, ctx, stack := frEnd :: { cf with pos := cf.pos + 1, dsts := [x] } :: rest })
    (hf : p.funcs[frEnd.fn]? = some F) (hb : F.blocks[frEnd.label]? = some B) (hpos : frEnd.pos = B.body.size)
    (ht : B.term = .ret as) (ha : evalArgs frEnd.env as = some [w]) :
    Sem.Star (semStep p) { mem, ctx, stack := cf :: rest } (1 + c + 0)
      { mem, ctx, stack := { cf with pos := cf.pos + 1, env := cf.env.insert x w, dsts := [] } :: rest } := by
  have h3 := step_ret_caller (p := p) (mem := mem) (ctx := ctx) (rest' := rest)
    (caller := { cf with pos := cf.pos + 1, dsts := [x] }) (ρ := cf.env.insert x w) hf hb hpos ht ha
    (by simp [bindParams])
  have := (Sem.Star.single (semStep_next.2 hstep)).trans (hrun.trans (Sem.Star.single (semStep_next.2 h3)))
  simpa using this

/-- Register lookups through inserts. -/
macro "regs" : tactic =>
  `(tactic| simp (config := { decide := true }) only [lir_eval, ↓reduceIte])

/-! ## `rt_nat_gcd` -/

theorem natGcd_b0 : natGcd.blocks[0]? = some { term := .jump ⟨1, [.v 0, .v 1]⟩ } := rfl
theorem natGcd_b1 : natGcd.blocks[1]? =
    some { params := [2, 3], term := .br .eq .w64 (.v 3) (.imm (UInt64.ofNat 1)) ⟨2, []⟩ ⟨3, []⟩ } := rfl
theorem natGcd_b2 : natGcd.blocks[2]? = some { term := .ret [.v 2] } := rfl
theorem natGcd_b3 : natGcd.blocks[3]? = some {
    body := #[.assign 4 (.bin .shr .w64 (.v 2) (.imm (UInt64.ofNat 1))),
      .assign 5 (.bin .shr .w64 (.v 3) (.imm (UInt64.ofNat 1))), .assign 6 (.bin .urem .w64 (.v 4) (.v 5)),
      .assign 7 (.addr { base := some (.v 6), index := some (6, .one), disp := 1 })]
    term := .jump ⟨1, [.v 3, .v 7]⟩ } := rfl

theorem gcd_step (a b : Nat) : Nat.gcd a b = Nat.gcd b (a % b) := by
  rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]

/-- The Euclid loop from its header with the words of `a` and `b` in `v2`,
`v3` reaches `ret v2` with the word of `gcd a b`. -/
theorem natGcd_loop {g : FunId} (hf : p.funcs[g]? = some natGcd) {rest : List Frame} :
    ∀ (b a : Nat) (ρ : Env) (wa wb : Word), natWord a = some wa → natWord b = some wb →
      ρ[2]? = some wa → ρ[3]? = some wb →
      ∃ c ρ' w, Sem.Star (semStep p) (atState mem ctx g 1 0 ρ rest) c (atState mem ctx g 2 0 ρ' rest) ∧
        ρ'[2]? = some w ∧ natWord (Nat.gcd a b) = some w := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
  intro a ρ wa wb ha hb h2 h3
  by_cases hb0 : b = 0
  · subst hb0
    have hw1 : wb = 1 := (natWord_eq_one hb).2 rfl
    have hs := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (e := ⟨2, []⟩) (va := wb)
      (vb := UInt64.ofNat 1) (vals := []) (ρ' := ρ) hf natGcd_b1 rfl rfl
      (by simp only [lir_eval, h3]) rfl (by simp only [lir_eval, hw1, ↓reduceIte, decide_true]) rfl natGcd_b2 rfl
    refine ⟨0, ρ, wa, star_of_step hs, h2, by simpa using ha⟩
  · have hne : wb ≠ 1 := fun h => hb0 ((natWord_eq_one hb).1 h)
    have hs1 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (e := ⟨3, []⟩) (va := wb)
      (vb := UInt64.ofNat 1) (vals := []) (ρ' := ρ) hf natGcd_b1 rfl rfl
      (by simp only [lir_eval, h3]) rfl (by simp [lir_eval, hne]) rfl natGcd_b3 rfl
    -- the body: untag, remainder, retag
    have hy0 : (wb >>> 1) ≠ 0 := by
      intro h
      have := untag_toNat hb
      rw [h] at this
      exact hb0 (by simpa using this.symm)
    have hq := natMod_word ha hb hb0
    let r := (wa >>> 1) % (wb >>> 1) + (wa >>> 1) % (wb >>> 1) + 1
    let ρ₁ := ((((ρ.insert 4 (wa >>> 1)).insert 5 (wb >>> 1)).insert 6 ((wa >>> 1) % (wb >>> 1))).insert 7 r)
    have hx : execList ρ mem ctx
        [.assign 4 (.bin .shr .w64 (.v 2) (.imm (UInt64.ofNat 1))),
          .assign 5 (.bin .shr .w64 (.v 3) (.imm (UInt64.ofNat 1))), .assign 6 (.bin .urem .w64 (.v 4) (.v 5)),
          .assign 7 (.addr { base := some (.v 6), index := some (6, .one), disp := 1 })] = some (ρ₁, mem) := by
      simp (config := { decide := true }) only [lir_eval, h2, h3, hy0, ↓reduceIte, UInt64.mul_one, ρ₁, r]
    have hstar := stmts_at (p := p) (ctx := ctx) (rest := rest) (pre := []) (post := []) hf natGcd_b3 rfl
      (by simp [Stmt.isCall]) hx
    have hs3 := jump_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 4) (ρ := ρ₁)
      (e := ⟨1, [.v 3, .v 7]⟩) (vals := [wb, r]) (ρ' := (ρ₁.insert 2 wb).insert 3 r) hf natGcd_b3 rfl rfl
      (by simp (config := { decide := true }) only [ρ₁, lir_eval, ↓reduceIte, h3]) natGcd_b1 (by regs)
    obtain ⟨c, ρ', w, hrun, hw2, hw⟩ := ih (a % b) (Nat.mod_lt _ (by omega)) b ((ρ₁.insert 2 wb).insert 3 r)
      wb r hb hq (by regs) (by regs)
    refine ⟨1 + c, ρ', w, ?_, hw2, by rw [gcd_step]; exact hw⟩
    have := (star_of_step hs1).trans (hstar.trans ((star_of_step hs3).trans hrun))
    simpa [Nat.add_comm] using this

/-- `rt_nat_gcd` from its entry with the words of `x` and `y` reaches its
`ret v2` with the word of `gcd x y`. -/
theorem natGcd_spec {g : FunId} (hf : p.funcs[g]? = some natGcd) {rest : List Frame} {x y : Nat}
    {wx wy : Word} (hx : natWord x = some wx) (hy : natWord y = some wy) :
    ∃ c ρ' w, Sem.Star (semStep p) (atState mem ctx g 0 0 ((({} : Env).insert 0 wx).insert 1 wy) rest) c
        (atState mem ctx g 2 0 ρ' rest) ∧ ρ'[2]? = some w ∧ natWord (Nat.gcd x y) = some w := by
  let ρ₀ : Env := (({} : Env).insert 0 wx).insert 1 wy
  have hs := jump_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρ₀)
    (e := ⟨1, [.v 0, .v 1]⟩) (vals := [wx, wy]) (ρ' := (ρ₀.insert 2 wx).insert 3 wy) hf natGcd_b0 rfl rfl
    (by simp (config := { decide := true }) only [ρ₀, lir_eval, ↓reduceIte]) natGcd_b1 (by regs)
  obtain ⟨c, ρ', w, hrun, hw2, hw⟩ := natGcd_loop (mem := mem) (ctx := ctx) hf y x
    ((ρ₀.insert 2 wx).insert 3 wy) wx wy hx hy (by regs) (by regs)
  exact ⟨0 + c, ρ', w, (star_of_step hs).trans hrun, hw2, hw⟩

end IxCC.Rt.Proof
