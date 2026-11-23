import IxCC.Rt.Procs.Nat
import IxCC.Rt.BigNat.Cell
import IxCC.Rt.Proof.Pow

/-! # Procedure-Level Phase 4 `BigNat` Specifications (`IxCC.Rt.BigNat.ProofProcs`)

Defines the zero-`natOverflow` failure predicate `FailsNoOvf`, the composable
LIR procedure contract `ProcSpec` (supporting both `.call` and `.tail` with
arbitrary memory updates `MemStep`), and proves exact specifications for the
upgraded Phase 4 runtime procedures in `IxCC.Rt.Procs.Nat`:

* `natGcdBig_proc_spec`: `Rt.Procs.natGcdBig slowGcd` computes exact `Nat.gcd`
  over all `NatVal` words (fast Euclid on small immediates, tail-call `slowGcd`
  on big operands) with ZERO `.natOverflow`.
* `natPowBig_proc_spec`: `Rt.Procs.natPowBig slowPow` computes exact `Nat.pow`
  over all `NatVal` words (fast square-and-multiply on small immediates,
  tail-call `slowPow` on big operands or any fixnum overflow) with ZERO `.natOverflow`.

Strictly standard axioms `[propext, Classical.choice, Quot.sound]`; zero `sorry`. -/

set_option autoImplicit false

namespace IxCC.Rt.BigNat

open IxCC.Lir
open IxCC.Rt
open IxCC.Rt.Procs
open IxCC.Rt.Proof

/-! ## Zero-`natOverflow` Resource Failure & Composable Procedure Contracts -/

/-- Explicit resource failure strictly excluding `.natOverflow`:
only genuine `.heap` or `.stack` exhaustion is permitted. -/
def FailsNoOvf (lp : Lir.Program) (s : Lir.State) : Prop :=
  ∃ c s' r, Sem.Star (Lir.semStep lp) s c s' ∧ Lir.semStep lp s' = .fail r ∧ r ≠ .natOverflow

theorem FailsNoOvf.prepend {lp : Lir.Program} {s s' : Lir.State} {c : Nat}
    (h : Sem.Star (Lir.semStep lp) s c s') (hf : FailsNoOvf lp s') : FailsNoOvf lp s := by
  obtain ⟨c', s'', r, h', hs, hne⟩ := hf
  exact ⟨c + c', s'', r, h.trans h', hs, hne⟩

theorem FailsNoOvf.toSemFails {lp : Lir.Program} {s : Lir.State} (hf : FailsNoOvf lp s) :
    Sem.Fails (Lir.semStep lp) s := by
  obtain ⟨c, s', r, h, hs, _⟩ := hf
  exact ⟨c, s', r, h, hs⟩

/-- Composable LIR procedure contract: entering `g` on `args` from `mem` and `ctx`
either returns to any suspended caller (with `caller.dsts = [x]`) binding `x` to `w`
in memory `mem'` satisfying `Post mem' w`, or fails without `.natOverflow`. -/
def ProcSpec (lp : Lir.Program) (g : Lir.FunId) (ctx : Word) (args : List Word)
    (mem : X86.Memory) (Post : X86.Memory → Word → Prop) : Prop :=
  ∃ callee, Lir.enter lp g args = some callee ∧
    ∀ (x : Lir.VReg) (caller : Lir.Frame) (rest : List Lir.Frame),
      caller.dsts = [x] →
      (∃ c mem' w,
          Sem.Star (Lir.semStep lp)
            { mem, ctx, stack := callee :: caller :: rest } c
            { mem := mem', ctx, stack := { caller with env := caller.env.insert x w, dsts := [] } :: rest } ∧
          Post mem' w) ∨
      FailsNoOvf lp { mem, ctx, stack := callee :: caller :: rest }

/-- Linked contract for a binary `Nat → Nat → Nat` slow-path procedure `g`. -/
def SlowNatBinSpec (lp : Lir.Program) (ctx : Word) (MemStep : X86.Memory → X86.Memory → Prop)
    (g : Lir.FunId) (f : Nat → Nat → Nat) : Prop :=
  ∀ (mem : X86.Memory) (p q : Nat) (wa wb : Word),
    NatVal mem p wa → NatVal mem q wb →
    ProcSpec lp g ctx [wa, wb] mem (fun mem' w => MemStep mem mem' ∧ NatVal mem' (f p q) w)

/-- Linked contract for a unary `Nat → Nat` slow-path procedure `g`. -/
def SlowNatUnSpec (lp : Lir.Program) (ctx : Word) (MemStep : X86.Memory → X86.Memory → Prop)
    (g : Lir.FunId) (f : Nat → Nat) : Prop :=
  ∀ (mem : X86.Memory) (p : Nat) (wa : Word),
    NatVal mem p wa →
    ProcSpec lp g ctx [wa] mem (fun mem' w => MemStep mem mem' ∧ NatVal mem' (f p) w)

/-- Linked contract for a binary `Nat → Nat → Bool` slow-path procedure `g`. -/
def SlowNatCmpSpec (lp : Lir.Program) (ctx : Word) (MemStep : X86.Memory → X86.Memory → Prop)
    (tWord fWord : Word) (g : Lir.FunId) (f : Nat → Nat → Bool) : Prop :=
  ∀ (mem : X86.Memory) (p q : Nat) (wa wb : Word),
    NatVal mem p wa → NatVal mem q wb →
    ProcSpec lp g ctx [wa, wb] mem (fun mem' w => MemStep mem mem' ∧ BoolVal tWord fWord (f p q) w)

/-- Execute a `.call [x] g as` statement using `ProcSpec`: steps the caller from `pos`
to `pos + 1` with `x` bound to `w` and `Post mem' w`, or fails with `FailsNoOvf`. -/
theorem call_procSpec {lp : Lir.Program} {ctx : Word} {mem : X86.Memory}
    {fn L pos : Nat} {F : Lir.Func} {B : Lir.Block} {ρ : Lir.Env} {rest : List Lir.Frame}
    {x : Lir.VReg} {g : Lir.FunId} {as : List Lir.Arg} {ws : List Word}
    {Post : X86.Memory → Word → Prop}
    (hF : lp.funcs[fn]? = some F) (hB : F.blocks[L]? = some B)
    (hpos : pos < B.body.size) (hcall : B.body[pos] = .call [x] g as)
    (hargs : Lir.evalArgs ρ as = some ws)
    (hspec : ProcSpec lp g ctx ws mem Post) :
    (∃ c mem' w,
        Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn L pos ρ rest) c
          (Lir.atState mem' ctx fn L (pos + 1) (ρ.insert x w) rest) ∧
        Post mem' w) ∨
    FailsNoOvf lp (Lir.atState mem ctx fn L pos ρ rest) := by
  obtain ⟨callee, henter, hrun⟩ := hspec
  let cf : Lir.Frame := { fn, label := L, pos, env := ρ }
  have hstep := Lir.step_call (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (fr := cf)
    hF hB hpos hcall hargs henter
  rcases hrun x { cf with pos := cf.pos + 1, dsts := [x] } rest rfl with
    ⟨c, mem', w, hstar, hpost⟩ | hfail
  · left
    refine ⟨1 + c, mem', w, ?_, hpost⟩
    exact (Lir.star_of_step hstep).trans hstar
  · right
    exact hfail.prepend (Lir.star_of_step hstep)

/-- Execute a `.tail g as` terminator using `ProcSpec` to deliver the result directly
to the suspended caller (or fail with `FailsNoOvf`). -/
theorem tail_procSpec {lp : Lir.Program} {ctx : Word} {mem : X86.Memory}
    {fn L pos : Nat} {F : Lir.Func} {B : Lir.Block} {ρ : Lir.Env}
    {x : Lir.VReg} {caller : Lir.Frame} {rest : List Lir.Frame}
    {g : Lir.FunId} {as : List Lir.Arg} {ws : List Word}
    {Post : X86.Memory → Word → Prop}
    (hF : lp.funcs[fn]? = some F) (hB : F.blocks[L]? = some B)
    (hpos : pos = B.body.size) (htail : B.term = .tail g as)
    (hargs : Lir.evalArgs ρ as = some ws)
    (hdsts : caller.dsts = [x])
    (hspec : ProcSpec lp g ctx ws mem Post) :
    (∃ c mem' w,
        Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn L pos ρ (caller :: rest)) c
          { mem := mem', ctx, stack := { caller with env := caller.env.insert x w, dsts := [] } :: rest } ∧
        Post mem' w) ∨
    FailsNoOvf lp (Lir.atState mem ctx fn L pos ρ (caller :: rest)) := by
  obtain ⟨callee, henter, hrun⟩ := hspec
  have hstep := Lir.step_tail (p := lp) (mem := mem) (ctx := ctx)
    (fr := { fn, label := L, pos, env := ρ }) (rest := caller :: rest)
    hF hB hpos htail hargs henter
  rcases hrun x caller rest hdsts with ⟨c, mem', w, hstar, hpost⟩ | hfail
  · left
    exact ⟨1 + c, mem', w, (Lir.star_of_step hstep).trans hstar, hpost⟩
  · right
    exact hfail.prepend (Lir.star_of_step hstep)

/-- Execute a `.ret [a]` terminator returning `w` to the suspended caller. -/
theorem ret_to_caller {lp : Lir.Program} {ctx : Word} {mem : X86.Memory}
    {fn L pos : Nat} {F : Lir.Func} {B : Lir.Block} {ρ : Lir.Env}
    {x : Lir.VReg} {caller : Lir.Frame} {rest : List Lir.Frame}
    {a : Lir.Arg} {w : Word}
    (hF : lp.funcs[fn]? = some F) (hB : F.blocks[L]? = some B)
    (hpos : pos = B.body.size) (hret : B.term = .ret [a])
    (ha : a.eval ρ = some w) (hdsts : caller.dsts = [x]) :
    Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn L pos ρ (caller :: rest)) 0
      { mem, ctx, stack := { caller with env := caller.env.insert x w, dsts := [] } :: rest } := by
  have hev : Lir.evalArgs ρ [a] = some [w] := by simp [Lir.evalArgs, ha]
  have hbp : Lir.bindParams caller.env caller.dsts [w] = some (caller.env.insert x w) := by
    simp [hdsts, Lir.bindParams]
  have hstep := Lir.step_ret_caller (p := lp) (mem := mem) (ctx := ctx)
    (fr := { fn, label := L, pos, env := ρ }) (caller := caller) (rest' := rest)
    hF hB hpos hret hev hbp
  exact Sem.Star.single (Lir.semStep_next.2 hstep)

/-! ## `rt_nat_gcd_big` Specification (`natGcdBig_proc_spec`) -/

private theorem natGcdBig_b0 (s : FunId) : (natGcdBig s).blocks[0]? = some {
    body := #[.assign 8 (.bin .and .w64 (.v 0) (.v 1))]
    term := .br .tz .w64 (.v 8) (.imm (UInt64.ofNat 1)) ⟨5, []⟩ ⟨1, []⟩ } := rfl
private theorem natGcdBig_b1 (s : FunId) : (natGcdBig s).blocks[1]? =
    some { term := .jump ⟨2, [.v 0, .v 1]⟩ } := rfl
private theorem natGcdBig_b2 (s : FunId) : (natGcdBig s).blocks[2]? =
    some { params := [2, 3], term := .br .eq .w64 (.v 3) (.imm (UInt64.ofNat 1)) ⟨3, []⟩ ⟨4, []⟩ } := rfl
private theorem natGcdBig_b3 (s : FunId) : (natGcdBig s).blocks[3]? =
    some { term := .ret [.v 2] } := rfl
private theorem natGcdBig_b4 (s : FunId) : (natGcdBig s).blocks[4]? = some {
    body := #[.assign 4 (.bin .shr .w64 (.v 2) (.imm (UInt64.ofNat 1))),
      .assign 5 (.bin .shr .w64 (.v 3) (.imm (UInt64.ofNat 1))),
      .assign 6 (.bin .urem .w64 (.v 4) (.v 5)),
      .assign 7 (.addr { base := some (.v 6), index := some (6, .one), disp := 1 })]
    term := .jump ⟨2, [.v 3, .v 7]⟩ } := rfl
private theorem natGcdBig_b5 (s : FunId) : (natGcdBig s).blocks[5]? =
    some { term := .tail s [.v 0, .v 1], cold := true } := rfl

private theorem natGcdBig_loop {lp : Program} {mem : X86.Memory} {ctx : Word}
    {g slowGcd : FunId} (hf : lp.funcs[g]? = some (natGcdBig slowGcd)) {rest : List Frame} :
    ∀ (b a : Nat) (ρ : Env) (wa wb : Word), natWord a = some wa → natWord b = some wb →
      ρ[2]? = some wa → ρ[3]? = some wb →
      ∃ c ρ' w, Sem.Star (semStep lp) (atState mem ctx g 2 0 ρ rest) c (atState mem ctx g 3 0 ρ' rest) ∧
        ρ'[2]? = some w ∧ natWord (Nat.gcd a b) = some w := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
  intro a ρ wa wb ha hb h2 h3
  by_cases hb0 : b = 0
  · subst hb0
    have hw1 : wb = 1 := (natWord_eq_one hb).2 rfl
    have hs := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (e := ⟨3, []⟩) (va := wb)
      (vb := UInt64.ofNat 1) (vals := []) (ρ' := ρ) hf (natGcdBig_b2 slowGcd) rfl rfl
      (by simp only [lir_eval, h3]) rfl (by simp only [lir_eval, hw1, ↓reduceIte, decide_true])
      rfl (natGcdBig_b3 slowGcd) rfl
    refine ⟨0, ρ, wa, star_of_step hs, h2, by simpa using ha⟩
  · have hne : wb ≠ 1 := fun h => hb0 ((natWord_eq_one hb).1 h)
    have hs1 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (e := ⟨4, []⟩) (va := wb)
      (vb := UInt64.ofNat 1) (vals := []) (ρ' := ρ) hf (natGcdBig_b2 slowGcd) rfl rfl
      (by simp only [lir_eval, h3]) rfl (by simp [lir_eval, hne]) rfl (natGcdBig_b4 slowGcd) rfl
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
          .assign 5 (.bin .shr .w64 (.v 3) (.imm (UInt64.ofNat 1))),
          .assign 6 (.bin .urem .w64 (.v 4) (.v 5)),
          .assign 7 (.addr { base := some (.v 6), index := some (6, .one), disp := 1 })] =
        some (ρ₁, mem) := by
      simp (config := { decide := true }) only [lir_eval, h2, h3, hy0, ↓reduceIte, UInt64.mul_one, ρ₁, r]
    have hstar := stmts_at (p := lp) (ctx := ctx) (rest := rest) (pre := []) (post := [])
      hf (natGcdBig_b4 slowGcd) rfl (by simp [Stmt.isCall]) hx
    have hs4 := jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (pos := 4) (ρ := ρ₁)
      (e := ⟨2, [.v 3, .v 7]⟩) (vals := [wb, r]) (ρ' := (ρ₁.insert 2 wb).insert 3 r)
      hf (natGcdBig_b4 slowGcd) rfl rfl
      (by simp (config := { decide := true }) only [ρ₁, lir_eval, ↓reduceIte, h3])
      (natGcdBig_b2 slowGcd) (by simp (config := { decide := true }) only [lir_eval])
    obtain ⟨c, ρ', w, hrun, hw2, hw⟩ := ih (a % b) (Nat.mod_lt _ (by omega)) b
      ((ρ₁.insert 2 wb).insert 3 r) wb r hb hq
      (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte])
      (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte])
    refine ⟨1 + c, ρ', w, ?_, hw2, by rw [gcd_step]; exact hw⟩
    have := (star_of_step hs1).trans (hstar.trans ((star_of_step hs4).trans hrun))
    simpa [Nat.add_comm] using this

/-- **`rt_nat_gcd_big` computes exact `Nat.gcd` across ALL arbitrary-precision `NatVal`s
(small or big) with ZERO `.natOverflow`.** -/
theorem natGcdBig_proc_spec {lp : Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {g slowGcd : FunId} (hf : lp.funcs[g]? = some (natGcdBig slowGcd))
    (hslow : SlowNatBinSpec lp ctx MemStep slowGcd Nat.gcd) :
    SlowNatBinSpec lp ctx MemStep g Nat.gcd := by
  intro mem p q wa wb hpa hqb
  refine ⟨{ fn := g, label := 0, pos := 0, env := (({} : Env).insert 0 wa).insert 1 wb }, ?_, ?_⟩
  · simp [Lir.enter, hf, natGcdBig, Lir.bindParams]
  · intro x caller rest hdsts
    let ρ₀ : Env := (({} : Env).insert 0 wa).insert 1 wb
    let ρ₁ : Env := ρ₀.insert 8 (wa &&& wb)
    have hx0 : execList ρ₀ mem ctx [.assign 8 (.bin .and .w64 (.v 0) (.v 1))] = some (ρ₁, mem) := by
      simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₀, ρ₁]
    have hstar0 := stmts_at (p := lp) (ctx := ctx) (rest := caller :: rest) (pre := []) (post := [])
      hf (natGcdBig_b0 slowGcd) rfl (by simp [Stmt.isCall]) hx0
    cases htz : Cond.holds .tz .w64 (wa &&& wb) 1 with
    | true =>
      have hs0 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 1)
        (ρ := ρ₁) (e := ⟨5, []⟩) (va := wa &&& wb) (vb := UInt64.ofNat 1) (vals := []) (ρ' := ρ₁)
        hf (natGcdBig_b0 slowGcd) rfl rfl
        (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
        rfl (by simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, htz, ↓reduceIte])
        rfl (natGcdBig_b5 slowGcd) rfl
      have hargs : evalArgs ρ₁ [.v 0, .v 1] = some [wa, wb] := by
        simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁, ρ₀]
      rcases tail_procSpec hf (natGcdBig_b5 slowGcd) rfl rfl hargs hdsts (hslow mem p q wa wb hpa hqb) with
        ⟨c, mem', w, htail, hpost⟩ | hfail
      · left
        exact ⟨_, mem', w, hstar0.trans ((star_of_step hs0).trans htail), hpost⟩
      · right
        exact hfail.prepend (hstar0.trans (star_of_step hs0))
    | false =>
      obtain ⟨hwa, hwb⟩ := (NatVal.and_tz_one_false_iff hpa hqb).mp htz
      have hs0 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 1)
        (ρ := ρ₁) (e := ⟨1, []⟩) (va := wa &&& wb) (vb := UInt64.ofNat 1) (vals := []) (ρ' := ρ₁)
        hf (natGcdBig_b0 slowGcd) rfl rfl
        (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
        rfl (by simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, htz, Bool.false_eq_true, ↓reduceIte])
        rfl (natGcdBig_b1 slowGcd) rfl
      have hs1 := jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 0)
        (ρ := ρ₁) (e := ⟨2, [.v 0, .v 1]⟩) (vals := [wa, wb]) (ρ' := (ρ₁.insert 2 wa).insert 3 wb)
        hf (natGcdBig_b1 slowGcd) rfl rfl
        (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁, ρ₀])
        (natGcdBig_b2 slowGcd) (by simp (config := { decide := true }) only [lir_eval])
      obtain ⟨c, ρ', w, hloop, h2, hw⟩ := natGcdBig_loop (mem := mem) (ctx := ctx)
        (rest := caller :: rest) hf q p ((ρ₁.insert 2 wa).insert 3 wb) wa wb hwa hwb
        (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte])
        (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte])
      have hret := ret_to_caller (ctx := ctx) (mem := mem) (ρ := ρ') (w := w) (caller := caller) (rest := rest)
        hf (natGcdBig_b3 slowGcd) rfl rfl (by simp [Arg.eval, h2]) hdsts
      left
      refine ⟨_, mem, w,
        hstar0.trans ((star_of_step hs0).trans ((star_of_step hs1).trans (hloop.trans hret))),
        hrefl mem, .small hw⟩

/-! ## `rt_nat_pow_big` Specification (`natPowBig_proc_spec`) -/

private theorem natPowBig_b0 (s : FunId) : (natPowBig s).blocks[0]? = some {
    body := #[.assign 22 (.bin .and .w64 (.v 0) (.v 1))]
    term := .br .tz .w64 (.v 22) (.imm (UInt64.ofNat 1)) ⟨15, []⟩ ⟨1, []⟩ } := rfl
private theorem natPowBig_b1 (s : FunId) : (natPowBig s).blocks[1]? = some {
    body := #[.assign 2 (.bin .shr .w64 (.v 0) (.imm (UInt64.ofNat 1))),
      .assign 3 (.bin .shr .w64 (.v 1) (.imm (UInt64.ofNat 1)))]
    term := .br .eq .w64 (.v 3) (.imm (UInt64.ofNat 0)) ⟨2, []⟩ ⟨3, []⟩ } := rfl
private theorem natPowBig_b2 (s : FunId) : (natPowBig s).blocks[2]? =
    some { term := .ret [.imm (UInt64.ofNat 3)] } := rfl
private theorem natPowBig_b3 (s : FunId) : (natPowBig s).blocks[3]? =
    some { term := .br .ule .w64 (.v 2) (.imm (UInt64.ofNat 1)) ⟨4, []⟩ ⟨5, []⟩ } := rfl
private theorem natPowBig_b4 (s : FunId) : (natPowBig s).blocks[4]? =
    some { term := .ret [.v 0] } := rfl
private theorem natPowBig_b5 (s : FunId) : (natPowBig s).blocks[5]? =
    some { term := .br .ugt .w64 (.v 3) (.imm (UInt64.ofNat 62)) ⟨6, []⟩ ⟨7, []⟩ } := rfl
private theorem natPowBig_b6 (s : FunId) : (natPowBig s).blocks[6]? =
    some { term := .tail s [.v 0, .v 1], cold := true } := rfl
private theorem natPowBig_b7 (s : FunId) : (natPowBig s).blocks[7]? =
    some { term := .jump ⟨8, [.imm (UInt64.ofNat 1), .v 2, .v 3]⟩ } := rfl
private theorem natPowBig_b8 (s : FunId) : (natPowBig s).blocks[8]? = some {
    params := [4, 5, 6]
    body := #[.assign 7 (.bin .and .w64 (.v 6) (.imm (UInt64.ofNat 1))),
      .assign 8 (.bin .mul .w64 (.v 4) (.v 5)), .assign 9 (.bin .udiv .w64 (.v 8) (.v 4)),
      .assign 10 (.test .ne .w64 (.v 9) (.v 5)),
      .assign 11 (.test .slt .w64 (.v 8) (.imm (UInt64.ofNat 0))),
      .assign 12 (.bin .or .w64 (.v 10) (.v 11)), .assign 13 (.bin .and .w64 (.v 12) (.v 7))]
    term := .br .ne .w64 (.v 13) (.imm (UInt64.ofNat 0)) ⟨9, []⟩ ⟨10, []⟩ } := rfl
private theorem natPowBig_b9 (s : FunId) : (natPowBig s).blocks[9]? =
    some { term := .tail s [.v 0, .v 1], cold := true } := rfl
private theorem natPowBig_b10 (s : FunId) : (natPowBig s).blocks[10]? = some {
    body := #[.assign 14 (.select .eq .w64 (.v 7) (.imm (UInt64.ofNat 0)) (.v 4) (.v 8)),
      .assign 15 (.bin .shr .w64 (.v 6) (.imm (UInt64.ofNat 1)))]
    term := .br .eq .w64 (.v 15) (.imm (UInt64.ofNat 0)) ⟨11, []⟩ ⟨12, []⟩ } := rfl
private theorem natPowBig_b11 (s : FunId) : (natPowBig s).blocks[11]? = some {
    body := #[.assign 16 (.addr { base := some (.v 14), index := some (14, .one), disp := 1 })]
    term := .ret [.v 16] } := rfl
private theorem natPowBig_b12 (s : FunId) : (natPowBig s).blocks[12]? = some {
    body := #[.assign 17 (.bin .mul .w64 (.v 5) (.v 5)),
      .assign 18 (.bin .udiv .w64 (.v 17) (.v 5)),
      .assign 19 (.test .ne .w64 (.v 18) (.v 5)),
      .assign 20 (.test .slt .w64 (.v 17) (.imm (UInt64.ofNat 0))),
      .assign 21 (.bin .or .w64 (.v 19) (.v 20))]
    term := .br .ne .w64 (.v 21) (.imm (UInt64.ofNat 0)) ⟨13, []⟩ ⟨14, []⟩ } := rfl
private theorem natPowBig_b13 (s : FunId) : (natPowBig s).blocks[13]? =
    some { term := .tail s [.v 0, .v 1], cold := true } := rfl
private theorem natPowBig_b14 (s : FunId) : (natPowBig s).blocks[14]? =
    some { term := .jump ⟨8, [.v 14, .v 17, .v 15]⟩ } := rfl
private theorem natPowBig_b15 (s : FunId) : (natPowBig s).blocks[15]? =
    some { term := .tail s [.v 0, .v 1], cold := true } := rfl

/-- Square-and-multiply loop of `rt_nat_pow_big` from block 8: either reaches block 11's
`ret v16` with the tagged word of `A * Bs ^ N`, or tail-calls `slowPow [wa, wb]` on overflow
(delivering `Post mem' w` to `caller` or `FailsNoOvf`). -/
private theorem natPowBig_loop {lp : Program} {mem : X86.Memory} {ctx : Word}
    {g slowPow : FunId} (hf : lp.funcs[g]? = some (natPowBig slowPow))
    {wa wb : Word} {x : VReg} {caller : Frame} {rest : List Frame}
    {Post : X86.Memory → Word → Prop}
    (hdsts : caller.dsts = [x])
    (hslow : ProcSpec lp slowPow ctx [wa, wb] mem Post) :
    ∀ (N A Bs : Nat) (ρ : Env) (acc base nw : Word),
      acc.toNat = A → base.toNat = Bs → nw.toNat = N →
      1 ≤ A → A < 2 ^ 63 → 2 ≤ Bs → Bs < 2 ^ 63 → 1 ≤ N →
      ρ[0]? = some wa → ρ[1]? = some wb →
      ρ[4]? = some acc → ρ[5]? = some base → ρ[6]? = some nw →
      (∃ c ρ' w,
          Sem.Star (semStep lp) (atState mem ctx g 8 0 ρ (caller :: rest)) c
            (atState mem ctx g 11 1 ρ' (caller :: rest)) ∧
          ρ'[16]? = some w ∧ natWord (A * Bs ^ N) = some w) ∨
      (∃ c mem' w,
          Sem.Star (semStep lp) (atState mem ctx g 8 0 ρ (caller :: rest)) c
            { mem := mem', ctx, stack := { caller with env := caller.env.insert x w, dsts := [] } :: rest } ∧
          Post mem' w) ∨
      FailsNoOvf lp (atState mem ctx g 8 0 ρ (caller :: rest)) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
  intro A Bs ρ acc base nw hA hB hN hA1 hA2 hB1 hB2 hN1 h0 h1 h4 h5 h6
  have hacc0 : acc ≠ 0 := word_ne_zero (by omega)
  have hbase0 : base ≠ 0 := word_ne_zero (by omega)
  let bit := nw &&& UInt64.ofNat 1
  let prod := acc * base
  let t10 : Word := if prod / acc ≠ base then 1 else 0
  let t11 : Word := if 2 ^ 63 ≤ prod.toNat then 1 else 0
  let ρ₈ := (((((((ρ.insert 7 bit).insert 8 prod).insert 9 (prod / acc)).insert 10 t10).insert 11 t11).insert 12
    (t10 ||| t11)).insert 13 ((t10 ||| t11) &&& bit))
  have hx8 : execList ρ mem ctx
      [.assign 7 (.bin .and .w64 (.v 6) (.imm (UInt64.ofNat 1))),
        .assign 8 (.bin .mul .w64 (.v 4) (.v 5)), .assign 9 (.bin .udiv .w64 (.v 8) (.v 4)),
        .assign 10 (.test .ne .w64 (.v 9) (.v 5)),
        .assign 11 (.test .slt .w64 (.v 8) (.imm (UInt64.ofNat 0))),
        .assign 12 (.bin .or .w64 (.v 10) (.v 11)), .assign 13 (.bin .and .w64 (.v 12) (.v 7))] =
      some (ρ₈, mem) := by
    simp (config := { decide := true }) only [lir_eval, ↓reduceIte, h4, h5, h6, hacc0, holds_slt_zero]
    simp [ρ₈, t10, t11, prod, bit]
  have hstar8 := stmts_at (p := lp) (ctx := ctx) (rest := caller :: rest) (pre := []) (post := [])
    hf (natPowBig_b8 slowPow) rfl (by simp [Stmt.isCall]) hx8
  have hbit := bit_cases nw
  have hbitN := bit_toNat nw
  by_cases ht13 : (t10 ||| t11) &&& bit = 0
  · have hround := (round_flag hbit).1 ht13
    let acc' := if bit = 0 then acc else prod
    have hacc' : acc'.toNat = (if N % 2 = 1 then A * Bs else A) ∧ acc'.toNat < 2 ^ 63 := by
      rcases hbit with hb0 | hb1
      · have : N % 2 = 0 := by rw [← hN, ← hbitN]; show (nw &&& UInt64.ofNat 1).toNat = 0; rw [hb0]; rfl
        simp only [acc', show bit = 0 from hb0, ↓reduceIte, this]
        exact ⟨hA, by omega⟩
      · have : N % 2 = 1 := by rw [← hN, ← hbitN]; show (nw &&& UInt64.ofNat 1).toNat = 1; rw [hb1]; rfl
        obtain ⟨hq, hlt⟩ := hround hb1
        have hne : bit ≠ 0 := by rw [show bit = 1 from hb1]; decide
        simp only [acc', hne, ↓reduceIte, this]
        refine ⟨?_, hlt⟩
        rw [checked_mul (by omega) hq hlt, hA, hB]
    have hs8 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 7)
      (ρ := ρ₈) (e := ⟨10, []⟩) (va := (t10 ||| t11) &&& bit) (vb := UInt64.ofNat 0)
      (vals := []) (ρ' := ρ₈) hf (natPowBig_b8 slowPow) rfl rfl
      (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₈])
      rfl (by simp only [lir_eval, ht13]; simp) rfl (natPowBig_b10 slowPow) rfl
    let half := nw >>> 1
    have hhalf : half.toNat = N / 2 := by
      have := half_toNat nw
      rw [and63_one] at this
      rw [← hN]; exact this
    let ρ₁₀ := (ρ₈.insert 14 acc').insert 15 half
    have hx10 : execList ρ₈ mem ctx
        [.assign 14 (.select .eq .w64 (.v 7) (.imm (UInt64.ofNat 0)) (.v 4) (.v 8)),
          .assign 15 (.bin .shr .w64 (.v 6) (.imm (UInt64.ofNat 1)))] = some (ρ₁₀, mem) := by
      simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₈, h4, h6]
      simp [ρ₁₀, acc', half]
      rfl
    have hstar10 := stmts_at (p := lp) (ctx := ctx) (rest := caller :: rest) (pre := []) (post := [])
      hf (natPowBig_b10 slowPow) rfl (by simp [Stmt.isCall]) hx10
    by_cases hN2 : N / 2 = 0
    · have hNodd : N % 2 = 1 := by omega
      have hhalf0 : half = 0 := UInt64.toNat_inj.mp (by rw [hhalf, hN2]; rfl)
      have hs10 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 2)
        (ρ := ρ₁₀) (e := ⟨11, []⟩) (va := half) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₁₀)
        hf (natPowBig_b10 slowPow) rfl rfl
        (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₀])
        rfl (by simp only [lir_eval, hhalf0]; simp) rfl (natPowBig_b11 slowPow) rfl
      let w := acc' + acc' + 1
      have hx11 : execList ρ₁₀ mem ctx
          [.assign 16 (.addr { base := some (.v 14), index := some (14, .one), disp := 1 })] =
          some (ρ₁₀.insert 16 w, mem) := by
        simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₀, UInt64.mul_one]
        rfl
      have hstar11 := stmts_at (p := lp) (ctx := ctx) (rest := caller :: rest) (pre := []) (post := [])
        hf (natPowBig_b11 slowPow) rfl (by simp [Stmt.isCall]) hx11
      left
      refine ⟨0, ρ₁₀.insert 16 w, w, ?_, by simp, ?_⟩
      · have := hstar8.trans ((star_of_step hs8).trans (hstar10.trans ((star_of_step hs10).trans hstar11)))
        simpa using this
      · have hN' : N = 1 := by omega
        subst hN'
        obtain ⟨h1a, h2a⟩ := hacc'
        simp only [hNodd, ↓reduceIte] at h1a
        refine natWord_iff.2 ⟨by rw [Nat.pow_one]; omega, ?_⟩
        rw [retag_toNat h2a, h1a, Nat.pow_one]
    · have hhalfne : half ≠ 0 := fun h => hN2 (by rw [← hhalf, h]; rfl)
      have hs10 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 2)
        (ρ := ρ₁₀) (e := ⟨12, []⟩) (va := half) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₁₀)
        hf (natPowBig_b10 slowPow) rfl rfl
        (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₀])
        rfl (by simp only [lir_eval]; simp [hhalfne]) rfl (natPowBig_b12 slowPow) rfl
      let sq := base * base
      let t19 : Word := if sq / base ≠ base then 1 else 0
      let t20 : Word := if 2 ^ 63 ≤ sq.toNat then 1 else 0
      let ρ₁₂ := ((((ρ₁₀.insert 17 sq).insert 18 (sq / base)).insert 19 t19).insert 20 t20).insert 21 (t19 ||| t20)
      have hx12 : execList ρ₁₀ mem ctx
          [.assign 17 (.bin .mul .w64 (.v 5) (.v 5)), .assign 18 (.bin .udiv .w64 (.v 17) (.v 5)),
            .assign 19 (.test .ne .w64 (.v 18) (.v 5)),
            .assign 20 (.test .slt .w64 (.v 17) (.imm (UInt64.ofNat 0))),
            .assign 21 (.bin .or .w64 (.v 19) (.v 20))] = some (ρ₁₂, mem) := by
        simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₀, ρ₈, h5, hbase0, holds_slt_zero]
        simp [ρ₁₂, t19, t20, sq]
        rfl
      have hstar12 := stmts_at (p := lp) (ctx := ctx) (rest := caller :: rest) (pre := []) (post := [])
        hf (natPowBig_b12 slowPow) rfl (by simp [Stmt.isCall]) hx12
      by_cases h21 : t19 ||| t20 = 0
      · obtain ⟨hsq, hsqlt⟩ := square_flag.1 h21
        have hsqN : sq.toNat = Bs * Bs := by rw [checked_mul (by omega) hsq hsqlt, hB]
        have hs12 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 5)
          (ρ := ρ₁₂) (e := ⟨14, []⟩) (va := t19 ||| t20) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₁₂)
          hf (natPowBig_b12 slowPow) rfl rfl
          (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₂])
          rfl (by simp only [lir_eval, h21]; simp) rfl (natPowBig_b14 slowPow) rfl
        let ρ₁₄ := ((ρ₁₂.insert 4 acc').insert 5 sq).insert 6 half
        have hs14 := jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 0)
          (ρ := ρ₁₂) (e := ⟨8, [.v 14, .v 17, .v 15]⟩) (vals := [acc', sq, half]) (ρ' := ρ₁₄)
          hf (natPowBig_b14 slowPow) rfl rfl
          (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₂, ρ₁₀])
          (natPowBig_b8 slowPow)
          (by simp (config := { decide := true }) only [lir_eval, ρ₁₄])
        have hpre := hstar8.trans ((star_of_step hs8).trans (hstar10.trans
          ((star_of_step hs10).trans (hstar12.trans ((star_of_step hs12).trans (star_of_step hs14))))))
        have hA'1 : 1 ≤ (if N % 2 = 1 then A * Bs else A) := by
          split
          · exact Nat.le_trans hA1 (Nat.le_mul_of_pos_right A (by omega))
          · exact hA1
        have hBs2 : 2 ≤ Bs * Bs := Nat.le_trans hB1 (Nat.le_mul_of_pos_right Bs (by omega))
        have hrec := ih (N / 2) (Nat.div_lt_self (by omega) (by decide))
          (if N % 2 = 1 then A * Bs else A) (Bs * Bs) ρ₁₄ acc' sq half
          hacc'.1 hsqN hhalf hA'1 (by rw [← hacc'.1]; exact hacc'.2) hBs2 (by omega) (by omega)
          (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₄, ρ₁₂, ρ₁₀, ρ₈, h0])
          (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₄, ρ₁₂, ρ₁₀, ρ₈, h1])
          (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₄])
          (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₄])
          (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₄])
        rcases hrec with ⟨c, ρ', w, hrun, h16, hw⟩ | ⟨c, mem', w, hrun, hpost⟩ | hfail
        · left
          exact ⟨_, ρ', w, hpre.trans hrun, h16, by rw [pow_round]; exact hw⟩
        · right; left
          exact ⟨_, mem', w, hpre.trans hrun, hpost⟩
        · right; right
          exact hfail.prepend hpre
      · -- base * base overflow → b13 tail-calls slowPow
        have hs12 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 5)
          (ρ := ρ₁₂) (e := ⟨13, []⟩) (va := t19 ||| t20) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₁₂)
          hf (natPowBig_b12 slowPow) rfl rfl
          (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₂])
          rfl (by simp only [lir_eval]; simp [h21]) rfl (natPowBig_b13 slowPow) rfl
        have hpre := hstar8.trans ((star_of_step hs8).trans (hstar10.trans
          ((star_of_step hs10).trans (hstar12.trans (star_of_step hs12)))))
        have hargs : evalArgs ρ₁₂ [.v 0, .v 1] = some [wa, wb] := by
          simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₂, ρ₁₀, ρ₈, h0, h1]
        rcases tail_procSpec hf (natPowBig_b13 slowPow) rfl rfl hargs hdsts hslow with
          ⟨c, mem', w, htail, hpost⟩ | hfail
        · right; left
          exact ⟨_, mem', w, hpre.trans htail, hpost⟩
        · right; right
          exact hfail.prepend hpre
  · -- acc * base overflow → b9 tail-calls slowPow
    have hs8 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 7)
      (ρ := ρ₈) (e := ⟨9, []⟩) (va := (t10 ||| t11) &&& bit) (vb := UInt64.ofNat 0)
      (vals := []) (ρ' := ρ₈) hf (natPowBig_b8 slowPow) rfl rfl
      (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₈])
      rfl (by simp only [lir_eval]; simp [ht13]) rfl (natPowBig_b9 slowPow) rfl
    have hpre := hstar8.trans (star_of_step hs8)
    have hargs : evalArgs ρ₈ [.v 0, .v 1] = some [wa, wb] := by
      simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₈, h0, h1]
    rcases tail_procSpec hf (natPowBig_b9 slowPow) rfl rfl hargs hdsts hslow with
      ⟨c, mem', w, htail, hpost⟩ | hfail
    · right; left
      exact ⟨_, mem', w, hpre.trans htail, hpost⟩
    · right; right
      exact hfail.prepend hpre

/-- **`rt_nat_pow_big` computes exact `Nat.pow` across ALL arbitrary-precision `NatVal`s
(small or big) with ZERO `.natOverflow`.** -/
theorem natPowBig_proc_spec {lp : Program} {ctx : Word}
    {MemStep : X86.Memory → X86.Memory → Prop} (hrefl : ∀ m, MemStep m m)
    {g slowPow : FunId} (hf : lp.funcs[g]? = some (natPowBig slowPow))
    (hslow : SlowNatBinSpec lp ctx MemStep slowPow (· ^ ·)) :
    SlowNatBinSpec lp ctx MemStep g (· ^ ·) := by
  intro mem p q wa wb hpa hqb
  refine ⟨{ fn := g, label := 0, pos := 0, env := (({} : Env).insert 0 wa).insert 1 wb }, ?_, ?_⟩
  · simp [Lir.enter, hf, natPowBig, Lir.bindParams]
  · intro x caller rest hdsts
    let ρ₀ : Env := (({} : Env).insert 0 wa).insert 1 wb
    let ρt : Env := ρ₀.insert 22 (wa &&& wb)
    have hx0 : execList ρ₀ mem ctx [.assign 22 (.bin .and .w64 (.v 0) (.v 1))] = some (ρt, mem) := by
      simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₀, ρt]
    have hstar0 := stmts_at (p := lp) (ctx := ctx) (rest := caller :: rest) (pre := []) (post := [])
      hf (natPowBig_b0 slowPow) rfl (by simp [Stmt.isCall]) hx0
    cases htz : Cond.holds .tz .w64 (wa &&& wb) 1 with
    | true =>
      have hs0 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 1)
        (ρ := ρt) (e := ⟨15, []⟩) (va := wa &&& wb) (vb := UInt64.ofNat 1) (vals := []) (ρ' := ρt)
        hf (natPowBig_b0 slowPow) rfl rfl
        (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρt])
        rfl (by simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, htz, ↓reduceIte])
        rfl (natPowBig_b15 slowPow) rfl
      have hargs : evalArgs ρt [.v 0, .v 1] = some [wa, wb] := by
        simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρt, ρ₀]
      rcases tail_procSpec hf (natPowBig_b15 slowPow) rfl rfl hargs hdsts (hslow mem p q wa wb hpa hqb) with
        ⟨c, mem', w, htail, hpost⟩ | hfail
      · left
        exact ⟨_, mem', w, hstar0.trans ((star_of_step hs0).trans htail), hpost⟩
      · right
        exact hfail.prepend (hstar0.trans (star_of_step hs0))
    | false =>
      obtain ⟨hwa, hwb⟩ := (NatVal.and_tz_one_false_iff hpa hqb).mp htz
      have hp_lt := natWord_lt hwa
      have hq_lt := natWord_lt hwb
      have hu := untag_toNat hwa
      have hv := untag_toNat hwb
      have hs0 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 1)
        (ρ := ρt) (e := ⟨1, []⟩) (va := wa &&& wb) (vb := UInt64.ofNat 1) (vals := []) (ρ' := ρt)
        hf (natPowBig_b0 slowPow) rfl rfl
        (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρt])
        rfl (by simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, htz, Bool.false_eq_true, ↓reduceIte])
        rfl (natPowBig_b1 slowPow) rfl
      let ρ₁ : Env := (ρt.insert 2 (wa >>> 1)).insert 3 (wb >>> 1)
      have hx1 : execList ρt mem ctx
          [.assign 2 (.bin .shr .w64 (.v 0) (.imm (UInt64.ofNat 1))),
            .assign 3 (.bin .shr .w64 (.v 1) (.imm (UInt64.ofNat 1)))] = some (ρ₁, mem) := by
        simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρt, ρ₀, ρ₁]
      have hstar1 := stmts_at (p := lp) (ctx := ctx) (rest := caller :: rest) (pre := []) (post := [])
        hf (natPowBig_b1 slowPow) rfl (by simp [Stmt.isCall]) hx1
      have hpre1 := hstar0.trans ((star_of_step hs0).trans hstar1)
      by_cases hq0 : q = 0
      · subst hq0
        have hv0 : wb >>> 1 = 0 := UInt64.toNat_inj.mp (by rw [hv]; rfl)
        have hs1 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 2)
          (ρ := ρ₁) (e := ⟨2, []⟩) (va := wb >>> 1) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₁)
          hf (natPowBig_b1 slowPow) rfl rfl
          (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
          rfl (by simp only [lir_eval, hv0]; simp) rfl (natPowBig_b2 slowPow) rfl
        have hret := ret_to_caller (ctx := ctx) (mem := mem) (ρ := ρ₁) (w := UInt64.ofNat 3) (caller := caller) (rest := rest)
          hf (natPowBig_b2 slowPow) rfl rfl rfl hdsts
        left
        refine ⟨_, mem, UInt64.ofNat 3, hpre1.trans ((star_of_step hs1).trans hret),
          hrefl mem, .small (by dsimp only; rw [Nat.pow_zero]; exact natWord_of_lt (by decide))⟩
      · have hvne : wb >>> 1 ≠ 0 := fun h => hq0 (by rw [← hv, h]; rfl)
        have hs1 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 2)
          (ρ := ρ₁) (e := ⟨3, []⟩) (va := wb >>> 1) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₁)
          hf (natPowBig_b1 slowPow) rfl rfl
          (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
          rfl (by simp only [lir_eval]; simp [hvne]) rfl (natPowBig_b3 slowPow) rfl
        by_cases hp1 : p ≤ 1
        · have hule : (wa >>> 1) ≤ (1 : Word) := by
            rw [UInt64.le_iff_toNat_le, hu]; exact hp1
          have hs3 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 0)
            (ρ := ρ₁) (e := ⟨4, []⟩) (va := wa >>> 1) (vb := UInt64.ofNat 1) (vals := []) (ρ' := ρ₁)
            hf (natPowBig_b3 slowPow) rfl rfl
            (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
            rfl (by simp only [lir_eval, hule, ↓reduceIte]) rfl (natPowBig_b4 slowPow) rfl
          have hret := ret_to_caller (ctx := ctx) (mem := mem) (ρ := ρ₁) (w := wa) (caller := caller) (rest := rest)
            hf (natPowBig_b4 slowPow) rfl rfl
            (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁, ρt, ρ₀]) hdsts
          have hpow : p ^ q = p := by
            rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
            · exact Nat.zero_pow (by omega)
            · exact Nat.one_pow q
          left
          refine ⟨_, mem, wa, hpre1.trans ((star_of_step hs1).trans ((star_of_step hs3).trans hret)),
            hrefl mem, by dsimp only; rw [hpow]; exact .small hwa⟩
        · have hnotle : ¬ (wa >>> 1) ≤ (1 : Word) := by
            rw [UInt64.le_iff_toNat_le, hu, show (1 : Word).toNat = 1 from rfl]; omega
          have hs3 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 0)
            (ρ := ρ₁) (e := ⟨5, []⟩) (va := wa >>> 1) (vb := UInt64.ofNat 1) (vals := []) (ρ' := ρ₁)
            hf (natPowBig_b3 slowPow) rfl rfl
            (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
            rfl (by simp only [lir_eval, hnotle, ↓reduceIte])
            rfl (natPowBig_b5 slowPow) rfl
          by_cases hq62 : 62 < q
          · have hugt : (62 : Word) < wb >>> 1 := by
              rw [UInt64.lt_iff_toNat_lt, hv, show (62 : Word).toNat = 62 from rfl]; exact hq62
            have hs5 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 0)
              (ρ := ρ₁) (e := ⟨6, []⟩) (va := wb >>> 1) (vb := UInt64.ofNat 62) (vals := []) (ρ' := ρ₁)
              hf (natPowBig_b5 slowPow) rfl rfl
              (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
              rfl (by simp only [lir_eval, show UInt64.ofNat 62 = (62 : Word) from rfl, hugt, ↓reduceIte])
              rfl (natPowBig_b6 slowPow) rfl
            have hpre := hpre1.trans ((star_of_step hs1).trans ((star_of_step hs3).trans (star_of_step hs5)))
            have hargs : evalArgs ρ₁ [.v 0, .v 1] = some [wa, wb] := by
              simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁, ρt, ρ₀]
            rcases tail_procSpec hf (natPowBig_b6 slowPow) rfl rfl hargs hdsts (hslow mem p q wa wb hpa hqb) with
              ⟨c, mem', w, htail, hpost⟩ | hfail
            · left
              exact ⟨_, mem', w, hpre.trans htail, hpost⟩
            · right
              exact hfail.prepend hpre
          · have hnotgt : ¬ (62 : Word) < wb >>> 1 := by
              rw [UInt64.lt_iff_toNat_lt, hv, show (62 : Word).toNat = 62 from rfl]; omega
            have hs5 := br_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 0)
              (ρ := ρ₁) (e := ⟨7, []⟩) (va := wb >>> 1) (vb := UInt64.ofNat 62) (vals := []) (ρ' := ρ₁)
              hf (natPowBig_b5 slowPow) rfl rfl
              (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
              rfl (by simp only [lir_eval, show UInt64.ofNat 62 = (62 : Word) from rfl, hnotgt, ↓reduceIte])
              rfl (natPowBig_b7 slowPow) rfl
            let ρ₇ := ((ρ₁.insert 4 (UInt64.ofNat 1)).insert 5 (wa >>> 1)).insert 6 (wb >>> 1)
            have hs7 := jump_at (p := lp) (mem := mem) (ctx := ctx) (rest := caller :: rest) (pos := 0)
              (ρ := ρ₁) (e := ⟨8, [.imm (UInt64.ofNat 1), .v 2, .v 3]⟩)
              (vals := [UInt64.ofNat 1, wa >>> 1, wb >>> 1]) (ρ' := ρ₇)
              hf (natPowBig_b7 slowPow) rfl rfl
              (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
              (natPowBig_b8 slowPow)
              (by simp (config := { decide := true }) only [lir_eval, ρ₇])
            have hpre := hpre1.trans ((star_of_step hs1).trans
              ((star_of_step hs3).trans ((star_of_step hs5).trans (star_of_step hs7))))
            have hloop := natPowBig_loop (mem := mem) (ctx := ctx) (rest := rest) hf hdsts (hslow mem p q wa wb hpa hqb)
              q 1 p ρ₇ (UInt64.ofNat 1) (wa >>> 1) (wb >>> 1)
              rfl hu hv (by decide) (by decide) (by omega) hp_lt (by omega)
              (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₇, ρ₁, ρt, ρ₀])
              (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₇, ρ₁, ρt, ρ₀])
              (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₇])
              (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₇])
              (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₇])
            rcases hloop with ⟨c, ρ', w, hrun, h16, hw⟩ | ⟨c, mem', w, hrun, hpost⟩ | hfail
            · have hret := ret_to_caller (ctx := ctx) (mem := mem) (ρ := ρ') (w := w) (caller := caller) (rest := rest)
                hf (natPowBig_b11 slowPow) rfl rfl (by simp [Arg.eval, h16]) hdsts
              left
              refine ⟨_, mem, w, hpre.trans (hrun.trans hret), hrefl mem, ?_⟩
              rw [Nat.one_mul] at hw
              exact .small hw
            · left
              exact ⟨_, mem', w, hpre.trans hrun, hpost⟩
            · right
              exact hfail.prepend hpre

end IxCC.Rt.BigNat
