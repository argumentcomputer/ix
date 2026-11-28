import IxCC.Cfg.Rc.Proof.InlineSites

/-! # Standalone runtime proc & shared-path execution lemmas for `Cfg.Rc.Inline`

Provides reusable execution lemmas shared across `.reuse`, `.reset`, `.fusedResetReuse`,
and `.fusedResetUReuseU1`:
1. Standalone `incProc`, `decProc`, `allocProc` frame execution (`raw_incProc_exec`,
   `raw_decProc_exec`, `raw_decProc_imm`, `raw_allocProc_exec`).
2. Generic 6-block inline alloc + publish execution (`exec_inlineAlloc_blocks`), used by
   `.reuse` and both branches of `.fusedResetReuse`.
3. Pure model `evalSharedIncList` and matching execution for `mkResetWrapper`'s shared
   increment loop (`raw_reset_shared_inc_loop`) and `mkSharedIncBlocks`
   (`inl_sharedIncBlocks_exec`), plus `mkSharedDecBlocks` (`inl_sharedDecBlocks_exec`). -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Inline

open IxCC.Cfg.Rc.Native

theorem star_reaches {σ α : Type} {st : σ → Sem.Step σ α} {s s' : σ} {c k : Nat}
    {r : Sem.Result α} (hstar : Sem.Star st s c s') (hr : Sem.Reaches st s' k r) :
    Sem.Reaches st s (c + k) r := by
  induction hstar with
  | refl => simpa using hr
  | free h _ ih => exact .free h (ih hr)
  | charge h _ ih =>
    have := Sem.Reaches.charge h (ih hr)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem w64_tnz_eq (a b : UInt64) : Lir.Cond.holds .tnz .w64 a b = ((a &&& b) != 0) := by
  simp only [Lir.Cond.holds, X86.Width.truncate, X86.Width.mask]
  have hm : (a &&& b) &&& (0xFFFFFFFFFFFFFFFF : UInt64) = a &&& b := by
    apply UInt64.eq_of_toBitVec_eq
    change (a &&& b).toBitVec &&& (0xFFFFFFFFFFFFFFFF : UInt64).toBitVec = (a &&& b).toBitVec
    have hall : (0xFFFFFFFFFFFFFFFF : UInt64).toBitVec = BitVec.allOnes 64 := by decide
    rw [hall, BitVec.and_allOnes]
  rw [hm]

/-! ## 1. Standalone `incProc`, `decProc`, `allocProc` frame execution -/

theorem raw_incProc_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {xVal ctx : Lir.Word} {mem : X86.Memory} {caller : Lir.Frame} {rest : List Lir.Frame}
    (hdst : caller.dsts = []) :
    let pFr0 : Lir.Frame := { fn := l.incProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal }
    match evalIncSite xVal mem with
    | .ok mem' =>
      Sem.Star (Lir.semStep raw) { mem, ctx, stack := pFr0 :: caller :: rest } 0
        { mem := mem', ctx, stack := caller :: rest }
    | .oom =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := pFr0 :: caller :: rest } 0 (.resource .heap)
    | .stuck =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := pFr0 :: caller :: rest } 0 .stuck := by
  intro pFr0
  let pEnv : Lir.Env := ({} : Lir.Env).insert 0 xVal
  have hret : ∀ (m : X86.Memory) (envP : Lir.Env),
      Sem.Star (Lir.semStep raw)
        { mem := m, ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := envP } :: caller :: rest } 0
        { mem := m, ctx, stack := caller :: rest } := by
    intro m envP
    have s5 : Lir.semStep raw
        { mem := m, ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := envP } :: caller :: rest } =
        .next { mem := m, ctx, stack := caller :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := l.incProc, label := 5, pos := 0, env := envP }) hr.incProc (by rfl) (by rfl)]
      have hcaller : ({ caller with dsts := [] } : Lir.Frame) = caller := by cases caller; simp at hdst; subst hdst; rfl
      simp [Rt.Rc.Procs.inc, Lir.evalArgs, Lir.bindParams, hdst, hcaller]
    exact .free s5 (.refl _)
  unfold evalIncSite
  by_cases htag : Lir.Cond.holds .tnz .w64 xVal 1 = true
  · simp only [htag, ↓reduceIte]
    have s3 : Lir.semStep raw { mem, ctx, stack := pFr0 :: caller :: rest } =
        .next { mem, ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := pEnv } :: caller :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := pFr0) hr.incProc (by rfl) (by rfl)]
      simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
        pFr0, pEnv, htag, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
    exact .free s3 (hret mem pEnv)
  · have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by simpa using htag
    simp only [htagF, Bool.false_eq_true, ↓reduceIte]
    have s3 : Lir.semStep raw { mem, ctx, stack := pFr0 :: caller :: rest } =
        .next { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 0, env := pEnv } :: caller :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := pFr0) hr.incProc (by rfl) (by rfl)]
      simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
        pFr0, pEnv, htagF, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
    cases hload : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none =>
      dsimp only
      refine .free s3 (.final ?_)
      have hst : Lir.step raw { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 0, env := pEnv } :: caller :: rest } = .stuck := by
        unfold Lir.step
        simp [hr.incProc, Rt.Rc.Procs.inc, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
          addr_cell pEnv ctx 0 xVal 4 (by simp [pEnv]), hload]
      rw [Lir.semStep, hst]; exact .stuck
    | some cnt =>
      dsimp only
      let pEnv1 := pEnv.insert 1 cnt
      have s4 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 0, env := pEnv } :: caller :: rest } =
          .next { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 } :: caller :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fn := l.incProc, label := 1, pos := 0, env := pEnv })
          hr.incProc (by rfl) (by simp [Rt.Rc.Procs.inc]) rfl rfl
          (by simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
            addr_cell pEnv ctx 0 xVal 4 (by simp [pEnv]), hload, pEnv1])
      by_cases hlt : (X86.Width.w32.truncate cnt).toNat < 2 ^ 31 - 1
      · simp only [hlt, ↓reduceIte]
        have hslt : Lir.Cond.holds .slt .w32 cnt 0 = false := by
          rw [w32_signedValue_lt_zero]; simp; omega
        have heq : Lir.Cond.holds .eq .w32 cnt (UInt64.ofNat (Rt.Rc.maxCount - 1)) = false := by
          rw [w32_eq_maxMinus1]; simp; omega
        have s5 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 } :: caller :: rest } =
            .next { mem, ctx, stack := { fn := l.incProc, label := 2, pos := 0, env := pEnv1 } :: caller :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 }) hr.incProc (by rfl) (by rfl)]
          simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval, pEnv1, hslt,
            Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        have s6 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 2, pos := 0, env := pEnv1 } :: caller :: rest } =
            .next { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 0, env := pEnv1 } :: caller :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fn := l.incProc, label := 2, pos := 0, env := pEnv1 }) hr.incProc (by rfl) (by rfl)]
          simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval, pEnv1, heq,
            Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        let pEnv2 := pEnv1.insert 2 (X86.Width.w32.truncate (cnt + 1))
        have s7 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 0, env := pEnv1 } :: caller :: rest } =
            .next { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 1, env := pEnv2 } :: caller :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fn := l.incProc, label := 3, pos := 0, env := pEnv1 })
            hr.incProc (by rfl) (by simp [Rt.Rc.Procs.inc]) rfl rfl
            (by simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Lir.Stmt.exec, Lir.Rhs.eval, Lir.BinOp.eval,
              Lir.Arg.eval, pEnv1, pEnv2])
        have hpEnv2_0 : pEnv2[0]? = some xVal := by
          rw [Lir.env_insert_ne _ _ (by decide), Lir.env_insert_ne _ _ (by decide), Lir.env_insert_self]
        cases hw : mem.write? .w32 (xVal + Lir.dispWord 4) (X86.Width.w32.truncate (cnt + 1)) with
        | error _ =>
          dsimp only
          refine .free s3 (.free s4 (.free s5 (.free s6 (.free s7 (.final ?_)))))
          have hst : Lir.step raw { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 1, env := pEnv2 } :: caller :: rest } = .stuck := by
            unfold Lir.step
            simp [hr.incProc, Rt.Rc.Procs.inc, Rt.Rc.Procs.cellAddr, Rt.Rc.Procs.v, Lir.Stmt.exec,
              addr_cell pEnv2 ctx 0 xVal 4 hpEnv2_0, Lir.Arg.eval, pEnv2, hw]
          rw [Lir.semStep, hst]; exact .stuck
        | ok mem' =>
          dsimp only
          have s8 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 1, env := pEnv2 } :: caller :: rest } =
              .next { mem := mem', ctx, stack := { fn := l.incProc, label := 3, pos := 2, env := pEnv2 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fn := l.incProc, label := 3, pos := 1, env := pEnv2 })
              hr.incProc (by rfl) (by simp [Rt.Rc.Procs.inc]) rfl rfl
              (by simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.cellAddr, Rt.Rc.Procs.v, Lir.Stmt.exec,
                addr_cell pEnv2 ctx 0 xVal 4 hpEnv2_0, Lir.Arg.eval, pEnv2, hw])
          have s9 : Lir.semStep raw { mem := mem', ctx, stack := { fn := l.incProc, label := 3, pos := 2, env := pEnv2 } :: caller :: rest } =
              .next { mem := mem', ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := pEnv2 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.incProc, label := 3, pos := 2, env := pEnv2 }) hr.incProc (by rfl) (by rfl)]
            simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.to, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          exact .free s3 (.free s4 (.free s5 (.free s6 (.free s7 (.free s8 (.free s9 (hret mem' pEnv2)))))))
      · simp only [hlt, ↓reduceIte]
        by_cases heqN : (X86.Width.w32.truncate cnt).toNat = 2 ^ 31 - 1
        · simp only [heqN, ↓reduceIte]
          have hslt : Lir.Cond.holds .slt .w32 cnt 0 = false := by
            rw [w32_signedValue_lt_zero]; simp; omega
          have heq : Lir.Cond.holds .eq .w32 cnt (UInt64.ofNat (Rt.Rc.maxCount - 1)) = true := by
            rw [w32_eq_maxMinus1]; simp [heqN]
          have s5 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 } :: caller :: rest } =
              .next { mem, ctx, stack := { fn := l.incProc, label := 2, pos := 0, env := pEnv1 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 }) hr.incProc (by rfl) (by rfl)]
            simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval, pEnv1, hslt,
              Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          have s6 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 2, pos := 0, env := pEnv1 } :: caller :: rest } =
              .next { mem, ctx, stack := { fn := l.incProc, label := 4, pos := 0, env := pEnv1 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.incProc, label := 2, pos := 0, env := pEnv1 }) hr.incProc (by rfl) (by rfl)]
            simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval, pEnv1, heq,
              Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          refine .free s3 (.free s4 (.free s5 (.free s6 (.final ?_))))
          have hst : Lir.step raw { mem, ctx, stack := { fn := l.incProc, label := 4, pos := 0, env := pEnv1 } :: caller :: rest } = .fail .heap := by
            rw [Lir.step_term (fr := { fn := l.incProc, label := 4, pos := 0, env := pEnv1 }) hr.incProc (by rfl) (by rfl)]; rfl
          rw [Lir.semStep, hst]; exact .fail
        · simp only [heqN, ↓reduceIte]
          have hslt : Lir.Cond.holds .slt .w32 cnt 0 = true := by
            rw [w32_signedValue_lt_zero]; simp; omega
          have s5 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 } :: caller :: rest } =
              .next { mem, ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := pEnv1 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 }) hr.incProc (by rfl) (by rfl)]
            simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval, pEnv1, hslt,
              Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          exact .free s3 (.free s4 (.free s5 (hret mem pEnv1)))

theorem raw_decProc_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {xVal ctx : Lir.Word} {mem : X86.Memory} {caller : Lir.Frame} {rest : List Lir.Frame}
    (hdst : caller.dsts = []) :
    let pFr0 : Lir.Frame := { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal }
    match evalDecSite xVal mem with
    | .ok mem' =>
      Sem.Star (Lir.semStep raw) { mem, ctx, stack := pFr0 :: caller :: rest } 0
        { mem := mem', ctx, stack := caller :: rest }
    | .free => True
    | .stuck =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := pFr0 :: caller :: rest } 0 .stuck := by
  intro pFr0
  let wEnv : Lir.Env := ({} : Lir.Env).insert 0 xVal
  let pEnv1 : Lir.Env := (wEnv.insert 1 xVal).insert 2 0
  have hstep3 : Lir.semStep raw { mem, ctx, stack := pFr0 :: caller :: rest } =
      .next { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := pEnv1 } :: caller :: rest } false := by
    apply Lir.semStep_next.mpr
    rw [Lir.step_term (fr := pFr0) hr.decProc (by rfl) (by rfl)]
    simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
      Lir.takeEdge, Lir.evalArgs, Lir.bindParams, pFr0, wEnv, pEnv1]
  have hret6 : ∀ (m : X86.Memory) (envP : Lir.Env),
      Sem.Star (Lir.semStep raw)
        { mem := m, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := envP.insert 8 0 } :: caller :: rest } 0
        { mem := m, ctx, stack := caller :: rest } := by
    intro m envP
    have s6 : Lir.semStep raw
        { mem := m, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := envP.insert 8 0 } :: caller :: rest } =
        .next { mem := m, ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := envP.insert 8 0 } :: caller :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := l.decProc, label := 6, pos := 0, env := envP.insert 8 0 }) hr.decProc (by rfl) (by rfl)]
      simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
        Lir.Cond.holds, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
    have s10 : Lir.semStep raw
        { mem := m, ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := envP.insert 8 0 } :: caller :: rest } =
        .next { mem := m, ctx, stack := caller :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := l.decProc, label := 10, pos := 0, env := envP.insert 8 0 }) hr.decProc (by rfl) (by rfl)]
      have hcaller : ({ caller with dsts := [] } : Lir.Frame) = caller := by cases caller; simp at hdst; subst hdst; rfl
      simp [Rt.Rc.Gen.dec, Lir.evalArgs, Lir.bindParams, hdst, hcaller]
    exact .free s6 (.free s10 (.refl _))
  have hp1_1 : pEnv1[1]? = some xVal := by rw [Lir.env_insert_ne _ _ (by decide), Lir.env_insert_self]
  have hp1_2 : pEnv1[2]? = some 0 := by simp [pEnv1]
  unfold evalDecSite
  by_cases htag : Lir.Cond.holds .tnz .w64 xVal 1 = true
  · simp only [htag, ↓reduceIte]
    have s4 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := pEnv1 } :: caller :: rest } =
        .next { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := pEnv1.insert 8 0 } :: caller :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := l.decProc, label := 1, pos := 0, env := pEnv1 }) hr.decProc (by rfl) (by rfl)]
      simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
        hp1_1, hp1_2, htag, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
    exact .free hstep3 (.free s4 (hret6 mem pEnv1))
  · have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by simpa using htag
    simp only [htagF, Bool.false_eq_true, ↓reduceIte]
    have s4 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := pEnv1 } :: caller :: rest } =
        .next { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := pEnv1 } :: caller :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := l.decProc, label := 1, pos := 0, env := pEnv1 }) hr.decProc (by rfl) (by rfl)]
      simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
        hp1_1, htagF, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
    cases hload : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none =>
      dsimp only
      refine .free hstep3 (.free s4 (.final ?_))
      have hst : Lir.step raw { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := pEnv1 } :: caller :: rest } = .stuck := by
        unfold Lir.step
        simp [hr.decProc, Rt.Rc.Gen.dec, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
          addr_cell pEnv1 ctx 1 xVal 4 hp1_1, hload]
      rw [Lir.semStep, hst]; exact .stuck
    | some cnt =>
      dsimp only
      by_cases hzero : (X86.Width.w32.truncate cnt).toNat = 0
      · simp only [hzero, ↓reduceIte]
      · simp only [hzero, ↓reduceIte]
        let pEnv2 := pEnv1.insert 3 cnt
        have hp2_1 : pEnv2[1]? = some xVal := by rw [Lir.env_insert_ne _ _ (by decide), hp1_1]
        have hp2_2 : pEnv2[2]? = some 0 := by rw [Lir.env_insert_ne _ _ (by decide), hp1_2]
        have s5 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := pEnv1 } :: caller :: rest } =
            .next { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := pEnv2 } :: caller :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fn := l.decProc, label := 2, pos := 0, env := pEnv1 })
            hr.decProc (by rfl) (by simp [Rt.Rc.Gen.dec]) rfl rfl
            (by simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
              addr_cell pEnv1 ctx 1 xVal 4 hp1_1, hload, pEnv2])
        by_cases hneg : 2 ^ 31 ≤ (X86.Width.w32.truncate cnt).toNat
        · simp only [hneg, ↓reduceIte]
          have hslt : Lir.Cond.holds .slt .w32 cnt 0 = true := by rw [w32_signedValue_lt_zero]; simp [hneg]
          have s6 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := pEnv2 } :: caller :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := pEnv2.insert 8 0 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.decProc, label := 2, pos := 1, env := pEnv2 }) hr.decProc (by rfl) (by rfl)]
            simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
              pEnv2, hp2_2, hslt, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          exact .free hstep3 (.free s4 (.free s5 (.free s6 (hret6 mem pEnv2))))
        · simp only [hneg, ↓reduceIte]
          have hslt : Lir.Cond.holds .slt .w32 cnt 0 = false := by rw [w32_signedValue_lt_zero]; simp [hneg]
          have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = false := by rw [w32_eq_zero]; simp [hzero]
          have s6 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := pEnv2 } :: caller :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := pEnv2 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.decProc, label := 2, pos := 1, env := pEnv2 }) hr.decProc (by rfl) (by rfl)]
            simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
              pEnv2, hslt, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          have s7 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := pEnv2 } :: caller :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 0, env := pEnv2 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.decProc, label := 3, pos := 0, env := pEnv2 }) hr.decProc (by rfl) (by rfl)]
            simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
              pEnv2, heq0, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          let pEnv3 := pEnv2.insert 4 (X86.Width.w32.truncate (cnt - 1))
          have hp3_1 : pEnv3[1]? = some xVal := by rw [Lir.env_insert_ne _ _ (by decide), hp2_1]
          have hp3_2 : pEnv3[2]? = some 0 := by rw [Lir.env_insert_ne _ _ (by decide), hp2_2]
          have s8 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 0, env := pEnv2 } :: caller :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 1, env := pEnv3 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fn := l.decProc, label := 4, pos := 0, env := pEnv2 })
              hr.decProc (by rfl) (by simp [Rt.Rc.Gen.dec]) rfl rfl
              (by simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Lir.Stmt.exec, Lir.Rhs.eval,
                Lir.BinOp.eval, Lir.Arg.eval, pEnv2, pEnv3])
          cases hw : mem.write? .w32 (xVal + Lir.dispWord 4) (X86.Width.w32.truncate (cnt - 1)) with
          | error _ =>
            dsimp only
            refine .free hstep3 (.free s4 (.free s5 (.free s6 (.free s7 (.free s8 (.final ?_))))))
            have hst : Lir.step raw { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 1, env := pEnv3 } :: caller :: rest } = .stuck := by
              unfold Lir.step
              simp [hr.decProc, Rt.Rc.Gen.dec, Rt.Rc.Procs.cellAddr, Rt.Rc.Procs.v, Lir.Stmt.exec,
                addr_cell pEnv3 ctx 1 xVal 4 hp3_1, Lir.Arg.eval, pEnv3, hw]
            rw [Lir.semStep, hst]; exact .stuck
          | ok mem' =>
            dsimp only
            have s9 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 1, env := pEnv3 } :: caller :: rest } =
                .next { mem := mem', ctx, stack := { fn := l.decProc, label := 4, pos := 2, env := pEnv3 } :: caller :: rest } false := by
              apply Lir.semStep_next.mpr
              exact Lir.step_stmt (fr := { fn := l.decProc, label := 4, pos := 1, env := pEnv3 })
                hr.decProc (by rfl) (by simp [Rt.Rc.Gen.dec]) rfl rfl
                (by simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.cellAddr, Rt.Rc.Procs.v, Lir.Stmt.exec,
                  addr_cell pEnv3 ctx 1 xVal 4 hp3_1, Lir.Arg.eval, pEnv3, hw])
            have s10 : Lir.semStep raw { mem := mem', ctx, stack := { fn := l.decProc, label := 4, pos := 2, env := pEnv3 } :: caller :: rest } =
                .next { mem := mem', ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := pEnv3.insert 8 0 } :: caller :: rest } false := by
              apply Lir.semStep_next.mpr
              rw [Lir.step_term (fr := { fn := l.decProc, label := 4, pos := 2, env := pEnv3 }) hr.decProc (by rfl) (by rfl)]
              simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.to, Lir.Arg.eval, hp3_2,
                Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
            exact .free hstep3 (.free s4 (.free s5 (.free s6 (.free s7 (.free s8 (.free s9 (.free s10 (hret6 mem' pEnv3))))))))

theorem raw_decProc_imm {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {xVal ctx : Lir.Word} {mem : X86.Memory} {caller : Lir.Frame} {rest : List Lir.Frame}
    (hdst : caller.dsts = []) (himm : Lir.Cond.holds .tnz .w64 xVal 1 = true) :
    let pFr0 : Lir.Frame := { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal }
    Sem.Star (Lir.semStep raw) { mem, ctx, stack := pFr0 :: caller :: rest } 0
      { mem, ctx, stack := caller :: rest } := by
  have h := raw_decProc_exec hr (xVal := xVal) (ctx := ctx) (mem := mem) (caller := caller) (rest := rest) hdst
  simpa [evalDecSite, himm] using h

theorem raw_allocProc_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {idx : Nat} {c : Lam.CtorInfo} {lay : Rt.Rc.CellLayout} {cls : Nat}
    {ctx : Lir.Word} {mem : X86.Memory} {caller : Lir.Frame} {rest : List Lir.Frame}
    {dst : Lir.VReg}
    (hc : l.ctors[idx]? = some c)
    (hlay : lay = Rt.Rc.CellLayout.ofFields c.arity c.tag)
    (hcls : lay.cls? = some cls) (hok : lay.ok = true)
    (hdst : caller.dsts = [dst]) :
    let pFr0 : Lir.Frame := { fn := l.allocProc idx, label := 0, pos := 0, env := {} }
    match evalAllocReserve lay cls mem ctx with
    | .ok addr mem₂ =>
      Sem.Star (Lir.semStep raw) { mem, ctx, stack := pFr0 :: caller :: rest } 0
        { mem := mem₂, ctx, stack := { caller with env := caller.env.insert dst addr, dsts := [] } :: rest }
    | .oom =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := pFr0 :: caller :: rest } 0 (.resource .heap)
    | .stuck =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := pFr0 :: caller :: rest } 0 .stuck := by
  intro pFr0
  have hprocF : raw.funcs[l.allocProc idx]? = some (Rt.Rc.Gen.allocFunc lay cls) := by
    have := hr.allocProc idx c hc
    rw [← hlay, Rt.Rc.Gen.alloc_eq hok hcls] at this
    exact this
  let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
  have hfinish : ∀ (addr : Lir.Word) (mem₁ : X86.Memory) (envP : Lir.Env),
      match mem₁.write? .w64 (addr + Lir.dispWord 0) hdr with
      | .error _ =>
        Sem.Reaches (Lir.semStep raw)
          { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := envP.insert 5 addr } :: caller :: rest } 0 .stuck
      | .ok mem₂ =>
        Sem.Star (Lir.semStep raw)
          { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := envP.insert 5 addr } :: caller :: rest } 0
          { mem := mem₂, ctx, stack := { caller with env := caller.env.insert dst addr, dsts := [] } :: rest } := by
    intro addr mem₁ envP
    cases hwH : mem₁.write? .w64 (addr + Lir.dispWord 0) hdr with
    | error _ =>
      dsimp only
      apply Sem.Reaches.final
      have hst : Lir.step raw { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := envP.insert 5 addr } :: caller :: rest } = .stuck := by
        unfold Lir.step
        simp [hprocF, Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec,
          addr_cell (envP.insert 5 addr) ctx 5 addr 0 (by simp), Lir.Arg.eval, hdr, hwH]
      rw [Lir.semStep, hst]; exact .stuck
    | ok mem₂ =>
      dsimp only
      have s5_0 : Lir.semStep raw
          { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := envP.insert 5 addr } :: caller :: rest } =
          .next { mem := mem₂, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 1, env := envP.insert 5 addr } :: caller :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fn := l.allocProc idx, label := 5, pos := 0, env := envP.insert 5 addr })
          hprocF (by rfl) (by simp [Rt.Rc.Gen.allocFunc]) rfl rfl
          (by simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec,
            addr_cell (envP.insert 5 addr) ctx 5 addr 0 (by simp), Lir.Arg.eval, hdr, hwH])
      have s5_1 : Lir.semStep raw
          { mem := mem₂, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 1, env := envP.insert 5 addr } :: caller :: rest } =
          .next { mem := mem₂, ctx, stack := { caller with env := caller.env.insert dst addr, dsts := [] } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 5, pos := 1, env := envP.insert 5 addr })
          hprocF (by rfl) (by rfl)]
        simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Lir.evalArgs, Lir.Arg.eval, hdst, Lir.bindParams]
      exact .free s5_0 (.free s5_1 (.refl _))
  unfold evalAllocReserve
  dsimp only
  cases hload0 : Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord (Int.ofNat (8 * cls))) with
  | none =>
    dsimp only
    apply Sem.Reaches.final
    have hst : Lir.step raw { mem, ctx, stack := pFr0 :: caller :: rest } = .stuck := by
      unfold Lir.step
      have h0 : (Rt.Rc.Gen.allocFunc lay cls).blocks[0]? = some (Rt.Rc.Gen.allocFunc lay cls).blocks[0]! := rfl
      have hlt0 : 0 < (Rt.Rc.Gen.allocFunc lay cls).blocks[0]!.body.size := by simp [Rt.Rc.Gen.allocFunc]
      have hget0 : (Rt.Rc.Gen.allocFunc lay cls).blocks[0]!.body[0] =
          .assign 0 (.load .w64 .zero (Rt.Rc.Procs.ctx (Int.ofNat (8 * cls)))) := rfl
      simp only [hprocF, pFr0, h0, hlt0, ↓reduceDIte, hget0,
        Lir.Stmt.exec, Lir.Rhs.eval, Rt.Rc.Procs.ctx, addr_ctx, Option.bind_eq_bind, Option.bind_some,
        Option.bind_none, hload0]
    rw [Lir.semStep, hst]; exact .stuck
  | some p0 =>
    dsimp only
    let e0 : Lir.Env := ({} : Lir.Env).insert 0 p0
    have s0 : Lir.semStep raw { mem, ctx, stack := pFr0 :: caller :: rest } =
        .next { mem, ctx, stack := { fn := l.allocProc idx, label := 0, pos := 1, env := e0 } :: caller :: rest } false := by
      apply Lir.semStep_next.mpr
      have hlt0 : 0 < (Rt.Rc.Gen.allocFunc lay cls).blocks[0]!.body.size := by simp [Rt.Rc.Gen.allocFunc]
      have hget0 : (Rt.Rc.Gen.allocFunc lay cls).blocks[0]!.body[0]'hlt0 =
          .assign 0 (.load .w64 .zero (Rt.Rc.Procs.ctx (Int.ofNat (8 * cls)))) := rfl
      exact Lir.step_stmt (fr := pFr0) (B := (Rt.Rc.Gen.allocFunc lay cls).blocks[0]!)
        hprocF rfl hlt0 hget0 rfl
        (by simp only [Rt.Rc.Procs.ctx, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx,
          Option.bind_eq_bind, Option.bind_some, hload0, pFr0, e0])
    by_cases hp0 : Lir.Cond.holds .eq .w64 p0 0 = true
    · simp only [hp0, ↓reduceIte]
      have s1 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 0, pos := 1, env := e0 } :: caller :: rest } =
          .next { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 0, env := e0 } :: caller :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 0, pos := 1, env := e0 }) hprocF (by rfl) (by rfl)]
        simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
          e0, hp0, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
      cases hlb : Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord Rt.bumpOff) with
      | none =>
        dsimp only
        refine .free s0 (.free s1 (.final ?_))
        have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 0, env := e0 } :: caller :: rest } = .stuck := by
          unfold Lir.step
          simp [hprocF, Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hlb]
        rw [Lir.semStep, hst]; exact .stuck
      | some b0 =>
        dsimp only
        let e2 := e0.insert 2 b0
        have s2 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 0, env := e0 } :: caller :: rest } =
            .next { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 1, env := e2 } :: caller :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fn := l.allocProc idx, label := 2, pos := 0, env := e0 })
            hprocF (by rfl) (by simp [Rt.Rc.Gen.allocFunc]) rfl rfl
            (by simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hlb, e2])
        cases hll : Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord Rt.limitOff) with
        | none =>
          dsimp only
          refine .free s0 (.free s1 (.free s2 (.final ?_)))
          have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 1, env := e2 } :: caller :: rest } = .stuck := by
            unfold Lir.step
            simp [hprocF, Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hll]
          rw [Lir.semStep, hst]; exact .stuck
        | some lim =>
          dsimp only
          let e3 := e2.insert 3 lim
          have he3_2 : e3[2]? = some b0 := by rw [Lir.env_insert_ne _ _ (by decide)]; simp [e2]
          have s3 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 1, env := e2 } :: caller :: rest } =
              .next { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 2, env := e3 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fn := l.allocProc idx, label := 2, pos := 1, env := e2 })
              hprocF (by rfl) (by simp [Rt.Rc.Gen.allocFunc]) rfl rfl
              (by simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hll, e3])
          cases hovf : Lir.Ovf.eval .addC b0 (UInt64.ofNat (Rt.Rc.classBytes cls)) with
          | mk b1 ovf =>
            dsimp only
            let e4 := e3.insert 4 b1
            cases ovf with
            | true =>
              simp only [↓reduceIte]
              have s4 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 2, env := e3 } :: caller :: rest } =
                  .next { mem, ctx, stack := { fn := l.allocProc idx, label := 6, pos := 0, env := e4 } :: caller :: rest } false := by
                apply Lir.semStep_next.mpr
                rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 2, pos := 2, env := e3 }) hprocF (by rfl) (by rfl)]
                simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
                  he3_2, hovf, Lir.takeEdge, Lir.evalArgs, Lir.bindParams, e4]
              refine .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.final ?_)))))
              have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 6, pos := 0, env := e4 } :: caller :: rest } = .fail .heap := by
                rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 6, pos := 0, env := e4 }) hprocF (by rfl) (by rfl)]; rfl
              rw [Lir.semStep, hst]; exact .fail
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              have s4 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 2, env := e3 } :: caller :: rest } =
                  .next { mem, ctx, stack := { fn := l.allocProc idx, label := 3, pos := 0, env := e4 } :: caller :: rest } false := by
                apply Lir.semStep_next.mpr
                rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 2, pos := 2, env := e3 }) hprocF (by rfl) (by rfl)]
                simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
                  he3_2, hovf, Lir.takeEdge, Lir.evalArgs, Lir.bindParams, e4]
              have he4_3 : e4[3]? = some lim := by rw [Lir.env_insert_ne _ _ (by decide)]; simp [e3]
              have he4_2 : e4[2]? = some b0 := by rw [Lir.env_insert_ne _ _ (by decide)]; exact he3_2
              by_cases hule : Lir.Cond.holds .ule .w64 b1 lim = true
              · simp only [hule, ↓reduceIte]
                have s5 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 3, pos := 0, env := e4 } :: caller :: rest } =
                    .next { mem, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 0, env := e4 } :: caller :: rest } false := by
                  apply Lir.semStep_next.mpr
                  rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 3, pos := 0, env := e4 }) hprocF (by rfl) (by rfl)]
                  simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.to, Lir.Arg.eval,
                    e4, he4_3, hule, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
                cases hwb : mem.write? .w64 (ctx + Lir.dispWord Rt.bumpOff) b1 with
                | error _ =>
                  dsimp only
                  refine .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.final ?_))))))
                  have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 0, env := e4 } :: caller :: rest } = .stuck := by
                    unfold Lir.step
                    simp [hprocF, Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Rt.Rc.Procs.v, Lir.Stmt.exec,
                      addr_ctx, Lir.Arg.eval, e4, hwb]
                  rw [Lir.semStep, hst]; exact .stuck
                | ok mem₁ =>
                  dsimp only
                  have s6 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 0, env := e4 } :: caller :: rest } =
                      .next { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 1, env := e4 } :: caller :: rest } false := by
                    apply Lir.semStep_next.mpr
                    exact Lir.step_stmt (fr := { fn := l.allocProc idx, label := 4, pos := 0, env := e4 })
                      hprocF (by rfl) (by simp [Rt.Rc.Gen.allocFunc]) rfl rfl
                      (by simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Rt.Rc.Procs.v, Lir.Stmt.exec,
                        addr_ctx, Lir.Arg.eval, e4, hwb])
                  have s7 : Lir.semStep raw { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 1, env := e4 } :: caller :: rest } =
                      .next { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := e4.insert 5 b0 } :: caller :: rest } false := by
                    apply Lir.semStep_next.mpr
                    rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 4, pos := 1, env := e4 }) hprocF (by rfl) (by rfl)]
                    simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.to, Lir.Arg.eval,
                      he4_2, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
                  have hf := hfinish b0 mem₁ e4
                  cases hwH : mem₁.write? .w64 (b0 + Lir.dispWord 0) hdr with
                  | error _ =>
                    rw [hwH] at hf
                    exact .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 hf)))))))
                  | ok mem₂ =>
                    rw [hwH] at hf
                    exact .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 hf)))))))
              · have huleF : Lir.Cond.holds .ule .w64 b1 lim = false := by simpa using hule
                simp only [huleF, Bool.false_eq_true, ↓reduceIte]
                have s5 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 3, pos := 0, env := e4 } :: caller :: rest } =
                    .next { mem, ctx, stack := { fn := l.allocProc idx, label := 6, pos := 0, env := e4 } :: caller :: rest } false := by
                  apply Lir.semStep_next.mpr
                  rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 3, pos := 0, env := e4 }) hprocF (by rfl) (by rfl)]
                  simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.to, Lir.Arg.eval,
                    e4, he4_3, huleF, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
                refine .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.final ?_))))))
                have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 6, pos := 0, env := e4 } :: caller :: rest } = .fail .heap := by
                  rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 6, pos := 0, env := e4 }) hprocF (by rfl) (by rfl)]; rfl
                rw [Lir.semStep, hst]; exact .fail
    · have hp0F : Lir.Cond.holds .eq .w64 p0 0 = false := by simpa using hp0
      simp only [hp0F, Bool.false_eq_true, ↓reduceIte]
      have s1 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 0, pos := 1, env := e0 } :: caller :: rest } =
          .next { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 0, env := e0 } :: caller :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 0, pos := 1, env := e0 }) hprocF (by rfl) (by rfl)]
        simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
          e0, hp0F, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
      cases hln : Lir.loadWord mem .w64 .zero (p0 + Lir.dispWord 0) with
      | none =>
        dsimp only
        refine .free s0 (.free s1 (.final ?_))
        have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 0, env := e0 } :: caller :: rest } = .stuck := by
          unfold Lir.step
          simp [hprocF, Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
            addr_cell e0 ctx 0 p0 0 (by simp [e0]), hln]
        rw [Lir.semStep, hst]; exact .stuck
      | some nextH =>
        dsimp only
        let e1 := e0.insert 1 nextH
        have he1_0 : e1[0]? = some p0 := by rw [Lir.env_insert_ne _ _ (by decide)]; simp [e0]
        have s2 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 0, env := e0 } :: caller :: rest } =
            .next { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 1, env := e1 } :: caller :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fn := l.allocProc idx, label := 1, pos := 0, env := e0 })
            hprocF (by rfl) (by simp [Rt.Rc.Gen.allocFunc]) rfl rfl
            (by simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
              addr_cell e0 ctx 0 p0 0 (by simp [e0]), hln, e1])
        cases hwh : mem.write? .w64 (ctx + Lir.dispWord (Int.ofNat (8 * cls))) nextH with
        | error _ =>
          dsimp only
          refine .free s0 (.free s1 (.free s2 (.final ?_)))
          have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 1, env := e1 } :: caller :: rest } = .stuck := by
            unfold Lir.step
            simp only [hprocF, Rt.Rc.Gen.allocFunc, List.size_toArray, List.length_cons, List.length_nil,
              show 1 < 7 by decide, ↓reduceDIte, Array.getElem?_eq_getElem, List.getElem_toArray,
              List.getElem_cons_succ, List.getElem_cons_zero, show 1 < 2 by decide,
              Lir.Stmt.exec, Rt.Rc.Procs.ctx, Rt.Rc.Procs.v, addr_ctx, Lir.Arg.eval,
              e1, Lir.env_insert_self, Option.bind_eq_bind, Option.bind_some, hwh]
          rw [Lir.semStep, hst]; exact .stuck
        | ok mem₁ =>
          dsimp only
          have s3 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 1, env := e1 } :: caller :: rest } =
              .next { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 2, env := e1 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fn := l.allocProc idx, label := 1, pos := 1, env := e1 })
              hprocF (by rfl) (by simp [Rt.Rc.Gen.allocFunc]) rfl rfl
              (by simp only [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Rt.Rc.Procs.v,
                List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
                Lir.Stmt.exec, addr_ctx, Lir.Arg.eval, e1, Lir.env_insert_self,
                Option.bind_eq_bind, Option.bind_some, hwh])
          have s4 : Lir.semStep raw { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 2, env := e1 } :: caller :: rest } =
              .next { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := e1.insert 5 p0 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 1, pos := 2, env := e1 }) hprocF (by rfl) (by rfl)]
            simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.to, Lir.Arg.eval,
              he1_0, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          have hf := hfinish p0 mem₁ e1
          cases hwH : mem₁.write? .w64 (p0 + Lir.dispWord 0) hdr with
          | error _ =>
            rw [hwH] at hf
            exact .free s0 (.free s1 (.free s2 (.free s3 (.free s4 hf))))
          | ok mem₂ =>
            rw [hwH] at hf
            exact .free s0 (.free s1 (.free s2 (.free s3 (.free s4 hf))))

/-! ## 2. Generic 6-block inline alloc + publish block execution -/

/-- Execute the 6 inline free-list/bump allocation blocks at `base .. base + 5` (using fresh
temporaries `aBase .. aBase + 4`), jumping to `pubLbl` (`base + 5 < pubLbl`) with optional
leading `(slot, slotArg, slotVal)` parameter plus `dst`, then executing header + field stores. -/
theorem exec_inlineAlloc_blocks {p : Lir.Program} {F' : Lir.Func} {pubBlk : Lir.Block}
    {fn : Lir.FunId} {base pubLbl : Lir.Label} {aBase bound : Nat}
    {dst : Lir.VReg} {lay : Rt.Rc.CellLayout} {cls : Nat}
    {args : List Lir.Arg} {vals : List Lir.Word} {postJ : List Lir.Stmt}
    {pre : Option (Lir.VReg × Lir.Arg × Lir.Word)}
    {env0 : Lir.Env} {mem : X86.Memory} {ctx : Lir.Word} {rest : List Lir.Frame}
    (hF' : p.funcs[fn]? = some F')
    (hpubGt : base + 5 < pubLbl)
    (haGe : bound ≤ aBase)
    (hargsLt : argsMax args 0 < bound)
    (hnoDst : argsContainVReg dst args = false)
    (hnoPre : ∀ sl a w, pre = some (sl, a, w) →
      dst ≠ sl ∧ argsContainVReg sl args = false ∧
      ∀ env', AgreeBelow aBase env0 env' → a.eval env' = some w)
    (hargs : Lir.evalArgs env0 args = some vals)
    (hpubParams : pubBlk.params = match pre with | none => [dst] | some (sl, _, _) => [sl, dst])
    (hpubBody : pubBlk.body.toList =
      [.store .w64 (cellAddr dst) (.imm (Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1))] ++
        mkFieldStores dst 0 args ++ postJ)
    (hb0 : F'.blocks[base]? = some {
      body := #[.assign aBase (.load .w64 .zero (ctxAddr (Int.ofNat (8 * cls))))],
      term := .br .eq .w64 (.v aBase) (.imm 0) ⟨base + 2, []⟩ ⟨base + 1, []⟩, cold := true })
    (hb1 : F'.blocks[base + 1]? = some {
      body := #[.assign (aBase + 1) (.load .w64 .zero (cellAddr aBase)),
        .store .w64 (ctxAddr (Int.ofNat (8 * cls))) (.v (aBase + 1))],
      term := .jump ⟨pubLbl, match pre with | none => [.v aBase] | some (_, a, _) => [a, .v aBase]⟩,
      cold := true })
    (hb2 : F'.blocks[base + 2]? = some {
      body := #[.assign (aBase + 2) (.load .w64 .zero (ctxAddr Rt.bumpOff)),
        .assign (aBase + 3) (.load .w64 .zero (ctxAddr Rt.limitOff))],
      term := .brOvf .addC (aBase + 4) (.v (aBase + 2)) (.imm (UInt64.ofNat (Rt.Rc.classBytes cls)))
        ⟨base + 3, []⟩ ⟨base + 5, []⟩, cold := true })
    (hb3 : F'.blocks[base + 3]? = some {
      body := #[],
      term := .br .ule .w64 (.v (aBase + 4)) (.v (aBase + 3)) ⟨base + 4, []⟩ ⟨base + 5, []⟩,
      cold := true })
    (hb4 : F'.blocks[base + 4]? = some {
      body := #[.store .w64 (ctxAddr Rt.bumpOff) (.v (aBase + 4))],
      term := .jump ⟨pubLbl, match pre with | none => [.v (aBase + 2)] | some (_, a, _) => [a, .v (aBase + 2)]⟩,
      cold := true })
    (hb5 : F'.blocks[base + 5]? = some { body := #[], term := .fail .heap, cold := true })
    (hpub : F'.blocks[pubLbl]? = some pubBlk) :
    let bindRes : Lir.Env → Lir.Word → Lir.Env := fun env addr =>
      match pre with
      | none => env.insert dst addr
      | some (sl, _, w) => (env.insert sl w).insert dst addr
    match evalAllocReserve lay cls mem ctx with
    | .ok addr mem₂ =>
      match writeFieldsMem mem₂ addr 0 vals with
      | some mem' =>
        ∃ env',
          Sem.Star (Lir.semStep p) { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } 0
            { mem := mem', ctx, stack := { fn, label := pubLbl, pos := 1 + args.length, env := env', dsts := [] } :: rest } ∧
          AgreeBelow bound (bindRes env0 addr) env'
      | none =>
        Sem.Reaches (Lir.semStep p) { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } 0 .stuck
    | .oom =>
      Sem.Reaches (Lir.semStep p) { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } 0 (.resource .heap)
    | .stuck =>
      Sem.Reaches (Lir.semStep p) { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } 0 .stuck := by
  intro bindRes
  let headOff := Int.ofNat (8 * cls)
  let bytes := UInt64.ofNat (Rt.Rc.classBytes cls)
  let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
  have hjbPos0 : 0 < pubBlk.body.size := by
    have := congrArg List.length hpubBody
    simp only [Array.length_toList, List.length_append, List.length_cons] at this
    omega
  have hjbStmt0 : pubBlk.body[0] = .store .w64 (cellAddr dst) (.imm hdr) := by
    have : pubBlk.body.toList[0]? = some (.store .w64 (cellAddr dst) (.imm hdr)) := by rw [hpubBody]; rfl
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hjbPos0, Option.some.injEq] at this
    exact this
  have hpubRun : ∀ (addr : Lir.Word) (mem₁ : X86.Memory) (envP : Lir.Env),
      AgreeBelow bound env0 envP →
      match mem₁.write? .w64 (addr + Lir.dispWord 0) hdr with
      | .error _ =>
        Sem.Reaches (Lir.semStep p)
          { mem := mem₁, ctx, stack := { fn, label := pubLbl, pos := 0, env := bindRes envP addr } :: rest } 0 .stuck
      | .ok mem₂ =>
        match writeFieldsMem mem₂ addr 0 vals with
        | some mem' =>
          Sem.Star (Lir.semStep p)
            { mem := mem₁, ctx, stack := { fn, label := pubLbl, pos := 0, env := bindRes envP addr } :: rest } 0
            { mem := mem', ctx, stack := { fn, label := pubLbl, pos := 1 + args.length, env := bindRes envP addr, dsts := [] } :: rest }
        | none =>
          Sem.Reaches (Lir.semStep p)
            { mem := mem₁, ctx, stack := { fn, label := pubLbl, pos := 0, env := bindRes envP addr } :: rest } 0 .stuck := by
    intro addr mem₁ envP hagP
    have hdstBind : (bindRes envP addr)[dst]? = some addr := by
      cases pre <;> simp [bindRes]
    have hargsP : Lir.evalArgs (bindRes envP addr) args = some vals := by
      cases hpr : pre with
      | none =>
        simp only [bindRes, hpr]
        rw [evalArgs_insert_not_mem (argsContainVReg_false hnoDst), ← hagP.evalArgs_eq hargsLt, hargs]
      | some t =>
        rcases t with ⟨sl, a, w⟩
        obtain ⟨_, hnsl, _⟩ := hnoPre sl a w hpr
        simp only [bindRes, hpr]
        rw [evalArgs_insert_not_mem (argsContainVReg_false hnoDst),
          evalArgs_insert_not_mem (argsContainVReg_false hnsl), ← hagP.evalArgs_eq hargsLt, hargs]
    cases hwH : mem₁.write? .w64 (addr + Lir.dispWord 0) hdr with
    | error _ =>
      dsimp only
      apply Sem.Reaches.final
      have hst : Lir.step p { mem := mem₁, ctx, stack := { fn, label := pubLbl, pos := 0, env := bindRes envP addr } :: rest } = .stuck := by
        unfold Lir.step
        simp [hF', hpub, hjbPos0, hjbStmt0, cellAddr, Lir.Stmt.exec,
          addr_cell (bindRes envP addr) ctx dst addr 0 hdstBind, Lir.Arg.eval, hwH]
      rw [Lir.semStep, hst]; exact .stuck
    | ok mem₂ =>
      dsimp only
      have sH : Lir.semStep p
          { mem := mem₁, ctx, stack := { fn, label := pubLbl, pos := 0, env := bindRes envP addr } :: rest } =
          .next { mem := mem₂, ctx, stack := { fn, label := pubLbl, pos := 1, env := bindRes envP addr } :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fn, label := pubLbl, pos := 0, env := bindRes envP addr })
          hF' hpub hjbPos0 hjbStmt0 rfl
          (by simp [cellAddr, Lir.Stmt.exec, addr_cell (bindRes envP addr) ctx dst addr 0 hdstBind, Lir.Arg.eval, hwH])
      have hst := exec_mkFieldStores (p := p) (F := F') (B := pubBlk)
        (fn := fn) (lbl := pubLbl) (dst := dst) (addr := addr) (ctx := ctx)
        (rest := rest) (env := bindRes envP addr)
        hF' hpub hdstBind (pre := [.store .w64 (cellAddr dst) (.imm hdr)]) (post := postJ)
        (j := 0) (args := args) (vals := vals) (mem := mem₂) hpubBody hargsP
      cases hwf : writeFieldsMem mem₂ addr 0 vals with
      | none =>
        rw [hwf] at hst
        exact .free sH (by simpa using hst)
      | some mem' =>
        rw [hwf] at hst
        exact .free sH (by simpa using hst)
  have hbindAgree : ∀ (envP : Lir.Env) (addr : Lir.Word),
      AgreeBelow bound env0 envP → AgreeBelow bound (bindRes env0 addr) (bindRes envP addr) := by
    intro envP addr hag
    cases pre with
    | none => exact hag.insert_same dst addr
    | some t => rcases t with ⟨sl, _, w⟩; exact (hag.insert_same sl w).insert_same dst addr
  have hpubJump : ∀ (m : X86.Memory) (srcLbl : Lir.Label) (srcPos : Nat) (srcBlk : Lir.Block)
      (envP : Lir.Env) (reg : Lir.VReg) (addr : Lir.Word),
      srcLbl < pubLbl →
      F'.blocks[srcLbl]? = some srcBlk →
      srcPos = srcBlk.body.size →
      srcBlk.term = .jump ⟨pubLbl, match (generalizing := false) pre with | none => [.v reg] | some (_, a, _) => [a, .v reg]⟩ →
      AgreeBelow aBase env0 envP →
      envP[reg]? = some addr →
      Lir.semStep p { mem := m, ctx, stack := { fn, label := srcLbl, pos := srcPos, env := envP } :: rest } =
        .next { mem := m, ctx, stack := { fn, label := pubLbl, pos := 0, env := bindRes envP addr } :: rest } false := by
    intro m srcLbl srcPos srcBlk envP reg addr hlt hsrcB hsrcP hsrcT hagA hreg
    apply Lir.semStep_next.mpr
    rw [Lir.step_term (fr := { fn, label := srcLbl, pos := srcPos, env := envP }) hF' hsrcB hsrcP]
    rw [hsrcT]
    have hfwd : ¬ (pubLbl ≤ srcLbl) := by dsimp only [Lir.Label] at hlt ⊢; omega
    cases pre with
    | none =>
      simp [Lir.takeEdge, Lir.evalArgs, Lir.Arg.eval, hreg, hpub, hpubParams, Lir.bindParams, bindRes, hfwd]
    | some t =>
      rcases t with ⟨sl, a, w⟩
      obtain ⟨_, _, haEval⟩ := hnoPre sl a w rfl
      have haE := haEval envP hagA
      have hrE : Lir.Arg.eval envP (.v reg) = some addr := hreg
      simp [Lir.takeEdge, Lir.evalArgs, haE, hrE, hpub, hpubParams, Lir.bindParams, bindRes, hfwd]
  unfold evalAllocReserve
  dsimp only
  cases hload0 : Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord headOff) with
  | none =>
    dsimp only
    apply Sem.Reaches.final
    have hst : Lir.step p { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } = .stuck := by
      unfold Lir.step
      simp only [hF', hb0, List.size_toArray, List.length_cons, List.length_nil,
        show 0 < 1 by decide, ↓reduceDIte, List.getElem_toArray, List.getElem_cons_zero,
        ctxAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, Option.bind_eq_bind, Option.bind_some,
        Option.bind_none, headOff, hload0]
    rw [Lir.semStep, hst]; exact .stuck
  | some p0 =>
    dsimp only
    let env1 := env0.insert aBase p0
    have hag1A : AgreeBelow aBase env0 env1 := AgreeBelow.refl.insert_ge (Nat.le_refl _) p0
    have hag1 : AgreeBelow bound env0 env1 := AgreeBelow.refl.insert_ge haGe p0
    have s0 : Lir.semStep p { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } =
        .next { mem, ctx, stack := { fn, label := base, pos := 1, env := env1 } :: rest } false := by
      apply Lir.semStep_next.mpr
      exact Lir.step_stmt (fr := { fn, label := base, pos := 0, env := env0 })
        hF' hb0 (by simp) rfl rfl
        (by simp only [List.getElem_toArray, List.getElem_cons_zero,
          ctxAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, Option.bind_eq_bind,
          Option.bind_some, headOff, hload0, env1])
    by_cases hp0 : Lir.Cond.holds .eq .w64 p0 0 = true
    · simp only [hp0, ↓reduceIte]
      have s1 : Lir.semStep p { mem, ctx, stack := { fn, label := base, pos := 1, env := env1 } :: rest } =
          .next { mem, ctx, stack := { fn, label := base + 2, pos := 0, env := env1 } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn, label := base, pos := 1, env := env1 }) hF' hb0 rfl]
        have hfwd : ¬ (base + 2 ≤ base) := by dsimp only [Lir.Label]; omega
        simp [Lir.Arg.eval, env1, hp0, Lir.takeEdge, Lir.evalArgs, hb2, Lir.bindParams, hfwd]
      cases hlb : Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord Rt.bumpOff) with
      | none =>
        dsimp only
        refine .free s0 (.free s1 (.final ?_))
        have hst : Lir.step p { mem, ctx, stack := { fn, label := base + 2, pos := 0, env := env1 } :: rest } = .stuck := by
          unfold Lir.step
          simp [hF', hb2, ctxAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hlb]
        rw [Lir.semStep, hst]; exact .stuck
      | some b0 =>
        dsimp only
        let env2 := env1.insert (aBase + 2) b0
        have s2 : Lir.semStep p { mem, ctx, stack := { fn, label := base + 2, pos := 0, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fn, label := base + 2, pos := 1, env := env2 } :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fn, label := base + 2, pos := 0, env := env1 })
            hF' hb2 (by simp) rfl rfl
            (by simp [ctxAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hlb, env2])
        cases hll : Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord Rt.limitOff) with
        | none =>
          dsimp only
          refine .free s0 (.free s1 (.free s2 (.final ?_)))
          have hst : Lir.step p { mem, ctx, stack := { fn, label := base + 2, pos := 1, env := env2 } :: rest } = .stuck := by
            unfold Lir.step
            simp [hF', hb2, ctxAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hll]
          rw [Lir.semStep, hst]; exact .stuck
        | some lim =>
          dsimp only
          let env3 := env2.insert (aBase + 3) lim
          have he3_2 : env3[aBase + 2]? = some b0 := by
            rw [Lir.env_insert_ne _ _ (by omega)]; simp [env2]
          have s3 : Lir.semStep p { mem, ctx, stack := { fn, label := base + 2, pos := 1, env := env2 } :: rest } =
              .next { mem, ctx, stack := { fn, label := base + 2, pos := 2, env := env3 } :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fn, label := base + 2, pos := 1, env := env2 })
              hF' hb2 (by simp) rfl rfl
              (by simp [ctxAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hll, env3])
          cases hovf : Lir.Ovf.eval .addC b0 bytes with
          | mk b1 ovf =>
            dsimp only
            let env4 := env3.insert (aBase + 4) b1
            have hag4A : AgreeBelow aBase env0 env4 :=
              ((hag1A.insert_ge (by omega) b0).insert_ge (by omega) lim).insert_ge (by omega) b1
            have hag4 : AgreeBelow bound env0 env4 :=
              ((hag1.insert_ge (by omega) b0).insert_ge (by omega) lim).insert_ge (by omega) b1
            have he4_3 : env4[aBase + 3]? = some lim := by
              rw [Lir.env_insert_ne _ _ (by omega)]; simp [env3]
            have he4_2 : env4[aBase + 2]? = some b0 := by
              rw [Lir.env_insert_ne _ _ (by omega)]; exact he3_2
            cases ovf with
            | true =>
              simp only [↓reduceIte]
              have s4 : Lir.semStep p { mem, ctx, stack := { fn, label := base + 2, pos := 2, env := env3 } :: rest } =
                  .next { mem, ctx, stack := { fn, label := base + 5, pos := 0, env := env4 } :: rest } false := by
                apply Lir.semStep_next.mpr
                rw [Lir.step_term (fr := { fn, label := base + 2, pos := 2, env := env3 }) hF' hb2 rfl]
                have hfwd : ¬ (base + 5 ≤ base + 2) := by dsimp only [Lir.Label]; omega
                simp [Lir.Arg.eval, he3_2, bytes, hovf, Lir.takeEdge, Lir.evalArgs, hb5, Lir.bindParams, env4, hfwd]
              refine .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.final ?_)))))
              have hst : Lir.step p { mem, ctx, stack := { fn, label := base + 5, pos := 0, env := env4 } :: rest } = .fail .heap := by
                rw [Lir.step_term (fr := { fn, label := base + 5, pos := 0, env := env4 }) hF' hb5 rfl]
              rw [Lir.semStep, hst]; exact .fail
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              have s4 : Lir.semStep p { mem, ctx, stack := { fn, label := base + 2, pos := 2, env := env3 } :: rest } =
                  .next { mem, ctx, stack := { fn, label := base + 3, pos := 0, env := env4 } :: rest } false := by
                apply Lir.semStep_next.mpr
                rw [Lir.step_term (fr := { fn, label := base + 2, pos := 2, env := env3 }) hF' hb2 rfl]
                have hfwd : ¬ (base + 3 ≤ base + 2) := by dsimp only [Lir.Label]; omega
                simp [Lir.Arg.eval, he3_2, bytes, hovf, Lir.takeEdge, Lir.evalArgs, hb3, Lir.bindParams, env4, hfwd]
              by_cases hule : Lir.Cond.holds .ule .w64 b1 lim = true
              · simp only [hule, ↓reduceIte]
                have s5 : Lir.semStep p { mem, ctx, stack := { fn, label := base + 3, pos := 0, env := env4 } :: rest } =
                    .next { mem, ctx, stack := { fn, label := base + 4, pos := 0, env := env4 } :: rest } false := by
                  apply Lir.semStep_next.mpr
                  rw [Lir.step_term (fr := { fn, label := base + 3, pos := 0, env := env4 }) hF' hb3 rfl]
                  have hfwd : ¬ (base + 4 ≤ base + 3) := by dsimp only [Lir.Label]; omega
                  simp [Lir.Arg.eval, env4, he4_3, hule, Lir.takeEdge, Lir.evalArgs, hb4, Lir.bindParams, hfwd]
                cases hwb : mem.write? .w64 (ctx + Lir.dispWord Rt.bumpOff) b1 with
                | error _ =>
                  dsimp only
                  refine .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.final ?_))))))
                  have hst : Lir.step p { mem, ctx, stack := { fn, label := base + 4, pos := 0, env := env4 } :: rest } = .stuck := by
                    unfold Lir.step
                    simp [hF', hb4, ctxAddr, Lir.Stmt.exec, addr_ctx, Lir.Arg.eval, env4, hwb]
                  rw [Lir.semStep, hst]; exact .stuck
                | ok mem₁ =>
                  dsimp only
                  have s6 : Lir.semStep p { mem, ctx, stack := { fn, label := base + 4, pos := 0, env := env4 } :: rest } =
                      .next { mem := mem₁, ctx, stack := { fn, label := base + 4, pos := 1, env := env4 } :: rest } false := by
                    apply Lir.semStep_next.mpr
                    exact Lir.step_stmt (fr := { fn, label := base + 4, pos := 0, env := env4 })
                      hF' hb4 (by simp) rfl rfl
                      (by simp [ctxAddr, Lir.Stmt.exec, addr_ctx, Lir.Arg.eval, env4, hwb])
                  have s7 : Lir.semStep p { mem := mem₁, ctx, stack := { fn, label := base + 4, pos := 1, env := env4 } :: rest } =
                      .next { mem := mem₁, ctx, stack := { fn, label := pubLbl, pos := 0, env := bindRes env4 b0 } :: rest } false :=
                    hpubJump mem₁ (base + 4) 1 _ env4 (aBase + 2) b0 (by dsimp only [Lir.Label] at hpubGt ⊢; omega)
                      hb4 rfl rfl hag4A he4_2
                  have hpr := hpubRun b0 mem₁ env4 hag4
                  cases hwH : mem₁.write? .w64 (b0 + Lir.dispWord 0) hdr with
                  | error _ =>
                    rw [hwH] at hpr
                    exact .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 hpr)))))))
                  | ok mem₂ =>
                    rw [hwH] at hpr; dsimp only at hpr ⊢
                    cases hwf : writeFieldsMem mem₂ b0 0 vals with
                    | none =>
                      dsimp only
                      rw [hwf] at hpr
                      exact .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 hpr)))))))
                    | some mem' =>
                      dsimp only
                      rw [hwf] at hpr
                      exact ⟨bindRes env4 b0,
                        .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 hpr))))))),
                        hbindAgree env4 b0 hag4⟩
              · have huleF : Lir.Cond.holds .ule .w64 b1 lim = false := by simpa using hule
                simp only [huleF, Bool.false_eq_true, ↓reduceIte]
                have s5 : Lir.semStep p { mem, ctx, stack := { fn, label := base + 3, pos := 0, env := env4 } :: rest } =
                    .next { mem, ctx, stack := { fn, label := base + 5, pos := 0, env := env4 } :: rest } false := by
                  apply Lir.semStep_next.mpr
                  rw [Lir.step_term (fr := { fn, label := base + 3, pos := 0, env := env4 }) hF' hb3 rfl]
                  have hfwd : ¬ (base + 5 ≤ base + 3) := by dsimp only [Lir.Label]; omega
                  simp [Lir.Arg.eval, env4, he4_3, huleF, Lir.takeEdge, Lir.evalArgs, hb5, Lir.bindParams, hfwd]
                refine .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.final ?_))))))
                have hst : Lir.step p { mem, ctx, stack := { fn, label := base + 5, pos := 0, env := env4 } :: rest } = .fail .heap := by
                  rw [Lir.step_term (fr := { fn, label := base + 5, pos := 0, env := env4 }) hF' hb5 rfl]
                rw [Lir.semStep, hst]; exact .fail
    · have hp0F : Lir.Cond.holds .eq .w64 p0 0 = false := by simpa using hp0
      simp only [hp0F, Bool.false_eq_true, ↓reduceIte]
      have s1 : Lir.semStep p { mem, ctx, stack := { fn, label := base, pos := 1, env := env1 } :: rest } =
          .next { mem, ctx, stack := { fn, label := base + 1, pos := 0, env := env1 } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn, label := base, pos := 1, env := env1 }) hF' hb0 rfl]
        have hfwd : ¬ (base + 1 ≤ base) := by dsimp only [Lir.Label]; omega
        simp [Lir.Arg.eval, env1, hp0F, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams, hfwd]
      cases hln : Lir.loadWord mem .w64 .zero (p0 + Lir.dispWord 0) with
      | none =>
        dsimp only
        refine .free s0 (.free s1 (.final ?_))
        have hst : Lir.step p { mem, ctx, stack := { fn, label := base + 1, pos := 0, env := env1 } :: rest } = .stuck := by
          unfold Lir.step
          simp [hF', hb1, cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
            addr_cell env1 ctx aBase p0 0 (by simp [env1]), hln]
        rw [Lir.semStep, hst]; exact .stuck
      | some nextH =>
        dsimp only
        let env2 := env1.insert (aBase + 1) nextH
        have hag2A : AgreeBelow aBase env0 env2 := hag1A.insert_ge (by omega) nextH
        have hag2 : AgreeBelow bound env0 env2 := hag1.insert_ge (by omega) nextH
        have he2_0 : env2[aBase]? = some p0 := by
          rw [Lir.env_insert_ne _ _ (by omega)]; simp [env1]
        have s2 : Lir.semStep p { mem, ctx, stack := { fn, label := base + 1, pos := 0, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fn, label := base + 1, pos := 1, env := env2 } :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fn, label := base + 1, pos := 0, env := env1 })
            hF' hb1 (by simp) rfl rfl
            (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
              addr_cell env1 ctx aBase p0 0 (by simp [env1]), hln, env2])
        cases hwh : mem.write? .w64 (ctx + Lir.dispWord headOff) nextH with
        | error _ =>
          dsimp only
          refine .free s0 (.free s1 (.free s2 (.final ?_)))
          have hst : Lir.step p { mem, ctx, stack := { fn, label := base + 1, pos := 1, env := env2 } :: rest } = .stuck := by
            unfold Lir.step
            simp only [hF', hb1, List.size_toArray, List.length_cons, List.length_nil,
              show 1 < 2 by decide, ↓reduceDIte, List.getElem_toArray,
              List.getElem_cons_succ, List.getElem_cons_zero,
              ctxAddr, Lir.Stmt.exec, addr_ctx, Lir.Arg.eval, env2, Lir.env_insert_self,
              Option.bind_eq_bind, Option.bind_some, headOff, hwh]
          rw [Lir.semStep, hst]; exact .stuck
        | ok mem₁ =>
          dsimp only
          have s3 : Lir.semStep p { mem, ctx, stack := { fn, label := base + 1, pos := 1, env := env2 } :: rest } =
              .next { mem := mem₁, ctx, stack := { fn, label := base + 1, pos := 2, env := env2 } :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fn, label := base + 1, pos := 1, env := env2 })
              hF' hb1 (by simp) rfl rfl
              (by simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
                ctxAddr, Lir.Stmt.exec, addr_ctx, Lir.Arg.eval, env2, Lir.env_insert_self,
                Option.bind_eq_bind, Option.bind_some, headOff, hwh])
          have s4 : Lir.semStep p { mem := mem₁, ctx, stack := { fn, label := base + 1, pos := 2, env := env2 } :: rest } =
              .next { mem := mem₁, ctx, stack := { fn, label := pubLbl, pos := 0, env := bindRes env2 p0 } :: rest } false :=
            hpubJump mem₁ (base + 1) 2 _ env2 aBase p0 (by dsimp only [Lir.Label] at hpubGt ⊢; omega)
              hb1 rfl rfl hag2A he2_0
          have hpr := hpubRun p0 mem₁ env2 hag2
          cases hwH : mem₁.write? .w64 (p0 + Lir.dispWord 0) hdr with
          | error _ =>
            rw [hwH] at hpr
            exact .free s0 (.free s1 (.free s2 (.free s3 (.free s4 hpr))))
          | ok mem₂ =>
            rw [hwH] at hpr; dsimp only at hpr ⊢
            cases hwf : writeFieldsMem mem₂ p0 0 vals with
            | none =>
              dsimp only
              rw [hwf] at hpr
              exact .free s0 (.free s1 (.free s2 (.free s3 (.free s4 hpr))))
            | some mem' =>
              dsimp only
              rw [hwf] at hpr
              exact ⟨bindRes env2 p0,
                .free s0 (.free s1 (.free s2 (.free s3 (.free s4 hpr)))),
                hbindAgree env2 p0 hag2⟩

/-! ## 3. Shared-path `inc` loop and `dec` execution (`mkResetWrapper` vs `mkSharedIncBlocks`/`mkSharedDecBlocks`) -/

inductive SharedIncOutcome where
  | ok (mem' : X86.Memory)
  | oom
  | stuck

def evalSharedIncList (xVal : Lir.Word) : List Nat → X86.Memory → SharedIncOutcome
  | [], mem => .ok mem
  | j :: rest, mem =>
    match Lir.loadWord mem .w64 .zero (xVal + Lir.dispWord (Int.ofNat (8 * (j + 1)))) with
    | none => .stuck
    | some fv =>
      match evalIncSite fv mem with
      | .ok mem' => evalSharedIncList xVal rest mem'
      | .oom => .oom
      | .stuck => .stuck

def liveFrom (n : Nat) (mask : UInt64) (k : Nat) : List Nat :=
  (List.range' k (n - k)).filter fun j => (mask &&& UInt64.ofNat (2 ^ (j + 1))) != 0

theorem liveFrom_zero (n : Nat) (mask : UInt64) : liveFrom n mask 0 = liveFields n mask := by
  simp [liveFrom, liveFields, List.range_eq_range']

theorem liveFrom_end (n : Nat) (mask : UInt64) : liveFrom n mask n = [] := by
  simp [liveFrom]

theorem liveFrom_step (n : Nat) (mask : UInt64) {k : Nat} (hk : k < n) :
    liveFrom n mask k =
      if (mask &&& UInt64.ofNat (2 ^ (k + 1))) != 0 then k :: liveFrom n mask (k + 1)
      else liveFrom n mask (k + 1) := by
  have hsub : n - k = (n - (k + 1)) + 1 := by omega
  unfold liveFrom
  rw [hsub, List.range'_succ, List.filter_cons]

theorem liveFrom_length_le (n : Nat) (mask : UInt64) (k : Nat) :
    (liveFrom n mask k).length ≤ (liveFields n mask).length := by
  rw [← liveFrom_zero]
  by_cases hkn : k ≤ n
  · have hsplit : List.range' 0 n = List.range' 0 k ++ List.range' k (n - k) := by
      have := List.range'_append (s := 0) (m := k) (n := n - k) (step := 1)
      simpa [Nat.add_sub_of_le hkn] using this.symm
    unfold liveFrom
    rw [Nat.sub_zero, hsplit, List.filter_append, List.length_append]
    omega
  · have : n - k = 0 := by omega
    simp [liveFrom, this]

theorem mkResetWrapper_shared_inc_blocks (isUniqueProc incProc decProc : Nat)
    (lay : Rt.Rc.CellLayout) (cls : Nat) {j : Nat} (hj : j < lay.nobj) :
    let W := mkResetWrapper isUniqueProc incProc decProc lay cls
    let sharedBase := 3 + 2 * lay.nobj
    let bit := UInt64.ofNat (2 ^ (j + 1))
    W.blocks[sharedBase + 2 * j]? =
      some ({ term := .br .tnz .w64 (.v 1) (.imm bit) ⟨sharedBase + 2 * j + 1, []⟩ ⟨sharedBase + 2 * j + 2, []⟩ } : Lir.Block) ∧
    W.blocks[sharedBase + 2 * j + 1]? =
      some ({
        body := #[
          Lir.Stmt.assign (3 + lay.nobj + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) }),
          Lir.Stmt.call [] incProc [.v (3 + lay.nobj + j)]],
        term := .jump ⟨sharedBase + 2 * j + 2, []⟩ } : Lir.Block) := by
  intro W sharedBase bit
  let n := lay.nobj
  let uniqueDecBlocks : List Lir.Block :=
    (List.range n).flatMap fun q =>
      let cur := 2 + 2 * q
      let b := UInt64.ofNat (2 ^ (q + 1))
      [ { term := .br .tnz .w64 (.v 1) (.imm b) ⟨cur + 2, []⟩ ⟨cur + 1, []⟩ },
        { body := #[.call [] decProc [.v (3 + q)]], term := .jump ⟨cur + 2, []⟩ } ]
  let sharedIncBlocks : List Lir.Block :=
    (List.range n).flatMap fun q =>
      let cur := sharedBase + 2 * q
      let b := UInt64.ofNat (2 ^ (q + 1))
      [ { term := .br .tnz .w64 (.v 1) (.imm b) ⟨cur + 1, []⟩ ⟨cur + 2, []⟩ },
        { body := #[
            .assign (3 + n + q) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (q + 1)) }),
            .call [] incProc [.v (3 + n + q)]],
          term := .jump ⟨cur + 2, []⟩ } ]
  have hflatLen : ∀ (f : Nat → List Lir.Block), (∀ q, (f q).length = 2) →
      ∀ m, ((List.range m).flatMap f).length = 2 * m := by
    intro f hf m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton, hf m]
      omega
  have hflatGet : ∀ (f : Nat → List Lir.Block), (∀ q, (f q).length = 2) →
      ∀ m q (hq : q < m),
        ((List.range m).flatMap f)[2 * q]? = (f q)[0]? ∧
        ((List.range m).flatMap f)[2 * q + 1]? = (f q)[1]? := by
    intro f hf m
    induction m with
    | zero => intro q hq; omega
    | succ m ih =>
      intro q hq
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      have hlen : ((List.range m).flatMap f).length = 2 * m := hflatLen f hf m
      by_cases hlt : q < m
      · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
        exact ih q hlt
      · have hqm : q = m := by omega
        subst hqm
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hlen]
        have h1 : 2 * q - 2 * q = 0 := by omega
        have h2 : 2 * q + 1 - 2 * q = 1 := by omega
        rw [h1, h2]; exact ⟨rfl, rfl⟩
  have huLen : uniqueDecBlocks.length = 2 * n := hflatLen _ (fun _ => rfl) n
  have hsLen : sharedIncBlocks.length = 2 * n := hflatLen _ (fun _ => rfl) n
  have hpreLen : ([W.blocks[0]!, W.blocks[1]!] ++ uniqueDecBlocks ++ [({ term := .ret [.v 0] } : Lir.Block)]).length = sharedBase := by
    simp [sharedBase, huLen, n]; omega
  have hgetS := hflatGet (fun q =>
    let cur := sharedBase + 2 * q
    let b := UInt64.ofNat (2 ^ (q + 1))
    [ { term := .br .tnz .w64 (.v 1) (.imm b) ⟨cur + 1, []⟩ ⟨cur + 2, []⟩ },
      { body := #[
          .assign (3 + n + q) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (q + 1)) }),
          .call [] incProc [.v (3 + n + q)]],
        term := .jump ⟨cur + 2, []⟩ } ]) (fun _ => rfl) n j hj
  have hW : W.blocks.toList =
      (([W.blocks[0]!, W.blocks[1]!] ++ uniqueDecBlocks ++ [({ term := .ret [.v 0] } : Lir.Block)]) ++
        sharedIncBlocks) ++ [({ body := #[.call [] decProc [.v 0]], term := .ret [.imm 1] } : Lir.Block)] := by
    simp [W, mkResetWrapper, uniqueDecBlocks, sharedIncBlocks, sharedBase, n, List.append_assoc]
  constructor
  · rw [← Array.getElem?_toList, hW]
    rw [List.getElem?_append_left (by rw [List.length_append, hpreLen, hsLen]; omega)]
    rw [List.getElem?_append_right (by omega), hpreLen, Nat.add_sub_cancel_left]
    exact hgetS.1
  · rw [← Array.getElem?_toList, hW]
    rw [List.getElem?_append_left (by rw [List.length_append, hpreLen, hsLen]; omega)]
    rw [List.getElem?_append_right (by omega), hpreLen]
    have hsub : sharedBase + 2 * j + 1 - sharedBase = 2 * j + 1 := by omega
    rw [hsub]
    exact hgetS.2

theorem mkResetWrapper_shared_ret_block (isUniqueProc incProc decProc : Nat)
    (lay : Rt.Rc.CellLayout) (cls : Nat) :
    let W := mkResetWrapper isUniqueProc incProc decProc lay cls
    let sharedBase := 3 + 2 * lay.nobj
    W.blocks[sharedBase + 2 * lay.nobj]? =
      some { body := #[.call [] decProc [.v 0]], term := .ret [.imm 1] } := by
  intro W sharedBase
  let n := lay.nobj
  have hflatLen : ∀ (f : Nat → List Lir.Block), (∀ q, (f q).length = 2) →
      ∀ m, ((List.range m).flatMap f).length = 2 * m := by
    intro f hf m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton, hf m]
      omega
  rw [← Array.getElem?_toList]
  simp only [W, mkResetWrapper, List.toList_toArray]
  have huLen : ((List.range n).flatMap fun j =>
        let cur := 2 + 2 * j
        let bit := UInt64.ofNat (2 ^ (j + 1))
        [ ({ term := .br .tnz .w64 (.v 1) (.imm bit) ⟨cur + 2, []⟩ ⟨cur + 1, []⟩ } : Lir.Block),
          ({ body := #[Lir.Stmt.call [] decProc [.v (3 + j)]], term := .jump ⟨cur + 2, []⟩ } : Lir.Block) ]).length = 2 * n :=
    hflatLen _ (fun _ => rfl) n
  have hsLen : ((List.range n).flatMap fun j =>
        let cur := sharedBase + 2 * j
        let bit := UInt64.ofNat (2 ^ (j + 1))
        [ ({ term := .br .tnz .w64 (.v 1) (.imm bit) ⟨cur + 1, []⟩ ⟨cur + 2, []⟩ } : Lir.Block),
          ({
              body := #[
                Lir.Stmt.assign (3 + n + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) }),
                Lir.Stmt.call [] incProc [.v (3 + n + j)]],
              term := .jump ⟨cur + 2, []⟩ } : Lir.Block) ]).length = 2 * n :=
    hflatLen _ (fun _ => rfl) n
  have hlen : (([
      { body := #[Lir.Stmt.call [2] isUniqueProc [.v 0]],
        term := .br .eq .w64 (.v 2) (.imm 1) ⟨1, []⟩ ⟨sharedBase, []⟩ },
      { body := (((List.range n).map fun j =>
          Lir.Stmt.assign (3 + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })) ++
          (Lir.Stmt.store .w64 { base := some (.v 0), disp := 0 } (.imm (Rt.Rc.dynamicHeader n cls lay.tag 1)) ::
            (List.range n).map fun j =>
              Lir.Stmt.store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.imm 1))).toArray,
        term := .jump ⟨2, []⟩ }] : List Lir.Block) ++
      ((List.range n).flatMap fun j =>
        let cur := 2 + 2 * j
        let bit := UInt64.ofNat (2 ^ (j + 1))
        [ ({ term := .br .tnz .w64 (.v 1) (.imm bit) ⟨cur + 2, []⟩ ⟨cur + 1, []⟩ } : Lir.Block),
          ({ body := #[Lir.Stmt.call [] decProc [.v (3 + j)]], term := .jump ⟨cur + 2, []⟩ } : Lir.Block) ]) ++
      [({ term := .ret [.v 0] } : Lir.Block)] ++
      ((List.range n).flatMap fun j =>
        let cur := sharedBase + 2 * j
        let bit := UInt64.ofNat (2 ^ (j + 1))
        [ ({ term := .br .tnz .w64 (.v 1) (.imm bit) ⟨cur + 1, []⟩ ⟨cur + 2, []⟩ } : Lir.Block),
          ({
              body := #[
                Lir.Stmt.assign (3 + n + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) }),
                Lir.Stmt.call [] incProc [.v (3 + n + j)]],
              term := .jump ⟨cur + 2, []⟩ } : Lir.Block) ])).length = sharedBase + 2 * n := by
    simp only [List.length_append, List.length_cons, List.length_nil, huLen, hsLen]
    dsimp only [sharedBase, n]; omega
  rw [List.getElem?_append_right (by rw [hlen]; dsimp only [sharedBase, n]; omega), hlen]
  have hsub : sharedBase + 2 * lay.nobj - (sharedBase + 2 * n) = 0 := by dsimp only [sharedBase, n]; omega
  rw [hsub]; rfl

theorem raw_reset_shared_inc_loop {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {idx : Nat} {c : Lam.CtorInfo} {lay : Rt.Rc.CellLayout} {cls : Nat}
    {xVal mask ctx : Lir.Word} {caller : Lir.Frame} {rest : List Lir.Frame}
    (hc : l.ctors[idx]? = some c)
    (hlay : lay = Rt.Rc.CellLayout.ofFields c.arity c.tag)
    (hcls : lay.cls? = some cls) :
    ∀ k (_ : k ≤ lay.nobj) (wEnv : Lir.Env) (mem : X86.Memory),
      wEnv[0]? = some xVal → wEnv[1]? = some mask →
      let sharedBase := 3 + 2 * lay.nobj
      let wFr : Lir.Frame := { fn := l.resetWrapper idx, label := sharedBase + 2 * k, pos := 0, env := wEnv }
      match evalSharedIncList xVal (liveFrom lay.nobj mask k) mem with
      | .ok mem' =>
        ∃ wEnv', wEnv'[0]? = some xVal ∧ wEnv'[1]? = some mask ∧
          Sem.Star (Lir.semStep raw) { mem, ctx, stack := wFr :: caller :: rest }
            (liveFrom lay.nobj mask k).length
            { mem := mem', ctx, stack := { fn := l.resetWrapper idx, label := sharedBase + 2 * lay.nobj, pos := 0, env := wEnv' } :: caller :: rest }
      | .oom =>
        Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := wFr :: caller :: rest }
          (liveFrom lay.nobj mask k).length (.resource .heap)
      | .stuck =>
        Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := wFr :: caller :: rest }
          (liveFrom lay.nobj mask k).length .stuck := by
  have hwrapF : raw.funcs[l.resetWrapper idx]? =
      some (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls) := by
    rw [hlay]; exact hr.resetWrap idx c cls hc (by rwa [← hlay])
  intro k hk
  induction hd : lay.nobj - k generalizing k with
  | zero =>
    intro wEnv mem hw0 hw1
    have hkeq : k = lay.nobj := by omega
    subst hkeq
    simp [liveFrom_end, evalSharedIncList]
    exact ⟨wEnv, hw0, hw1, .refl _⟩
  | succ rem ih =>
    intro wEnv mem hw0 hw1
    have hlt : k < lay.nobj := by omega
    let sharedBase := 3 + 2 * lay.nobj
    let bit := UInt64.ofNat (2 ^ (k + 1))
    obtain ⟨hb0, hb1⟩ := mkResetWrapper_shared_inc_blocks l.isUniqueProc l.incProc l.decProc lay cls hlt
    have hnextBlk : ∃ nb, (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls).blocks[sharedBase + 2 * k + 2]? = some nb ∧
        nb.params = [] := by
      by_cases hlast : k + 1 < lay.nobj
      · obtain ⟨hnb, _⟩ := mkResetWrapper_shared_inc_blocks l.isUniqueProc l.incProc l.decProc lay cls hlast
        have hidx : sharedBase + 2 * (k + 1) = sharedBase + 2 * k + 2 := by omega
        rw [hidx] at hnb
        exact ⟨_, hnb, rfl⟩
      · have hke : sharedBase + 2 * k + 2 = sharedBase + 2 * lay.nobj := by omega
        rw [hke]
        exact ⟨_, mkResetWrapper_shared_ret_block l.isUniqueProc l.incProc l.decProc lay cls, rfl⟩
    obtain ⟨nb, hnb, hnbp⟩ := hnextBlk
    have hnextIdx : sharedBase + 2 * k + 2 = sharedBase + 2 * (k + 1) := by omega
    rw [liveFrom_step lay.nobj mask hlt]
    by_cases hbit : (mask &&& bit) != 0
    · simp only [bit] at hbit
      simp only [hbit, ↓reduceIte, List.length_cons]
      have htnz : Lir.Cond.holds .tnz .w64 mask (UInt64.ofNat (2 ^ (k + 1))) = true := by
        rw [w64_tnz_eq]; exact hbit
      have sBr : Lir.semStep raw
          { mem, ctx, stack := { fn := l.resetWrapper idx, label := sharedBase + 2 * k, pos := 0, env := wEnv } :: caller :: rest } =
          .next { mem, ctx, stack := { fn := l.resetWrapper idx, label := sharedBase + 2 * k + 1, pos := 0, env := wEnv } :: caller :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := l.resetWrapper idx, label := sharedBase + 2 * k, pos := 0, env := wEnv }) hwrapF hb0 rfl]
        have hfwd : ¬ (3 + 2 * lay.nobj + 2 * k + 1 ≤ 3 + 2 * lay.nobj + 2 * k) := by omega
        simp [sharedBase, Lir.Arg.eval, hw1, htnz, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams, hfwd]
      unfold evalSharedIncList
      cases hload : Lir.loadWord mem .w64 .zero (xVal + Lir.dispWord (Int.ofNat (8 * (k + 1)))) with
      | none =>
        dsimp only
        have hst : Lir.step raw { mem, ctx, stack := { fn := l.resetWrapper idx, label := sharedBase + 2 * k + 1, pos := 0, env := wEnv } :: caller :: rest } = .stuck := by
          unfold Lir.step
          simp only [sharedBase, hwrapF, hb1, List.size_toArray, List.length_cons, List.length_nil,
            show 0 < 2 by decide, ↓reduceDIte, List.getElem_toArray, List.getElem_cons_zero,
            Lir.Stmt.exec, Lir.Rhs.eval, addr_cell wEnv ctx 0 xVal _ hw0,
            Option.bind_eq_bind, Option.bind_some, Option.bind_none, hload]
        exact (Sem.Reaches.free sBr (Sem.Reaches.final (by rw [Lir.semStep, hst]; exact .stuck))).mono (by simp) (Nat.zero_le _)
      | some fv =>
        dsimp only
        let wEnv1 := wEnv.insert (3 + lay.nobj + k) fv
        have hw1_0 : wEnv1[0]? = some xVal := by rw [Lir.env_insert_ne _ _ (by omega), hw0]
        have hw1_1 : wEnv1[1]? = some mask := by rw [Lir.env_insert_ne _ _ (by omega), hw1]
        have sLd : Lir.semStep raw
            { mem, ctx, stack := { fn := l.resetWrapper idx, label := sharedBase + 2 * k + 1, pos := 0, env := wEnv } :: caller :: rest } =
            .next { mem, ctx, stack := { fn := l.resetWrapper idx, label := sharedBase + 2 * k + 1, pos := 1, env := wEnv1 } :: caller :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fn := l.resetWrapper idx, label := sharedBase + 2 * k + 1, pos := 0, env := wEnv })
            hwrapF hb1 (by simp) rfl rfl
            (by simp only [List.getElem_toArray, List.getElem_cons_zero,
              Lir.Stmt.exec, Lir.Rhs.eval, addr_cell wEnv ctx 0 xVal _ hw0,
              Option.bind_eq_bind, Option.bind_some, hload, wEnv1])
        let pFr0 : Lir.Frame := { fn := l.incProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 fv }
        let wRet : Lir.Frame := { fn := l.resetWrapper idx, label := sharedBase + 2 * k + 1, pos := 2, env := wEnv1, dsts := [] }
        have sCall : Lir.semStep raw
            { mem, ctx, stack := { fn := l.resetWrapper idx, label := sharedBase + 2 * k + 1, pos := 1, env := wEnv1 } :: caller :: rest } =
            .next { mem, ctx, stack := pFr0 :: wRet :: caller :: rest } true := by
          apply Lir.semStep_next.mpr
          exact Lir.step_call (fr := { fn := l.resetWrapper idx, label := sharedBase + 2 * k + 1, pos := 1, env := wEnv1 })
            (vs := [fv]) hwrapF hb1 (by simp) rfl
            (by simp [Lir.evalArgs, Lir.Arg.eval, wEnv1])
            (by simp [Lir.enter, hr.incProc, Rt.Rc.Procs.inc, Lir.bindParams, pFr0])
        have hinc := raw_incProc_exec hr (xVal := fv) (ctx := ctx) (mem := mem)
          (caller := wRet) (rest := caller :: rest) rfl
        cases hincEv : evalIncSite fv mem with
        | oom =>
          dsimp only
          rw [hincEv] at hinc
          exact (Sem.Reaches.free sBr (Sem.Reaches.free sLd (Sem.Reaches.charge sCall hinc))).mono (by simp) (by omega)
        | stuck =>
          dsimp only
          rw [hincEv] at hinc
          exact (Sem.Reaches.free sBr (Sem.Reaches.free sLd (Sem.Reaches.charge sCall hinc))).mono (by simp) (by omega)
        | ok mem₁ =>
          dsimp only
          rw [hincEv] at hinc
          have sJmp : Lir.semStep raw { mem := mem₁, ctx, stack := wRet :: caller :: rest } =
              .next { mem := mem₁, ctx, stack := { fn := l.resetWrapper idx, label := sharedBase + 2 * (k + 1), pos := 0, env := wEnv1 } :: caller :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := wRet) hwrapF hb1 rfl]
            dsimp only [wRet, sharedBase] at hnb hnextIdx ⊢
            rw [hnextIdx] at hnb
            rw [Lir.takeEdge, Lir.evalArgs]
            simp only [List.mapM_nil, pure, hnextIdx, hnb, hnbp, Lir.bindParams]
            have hfwd : ¬ (3 + 2 * lay.nobj + 2 * (k + 1) ≤ 3 + 2 * lay.nobj + 2 * k + 1) := by omega
            simp [hfwd]
          have hpref : Sem.Star (Lir.semStep raw)
              { mem, ctx, stack := { fn := l.resetWrapper idx, label := sharedBase + 2 * k, pos := 0, env := wEnv } :: caller :: rest } 1
              { mem := mem₁, ctx, stack := { fn := l.resetWrapper idx, label := sharedBase + 2 * (k + 1), pos := 0, env := wEnv1 } :: caller :: rest } :=
            .free sBr (.free sLd (.charge sCall (hinc.trans (.free sJmp (.refl _)))))
          have hrec := ih (k + 1) (by omega) (by omega) wEnv1 mem₁ hw1_0 hw1_1
          cases htail : evalSharedIncList xVal (liveFrom lay.nobj mask (k + 1)) mem₁ with
          | ok mem' =>
            dsimp only
            rw [htail] at hrec
            obtain ⟨wEnv', h0', h1', hstar'⟩ := hrec
            exact ⟨wEnv', h0', h1', by simpa [sharedBase, Nat.add_comm] using hpref.trans hstar'⟩
          | oom =>
            dsimp only
            rw [htail] at hrec
            have hr' := star_reaches hpref hrec
            simpa [sharedBase, Nat.add_comm] using hr'
          | stuck =>
            dsimp only
            rw [htail] at hrec
            have hr' := star_reaches hpref hrec
            simpa [sharedBase, Nat.add_comm] using hr'
    · simp only [bit] at hbit
      simp only [hbit, Bool.false_eq_true, ↓reduceIte]
      have htnzF : Lir.Cond.holds .tnz .w64 mask (UInt64.ofNat (2 ^ (k + 1))) = false := by
        rw [w64_tnz_eq]; simpa using hbit
      have sBr : Lir.semStep raw
          { mem, ctx, stack := { fn := l.resetWrapper idx, label := sharedBase + 2 * k, pos := 0, env := wEnv } :: caller :: rest } =
          .next { mem, ctx, stack := { fn := l.resetWrapper idx, label := sharedBase + 2 * (k + 1), pos := 0, env := wEnv } :: caller :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := l.resetWrapper idx, label := sharedBase + 2 * k, pos := 0, env := wEnv }) hwrapF hb0 rfl]
        dsimp only [sharedBase] at hnb hnextIdx ⊢
        rw [hnextIdx] at hnb
        simp only [Lir.Arg.eval, hw1, htnzF, Bool.false_eq_true, ↓reduceIte, Lir.takeEdge, Lir.evalArgs,
          List.mapM_nil, pure, hnextIdx, hnb, hnbp, Lir.bindParams]
        have hfwd : ¬ (3 + 2 * lay.nobj + 2 * (k + 1) ≤ 3 + 2 * lay.nobj + 2 * k) := by omega
        simp [hfwd]
      have hrec := ih (k + 1) (by omega) (by omega) wEnv mem hw0 hw1
      cases htail : evalSharedIncList xVal (liveFrom lay.nobj mask (k + 1)) mem with
      | ok mem' =>
        dsimp only
        rw [htail] at hrec
        obtain ⟨wEnv', h0', h1', hstar'⟩ := hrec
        exact ⟨wEnv', h0', h1', .free sBr hstar'⟩
      | oom =>
        dsimp only
        rw [htail] at hrec
        exact .free sBr hrec
      | stuck =>
        dsimp only
        rw [htail] at hrec
        exact .free sBr hrec

theorem inl_sharedIncBlocks_exec {p : Lir.Program} {F' : Lir.Func} {fn : Lir.FunId}
    {x : Lir.VReg} {xVal ctx : Lir.Word} {rest : List Lir.Frame} {bound : Nat}
    (hF' : p.funcs[fn]? = some F') (hxLt : (x : Nat) < bound) :
    ∀ (live : List Nat) (base : Lir.Label) (tmp : Lir.VReg) (env0 : Lir.Env) (mem : X86.Memory),
      bound ≤ tmp → env0[x]? = some xVal →
      (∀ k blk, (mkSharedIncBlocks x base tmp live)[k]? = some blk → F'.blocks[base + k]? = some blk) →
      (∃ nb, F'.blocks[base + 5 * live.length]? = some nb ∧ nb.params = []) →
      match evalSharedIncList xVal live mem with
      | .ok mem' =>
        ∃ env', AgreeBelow bound env0 env' ∧
          Sem.Star (Lir.semStep p)
            { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } 0
            { mem := mem', ctx, stack := { fn, label := base + 5 * live.length, pos := 0, env := env' } :: rest }
      | .oom =>
        Sem.Reaches (Lir.semStep p)
          { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } 0 (.resource .heap)
      | .stuck =>
        Sem.Reaches (Lir.semStep p)
          { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } 0 .stuck := by
  intro live
  induction live with
  | nil =>
    intro base tmp env0 mem _ _ _ _
    simp [evalSharedIncList]
    exact ⟨env0, AgreeBelow.refl, .refl _⟩
  | cons j tl ih =>
    intro base tmp env0 mem htmp hx hblks ⟨nbEnd, hnbEnd, hnbEndP⟩
    have hb0 : F'.blocks[base]? = some ({
        body := #[.assign tmp (.load .w64 .zero (cellAddr x (Int.ofNat (8 * (j + 1)))))],
        term := .br .tnz .w64 (.v tmp) (.imm 1) ⟨base + 5, []⟩ ⟨base + 1, []⟩, cold := true } : Lir.Block) := by
      simpa using hblks 0 _ rfl
    have hb1 : F'.blocks[base + 1]? = some ({
        body := #[.assign (tmp + 1) (.load .w32 .zero (cellAddr tmp 4))],
        term := .br .ult .w32 (.v (tmp + 1)) (.imm (UInt64.ofNat (Rt.Rc.maxCount - 1)))
          ⟨base + 2, []⟩ ⟨base + 3, []⟩, cold := true } : Lir.Block) := hblks 1 _ rfl
    have hb2 : F'.blocks[base + 2]? = some ({
        body := #[.assign (tmp + 2) (.bin .add .w32 (.v (tmp + 1)) (.imm 1)),
          .store .w32 (cellAddr tmp 4) (.v (tmp + 2))],
        term := .jump ⟨base + 5, []⟩, cold := true } : Lir.Block) := hblks 2 _ rfl
    have hb3 : F'.blocks[base + 3]? = some ({
        body := #[],
        term := .br .eq .w32 (.v (tmp + 1)) (.imm (UInt64.ofNat (Rt.Rc.maxCount - 1)))
          ⟨base + 4, []⟩ ⟨base + 5, []⟩, cold := true } : Lir.Block) := hblks 3 _ rfl
    have hb4 : F'.blocks[base + 4]? = some ({
        body := #[], term := .fail .heap, cold := true } : Lir.Block) := hblks 4 _ rfl
    have htlBlks : ∀ k blk, (mkSharedIncBlocks x (base + 5) (tmp + 3) tl)[k]? = some blk →
        F'.blocks[(base + 5) + k]? = some blk := by
      intro k blk hk
      have h := hblks (5 + k) blk (by simp [mkSharedIncBlocks, Nat.add_comm 5 k, hk])
      simpa [Nat.add_assoc] using h
    have hnextBlk : ∃ nb, F'.blocks[base + 5]? = some nb ∧ nb.params = [] := by
      cases tl with
      | nil => exact ⟨nbEnd, by simpa using hnbEnd, hnbEndP⟩
      | cons j2 tl2 =>
        exact ⟨_, by simpa using htlBlks 0 _ rfl, rfl⟩
    obtain ⟨nb5, hnb5, hnb5p⟩ := hnextBlk
    have hendIdx : (base + 5) + 5 * tl.length = base + 5 * (j :: tl).length := by
      dsimp only [Lir.Label]; simp only [List.length_cons]; omega
    unfold evalSharedIncList
    cases hload : Lir.loadWord mem .w64 .zero (xVal + Lir.dispWord (Int.ofNat (8 * (j + 1)))) with
    | none =>
      dsimp only
      apply Sem.Reaches.final
      have hst : Lir.step p { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } = .stuck := by
        unfold Lir.step
        simp only [hF', hb0, List.size_toArray, List.length_cons, List.length_nil,
          show 0 < 1 by decide, ↓reduceDIte, List.getElem_toArray, List.getElem_cons_zero,
          cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell env0 ctx x xVal _ hx,
          Option.bind_eq_bind, Option.bind_some, Option.bind_none, hload]
      rw [Lir.semStep, hst]; exact .stuck
    | some fv =>
      dsimp only
      let env1 := env0.insert tmp fv
      have hag1 : AgreeBelow bound env0 env1 := AgreeBelow.refl.insert_ge htmp fv
      have sLd : Lir.semStep p { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } =
          .next { mem, ctx, stack := { fn, label := base, pos := 1, env := env1 } :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fn, label := base, pos := 0, env := env0 })
          hF' hb0 (by simp) rfl rfl
          (by simp only [List.getElem_toArray, List.getElem_cons_zero,
            cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell env0 ctx x xVal _ hx,
            Option.bind_eq_bind, Option.bind_some, hload, env1])
      have hcont : ∀ (mem₁ : X86.Memory) (envNext : Lir.Env),
          AgreeBelow bound env0 envNext →
          Sem.Star (Lir.semStep p)
            { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } 0
            { mem := mem₁, ctx, stack := { fn, label := base + 5, pos := 0, env := envNext } :: rest } →
          match evalSharedIncList xVal tl mem₁ with
          | .ok mem' =>
            ∃ env', AgreeBelow bound env0 env' ∧
              Sem.Star (Lir.semStep p)
                { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } 0
                { mem := mem', ctx, stack := { fn, label := base + 5 * (j :: tl).length, pos := 0, env := env' } :: rest }
          | .oom =>
            Sem.Reaches (Lir.semStep p)
              { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } 0 (.resource .heap)
          | .stuck =>
            Sem.Reaches (Lir.semStep p)
              { mem, ctx, stack := { fn, label := base, pos := 0, env := env0 } :: rest } 0 .stuck := by
        intro mem₁ envNext hagN hpref
        have hxN : envNext[x]? = some xVal := by rw [← hagN x hxLt, hx]
        have hrec := ih (base + 5) (tmp + 3) envNext mem₁ (by omega) hxN htlBlks
          ⟨nbEnd, by simpa [hendIdx] using hnbEnd, hnbEndP⟩
        cases htl : evalSharedIncList xVal tl mem₁ with
        | ok mem' =>
          dsimp only
          rw [htl] at hrec
          obtain ⟨env', hag', hstar'⟩ := hrec
          exact ⟨env', fun r hr => (hagN r hr).trans (hag' r hr),
            by simpa [hendIdx] using hpref.trans hstar'⟩
        | oom =>
          dsimp only
          rw [htl] at hrec
          exact by simpa using star_reaches hpref hrec
        | stuck =>
          dsimp only
          rw [htl] at hrec
          exact by simpa using star_reaches hpref hrec
      unfold evalIncSite
      by_cases htag : Lir.Cond.holds .tnz .w64 fv 1 = true
      · simp only [htag, ↓reduceIte]
        have sBr : Lir.semStep p { mem, ctx, stack := { fn, label := base, pos := 1, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fn, label := base + 5, pos := 0, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fn, label := base, pos := 1, env := env1 }) hF' hb0 rfl]
          have hfwd : ¬ (base + 5 ≤ base) := by dsimp only [Lir.Label]; omega
          simp [Lir.Arg.eval, env1, htag, Lir.takeEdge, Lir.evalArgs, hnb5, hnb5p, Lir.bindParams, hfwd]
        exact hcont mem env1 hag1 (.free sLd (.free sBr (.refl _)))
      · have htagF : Lir.Cond.holds .tnz .w64 fv 1 = false := by simpa using htag
        simp only [htagF, Bool.false_eq_true, ↓reduceIte]
        have sBr : Lir.semStep p { mem, ctx, stack := { fn, label := base, pos := 1, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fn, label := base + 1, pos := 0, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fn, label := base, pos := 1, env := env1 }) hF' hb0 rfl]
          have hfwd : ¬ (base + 1 ≤ base) := by dsimp only [Lir.Label]; omega
          simp [Lir.Arg.eval, env1, htagF, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams, hfwd]
        cases hlc : Lir.loadWord mem .w32 .zero (fv + Lir.dispWord 4) with
        | none =>
          dsimp only
          refine .free sLd (.free sBr (.final ?_))
          have hst : Lir.step p { mem, ctx, stack := { fn, label := base + 1, pos := 0, env := env1 } :: rest } = .stuck := by
            unfold Lir.step
            simp [hF', hb1, cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
              addr_cell env1 ctx tmp fv 4 (by simp [env1]), hlc]
          rw [Lir.semStep, hst]; exact .stuck
        | some cnt =>
          dsimp only
          let env2 := env1.insert (tmp + 1) cnt
          have hag2 : AgreeBelow bound env0 env2 := hag1.insert_ge (by omega) cnt
          have sLc : Lir.semStep p { mem, ctx, stack := { fn, label := base + 1, pos := 0, env := env1 } :: rest } =
              .next { mem, ctx, stack := { fn, label := base + 1, pos := 1, env := env2 } :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fn, label := base + 1, pos := 0, env := env1 })
              hF' hb1 (by simp) rfl rfl
              (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
                addr_cell env1 ctx tmp fv 4 (by simp [env1]), hlc, env2])
          by_cases hlt : (X86.Width.w32.truncate cnt).toNat < 2 ^ 31 - 1
          · simp only [hlt, ↓reduceIte]
            have hult : Lir.Cond.holds .ult .w32 cnt (UInt64.ofNat (Rt.Rc.maxCount - 1)) = true := by
              rw [w32_ult_maxMinus1]; simp [hlt]
            have sUlt : Lir.semStep p { mem, ctx, stack := { fn, label := base + 1, pos := 1, env := env2 } :: rest } =
                .next { mem, ctx, stack := { fn, label := base + 2, pos := 0, env := env2 } :: rest } false := by
              apply Lir.semStep_next.mpr
              rw [Lir.step_term (fr := { fn, label := base + 1, pos := 1, env := env2 }) hF' hb1 rfl]
              have hfwd : ¬ (base + 2 ≤ base + 1) := by dsimp only [Lir.Label]; omega
              simp [Lir.Arg.eval, env2, hult, Lir.takeEdge, Lir.evalArgs, hb2, Lir.bindParams, hfwd]
            let env3 := env2.insert (tmp + 2) (X86.Width.w32.truncate (cnt + 1))
            have hag3 : AgreeBelow bound env0 env3 := hag2.insert_ge (by omega) _
            have hf3 : env3[tmp]? = some fv := by
              rw [Lir.env_insert_ne _ _ (by omega), Lir.env_insert_ne _ _ (by omega)]; simp [env1]
            have sAdd : Lir.semStep p { mem, ctx, stack := { fn, label := base + 2, pos := 0, env := env2 } :: rest } =
                .next { mem, ctx, stack := { fn, label := base + 2, pos := 1, env := env3 } :: rest } false := by
              apply Lir.semStep_next.mpr
              exact Lir.step_stmt (fr := { fn, label := base + 2, pos := 0, env := env2 })
                hF' hb2 (by simp) rfl rfl
                (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.BinOp.eval, Lir.Arg.eval, env2, env3])
            cases hw : mem.write? .w32 (fv + Lir.dispWord 4) (X86.Width.w32.truncate (cnt + 1)) with
            | error _ =>
              dsimp only
              refine .free sLd (.free sBr (.free sLc (.free sUlt (.free sAdd (.final ?_)))))
              have hst : Lir.step p { mem, ctx, stack := { fn, label := base + 2, pos := 1, env := env3 } :: rest } = .stuck := by
                unfold Lir.step
                simp [hF', hb2, cellAddr, Lir.Stmt.exec, addr_cell env3 ctx tmp fv 4 hf3, Lir.Arg.eval, env3, hw]
              rw [Lir.semStep, hst]; exact .stuck
            | ok mem₁ =>
              dsimp only
              have sSt : Lir.semStep p { mem, ctx, stack := { fn, label := base + 2, pos := 1, env := env3 } :: rest } =
                  .next { mem := mem₁, ctx, stack := { fn, label := base + 2, pos := 2, env := env3 } :: rest } false := by
                apply Lir.semStep_next.mpr
                exact Lir.step_stmt (fr := { fn, label := base + 2, pos := 1, env := env3 })
                  hF' hb2 (by simp) rfl rfl
                  (by simp [cellAddr, Lir.Stmt.exec, addr_cell env3 ctx tmp fv 4 hf3, Lir.Arg.eval, env3, hw])
              have sJmp : Lir.semStep p { mem := mem₁, ctx, stack := { fn, label := base + 2, pos := 2, env := env3 } :: rest } =
                  .next { mem := mem₁, ctx, stack := { fn, label := base + 5, pos := 0, env := env3 } :: rest } false := by
                apply Lir.semStep_next.mpr
                rw [Lir.step_term (fr := { fn, label := base + 2, pos := 2, env := env3 }) hF' hb2 rfl]
                have hfwd : ¬ (base + 5 ≤ base + 2) := by dsimp only [Lir.Label]; omega
                simp [Lir.takeEdge, Lir.evalArgs, hnb5, hnb5p, Lir.bindParams, hfwd]
              exact hcont mem₁ env3 hag3
                (.free sLd (.free sBr (.free sLc (.free sUlt (.free sAdd (.free sSt (.free sJmp (.refl _))))))))
          · simp only [hlt, ↓reduceIte]
            have hultF : Lir.Cond.holds .ult .w32 cnt (UInt64.ofNat (Rt.Rc.maxCount - 1)) = false := by
              rw [w32_ult_maxMinus1]; simp [hlt]
            have sUlt : Lir.semStep p { mem, ctx, stack := { fn, label := base + 1, pos := 1, env := env2 } :: rest } =
                .next { mem, ctx, stack := { fn, label := base + 3, pos := 0, env := env2 } :: rest } false := by
              apply Lir.semStep_next.mpr
              rw [Lir.step_term (fr := { fn, label := base + 1, pos := 1, env := env2 }) hF' hb1 rfl]
              have hfwd : ¬ (base + 3 ≤ base + 1) := by dsimp only [Lir.Label]; omega
              simp [Lir.Arg.eval, env2, hultF, Lir.takeEdge, Lir.evalArgs, hb3, Lir.bindParams, hfwd]
            by_cases heqN : (X86.Width.w32.truncate cnt).toNat = 2 ^ 31 - 1
            · simp only [heqN, ↓reduceIte]
              have heqT : Lir.Cond.holds .eq .w32 cnt (UInt64.ofNat (Rt.Rc.maxCount - 1)) = true := by
                rw [w32_eq_maxMinus1]; simp [heqN]
              have sEq : Lir.semStep p { mem, ctx, stack := { fn, label := base + 3, pos := 0, env := env2 } :: rest } =
                  .next { mem, ctx, stack := { fn, label := base + 4, pos := 0, env := env2 } :: rest } false := by
                apply Lir.semStep_next.mpr
                rw [Lir.step_term (fr := { fn, label := base + 3, pos := 0, env := env2 }) hF' hb3 rfl]
                have hfwd : ¬ (base + 4 ≤ base + 3) := by dsimp only [Lir.Label]; omega
                simp [Lir.Arg.eval, env2, heqT, Lir.takeEdge, Lir.evalArgs, hb4, Lir.bindParams, hfwd]
              refine .free sLd (.free sBr (.free sLc (.free sUlt (.free sEq (.final ?_)))))
              have hst : Lir.step p { mem, ctx, stack := { fn, label := base + 4, pos := 0, env := env2 } :: rest } = .fail .heap := by
                rw [Lir.step_term (fr := { fn, label := base + 4, pos := 0, env := env2 }) hF' hb4 rfl]
              rw [Lir.semStep, hst]; exact .fail
            · simp only [heqN, ↓reduceIte]
              have heqF : Lir.Cond.holds .eq .w32 cnt (UInt64.ofNat (Rt.Rc.maxCount - 1)) = false := by
                rw [w32_eq_maxMinus1]; simp [heqN]
              have sEq : Lir.semStep p { mem, ctx, stack := { fn, label := base + 3, pos := 0, env := env2 } :: rest } =
                  .next { mem, ctx, stack := { fn, label := base + 5, pos := 0, env := env2 } :: rest } false := by
                apply Lir.semStep_next.mpr
                rw [Lir.step_term (fr := { fn, label := base + 3, pos := 0, env := env2 }) hF' hb3 rfl]
                have hfwd : ¬ (base + 5 ≤ base + 3) := by dsimp only [Lir.Label]; omega
                simp [Lir.Arg.eval, env2, heqF, Lir.takeEdge, Lir.evalArgs, hnb5, hnb5p, Lir.bindParams, hfwd]
              exact hcont mem env2 hag2 (.free sLd (.free sBr (.free sLc (.free sUlt (.free sEq (.refl _))))))

theorem inl_sharedDecBlocks_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F' : Lir.Func} {fn : Lir.FunId} {decLbl doneLbl : Lir.Label} {tmp bound : Nat}
    {x : Lir.VReg} {xVal ctx : Lir.Word} {doneSlot : Option Lir.VReg} {doneBlk : Lir.Block}
    {env0 : Lir.Env} {mem : X86.Memory} {rest : List Lir.Frame}
    (hF' : (inlineProgram l raw).funcs[fn]? = some F')
    (hxLt : (x : Nat) < bound) (htmp : bound ≤ tmp) (hx : env0[x]? = some xVal)
    (hdoneGt : decLbl + 4 < doneLbl)
    (hdoneBlk : F'.blocks[doneLbl]? = some doneBlk)
    (hdoneParams : doneBlk.params = match doneSlot with | some slot => [slot] | none => [])
    (hblks : ∀ k blk, (mkSharedDecBlocks l.decProc x decLbl tmp
        ⟨doneLbl, match doneSlot with | some _ => [.imm 1] | none => []⟩)[k]? = some blk →
      F'.blocks[decLbl + k]? = some blk) :
    let inl := inlineProgram l raw
    let pFr0 : Lir.Frame := { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal }
    let expectEnv := match doneSlot with | some slot => env0.insert slot 1 | none => env0
    match evalDecSite xVal mem with
    | .ok mem' =>
      ∃ envD,
        Sem.Star (Lir.semStep inl)
          { mem, ctx, stack := { fn, label := decLbl, pos := 0, env := env0 } :: rest } 0
          { mem := mem', ctx, stack := { fn, label := doneLbl, pos := 0, env := envD } :: rest } ∧
        AgreeBelow bound expectEnv envD
    | .free =>
      ∃ env1,
        AgreeBelow bound env0 env1 ∧
        Sem.Star (Lir.semStep inl)
          { mem, ctx, stack := { fn, label := decLbl, pos := 0, env := env0 } :: rest } 1
          { mem, ctx, stack := pFr0 :: { fn, label := decLbl + 2, pos := 1, env := env1, dsts := [] } :: rest }
    | .stuck =>
      Sem.Reaches (Lir.semStep inl)
        { mem, ctx, stack := { fn, label := decLbl, pos := 0, env := env0 } :: rest } 0 .stuck := by
  intro inl pFr0 expectEnv
  let doneEdge : Lir.Edge := ⟨doneLbl, match (generalizing := false) doneSlot with | some _ => [.imm 1] | none => []⟩
  let bindDone : Lir.Env → Lir.Env := fun env' =>
    match (generalizing := false) doneSlot with | some slot => env'.insert slot 1 | none => env'
  have htakeDone : ∀ (m : X86.Memory) (cur : Lir.Label) (pos : Nat) (env' : Lir.Env), cur ≤ decLbl + 4 →
      Lir.takeEdge F' { mem := m, ctx, stack := { fn, label := cur, pos, env := env' } :: rest }
        { fn, label := cur, pos, env := env' } rest env' doneEdge =
        .next { mem := m, ctx, stack := { fn, label := doneLbl, pos := 0, env := bindDone env' } :: rest } false := by
    intro m cur pos env' hcur
    have hfwd : ¬ (doneLbl ≤ cur) := by dsimp only [Lir.Label] at hdoneGt hcur ⊢; omega
    cases doneSlot with
    | none =>
      simp [doneEdge, bindDone, Lir.takeEdge, Lir.evalArgs, hdoneBlk, hdoneParams, Lir.bindParams, hfwd]
    | some slot =>
      simp [doneEdge, bindDone, Lir.takeEdge, Lir.evalArgs, Lir.Arg.eval, hdoneBlk, hdoneParams, Lir.bindParams, hfwd]
  have hagDone : ∀ env', AgreeBelow bound env0 env' → AgreeBelow bound expectEnv (bindDone env') := by
    intro env' hag
    cases doneSlot with
    | none => exact hag
    | some slot => exact hag.insert_same slot 1
  have hb0 : F'.blocks[decLbl]? = some ({
      body := #[],
      term := .br .tnz .w64 (.v x) (.imm 1) doneEdge ⟨decLbl + 1, []⟩,
      cold := true } : Lir.Block) := by
    simpa [doneEdge] using hblks 0 _ rfl
  have hb1 : F'.blocks[decLbl + 1]? = some ({
      body := #[.assign tmp (.load .w32 .zero (cellAddr x 4))],
      term := .br .eq .w32 (.v tmp) (.imm 0) ⟨decLbl + 2, []⟩ ⟨decLbl + 3, []⟩,
      cold := true } : Lir.Block) :=
    hblks 1 _ rfl
  have hb2 : F'.blocks[decLbl + 2]? = some ({
      body := #[.call [] l.decProc [.v x]],
      term := .jump doneEdge,
      cold := true } : Lir.Block) :=
    hblks 2 _ rfl
  have hb3 : F'.blocks[decLbl + 3]? = some ({
      body := #[],
      term := .br .slt .w32 (.v tmp) (.imm 0) doneEdge ⟨decLbl + 4, []⟩,
      cold := true } : Lir.Block) :=
    hblks 3 _ rfl
  have hb4 : F'.blocks[decLbl + 4]? = some ({
      body := #[.assign (tmp + 1) (.bin .sub .w32 (.v tmp) (.imm 1)),
        .store .w32 (cellAddr x 4) (.v (tmp + 1))],
      term := .jump doneEdge,
      cold := true } : Lir.Block) :=
    hblks 4 _ rfl
  have hdecF : inl.funcs[l.decProc]? = some Rt.Rc.Gen.dec := inlineProgram_decProc l raw hr
  unfold evalDecSite
  by_cases htag : Lir.Cond.holds .tnz .w64 xVal 1 = true
  · simp only [htag, ↓reduceIte]
    have s0 : Lir.semStep inl { mem, ctx, stack := { fn, label := decLbl, pos := 0, env := env0 } :: rest } =
        .next { mem, ctx, stack := { fn, label := doneLbl, pos := 0, env := bindDone env0 } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn, label := decLbl, pos := 0, env := env0 }) hF' hb0 rfl]
      simp only [Lir.Arg.eval, hx, htag, ↓reduceIte]
      exact htakeDone mem decLbl 0 env0 (by dsimp only [Lir.Label]; omega)
    exact ⟨bindDone env0, .free s0 (.refl _), hagDone env0 AgreeBelow.refl⟩
  · have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by simpa using htag
    simp only [htagF, Bool.false_eq_true, ↓reduceIte]
    have s0 : Lir.semStep inl { mem, ctx, stack := { fn, label := decLbl, pos := 0, env := env0 } :: rest } =
        .next { mem, ctx, stack := { fn, label := decLbl + 1, pos := 0, env := env0 } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn, label := decLbl, pos := 0, env := env0 }) hF' hb0 rfl]
      have hfwd : ¬ (decLbl + 1 ≤ decLbl) := by dsimp only [Lir.Label]; omega
      simp [Lir.Arg.eval, hx, htagF, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams, hfwd]
    cases hlc : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none =>
      dsimp only
      refine .free s0 (.final ?_)
      have hst : Lir.step inl { mem, ctx, stack := { fn, label := decLbl + 1, pos := 0, env := env0 } :: rest } = .stuck := by
        unfold Lir.step
        simp [inl, hF', hb1, cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell env0 ctx x xVal 4 hx, hlc]
      rw [Lir.semStep, hst]; exact .stuck
    | some cnt =>
      dsimp only
      let env1 := env0.insert tmp cnt
      have hag1 : AgreeBelow bound env0 env1 := AgreeBelow.refl.insert_ge htmp cnt
      have hx1 : env1[x]? = some xVal := by rw [← hag1 x hxLt, hx]
      have s1 : Lir.semStep inl { mem, ctx, stack := { fn, label := decLbl + 1, pos := 0, env := env0 } :: rest } =
          .next { mem, ctx, stack := { fn, label := decLbl + 1, pos := 1, env := env1 } :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fn, label := decLbl + 1, pos := 0, env := env0 })
          hF' hb1 (by simp) rfl rfl
          (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell env0 ctx x xVal 4 hx, hlc, env1])
      by_cases hzero : (X86.Width.w32.truncate cnt).toNat = 0
      · simp only [hzero, ↓reduceIte]
        have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = true := by rw [w32_eq_zero]; simp [hzero]
        have s2 : Lir.semStep inl { mem, ctx, stack := { fn, label := decLbl + 1, pos := 1, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fn, label := decLbl + 2, pos := 0, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fn, label := decLbl + 1, pos := 1, env := env1 }) hF' hb1 rfl]
          have hfwd : ¬ (decLbl + 2 ≤ decLbl + 1) := by dsimp only [Lir.Label]; omega
          simp [Lir.Arg.eval, env1, heq0, Lir.takeEdge, Lir.evalArgs, hb2, Lir.bindParams, hfwd]
        have s3 : Lir.semStep inl { mem, ctx, stack := { fn, label := decLbl + 2, pos := 0, env := env1 } :: rest } =
            .next { mem, ctx, stack := pFr0 :: { fn, label := decLbl + 2, pos := 1, env := env1, dsts := [] } :: rest } true := by
          apply Lir.semStep_next.mpr
          exact Lir.step_call (fr := { fn, label := decLbl + 2, pos := 0, env := env1 })
            (vs := [xVal]) hF' hb2 (by simp) rfl
            (by simp [Lir.evalArgs, Lir.Arg.eval, hx1])
            (by simp [Lir.enter, hdecF, Rt.Rc.Gen.dec, Lir.bindParams, pFr0])
        exact ⟨env1, hag1, .free s0 (.free s1 (.free s2 (.charge s3 (.refl _))))⟩
      · simp only [hzero, ↓reduceIte]
        have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = false := by rw [w32_eq_zero]; simp [hzero]
        have s2 : Lir.semStep inl { mem, ctx, stack := { fn, label := decLbl + 1, pos := 1, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fn, label := decLbl + 3, pos := 0, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fn, label := decLbl + 1, pos := 1, env := env1 }) hF' hb1 rfl]
          have hfwd : ¬ (decLbl + 3 ≤ decLbl + 1) := by dsimp only [Lir.Label]; omega
          simp [Lir.Arg.eval, env1, heq0, Lir.takeEdge, Lir.evalArgs, hb3, Lir.bindParams, hfwd]
        by_cases hneg : 2 ^ 31 ≤ (X86.Width.w32.truncate cnt).toNat
        · simp only [hneg, ↓reduceIte]
          have hslt : Lir.Cond.holds .slt .w32 cnt 0 = true := by rw [w32_signedValue_lt_zero]; simp [hneg]
          have s3 : Lir.semStep inl { mem, ctx, stack := { fn, label := decLbl + 3, pos := 0, env := env1 } :: rest } =
              .next { mem, ctx, stack := { fn, label := doneLbl, pos := 0, env := bindDone env1 } :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn, label := decLbl + 3, pos := 0, env := env1 }) hF' hb3 rfl]
            simp only [Lir.Arg.eval, env1, Lir.env_insert_self, hslt, ↓reduceIte]
            exact htakeDone mem (decLbl + 3) 0 env1 (by dsimp only [Lir.Label]; omega)
          exact ⟨bindDone env1, .free s0 (.free s1 (.free s2 (.free s3 (.refl _)))), hagDone env1 hag1⟩
        · simp only [hneg, ↓reduceIte]
          have hslt : Lir.Cond.holds .slt .w32 cnt 0 = false := by rw [w32_signedValue_lt_zero]; simp [hneg]
          have s3 : Lir.semStep inl { mem, ctx, stack := { fn, label := decLbl + 3, pos := 0, env := env1 } :: rest } =
              .next { mem, ctx, stack := { fn, label := decLbl + 4, pos := 0, env := env1 } :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn, label := decLbl + 3, pos := 0, env := env1 }) hF' hb3 rfl]
            have hfwd : ¬ (decLbl + 4 ≤ decLbl + 3) := by dsimp only [Lir.Label]; omega
            simp [Lir.Arg.eval, env1, hslt, Lir.takeEdge, Lir.evalArgs, hb4, Lir.bindParams, hfwd]
          let env2 := env1.insert (tmp + 1) (X86.Width.w32.truncate (cnt - 1))
          have hag2 : AgreeBelow bound env0 env2 := hag1.insert_ge (by omega) _
          have hx2 : env2[x]? = some xVal := by rw [← hag2 x hxLt, hx]
          have s4 : Lir.semStep inl { mem, ctx, stack := { fn, label := decLbl + 4, pos := 0, env := env1 } :: rest } =
              .next { mem, ctx, stack := { fn, label := decLbl + 4, pos := 1, env := env2 } :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fn, label := decLbl + 4, pos := 0, env := env1 })
              hF' hb4 (by simp) rfl rfl
              (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.BinOp.eval, Lir.Arg.eval, env1, env2])
          cases hw : mem.write? .w32 (xVal + Lir.dispWord 4) (X86.Width.w32.truncate (cnt - 1)) with
          | error _ =>
            dsimp only
            refine .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.final ?_)))))
            have hst : Lir.step inl { mem, ctx, stack := { fn, label := decLbl + 4, pos := 1, env := env2 } :: rest } = .stuck := by
              unfold Lir.step
              simp [inl, hF', hb4, cellAddr, Lir.Stmt.exec, addr_cell env2 ctx x xVal 4 hx2, Lir.Arg.eval, env2, hw]
            rw [Lir.semStep, hst]; exact .stuck
          | ok mem' =>
            dsimp only
            have s5 : Lir.semStep inl { mem, ctx, stack := { fn, label := decLbl + 4, pos := 1, env := env2 } :: rest } =
                .next { mem := mem', ctx, stack := { fn, label := decLbl + 4, pos := 2, env := env2 } :: rest } false := by
              apply Lir.semStep_next.mpr
              exact Lir.step_stmt (fr := { fn, label := decLbl + 4, pos := 1, env := env2 })
                hF' hb4 (by simp) rfl rfl
                (by simp [cellAddr, Lir.Stmt.exec, addr_cell env2 ctx x xVal 4 hx2, Lir.Arg.eval, env2, hw])
            have s6 : Lir.semStep inl { mem := mem', ctx, stack := { fn, label := decLbl + 4, pos := 2, env := env2 } :: rest } =
                .next { mem := mem', ctx, stack := { fn, label := doneLbl, pos := 0, env := bindDone env2 } :: rest } false := by
              apply Lir.semStep_next.mpr
              rw [Lir.step_term (fr := { fn, label := decLbl + 4, pos := 2, env := env2 }) hF' hb4 rfl]
              exact htakeDone mem' (decLbl + 4) 2 env2 (by dsimp only [Lir.Label]; omega)
            exact ⟨bindDone env2, .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.refl _))))))), hagDone env2 hag2⟩

end IxCC.Cfg.Rc.Inline
