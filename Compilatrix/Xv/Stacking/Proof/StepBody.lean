import Compilatrix.Xv.Stacking.Proof.Machine

/-!
# Body instructions, step by step

Each Xl body instruction other than a call is matched by checked machine
steps of its stacked code, after which the invariant holds one instruction
on: a row (`step_op`, one step).
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream

theorem offsetOf_succ {l : FrameLayout} {label pos : Nat} {codes : List (List Instr)} {code : List Instr}
    (hc : codes[pos]? = some code) :
    offsetOf l label (pos + 1) codes = offsetOf l label pos codes + code.length := by
  simp only [offsetOf, List.take_succ, hc, Option.toList_some, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.length_append]
  omega

theorem machine_next {m : Machine} (hr : m.status = .running) {S : Stk} {pl : Placed} {label offset : Nat}
    {core : Core} :
    { m with core, pc := pcOf S pl label offset } =
      inFrame core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + label)) offset m.returns := by
  obtain ⟨core₀, pc, returns, status⟩ := m
  simp only at hr
  subst hr
  rfl

/-- Holes after a row: only fewer, and none on what it writes. -/
theorem nextHoles_op_sub {holes : Holes} {o : Op} {xs : List Arg} {core : Core} (x : Word)
    (h : nextHoles holes (.op o xs) core x) : holes x :=
  clearAccesses_sub _ _ x h

theorem nextHoles_op_clears {holes : Holes} {o : Op} {xs : List Arg} {core : Core} {acc : Access}
    (h : acc ∈ Op.writes o xs core) : ReadableData (nextHoles holes (.op o xs) core) acc.address acc.bytes :=
  clearAccesses_clears h

/-- A row: one checked step, after which the invariant holds one
instruction on. -/
theorem step_op {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    {o : Op} {defs : List Loc} {args : List (XArg Loc)} (hx : b.body[fr.pos]? = some (.op o defs args))
    {regs' : Xl.Regs} {fr'' : Xl.Frame} {mem' : Memory}
    (hexec : Xl.execInst s.regs fr s.mem s.ctx (.op o defs args) = some (regs', fr'', mem')) :
    ∃ holes' m', SafeSteps Runtime.rejecting S.cs 1 holes m holes' m' ∧
      Match S W { s with mem := mem', regs := regs', stack := { fr'' with pos := fr.pos + 1 } :: below.map (·.1) }
        m' holes' { fr'' with pos := fr.pos + 1 } a ret below := by
  simp only [Xl.execInst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hexec
  obtain ⟨bs, hbs, ⟨regs₁, fr₁, mem₁, fl⟩, hrun, he⟩ := hexec
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  rw [hm.ctx] at hrun
  -- The stacked code
  obtain ⟨code, hcode, hinst⟩ := hpos.insts fr.pos _ hx
  simp only [FnCtx.inst, FnCtx.bind, hbs, bind, Except.bind, pure, Except.pure] at hinst
  have key : ∃ xs, (ctxOf S.placed pl).rowArgs bs = .ok xs ∧ rowShape o bs xs false = true ∧
      code = [.op o xs] := by
    split at hinst
    · simp at hinst
    rename_i xs hxs
    split at hinst
    · rename_i hcond
      simp only [Except.ok.injEq] at hinst
      simp only [Bool.and_eq_true] at hcond
      exact ⟨xs, hxs, hcond.2, hinst.symm⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at hinst
  obtain ⟨xs, hxs, hshape, rfl⟩ := key
  -- Xl's uses are defined
  have huses : ∀ u ∈ bs.flatMap Bound.uses, ∃ v, Xl.read s.regs fr u = some v := by
    have h := hrun
    rw [Xl.execBound_eq] at h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, _, -, _, -, vs, hread, -⟩ := h
    exact readAll_some hread
  obtain ⟨core', hex, hafter, hfoot, -⟩ := op_sim hbs hxs hshape htop.agree hrun
  rw [(bindRow_regs hbs).2] at hafter
  obtain ⟨hseg, hfits⟩ := hpos.segment hcode
  have hsafe := hfoot.safe hm htop rfl fun u hu _ => huses u hu
  have hstep := hseg.safe_op (by simpa using hfits) Runtime.rejecting hsafe hex
  rw [← machine_at hm.running hpc] at hstep
  refine ⟨_, _, hstep, ?_⟩
  have hb := Match.body hm htop hpos hx (x := .op o defs args) hafter
    (fun y hy => nextHoles_op_sub y hy)
    (fun y hy hc mm hmm => by
      have := hfoot.defs y (by rw [(bindRow_regs hbs).2]; exact hy) hc mm hmm
      exact nextHoles_op_clears this)
  rwa [machine_next hm.running, offsetOf_succ hcode] at hb

/-- An instruction whose stacked code is one row: one checked step. -/
theorem step_row {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    {x : Inst Loc} (hx : b.body[fr.pos]? = some x) {o : Op} {xs : List Arg}
    (hcode : codes[fr.pos]? = some [.op o xs]) {core' : Core} {fl : ByteEval.Flags}
    (hex : o.exec xs m.core {} = .ok (core', fl)) {U D : List Loc}
    (hfoot : Foot (ctxOf S.placed pl) o xs s.mem m.core U D)
    (hU : ∀ u ∈ U, u.isCell = true → ∃ v, Xl.read s.regs fr u = some v)
    (hD : ∀ y ∈ x.defs, y.isCell = true → y ∈ D)
    {regs' : Xl.Regs} {fr'' : Xl.Frame} {mem' : Memory}
    (hafter : After (ctxOf S.placed pl) x.defs s.regs fr s.mem m.core regs' fr'' mem' W.ctx core') :
    ∃ holes' m', SafeSteps Runtime.rejecting S.cs 1 holes m holes' m' ∧
      Match S W { s with mem := mem', regs := regs', stack := { fr'' with pos := fr.pos + 1 } :: below.map (·.1) }
        m' holes' { fr'' with pos := fr.pos + 1 } a ret below := by
  obtain ⟨hseg, hfits⟩ := hpos.segment hcode
  have hsafe := hfoot.safe hm htop rfl hU
  have hstep := hseg.safe_op (by simpa using hfits) Runtime.rejecting hsafe hex
  rw [← machine_at hm.running hpc] at hstep
  refine ⟨_, _, hstep, ?_⟩
  have hb := Match.body hm htop hpos hx hafter (fun y hy => nextHoles_op_sub y hy)
    (fun y hy hc mm hmm => nextHoles_op_clears (hfoot.defs y (hD y hy hc) hc mm hmm))
  rwa [machine_next hm.running, offsetOf_succ hcode] at hb

/-- A move: no step (a location to itself) or one row. -/
theorem step_move {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    {dst src : Loc} (hx : b.body[fr.pos]? = some (.move dst src))
    {regs' : Xl.Regs} {fr'' : Xl.Frame} {mem' : Memory}
    (hexec : Xl.execInst s.regs fr s.mem s.ctx (.move dst src) = some (regs', fr'', mem')) :
    ∃ n holes' m', SafeSteps Runtime.rejecting S.cs n holes m holes' m' ∧
      Match S W { s with mem := mem', regs := regs', stack := { fr'' with pos := fr.pos + 1 } :: below.map (·.1) }
        m' holes' { fr'' with pos := fr.pos + 1 } a ret below := by
  simp only [Xl.execInst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hexec
  obtain ⟨v, hv, ⟨regs₁, fr₁⟩, hw, he⟩ := hexec
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨code, hcode, hinst⟩ := hpos.insts fr.pos _ hx
  simp only [FnCtx.inst] at hinst
  rcases move_sim hinst htop.agree hv hw with ⟨rfl, hafter⟩ | ⟨o, xs, core', fl, rfl, hex, -, hfoot, hafter⟩
  · refine ⟨0, holes, m, .refl _ _, ?_⟩
    have hds : dst = src := by
      rcases move_cases hinst with ⟨h, -⟩ | h | h | h
      · exact h
      all_goals (obtain ⟨_, _, _, _, _, _, h'⟩ := h; simp at h')
    subst hds
    have hb := Match.body hm htop hpos hx (x := .move dst dst) hafter (fun _ h => h) (fun y hy hc mm hmm => by
      simp only [Inst.defs, List.mem_singleton] at hy
      subst hy
      exact htop.cellsData _ hc v hv mm hmm)
    have hm' : { m with core := m.core, pc := pcOf S pl fr.label (offsetOf l fr.label (fr.pos + 1) codes) } = m := by
      rw [offsetOf_succ hcode, List.length_nil, Nat.add_zero, ← hpc]
    rwa [hm'] at hb
  · obtain ⟨holes', m', hstep, hmatch⟩ := step_row hm htop hpos hpc hx hcode hex hfoot
      (fun u hu _ => by simp at hu; subst hu; exact ⟨v, hv⟩) (fun y hy _ => hy) hafter
    exact ⟨1, holes', m', hstep, hmatch⟩

/-- A zeroing: one row. -/
theorem step_zero {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    {x : Loc} (hx : b.body[fr.pos]? = some (.zero x))
    {regs' : Xl.Regs} {fr'' : Xl.Frame} {mem' : Memory}
    (hexec : Xl.execInst s.regs fr s.mem s.ctx (.zero x) = some (regs', fr'', mem')) :
    ∃ holes' m', SafeSteps Runtime.rejecting S.cs 1 holes m holes' m' ∧
      Match S W { s with mem := mem', regs := regs', stack := { fr'' with pos := fr.pos + 1 } :: below.map (·.1) }
        m' holes' { fr'' with pos := fr.pos + 1 } a ret below := by
  cases x with
  | reg r =>
    obtain ⟨hr, e₁, e₂, e₃⟩ := zero_sim hexec
    subst regs' fr'' mem'
    obtain ⟨code, hcode, hinst⟩ := hpos.insts fr.pos _ hx
    simp only [FnCtx.inst, bind, Except.bind, pure, Except.pure] at hinst
    split at hinst
    · simp at hinst
    rename_i r' hg
    obtain ⟨-, e⟩ := gpr_ok hg
    subst r'
    simp only [Except.ok.injEq] at hinst
    subst hinst
    obtain ⟨fl, hex⟩ := zero_exec r m.core {}
    have hw : Xl.write s.regs fr (.reg r) 0 = some (s.regs.set r (some 0), fr) := by simp [Xl.write, hr]
    have hafter := after_reg htop.agree hw
    have hfoot : Foot (ctxOf S.placed pl) zeroRow [.reg r, .reg r] s.mem m.core [] [] :=
      ⟨(fun acc h => by rw [(zero_foot r m.core).1] at h; cases h),
        (fun acc h => by rw [(zero_foot r m.core).2] at h; cases h), (fun _ h => by cases h)⟩
    exact step_row hm htop hpos hpc hx (x := .zero (.reg r)) hcode hex hfoot (fun _ h => by cases h)
      (fun y hy hc => by simp only [Inst.defs, List.mem_singleton] at hy; subst hy; simp [Loc.isCell] at hc) hafter
  | _ => simp [Xl.execInst] at hexec

/-! ## Fused pairs -/

/-- The registers `zs` zeroed in turn. -/
def zeroAll (core : Core) : List GPR → Core
  | [] => core
  | r :: rs => zeroAll (core.setReg r 0) rs

theorem zeroAll_readReg : ∀ (core : Core) (zs : List GPR) (q : GPR),
    (zeroAll core zs).readReg q = if q ∈ zs then 0 else core.readReg q
  | core, [], q => by simp [zeroAll]
  | core, r :: rs, q => by
      rw [zeroAll, zeroAll_readReg]
      by_cases hq : q ∈ rs
      · simp [hq]
      · by_cases e : q = r
        · subst e; simp [hq, Validate.readReg_setReg]
        · simp [hq, e, Validate.readReg_setReg]

theorem zeroAll_memory : ∀ (core : Core) (zs : List GPR), (zeroAll core zs).memory = core.memory
  | _, [] => rfl
  | core, r :: rs => by rw [zeroAll, zeroAll_memory]; rfl

/-- The zeroing before a fused pair: one checked step per register, no
memory touched. -/
theorem zero_steps {cs : Checked} {block : BlockId} {returns : List ReturnFrame} {holes : Holes} :
    ∀ (zs : List GPR) {off : Nat} {core : Core}, Straight.Segment cs block off (zs.map zeroReg) →
      off + zs.length < UInt32.size →
      SafeSteps Runtime.rejecting cs zs.length holes (inFrame core block off returns) holes
        (inFrame (zeroAll core zs) block (off + zs.length) returns)
  | [], off, core, _, _ => by simpa [zeroAll] using SafeSteps.refl holes (inFrame core block off returns)
  | r :: rs, off, core, hseg, hfits => by
      have hseg' : Straight.Segment cs block off ([zeroReg r] ++ rs.map zeroReg) := by simpa using hseg
      obtain ⟨fl, hex⟩ := zero_exec r core {}
      obtain ⟨hsafe, hkeep⟩ := OperationSafe.of_noMemory (o := zeroRow) (args := [.reg r, .reg r]) (core := core)
        (holes := holes) (returns := returns)
        (zero_foot r core).1 (zero_foot r core).2
      have one := hseg'.left.safe_op (by simp at hfits; omega) Runtime.rejecting hsafe hex
      rw [hkeep] at one
      have rest := zero_steps (returns := returns) (holes := holes) rs (off := off + 1) (core := core.setReg r 0) (by simpa using hseg'.right)
        (by simp [UInt32.size] at hfits ⊢; omega)
      have := one.append rest
      simpa [zeroAll, Nat.add_assoc, Nat.add_comm 1] using this

theorem zeroes_regs {g : Loc → Except String Instr}
    (hg : ∀ l z, g l = .ok z → ∃ r, l = .reg r ∧ Xl.reserved r = false ∧ z = zeroReg r) :
    ∀ {L : List Loc} {zeroes : List Instr}, L.mapM g = .ok zeroes →
      ∃ zs : List GPR, L = zs.map Loc.reg ∧ zeroes = zs.map zeroReg ∧ ∀ r ∈ zs, Xl.reserved r = false
  | [], zeroes, h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨[], rfl, h.symm, by simp⟩
  | l :: L, zeroes, h => by
      rw [List.mapM_cons] at h
      obtain ⟨z, hz, h'⟩ := bind_ok.1 h
      obtain ⟨zs', hzs, h''⟩ := bind_ok.1 h'
      cases h''
      obtain ⟨r, rfl, hr, rfl⟩ := hg l z hz
      obtain ⟨zs, rfl, rfl, hzs'⟩ := zeroes_regs hg hzs
      refine ⟨r :: zs, rfl, rfl, fun q hq => ?_⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hr
      · exact hzs' q hq

/-- A fused pair: one step per zeroed register, then the pair. -/
theorem step_fused {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    {p q : Op} {pargs cargs : List (XArg Loc)} {defs : List Loc}
    (hx : b.body[fr.pos]? = some (.fused p pargs q defs cargs))
    {regs' : Xl.Regs} {fr'' : Xl.Frame} {mem' : Memory}
    (hexec : Xl.execInst s.regs fr s.mem s.ctx (.fused p pargs q defs cargs) = some (regs', fr'', mem')) :
    ∃ n holes' m', SafeSteps Runtime.rejecting S.cs n holes m holes' m' ∧
      Match S W { s with mem := mem', regs := regs', stack := { fr'' with pos := fr.pos + 1 } :: below.map (·.1) }
        m' holes' { fr'' with pos := fr.pos + 1 } a ret below := by
  simp only [Xl.execInst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hexec
  obtain ⟨pb, hpb, qb, hqb, ⟨regs₁, fr₁, mem₁, fl⟩, hrun, he⟩ := hexec
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  rw [hm.ctx] at hrun
  obtain ⟨code, hcode, hinst⟩ := hpos.insts fr.pos _ hx
  simp only [FnCtx.inst, FnCtx.bind, hpb, hqb, bind, Except.bind, pure, Except.pure] at hinst
  have key : ∃ (pxs qxs : List Arg) (zs : List GPR), (ctxOf S.placed pl).rowArgs pb = .ok pxs ∧ (ctxOf S.placed pl).rowArgs qb = .ok qxs ∧
      rowShape p pb pxs false = true ∧ rowShape q qb qxs true = true ∧
      (qb.filter Bound.narrowOutput).flatMap Bound.defs = zs.map Loc.reg ∧ (∀ r ∈ zs, Xl.reserved r = false) ∧
      code = zs.map zeroReg ++ [.fused p pxs q qxs] := by
    split at hinst
    · simp at hinst
    rename_i pxs hpxs
    split at hinst
    · simp at hinst
    rename_i qxs hqxs
    split at hinst
    · rename_i hcond
      split at hinst
      · simp at hinst
      rename_i zeroes hzeroes
      simp only [Except.ok.injEq] at hinst
      have hz := zeroes_regs ?_ hzeroes
      · obtain ⟨zs, hzs, rfl, hzr⟩ := hz
        simp only [Bool.and_eq_true] at hcond
        exact ⟨pxs, qxs, zs, hpxs, hqxs, hcond.1.2, hcond.2, hzs, hzr, hinst.symm⟩
      · intro l z hz
        try simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hz
        split at hz
        · simp at hz
        · split at hz
          · simp at hz
          · rename_i r hg
            simp only [Except.ok.injEq] at hz
            cases l with
            | reg r' =>
              obtain ⟨hres, e⟩ := gpr_ok hg
              subst e
              exact ⟨_, rfl, hres, hz.symm⟩
            | _ => simp [gpr, throw, throwThe, MonadExceptOf.throw] at hg
    · simp [throw, throwThe, MonadExceptOf.throw] at hinst
  obtain ⟨pxs, qxs, zs, hpx, hqx, hps, hqs, hzs, hzr, rfl⟩ := key
  have hzsp : GPR.rsp ∉ zs := fun h => by have := hzr _ h; simp [Xl.reserved] at this
  -- Xl's uses are defined
  have huses : ∀ u ∈ (pb ++ qb).flatMap Bound.uses, ∃ v, Xl.read s.regs fr u = some v := by
    have h := hrun
    rw [Xl.execBound_eq] at h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, _, -, _, -, vs, hread, -⟩ := h
    exact readAll_some hread
  have hz₁ : ∀ r ∈ zs, (zeroAll m.core zs).readReg r = 0 := fun r hr => by simp [zeroAll_readReg, hr]
  have hz₂ : ∀ r, r ∉ zs → (zeroAll m.core zs).readReg r = m.core.readReg r := fun r hr => by
    simp [zeroAll_readReg, hr]
  obtain ⟨core₁, fl₁, core', hp, hq, hafter, footP, footQ, -, -⟩ :=
    fused_sim hpb hqb hpx hqx hps hqs hzs htop.agree hz₁ hz₂ (zeroAll_memory _ _) hrun
  rw [(bindRow_regs hqb).2] at hafter
  have hcz : (zeroAll m.core zs).readReg .rsp = m.core.readReg .rsp := hz₂ _ hzsp
  have hpsafe := footP.safe hm htop hcz fun u hu _ => huses u (by rw [List.flatMap_append]; exact List.mem_append_left _ hu)
  have hqsafe := footQ.safe hm htop hcz fun u hu _ => huses u (by rw [List.flatMap_append]; exact List.mem_append_right _ hu)
  obtain ⟨hseg, hfits⟩ := hpos.segment hcode
  have hzero := zero_steps (returns := m.returns) (holes := holes) zs (core := m.core) hseg.left
    (by simp [UInt32.size] at hfits ⊢; omega)
  have hfused := hseg.right.safe_fused (by simp [UInt32.size] at hfits ⊢; omega) Runtime.rejecting hpsafe hqsafe hp hq
  rw [List.length_map] at hfused
  have hsteps := hzero.append hfused
  rw [← machine_at hm.running hpc] at hsteps
  refine ⟨_, _, _, hsteps, ?_⟩
  have hb := Match.body hm htop hpos hx (x := .fused p pargs q defs cargs) hafter (fun y hy => nextHoles_op_sub y hy)
    (fun y hy hc mm hmm => by
      have := footQ.defs y (by rw [(bindRow_regs hqb).2]; exact hy) hc mm hmm
      have hcl := nextHoles_op_clears (holes := holes) this
      rwa [cell_rsp hmm hcz] at hcl)
  rw [machine_next hm.running, offsetOf_succ hcode] at hb
  simpa [Nat.add_assoc] using hb

end Compilatrix.Xv.Stacking.Proof
