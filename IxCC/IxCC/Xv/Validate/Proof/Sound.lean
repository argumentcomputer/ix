import IxCC.Xv.Validate.Proof.Frames
import IxCC.Xv.Validate.Proof.Diagram

/-!
# Each Xv step is simulated

`Validate.sound`: from matching states, each Xv step is matched by
Xl steps (the edits before the instruction as silent moves, then its image)
spending the same charges, and each final Xv step other than a stuck one by
the same final Xl step. `Validate.diagram` packs both as a `LockStep`. -/

namespace IxCC.Xv.Validate

open IxCC.Lir (VReg Word Env Label FunId)
open IxCC.Xv.Alloc (Edit Output BlockOut)
open IxCC.Xv

variable {env : Xl.Env} {p : VProgram} {outs : List Output} {q : LProgram}

/-! ## Instructions -/

/-- A non-call instruction, with its edits. -/
theorem inst_case {t : Xl.State} {fr : Lir.Frame} {fl : Xl.Frame} {rest' : List Xl.Frame}
    (hts : t.stack = fl :: rest') (hsize : t.regs.size = 16)
    {f : Func VReg} {o : Output} {g : Func Loc} {b : Block VReg} {bo : BlockOut} {bl : Block Loc}
    {a : AState} (hr : Running env p outs q fr fl t.regs f o g b bo bl a)
    {inst : Inst VReg} {insts : List (Inst VReg)} (hd : b.body.toList.drop fr.pos = inst :: insts)
    (hnc : ∀ g a r, inst ≠ .call g a r) {ρ : Env} {mem : X86.Memory}
    (hx : inst.exec fr.env t.mem t.ctx = some (ρ, mem)) :
    ∃ t', Sem.Star (Xl.step q env) t 0 t' ∧ t'.mem = mem ∧ t'.ctx = t.ctx ∧ t'.regs.size = 16 ∧
      ∃ fl', t'.stack = fl' :: rest' ∧
        RunMatch env p outs q { fr with pos := fr.pos + 1, env := ρ } fl' t'.regs := by
  obtain ⟨ls, now, x, a₁, a₂, hdl, he, hsi, hsub, hrest'⟩ := hr.rest.inst hd
  have hg' : q.funcs[fl.fn]? = some g := by rw [hr.fn]; exact hr.hg
  have hbl' : g.blocks[fl.label]? = some bl := by rw [hr.label]; exact hr.hbl
  obtain ⟨regs₁, fl₁, hstar, hpos₁, hfn₁, hlab₁, hin₁, hag₁, hs₁, hd₁⟩ :=
    xl_edits q env hts hg' hbl' hdl he hr.agree hsize hr.inArgs
  obtain ⟨hxnc, regs', fl', hxl, hs', hctl, hag'⟩ :=
    inst_sound hnc hsi hsub hag₁ hs₁ (by rw [hin₁]; exact hr.inArgs) hx
  have hstep := xl_step_inst q env (t := { t with regs := regs₁, stack := fl₁ :: rest' }) rfl
    (by rw [hfn₁]; exact hg') (by rw [hlab₁]; exact hbl') hd₁ hxnc hxl
  refine ⟨_, star_zero_step hstar hstep, rfl, rfl, hs', _, rfl, ?_⟩
  refine ⟨by rw [hctl.fn, hfn₁, hr.fn], by rw [hctl.label, hlab₁, hr.label], f, o, g, b, bo, bl, a₂,
    hr.hf, hr.ho, hr.hg, hr.hfunc, hr.happ, hr.hb, hr.hbo, hr.hbl, ?_, ?_, ?_⟩
  · show BlockRest _ _ b bo bl (fr.pos + 1) (fl₁.pos + 1) a₂
    rw [hpos₁]
    exact hrest'
  · simp only
    rw [read_pos]
    exact hag'
  · show fl'.inArgs.size = _
    rw [hctl.inArgs, hin₁]
    exact hr.inArgs

/-- A call, with its edits: Xl calls the same function on the same
arguments, and the caller matches at the return point whatever comes
back. -/
theorem call_case (hacc : Accepted env p outs q) {t : Xl.State} {fr : Lir.Frame} {fl : Xl.Frame}
    {rest' : List Xl.Frame} (hts : t.stack = fl :: rest') (hsize : t.regs.size = 16)
    {f : Func VReg} {o : Output} {g : Func Loc} {b : Block VReg} {bo : BlockOut} {bl : Block Loc}
    {a : AState} (hr : Running env p outs q fr fl t.regs f o g b bo bl a)
    {g' : FunId} {args rets : List VReg} {insts : List (Inst VReg)}
    (hd : b.body.toList.drop fr.pos = .call g' args rets :: insts)
    {vals : List Word} {callee : Lir.Frame} (hvals : Xv.readAll fr.env args = some vals)
    (hcallee : Xv.enter p g' vals = some callee) :
    ∃ t', Sem.Star (Xl.step q env) t 1 t' ∧ t'.mem = t.mem ∧ t'.ctx = t.ctx ∧
      t'.regs.size = 16 ∧ ∃ cl fl', t'.stack = cl :: fl' :: rest' ∧
        RunMatch env p outs q callee cl t'.regs ∧
        RetMatch env p outs q { fr with pos := fr.pos + 1, dsts := rets } fl' := by
  obtain ⟨ls, now, x, a₁, a₂, hdl, he, hsi, hsub, hrest'⟩ := hr.rest.inst hd
  have hg' : q.funcs[fl.fn]? = some g := by rw [hr.fn]; exact hr.hg
  have hbl' : g.blocks[fl.label]? = some bl := by rw [hr.label]; exact hr.hbl
  obtain ⟨regs₁, fl₁, hstar, hpos₁, hfn₁, hlab₁, hin₁, hag₁, hs₁, hd₁⟩ :=
    xl_edits q env hts hg' hbl' hdl he hr.agree hsize hr.inArgs
  obtain ⟨hlen, hk, hnd, htake, hdrop, hholds, ha₂⟩ := call_check hsi
  have hx := call_substitute hsub
  rw [htake, hdrop] at hx
  subst hx
  have hread : Xl.readAll regs₁ fl₁ (argLocs args.length) = some vals :=
    readAll_of_holds hag₁ (argLocs_length _).symm hholds hvals
  obtain ⟨cl, hent, hcm⟩ := callee_match hacc hcallee
  have hstep := xl_step_call q env (t := { t with regs := regs₁, stack := fl₁ :: rest' }) rfl
    (by rw [hfn₁]; exact hg') (by rw [hlab₁]; exact hbl') hd₁ (conventionArgs_argLocs _)
    (conventionResults_resultLocs hk) hread hent
  refine ⟨_, star_zero_step hstar hstep, rfl, rfl, entryRegs_size vals, cl, _, rfl,
    hcm, ?_, hs₁, ?_⟩
  · exact resultLocs_length hk
  · intro vals' ρ' hb
    refine ⟨by show fl₁.fn = fr.fn; rw [hfn₁, hr.fn], by show fl₁.label = fr.label; rw [hlab₁, hr.label],
      f, o, g, b, bo, bl, a₂, hr.hf, hr.ho, hr.hg, hr.hfunc, hr.happ, hr.hb, hr.hbo, hr.hbl, ?_, ?_, ?_⟩
    · show BlockRest _ _ b bo bl (fr.pos + 1) (fl₁.pos + 1) a₂
      rw [hpos₁]
      exact hrest'
    · rw [ha₂]
      exact call_agree hag₁ hs₁ hk hnd hb _ rfl rfl rfl
    · show fl₁.inArgs.size = _
      rw [hin₁]
      exact hr.inArgs

/-! ## Terminators -/

/-- A terminator step, with the edits before it. -/
theorem term_next (hacc : Accepted env p outs q) {s s' : Lir.State} {t : Xl.State} {c : Bool}
    {fr : Lir.Frame} {rest : List Lir.Frame} {fl : Xl.Frame} {rest' : List Xl.Frame}
    (hmem : s.mem = t.mem) (hctx : s.ctx = t.ctx) (hsize : t.regs.size = 16)
    (hss : s.stack = fr :: rest) (hts : t.stack = fl :: rest')
    (hstack : StackMatch env p outs q rest rest')
    {f : Func VReg} {o : Output} {g : Func Loc} {b : Block VReg} {bo : BlockOut} {bl : Block Loc}
    {a : AState} (hr : Running env p outs q fr fl t.regs f o g b bo bl a)
    (hpos : ¬ fr.pos < b.body.size) (hs : Xv.step p s = .next s' c) :
    ∃ t', Sem.Star (Xl.step q env) t c.toNat t' ∧ Match env p outs q s' t' := by
  obtain ⟨now, a₁, a₂, hdl, he, ht, hce⟩ := hr.rest.atTerm (by omega)
  have hg' : q.funcs[fl.fn]? = some g := by rw [hr.fn]; exact hr.hg
  have hbl' : g.blocks[fl.label]? = some bl := by rw [hr.label]; exact hr.hbl
  obtain ⟨regs₁, fl₁, hstar, hpos₁, hfn₁, hlab₁, hin₁, hag₁, hs₁, hd₁⟩ :=
    xl_edits q env (more := []) hts hg' hbl' (by rw [hdl, List.append_nil]) he hr.agree hsize hr.inArgs
  have hsubT := hr.rest.term
  have hgf : q.funcs[fl₁.fn]? = some g := by rw [hfn₁]; exact hg'
  have hblf : g.blocks[fl₁.label]? = some bl := by rw [hlab₁]; exact hbl'
  have hfn' : fl₁.fn = fr.fn := by rw [hfn₁, hr.fn]
  have hlab' : fl₁.label = fr.label := by rw [hlab₁, hr.label]
  have hin' : fl₁.inArgs.size = (funcCtx env f o).stackParams := by rw [hin₁]; exact hr.inArgs
  unfold Xv.step at hs
  rw [hss] at hs
  simp only [hr.hf, hr.hb, hpos, ↓reduceDIte] at hs
  cases hT : b.term with
  | jmp e =>
    simp only [hT] at hs
    rw [hT] at hsubT ht hce
    have hblT := jmp_substitute hsubT
    have ha := jmp_check ht
    subst ha
    obtain ⟨hxl, fr', rfl, hrun'⟩ := edge_sound hag₁ hce (by simp [Term.edges]) hs hr.hf hr.ho hr.hg
      hr.hfunc hr.happ hfn' hlab' hin' { t with regs := regs₁, stack := fl₁ :: rest' } rest'
    have hstep := (xl_step_jmp q env (t := { t with regs := regs₁, stack := fl₁ :: rest' }) rfl hgf hblf
      hd₁ hblT).trans hxl
    exact ⟨_, star_zero_step hstar hstep, hmem, hctx, hs₁, _, _, _, _, rfl, rfl,
      hrun', hstack⟩
  | jcc p' pargs defs cond e₁ e₂ =>
    simp only [hT] at hs
    rw [hT] at hsubT ht hce
    obtain ⟨pargs', defs', hblT, hsubI⟩ := jcc_substitute (by simpa [Term.edges] using hsubT)
    cases hj : execJcc p' pargs defs cond fr.env s.mem s.ctx with
    | none => simp [hj] at hs
    | some r =>
      obtain ⟨ρ, mem', taken⟩ := r
      simp only [hj] at hs
      rw [hmem, hctx] at hj
      obtain ⟨bs', hbr, regs', fr', flags, hex, htk, hs', hctl, hag'⟩ :=
        jcc_sound ht hsubI hag₁ hs₁ hin' hj
      have hstep := xl_step_jcc q env (t := { t with regs := regs₁, stack := fl₁ :: rest' }) rfl hgf hblf
        hd₁ hblT hbr hex htk
      obtain ⟨hxl, fr'', rfl, hrun'⟩ := edge_sound hag' hce (e := if taken then e₁ else e₂)
        (by cases taken <;> simp [Term.edges]) hs hr.hf hr.ho hr.hg hr.hfunc hr.happ
        (by rw [hctl.fn, hfn']) (by rw [hctl.label, hlab']) (by rw [hctl.inArgs, hin'])
        { t with regs := regs₁, stack := fl₁ :: rest', mem := mem' } rest'
      have hedge : (if taken then (⟨e₁.target, []⟩ : Edge Loc) else ⟨e₂.target, []⟩) =
          ⟨(if taken then e₁ else e₂).target, []⟩ := by cases taken <;> rfl
      rw [hedge, hxl] at hstep
      exact ⟨_, star_zero_step hstar hstep, rfl, hctx, hs', _, _, _, _, rfl, rfl,
        hrun', hstack⟩
  | ret vs =>
    simp only [hT] at hs
    rw [hT] at hsubT ht
    have hblT := ret_substitute hsubT
    obtain ⟨hk, hls, hholds, -⟩ := ret_check ht
    rw [hls] at hblT hholds
    cases hv : Xv.readAll fr.env vs with
    | none => simp [hv] at hs
    | some vals =>
      simp only [hv] at hs
      have hread : Xl.readAll regs₁ fl₁ (resultLocs vs.length) = some vals :=
        readAll_of_holds hag₁ (resultLocs_length hk).symm hholds hv
      cases rest with
      | nil => simp at hs
      | cons caller rest₂ =>
        simp only at hs
        cases hb : Lir.bindParams caller.env caller.dsts vals with
        | none => simp [hb] at hs
        | some ρ =>
          simp only [hb, Sem.Step.next.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          cases rest' with
          | nil => simp [StackMatch] at hstack
          | cons cl rest₃ =>
            obtain ⟨⟨hres, hsaved, hret⟩, hstack'⟩ := hstack
            have hstep := xl_step_ret q env (t := { t with regs := regs₁, stack := fl₁ :: cl :: rest₃ }) rfl
              hgf hblf hd₁ hblT (conventionResults_resultLocs hk) hread
              (by rw [hres, bindParams_length hb])
            exact ⟨_, star_zero_step hstar hstep, hmem, hctx,
              returnRegs_size hsaved _ _, _, _, _, _, rfl, rfl, hret vals ρ hb, hstack'⟩
  | tail g' args =>
    simp only [hT] at hs
    rw [hT] at hsubT ht
    have hblT := tail_substitute hsubT
    obtain ⟨hk, hls, hholds, -⟩ := tail_check ht
    rw [hls] at hblT hholds
    cases hv : Xv.readAll fr.env args with
    | none => simp [hv] at hs
    | some vals =>
      cases hen : Xv.enter p g' vals with
      | none => simp [hv, hen] at hs
      | some callee =>
        simp only [hv, hen, Option.bind_eq_bind, Option.bind_some, Sem.Step.next.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have hread : Xl.readAll regs₁ fl₁ (argLocs args.length) = some vals :=
          readAll_of_holds hag₁ (argLocs_length _).symm hholds hv
        obtain ⟨cl, hent, hcm⟩ := callee_match hacc hen
        have hstep := xl_step_tail q env (t := { t with regs := regs₁, stack := fl₁ :: rest' }) rfl hgf hblf
          hd₁ hblT (by rw [argLocs_length]; exact hk) (conventionArgs_argLocs _) hread hent
        exact ⟨_, star_zero_step hstar hstep, hmem, hctx, entryRegs_size vals,
          _, _, _, _, rfl, rfl, hcm, hstack⟩
  | fail failure => simp [hT] at hs
  | trap => simp [hT] at hs

/-! ## Steps -/

theorem drop_getElem_cons {α : Type} {arr : Array α} {i : Nat} (h : i < arr.size) :
    arr.toList.drop i = arr[i] :: arr.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

/-- Per-step simulation: matching states stay matched through each
Xv step, the Xl steps (edits, then the image) spending exactly its charge. -/
theorem sound (hacc : Accepted env p outs q) {s s' : Lir.State} {t : Xl.State} {c : Bool}
    (hm : Match env p outs q s t) (hs : Xv.step p s = .next s' c) :
    ∃ t', Sem.Star (Xl.step q env) t c.toNat t' ∧ Match env p outs q s' t' := by
  obtain ⟨hmem, hctx, hsize, fr, rest, fl, rest', hss, hts, hrun, hstack⟩ := hm
  obtain ⟨f, o, g, b, bo, bl, a, hr⟩ := hrun.running
  by_cases hpos : fr.pos < b.body.size
  · have hd := drop_getElem_cons hpos
    unfold Xv.step at hs
    rw [hss] at hs
    simp only [hr.hf, hr.hb, hpos, ↓reduceDIte] at hs
    split at hs
    · rename_i g' args rets heq
      rw [heq] at hd
      cases hc : (Xv.readAll fr.env args >>= Xv.enter p g') with
      | none => simp [hc] at hs
      | some callee =>
        simp only [hc, Sem.Step.next.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hc
        obtain ⟨vals, hv, hen⟩ := hc
        obtain ⟨t', hstar, hmem', hctx', hs', cl, fl', hts', hcm, hret⟩ :=
          call_case hacc hts hsize hr hd hv hen
        exact ⟨t', hstar, by rw [hmem']; exact hmem, by rw [hctx']; exact hctx, hs',
          callee, _, cl, _, rfl, hts', hcm, hret, hstack⟩
    · rename_i hnc
      cases hx : b.body[fr.pos].exec fr.env s.mem s.ctx with
      | none => simp [hx] at hs
      | some r =>
        obtain ⟨ρ, mem⟩ := r
        simp only [hx, Sem.Step.next.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        rw [hmem, hctx] at hx
        obtain ⟨t', hstar, hmem', hctx', hs', fl', hts', hrun'⟩ :=
          inst_case hts hsize hr hd (fun g a r e => hnc g a r e) hx
        exact ⟨t', hstar, hmem'.symm, by rw [hctx']; exact hctx, hs', _, _, _, _, rfl, hts',
          hrun', hstack⟩
  · exact term_next hacc hmem hctx hsize hss hts hstack hr hpos hs

/-- Each final Xv step other than a stuck one is matched by the same final
Xl step, after the edits before the terminator. -/
theorem sound_final {s : Lir.State} {t : Xl.State}
    {r : Sem.Result (List Word × X86.Memory)} (hm : Match env p outs q s t)
    (hf : Sem.Final (Xv.step p s) r) (hr : r ≠ .stuck) :
    ∃ t', Sem.Star (Xl.step q env) t 0 t' ∧ Sem.Final (Xl.step q env t') r := by
  obtain ⟨hmem, -, hsize, fr, rest, fl, rest', hss, hts, hrun, hstack⟩ := hm
  obtain ⟨f, o, g, b, bo, bl, a, hru⟩ := hrun.running
  obtain ⟨hpos, hcase⟩ := xv_step_final hss hru.hf hru.hb hf hr
  obtain ⟨now, a₁, a₂, hdl, he, ht, -⟩ := hru.rest.atTerm (by omega)
  have hg' : q.funcs[fl.fn]? = some g := by rw [hru.fn]; exact hru.hg
  have hbl' : g.blocks[fl.label]? = some bl := by rw [hru.label]; exact hru.hbl
  obtain ⟨regs₁, fl₁, hstar, -, hfn₁, hlab₁, -, hag₁, -, hd₁⟩ :=
    xl_edits q env (more := []) hts hg' hbl' (by rw [hdl, List.append_nil]) he hru.agree hsize hru.inArgs
  have hsubT := hru.rest.term
  have hgf : q.funcs[fl₁.fn]? = some g := by rw [hfn₁]; exact hg'
  have hblf : g.blocks[fl₁.label]? = some bl := by rw [hlab₁]; exact hbl'
  rcases hcase with ⟨vs, vals, hT, hv, rfl, rfl⟩ | ⟨failure, hT, rfl⟩ | ⟨hT, rfl⟩
  · rw [hT] at hsubT ht
    have hblT := ret_substitute hsubT
    obtain ⟨hk, hls, hholds, -⟩ := ret_check ht
    rw [hls] at hblT hholds
    have hread : Xl.readAll regs₁ fl₁ (resultLocs vs.length) = some vals :=
      readAll_of_holds hag₁ (resultLocs_length hk).symm hholds hv
    cases rest' with
    | cons => simp [StackMatch] at hstack
    | nil =>
      have hstep := xl_step_ret_done q env (t := { t with regs := regs₁, stack := [fl₁] }) rfl hgf hblf hd₁
        hblT (conventionResults_resultLocs hk) hread
      refine ⟨_, hstar, ?_⟩
      rw [hstep, hmem]
      exact .done
  · rw [hT] at hsubT
    have hstep := xl_step_fail q env (t := { t with regs := regs₁, stack := fl₁ :: rest' }) rfl hgf hblf hd₁
      (fail_substitute hsubT)
    refine ⟨_, hstar, ?_⟩
    rw [hstep]
    exact .fail
  · rw [hT] at hsubT
    have hstep := xl_step_trap q env (t := { t with regs := regs₁, stack := fl₁ :: rest' }) rfl hgf hblf hd₁
      (trap_substitute hsubT)
    refine ⟨_, hstar, ?_⟩
    rw [hstep]
    exact .trap

/-- The validator's simulation diagram between Xv and Xl. -/
theorem diagram (hacc : Accepted env p outs q) :
    LockStep (Xv.step p) (Xl.step q env) (Match env p outs q) where
  next hm hs := sound hacc hm hs
  final hm hf hr := sound_final hm hf hr

end IxCC.Xv.Validate
