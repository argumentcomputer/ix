import IxCC.Xv.Validate.Proof.Steps

/-!
# The simulation relation

`Match s t`: an Xv state and an Xl state at the same label and
instruction (the Xl position is the one before the edits of that
instruction), with the same memory and context word, the validator's state
at that point agreeing with the Xv environment and the Xl locations
(`RunMatch`), and each suspended caller matching at its call's return
point, whatever values come back (`RetMatch`, CompCert's `return_regs`
discipline). -/

namespace IxCC.Xv.Validate

open IxCC.Lir (VReg Word Env Label FunId)
open IxCC.Xv.Alloc (Edit Output BlockOut)
open IxCC.Xv

section Match

variable (env : Xl.Env) (p : VProgram) (outs : List Output) (q : LProgram)

/-- A running Xv frame and its Xl image under the registers `regs`. -/
def RunMatch (fr : Lir.Frame) (fl : Xl.Frame) (regs : Xl.Regs) : Prop :=
  fl.fn = fr.fn ∧ fl.label = fr.label ∧
  ∃ f o g b bo bl a,
    p.funcs[fr.fn]? = some f ∧ outs[fr.fn]? = some o ∧ q.funcs[fr.fn]? = some g ∧
    func env fr.fn f o = .ok () ∧ Alloc.apply f o = .ok g ∧
    f.blocks[fr.label]? = some b ∧ o.blocks[fr.label]? = some bo ∧ g.blocks[fr.label]? = some bl ∧
    BlockRest (funcCtx env f o) (funcInfo f o) b bo bl fr.pos fl.pos a ∧
    a.Agree fr.env (Xl.read regs fl) ∧ fl.inArgs.size = (funcCtx env f o).stackParams

/-- A suspended Xv caller and its Xl image: whatever values the callee
returns, the resumed frames match. -/
def RetMatch (cf : Lir.Frame) (cl : Xl.Frame) : Prop :=
  cl.results = cf.dsts.length ∧ cl.saved.size = 16 ∧
  ∀ vals ρ', Lir.bindParams cf.env cf.dsts vals = some ρ' →
    RunMatch env p outs q { cf with env := ρ', dsts := [] }
      { cl with saved := Xl.Regs.empty, clobber := [], results := 0 }
      (Xl.returnRegs cl.saved cl.clobber vals)

/-- The suspended callers, frame by frame. -/
def StackMatch : List Lir.Frame → List Xl.Frame → Prop
  | [], [] => True
  | cf :: cs, cl :: ls => RetMatch env p outs q cf cl ∧ StackMatch cs ls
  | _, _ => False

/-- The simulation relation between Xv and Xl states. -/
def Match (s : Lir.State) (t : Xl.State) : Prop :=
  s.mem = t.mem ∧ s.ctx = t.ctx ∧ t.regs.size = 16 ∧
  ∃ fr rest fl rest', s.stack = fr :: rest ∧ t.stack = fl :: rest' ∧
    RunMatch env p outs q fr fl t.regs ∧ StackMatch env p outs q rest rest'

end Match

/-! ## Entering a function -/

theorem func_block0 {env : Xl.Env} {f : Func VReg} {o : Output} (hf : FuncOk env f o) :
    ∃ b0 o0, f.blocks[0]? = some b0 ∧ o.blocks[0]? = some o0 ∧
      (AState.ofList o0.cert).le (entryState f.params) = true := by
  obtain ⟨o0, rest, ho, hle⟩ := hf.entry
  have hsz : 0 < f.blocks.size := by rw [hf.len, ho]; simp
  exact ⟨f.blocks[0], o0, by simp [hsz], by simp [ho], hle⟩

/-- A call's callee: Xl enters it too, and the frames match. -/
theorem callee_match {env : Xl.Env} {p : VProgram} {outs : List Output} {q : LProgram}
    (hacc : Accepted env p outs q) {g : FunId} {vals : List Word} {fr : Lir.Frame}
    (he : Xv.enter p g vals = some fr) :
    ∃ fl, Xl.enter q g vals = some (fl, Xl.entryRegs vals) ∧
      RunMatch env p outs q fr fl (Xl.entryRegs vals) := by
  simp only [Xv.enter, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
  obtain ⟨f, hf, ρ, hρ, he⟩ := he
  simp only [Option.some.injEq] at he
  subst he
  obtain ⟨o, gl, ho, hg, hv, happ⟩ := hacc.funcs g f hf
  have hfo := func_ok hv
  have hap := apply_ok happ
  have hlen := bindParams_length hρ
  obtain ⟨b0, o0, hb0, ho0, hle⟩ := func_block0 hfo
  obtain ⟨bl0, hbl0, hab0⟩ := hap.blocks 0 b0 o0 hb0 ho0
  refine ⟨{ fn := g, label := 0, pos := 0, inArgs := (vals.drop Xl.nArgRegs).toArray }, ?_, rfl, rfl,
    f, o, gl, b0, o0, bl0, AState.ofList o0.cert, hf, ho, hg, hv, happ, hb0, ho0,
    hbl0, BlockRest.start (hfo.blocks 0 b0 o0 hb0 ho0) hab0,
    AState.Agree.antitone hle (entry_agree hfo.params hρ), ?_⟩
  · simp [Xl.enter, hg, hap.params, hlen, guard]
  · simp [funcCtx, hlen]

end IxCC.Xv.Validate
