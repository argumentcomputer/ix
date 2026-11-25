import IxCC.Lir.Opt.Driver
import IxCC.Lir.Proof.Opt.Seg
import IxCC.Lir.Proof.Opt.Inline
import IxCC.Lir.Proof.Opt.Unroll
import IxCC.Lir.Proof.Opt.IfConv
import IxCC.Lir.Proof.Run
import IxCC.Sem.Forward
import IxCC.Sem.Simulation

/-!
# End-to-end simulation and refinement soundness for `Lir.Opt`

Proves the formal soundness theorems for the validated Lir SSA optimizer using
a **Lazy-Segment-Sync** forward simulation (`Sem.Forward`):
- `checkProgramWithPlan_forward`: any program pair `(p, q)` accepted by the
  trusted validator `checkProgramWithPlan p q plan` satisfies a `Sem.Forward`
  diagram preserving exact values, memory, traps, and divergence.
- `checkProgramWithPlan_sim` & `check_sim`: clocked simulation `Sem.Sim Eq id`
  between `Lir.eval p` and `Lir.eval q`.
- `check_refines`: behaviour refinement `Sem.Behaviour.Refines Eq` (including
  termination, divergence, traps, and resource failures).
- `run_wellFormed`, `run_sim`, `run_refines`: end-to-end soundness of
  `Lir.Opt.run`.
- `validateCert_wellFormed`, `validateCert_sim`, `validateCert_refines`:
  soundness of external certificate replay `Lir.Opt.validateCert`.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Label FunId Width Ext Base Addr Arg Cond BinOp Ovf LimbOp
  Rhs Stmt Edge Term Block Func Program Word Env Frame State Step semStep semStep_next
  semStep_fail semStep_trap semStep_done evalArgs bindParams execList enter takeEdge
  step step_stmt step_call step_term step_jump step_br step_brOvf step_ret_done
  step_ret_caller step_tail step_fail step_trap star_stmts fails_of_star star_of_step
  eval eval_mono runs_eval atState)

/-! ## Reconstructing block bodies from `splitByCalls` -/

/-- Reconstruct a block body from its leading segment and trailing call splits. -/
def reconBody (seg0 : List Stmt) : List CallSplit → List Stmt
  | [] => seg0
  | c :: cs => seg0 ++ (.call c.rs c.fn c.args :: reconBody c.after cs)

/-- Trailing suffix of a block starting at the next call (empty when `calls = []`). -/
def callsTail : List CallSplit → List Stmt
  | [] => []
  | c :: cs => .call c.rs c.fn c.args :: reconBody c.after cs

theorem reconBody_eq_append (seg0 : List Stmt) (calls : List CallSplit) :
    reconBody seg0 calls = seg0 ++ callsTail calls := by
  cases calls <;> simp [reconBody, callsTail]

theorem splitByCallsAux_eq :
    ∀ (acc stmts : List Stmt),
      (∀ s ∈ acc, s.isCall = false) →
      let (seg0, calls) := splitByCallsAux acc stmts
      acc.reverse ++ stmts = reconBody seg0 calls ∧
      (∀ s ∈ seg0, s.isCall = false) ∧
      (∀ c ∈ calls, ∀ s ∈ c.after, s.isCall = false)
  | acc, [], hacc => by
      simp only [splitByCallsAux, reconBody, List.append_nil]
      exact ⟨trivial, fun s hs => hacc s (by simpa using hs), fun _ h => by cases h⟩
  | acc, .call rs f as :: rest, hacc => by
      have ih := splitByCallsAux_eq [] rest (fun _ h => by cases h)
      simp only [splitByCallsAux]
      generalize hsp : splitByCallsAux [] rest = pair at ih ⊢
      obtain ⟨seg1, more⟩ := pair
      obtain ⟨heq, hnc1, hncm⟩ := ih
      simp only [List.reverse_nil, List.nil_append] at heq
      refine ⟨by simp [reconBody, heq], fun s hs => hacc s (by simpa using hs), ?_⟩
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hnc1
      · exact hncm c hc
  | acc, .assign x r :: rest, hacc => by
      have hacc' : ∀ s ∈ (Stmt.assign x r :: acc), s.isCall = false := fun s hs => by
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs
        · rfl
        · exact hacc s hs
      have ih := splitByCallsAux_eq (.assign x r :: acc) rest hacc'
      simpa [splitByCallsAux, List.reverse_cons, List.append_assoc] using ih
  | acc, .limb r1 r2 op :: rest, hacc => by
      have hacc' : ∀ s ∈ (Stmt.limb r1 r2 op :: acc), s.isCall = false := fun s hs => by
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs
        · rfl
        · exact hacc s hs
      have ih := splitByCallsAux_eq (.limb r1 r2 op :: acc) rest hacc'
      simpa [splitByCallsAux, List.reverse_cons, List.append_assoc] using ih
  | acc, .store w m a :: rest, hacc => by
      have hacc' : ∀ s ∈ (Stmt.store w m a :: acc), s.isCall = false := fun s hs => by
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs
        · rfl
        · exact hacc s hs
      have ih := splitByCallsAux_eq (.store w m a :: acc) rest hacc'
      simpa [splitByCallsAux, List.reverse_cons, List.append_assoc] using ih

theorem splitByCalls_eq (stmts : List Stmt) :
    let (seg0, calls) := splitByCalls stmts
    stmts = reconBody seg0 calls ∧
    (∀ s ∈ seg0, s.isCall = false) ∧
    (∀ c ∈ calls, ∀ s ∈ c.after, s.isCall = false) := by
  have h := splitByCallsAux_eq [] stmts (fun _ h => by cases h)
  simpa [splitByCalls] using h

theorem execList_append {ρ ρ₁ ρ₂ : Env} {mem mem₁ mem₂ : X86.Memory} {ctx : Word} :
    ∀ {xs ys : List Stmt},
      execList ρ mem ctx xs = some (ρ₁, mem₁) →
      execList ρ₁ mem₁ ctx ys = some (ρ₂, mem₂) →
      execList ρ mem ctx (xs ++ ys) = some (ρ₂, mem₂)
  | [], _, h1, h2 => by
      simp only [execList, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1; exact h2
  | s :: xs, ys, h1, h2 => by
      simp only [execList] at h1
      split at h1
      · rename_i ρ' mem' hs
        simp only [List.cons_append, execList, hs]
        exact execList_append h1 h2
      · cases h1

theorem execList_snoc {ρ ρ₁ ρ₂ : Env} {mem mem₁ mem₂ : X86.Memory} {ctx : Word}
    {xs : List Stmt} {s : Stmt}
    (h1 : execList ρ mem ctx xs = some (ρ₁, mem₁))
    (h2 : s.exec ρ₁ mem₁ ctx = some (ρ₂, mem₂)) :
    execList ρ mem ctx (xs ++ [s]) = some (ρ₂, mem₂) :=
  execList_append h1 (by simp [execList, h2])

/-! ## Extracting validated facts from `checkProgramWithPlan` -/

private theorem checkProgramWithPlan_func {p q : Program} {plan : ProgPlan}
    (hp : checkProgramWithPlan p q plan = true) {fi : FunId} {F : Func}
    (hF : p.funcs[fi]? = some F) :
    (q.funcs[fi]? = some F ∧ plan.funcs[fi]? = some none) ∨
    (∃ G fplan, q.funcs[fi]? = some G ∧ plan.funcs[fi]? = some (some fplan) ∧
      checkFuncWithPlan F G fplan = true) := by
  unfold checkProgramWithPlan at hp
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hp
  obtain ⟨⟨⟨_, hszq⟩, hszp⟩, hall⟩ := hp
  have hlt : fi < p.funcs.size := (Array.getElem?_eq_some_iff.1 hF).1
  have hmem : fi ∈ List.range p.funcs.size := List.mem_range.2 hlt
  have hfi := hall fi hmem
  have hltq : fi < q.funcs.size := by rw [hszq]; exact hlt
  have hltp : fi < plan.funcs.size := by rw [hszp]; exact hlt
  rw [hF, Array.getElem?_eq_getElem hltq, Array.getElem?_eq_getElem hltp] at hfi
  cases hpf : plan.funcs[fi] with
  | none =>
      rw [hpf] at hfi; simp only [beq_iff_eq] at hfi
      exact .inl ⟨by rw [Array.getElem?_eq_getElem hltq, ← hfi], by rw [Array.getElem?_eq_getElem hltp, hpf]⟩
  | some fplan =>
      rw [hpf] at hfi
      exact .inr ⟨q.funcs[fi], fplan, Array.getElem?_eq_getElem hltq,
        by rw [Array.getElem?_eq_getElem hltp, hpf], hfi⟩

private theorem checkFuncWithPlan_block {F G : Func} {fplan : FuncPlan}
    (hfp : checkFuncWithPlan F G fplan = true) {L : Label} {bp : BlockPlan}
    (hbp : fplan.blocks[L]? = some (some bp)) :
    checkBlock F G fplan L bp = true := by
  unfold checkFuncWithPlan at hfp
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hfp
  obtain ⟨⟨⟨⟨_, _⟩, hsz⟩, _⟩, hall⟩ := hfp
  have hlt : L < fplan.blocks.size := (Array.getElem?_eq_some_iff.1 hbp).1
  have hltF : L < F.blocks.size := by rw [← hsz]; exact hlt
  have hL := hall L (List.mem_range.2 hltF)
  rw [hbp] at hL
  exact hL

private theorem checkFuncWithPlan_entry {F G : Func} {fplan : FuncPlan}
    (hfp : checkFuncWithPlan F G fplan = true) :
    G.params = F.params ∧ G.results = F.results ∧
    ∃ fb0 gb0 bp0,
      F.blocks[0]? = some fb0 ∧ G.blocks[0]? = some gb0 ∧
      fplan.blocks[0]? = some (some bp0) ∧
      bp0.target = 0 ∧ checkEntryInv F.params bp0.entryInv = true := by
  unfold checkFuncWithPlan at hfp
  simp only [Bool.and_eq_true, beq_iff_eq] at hfp
  obtain ⟨⟨⟨⟨⟨hpar, hres⟩, _⟩, _⟩, hentry⟩, _⟩ := hfp
  refine ⟨hpar, hres, ?_⟩
  cases hf0 : F.blocks[0]? with
  | none => rw [hf0] at hentry; cases hentry
  | some fb0 =>
      cases hg0 : G.blocks[0]? with
      | none => rw [hf0, hg0] at hentry; cases hentry
      | some gb0 =>
          cases hp0 : fplan.blocks[0]? with
          | none => rw [hf0, hg0, hp0] at hentry; cases hentry
          | some obp =>
              cases obp with
              | none => rw [hf0, hg0, hp0] at hentry; cases hentry
              | some bp0 =>
                  rw [hf0, hg0, hp0] at hentry
                  simp only [Bool.and_eq_true, beq_iff_eq] at hentry
                  exact ⟨fb0, gb0, bp0, rfl, rfl, rfl, hentry.1.2, hentry.2⟩

/-! ## Lazy-Segment-Sync simulation relation (`TopFrameRel`, `CallerFrameRel`, `StateRel`) -/

/-- Witness data for the active (top) execution frame: `fr₁` is mid-segment inside
`done₁ ++ rem₁`, while `fr₂` is parked at the start of `seg₂` with memory `mem₂`
(= segment-entry memory `mem₀`). -/
structure TopFrameData (p q : Program) (plan : ProgPlan) (ctx : Word)
    (mem₁ : X86.Memory) (fr₁ : Frame) (mem₂ : X86.Memory) (fr₂ : Frame) : Type where
  fnEq : fr₂.fn = fr₁.fn
  dsts1 : fr₁.dsts = []
  dsts2 : fr₂.dsts = []
  F : Func
  G : Func
  fplan : FuncPlan
  bp : BlockPlan
  B₁ : Block
  B₂ : Block
  hF : p.funcs[fr₁.fn]? = some F
  hG : q.funcs[fr₁.fn]? = some G
  hFP : plan.funcs[fr₁.fn]? = some (some fplan)
  hBP : fplan.blocks[fr₁.label]? = some (some bp)
  hL' : fr₂.label = bp.target
  hB₁ : F.blocks[fr₁.label]? = some B₁
  hB₂ : G.blocks[bp.target]? = some B₂
  pre₁ : List Stmt
  done₁ : List Stmt
  rem₁ : List Stmt
  calls₁ : List CallSplit
  pre₂ : List Stmt
  seg₂ : List Stmt
  calls₂ : List CallSplit
  inv : BlockInv
  afterInvs : List BlockInv
  hBody₁ : B₁.body.toList = pre₁ ++ (done₁ ++ rem₁) ++ callsTail calls₁
  hBody₂ : B₂.body.toList = pre₂ ++ seg₂ ++ callsTail calls₂
  hNoCall₁ : ∀ s ∈ done₁ ++ rem₁, s.isCall = false
  hNoCall₂ : ∀ s ∈ seg₂, s.isCall = false
  hCallsNoCall₁ : ∀ c ∈ calls₁, ∀ s ∈ c.after, s.isCall = false
  hCallsNoCall₂ : ∀ c ∈ calls₂, ∀ s ∈ c.after, s.isCall = false
  hPos₁ : fr₁.pos = pre₁.length + done₁.length
  hPos₂ : fr₂.pos = pre₂.length
  ρ₁₀ : Env
  hInv : inv.Holds ρ₁₀ fr₂.env ctx
  hDone₁ : execList ρ₁₀ mem₂ ctx done₁ = some (fr₁.env, mem₁)
  st : SegState
  hCheckSeg : checkSeg inv (done₁ ++ rem₁) seg₂ = some st
  hCheckRest : checkCallsAndTerm F G fplan fr₁.label bp.target B₁.term B₂.term st calls₁ calls₂ afterInvs = true

/-- Prop-level active frame relation (`Nonempty TopFrameData` or identical unchanged function). -/
def TopFrameRel (p q : Program) (plan : ProgPlan) (ctx : Word)
    (mem₁ : X86.Memory) (fr₁ : Frame) (mem₂ : X86.Memory) (fr₂ : Frame) : Prop :=
  Nonempty (TopFrameData p q plan ctx mem₁ fr₁ mem₂ fr₂) ∨
  (mem₁ = mem₂ ∧ fr₁ = fr₂ ∧ p.funcs[fr₁.fn]? = q.funcs[fr₁.fn]?)

/-- Memory-independent witness data for a suspended caller frame waiting for a callee to return. -/
structure CallerFrameData (p q : Program) (plan : ProgPlan) (ctx : Word)
    (fr₁ fr₂ : Frame) : Type where
  fnEq : fr₂.fn = fr₁.fn
  dstsEq : fr₂.dsts = fr₁.dsts
  F : Func
  G : Func
  fplan : FuncPlan
  bp : BlockPlan
  B₁ : Block
  B₂ : Block
  hF : p.funcs[fr₁.fn]? = some F
  hG : q.funcs[fr₁.fn]? = some G
  hFP : plan.funcs[fr₁.fn]? = some (some fplan)
  hBP : fplan.blocks[fr₁.label]? = some (some bp)
  hL' : fr₂.label = bp.target
  hB₁ : F.blocks[fr₁.label]? = some B₁
  hB₂ : G.blocks[bp.target]? = some B₂
  pre₁ : List Stmt
  seg₁ : List Stmt
  calls₁ : List CallSplit
  pre₂ : List Stmt
  seg₂ : List Stmt
  calls₂ : List CallSplit
  postInv : BlockInv
  afterInvs : List BlockInv
  hBody₁ : B₁.body.toList = pre₁ ++ seg₁ ++ callsTail calls₁
  hBody₂ : B₂.body.toList = pre₂ ++ seg₂ ++ callsTail calls₂
  hNoCall₁ : ∀ s ∈ seg₁, s.isCall = false
  hNoCall₂ : ∀ s ∈ seg₂, s.isCall = false
  hCallsNoCall₁ : ∀ c ∈ calls₁, ∀ s ∈ c.after, s.isCall = false
  hCallsNoCall₂ : ∀ c ∈ calls₂, ∀ s ∈ c.after, s.isCall = false
  hPos₁ : fr₁.pos = pre₁.length
  hPos₂ : fr₂.pos = pre₂.length
  hResume : ∀ vals ρ₁' ρ₂',
    bindParams fr₁.env fr₁.dsts vals = some ρ₁' →
    bindParams fr₂.env fr₂.dsts vals = some ρ₂' →
    postInv.Holds ρ₁' ρ₂' ctx
  st : SegState
  hCheckSeg : checkSeg postInv seg₁ seg₂ = some st
  hCheckRest : checkCallsAndTerm F G fplan fr₁.label bp.target B₁.term B₂.term st calls₁ calls₂ afterInvs = true

/-- Prop-level caller frame relation (`Nonempty CallerFrameData` or identical unchanged function). -/
def CallerFrameRel (p q : Program) (plan : ProgPlan) (ctx : Word)
    (fr₁ fr₂ : Frame) : Prop :=
  Nonempty (CallerFrameData p q plan ctx fr₁ fr₂) ∨
  (fr₁ = fr₂ ∧ p.funcs[fr₁.fn]? = q.funcs[fr₁.fn]?)

/-- Whole-state simulation relation between `s₁` (in `p`) and `s₂` (in `q`). -/
def StateRel (p q : Program) (plan : ProgPlan) (s₁ s₂ : State) : Prop :=
  s₂.ctx = s₁.ctx ∧
  match s₁.stack, s₂.stack with
  | fr₁ :: rest₁, fr₂ :: rest₂ =>
      TopFrameRel p q plan s₁.ctx s₁.mem fr₁ s₂.mem fr₂ ∧
      ListRel (CallerFrameRel p q plan s₁.ctx) rest₁ rest₂
  | _, _ => False

/-! ## Constructing `TopFrameRel` at block entry -/

private theorem topFrameRel_atBlock {p q : Program} {plan : ProgPlan}
    (hp : checkProgramWithPlan p q plan = true)
    {fn L : Nat} {F G : Func} {fplan : FuncPlan} {bp : BlockPlan}
    {ρ₁ ρ₂ : Env} {mem : X86.Memory} {ctx : Word}
    (hF : p.funcs[fn]? = some F) (hG : q.funcs[fn]? = some G)
    (hFP : plan.funcs[fn]? = some (some fplan)) (hBP : fplan.blocks[L]? = some (some bp))
    (hInv : bp.entryInv.Holds ρ₁ ρ₂ ctx) :
    TopFrameRel p q plan ctx mem { fn, label := L, pos := 0, env := ρ₁, dsts := [] }
      mem { fn, label := bp.target, pos := 0, env := ρ₂, dsts := [] } := by
  rcases checkProgramWithPlan_func hp hF with ⟨_, hNone⟩ | ⟨G', fplan', hG', hFP', hfunc⟩
  · rw [hFP] at hNone; cases hNone
  rw [hG] at hG'; cases hG'
  rw [hFP] at hFP'; cases hFP'
  have hblk := checkFuncWithPlan_block hfunc hBP
  unfold checkBlock at hblk
  cases hB₁ : F.blocks[L]? with
  | none => rw [hB₁] at hblk; cases hblk
  | some B₁ =>
      cases hB₂ : G.blocks[bp.target]? with
      | none => rw [hB₁, hB₂] at hblk; cases hblk
      | some B₂ =>
          rw [hB₁, hB₂] at hblk
          simp only [Bool.and_eq_true] at hblk
          obtain ⟨_, hchk⟩ := hblk
          have hsp1 := splitByCalls_eq B₁.body.toList
          have hsp2 := splitByCalls_eq B₂.body.toList
          generalize hs1_eq : splitByCalls B₁.body.toList = p1 at hsp1 hchk
          generalize hs2_eq : splitByCalls B₂.body.toList = p2 at hsp2 hchk
          obtain ⟨seg1, calls1⟩ := p1
          obtain ⟨seg2, calls2⟩ := p2
          obtain ⟨hb1_eq, hnc1, hcnc1⟩ := hsp1
          obtain ⟨hb2_eq, hnc2, hcnc2⟩ := hsp2
          cases hcs : checkSeg bp.entryInv seg1 seg2 with
          | none => rw [hcs] at hchk; cases hchk
          | some st =>
              rw [hcs] at hchk
              exact .inl
                ⟨{ fnEq := rfl, dsts1 := rfl, dsts2 := rfl
                   F, G, fplan, bp, B₁, B₂, hF, hG, hFP, hBP, hL' := rfl, hB₁, hB₂
                   pre₁ := [], done₁ := [], rem₁ := seg1, calls₁ := calls1
                   pre₂ := [], seg₂ := seg2, calls₂ := calls2
                   inv := bp.entryInv, afterInvs := bp.afterCalls
                   hBody₁ := by rw [hb1_eq, reconBody_eq_append]; simp
                   hBody₂ := by rw [hb2_eq, reconBody_eq_append]; simp
                   hNoCall₁ := by simpa using hnc1
                   hNoCall₂ := hnc2
                   hCallsNoCall₁ := hcnc1
                   hCallsNoCall₂ := hcnc2
                   hPos₁ := rfl, hPos₂ := rfl
                   ρ₁₀ := ρ₁, hInv, hDone₁ := rfl
                   st, hCheckSeg := by simpa using hcs, hCheckRest := hchk }⟩

/-! ## Edge and terminator soundness (`checkEdge_sound`, `checkTerm_sound`) -/

private theorem fails_of_star_fails {q : Program} {s s' : State} {c : Nat}
    (hst : Sem.Star (semStep q) s c s') (hf : Sem.Fails (semStep q) s') :
    Sem.Fails (semStep q) s := by
  obtain ⟨c2, sf, r, hst2, hsf⟩ := hf
  exact ⟨c + c2, sf, r, hst.trans hst2, hsf⟩

private theorem isFailEdge_fails {q : Program} {G : Func} {fn curL' : Nat} {B : Block}
    {mem : X86.Memory} {ctx : Word} {ρ₂ : Env} {rest₂ : List Frame} {e : Edge}
    (hG : q.funcs[fn]? = some G)
    (hfe : isFailEdge G e = true)
    (hstep : step q (atState mem ctx fn curL' B.body.size ρ₂ rest₂) =
      takeEdge G (atState mem ctx fn curL' B.body.size ρ₂ rest₂)
        { fn, label := curL', pos := B.body.size, env := ρ₂, dsts := [] } rest₂ ρ₂ e) :
    Sem.Fails (semStep q) (atState mem ctx fn curL' B.body.size ρ₂ rest₂) := by
  unfold isFailEdge at hfe
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hfe
  obtain ⟨hargs, hblk⟩ := hfe
  cases hfb : G.blocks[e.target]? with
  | none => rw [hfb] at hblk; cases hblk
  | some fb =>
      rw [hfb] at hblk
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hblk
      obtain ⟨⟨hpar, hbody⟩, hterm⟩ := hblk
      cases ht : fb.term with
      | fail r =>
          have htake : takeEdge G (atState mem ctx fn curL' B.body.size ρ₂ rest₂)
              { fn, label := curL', pos := B.body.size, env := ρ₂, dsts := [] } rest₂ ρ₂ e =
              .next (atState mem ctx fn e.target 0 ρ₂ rest₂) (decide (e.target ≤ curL')) := by
            unfold takeEdge; simp [hargs, hfb, hpar, bindParams]
          rw [htake] at hstep
          have hst := star_of_step hstep
          have hpos0 : (0 : Nat) = fb.body.size := by
            simp only [Array.isEmpty, decide_eq_true_eq] at hbody; exact hbody.symm
          have hfl := step_fail (p := q) (F := G) (B := fb)
            (fr := { fn, label := e.target, pos := 0, env := ρ₂, dsts := [] }) (rest := rest₂)
            (mem := mem) (ctx := ctx) hG hfb hpos0 ht
          exact fails_of_star hst hfl
      | _ => rw [ht] at hterm; cases hterm

/-- Helper: `evalArgs` maps to `ListRel` on normalized `argToSym`. -/
private theorem evalArgs_argToSym {ρ₁ ρ₁₀ : Env} {ctx : Word} {snaps : MemSnaps}
    {srcEnv : Src.NatMap SymExpr}
    (hsrc : ∀ x v, ρ₁[x]? = some v → (srcLookup srcEnv x).eval ρ₁₀ ctx snaps = some v) :
    ∀ {args : List Arg} {vals : List Word},
      evalArgs ρ₁ args = some vals →
      ListRel (fun e v => e.eval ρ₁₀ ctx snaps = some v)
        (args.map fun a => (argToSym (srcLookup srcEnv) a).norm) vals
  | [], _, h => by simp only [evalArgs_nil, Option.some.injEq] at h; subst h; exact .nil
  | a :: rest, _, h => by
      simp only [evalArgs_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨v, hv, vs, hvs, rfl⟩ := h
      exact .cons (SymExpr.norm_sound (argToSym_eval hsrc hv)) (evalArgs_argToSym hsrc hvs)

private theorem evalTgtArgs_length {tgtEnv : Src.NatMap SymExpr} :
    ∀ {as : List Arg} {es : List SymExpr}, evalTgtArgs tgtEnv as = some es → as.length = es.length
  | [], _, h => by simp only [evalTgtArgs, Option.some.injEq] at h; subst h; rfl
  | _ :: r, _, h => by
      simp only [evalTgtArgs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨_, _, es', hes', rfl⟩ := h
      simp [evalTgtArgs_length hes']

private theorem bindParams_length_eq :
    ∀ {ρ ρ' : Env} {ps : List VReg} {vs : List Word}, bindParams ρ ps vs = some ρ' → ps.length = vs.length
  | _, _, [], [], _ => rfl
  | _, _, _ :: _, _ :: _, h => by simp only [bindParams] at h; simp [bindParams_length_eq h]
  | _, _, [], _ :: _, h | _, _, _ :: _, [], h => by cases h

/-- Helper: adding a concrete evaluated condition fact preserves `FactsHold`. -/
private theorem addFact_holds {ρ₁₀ : Env} {ctx : Word} {snaps : MemSnaps}
    {facts : List PFact} {c : Cond} {w : Width} {a b : SymExpr} {va vb : Word} {res : Bool}
    (hfacts : FactsHold ρ₁₀ ctx snaps facts)
    (ha : a.eval ρ₁₀ ctx snaps = some va) (hb : b.eval ρ₁₀ ctx snaps = some vb)
    (hc : c.holds w va vb = res) :
    FactsHold ρ₁₀ ctx snaps (addFact facts c w a b res) := by
  unfold addFact
  dsimp only
  split
  · intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact ⟨va, vb, SymExpr.norm_sound ha, SymExpr.norm_sound hb, hc⟩
    · exact hfacts f hf
  · exact hfacts

/-- `checkEdge` soundness: taking target edge `e'` from `curL'` either reaches
`(bp.target, 0)` in `c ≥ needCharge.toNat` charges with `TopFrameRel`, OR fails
on a hoisted `.fail` guard (`Sem.Fails`). -/
private theorem checkEdge_sound {p q : Program} {plan : ProgPlan}
    (hp : checkProgramWithPlan p q plan = true)
    {fn : FunId} {F G : Func} {fplan : FuncPlan}
    (hF : p.funcs[fn]? = some F) (hG : q.funcs[fn]? = some G) (hFP : plan.funcs[fn]? = some (some fplan))
    {ρ₁₀ ρ₁ ρ₁' : Env} {mem : X86.Memory} {ctx : Word} {snaps : MemSnaps} {rest₂ : List Frame}
    {srcEnv : Src.NatMap SymExpr} {srcDef : Src.NatSet}
    {e : Edge} {fTgt : Block} {vals₁ : List Word}
    (hsrc : ∀ x v, ρ₁[x]? = some v → (srcLookup srcEnv x).eval ρ₁₀ ctx snaps = some v)
    (hdef : ∀ x, srcDef.contains x = true → ρ₁[x]?.isSome = true)
    (hftgt : F.blocks[e.target]? = some fTgt)
    (hevals₁ : evalArgs ρ₁ e.args = some vals₁)
    (hbp₁ : bindParams ρ₁ fTgt.params vals₁ = some ρ₁') :
    ∀ (fuel : Nat) (tgtEnv : Src.NatMap SymExpr) (allFacts : List PFact)
      (curL' curPos : Label) (needCharge : Bool) (e' : Edge) (ρ₂Orig ρ₂ : Env),
      (∀ y ey, tgtEnv.get? y = some ey → ∃ v, ρ₂[y]? = some v ∧ ey.eval ρ₁₀ ctx snaps = some v) →
      FactsHold ρ₁₀ ctx snaps allFacts →
      checkEdge F G fplan srcEnv srcDef tgtEnv allFacts curL' needCharge e e' fuel = true →
      step q (atState mem ctx fn curL' curPos ρ₂Orig rest₂) =
        takeEdge G (atState mem ctx fn curL' curPos ρ₂Orig rest₂)
          { fn, label := curL', pos := curPos, env := ρ₂Orig, dsts := [] } rest₂ ρ₂ e' →
      (∃ c ρ₂' bp,
        fplan.blocks[e.target]? = some (some bp) ∧
        Sem.Star (semStep q) (atState mem ctx fn curL' curPos ρ₂Orig rest₂) c
          (atState mem ctx fn bp.target 0 ρ₂' rest₂) ∧
        needCharge.toNat ≤ c ∧
        TopFrameRel p q plan ctx mem { fn, label := e.target, pos := 0, env := ρ₁', dsts := [] }
          mem { fn, label := bp.target, pos := 0, env := ρ₂', dsts := [] }) ∨
      Sem.Fails (semStep q) (atState mem ctx fn curL' curPos ρ₂Orig rest₂)
  | 0, _, _, _, _, _, _, _, _, _, _, hck, _ => by simp [checkEdge] at hck
  | fuel + 1, tgtEnv, allFacts, curL', curPos, needCharge, e', ρ₂Orig, ρ₂, htgt, hfacts, hck, hstep => by
      unfold checkEdge at hck
      cases hbp_eq : fplan.blocks[e.target]? with
      | none => rw [hbp_eq, hftgt] at hck; cases hck
      | some obp =>
          cases obp with
          | none => rw [hbp_eq, hftgt] at hck; cases hck
          | some bp =>
              rw [hbp_eq, hftgt] at hck
              dsimp only at hck
              by_cases hsame : (e'.target == bp.target) = true
              · have hsame' : e'.target = bp.target := by simpa using hsame
                simp only [hsame, ↓reduceIte] at hck
                cases hgTgt : G.blocks[bp.target]? with
                | none => rw [hgTgt] at hck; cases hck
                | some gTgt =>
                    cases htargs : evalTgtArgs tgtEnv e'.args with
                    | none => rw [hgTgt, htargs] at hck; cases hck
                    | some tArgs =>
                        rw [hgTgt, htargs] at hck
                        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                          beq_iff_eq] at hck
                        obtain ⟨⟨⟨hchg, _⟩, hlenG⟩, hent⟩ := hck
                        obtain ⟨vals₂, hevals₂, hfa₂⟩ := evalTgtArgs_sound htgt htargs
                        have hlen_t : tArgs.length = vals₂.length := hfa₂.length_eq
                        have hlen_e : e'.args.length = vals₂.length := (evalTgtArgs_length htargs).trans hlen_t
                        obtain ⟨ρ₂', hbp₂⟩ := bindParams_exists (ρ := ρ₂) (ps := gTgt.params) (vs := vals₂)
                          (by rw [← hlenG, hlen_e])
                        have htake : takeEdge G (atState mem ctx fn curL' curPos ρ₂Orig rest₂)
                            { fn, label := curL', pos := curPos, env := ρ₂Orig, dsts := [] } rest₂ ρ₂ e' =
                            .next (atState mem ctx fn bp.target 0 ρ₂' rest₂) (decide (e'.target ≤ curL')) := by
                          unfold takeEdge
                          rw [hevals₂, hsame', hgTgt]; dsimp only; rw [hbp₂]
                        rw [htake] at hstep
                        have hst := star_of_step hstep
                        have hfa₁ := evalArgs_argToSym hsrc hevals₁
                        obtain ⟨hsrc1, hdef1⟩ := bindParams_src_inv hbp₁ hfa₁ hsrc hdef
                        have htgt1 := bindParams_tgt_inv hbp₂ hfa₂ htgt
                        have hinv := checkEntails_sound hsrc1 hdef1 htgt1 hfacts hent
                        have htop := topFrameRel_atBlock (mem := mem) hp hF hG hFP hbp_eq hinv
                        have hc_le : needCharge.toNat ≤ (decide (e'.target ≤ curL')).toNat := by
                          rcases hchg with hn | hc
                          · simp [hn]
                          · simp [hc]; cases needCharge <;> decide
                        exact .inl ⟨(decide (e'.target ≤ curL')).toNat, ρ₂', bp, rfl, hst, hc_le, htop⟩
              · simp only [hsame, Bool.false_eq_true, ↓reduceIte] at hck
                cases hph : G.blocks[e'.target]? with
                | none => rw [hph] at hck; cases hck
                | some phBlk =>
                    cases htargs : evalTgtArgs tgtEnv e'.args with
                    | none => rw [hph, htargs] at hck; cases hck
                    | some tArgs =>
                        rw [hph, htargs] at hck
                        by_cases hlen : (e'.args.length != phBlk.params.length) = true
                        · simp [hlen] at hck
                        · have hlen_eq : e'.args.length = phBlk.params.length := by simpa [bne] using hlen
                          simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hck
                          obtain ⟨vals₂, hevals₂, hfa₂⟩ := evalTgtArgs_sound htgt htargs
                          have hlen_t : e'.args.length = vals₂.length := (evalTgtArgs_length htargs).trans hfa₂.length_eq
                          obtain ⟨ρ₂Ph0, hbpPh⟩ := bindParams_exists (ρ := ρ₂) (ps := phBlk.params) (vs := vals₂)
                            (by rw [← hlen_eq, hlen_t])
                          have htgtPh0 := bindParams_tgt_inv hbpPh hfa₂ htgt
                          have htake : takeEdge G (atState mem ctx fn curL' curPos ρ₂Orig rest₂)
                              { fn, label := curL', pos := curPos, env := ρ₂Orig, dsts := [] } rest₂ ρ₂ e' =
                              .next (atState mem ctx fn e'.target 0 ρ₂Ph0 rest₂) (decide (e'.target ≤ curL')) := by
                            unfold takeEdge; rw [hevals₂, hph]; dsimp only; rw [hbpPh]
                          rw [htake] at hstep
                          have hst1 := star_of_step hstep
                          cases htot : stepTotalTgtList (bindNatMap tgtEnv phBlk.params tArgs) phBlk.body.toList with
                          | none => rw [htot] at hck; cases hck
                          | some tgtEnvPh =>
                              rw [htot] at hck; dsimp only at hck
                              obtain ⟨hncPh, ρ₂Ph, hxPh, htgtPh⟩ := stepTotalTgtList_sound (mem := mem) htgtPh0 htot
                              have hst2 : Sem.Star (semStep q) (atState mem ctx fn e'.target 0 ρ₂Ph0 rest₂) 0
                                  (atState mem ctx fn e'.target phBlk.body.size ρ₂Ph rest₂) := by
                                have := star_stmts (p := q) (F := G) (B := phBlk) (fn := fn) (L := e'.target)
                                  (dsts := []) (rest := rest₂) (pre := []) (ss := phBlk.body.toList) (post := [])
                                  hG hph (by simp) hncPh hxPh
                                simpa using this
                              have hst12 := hst1.trans hst2
                              have hcharge_add : ∀ c2 : Nat,
                                  (needCharge && !decide (e'.target ≤ curL')).toNat ≤ c2 →
                                  needCharge.toNat ≤ (decide (e'.target ≤ curL')).toNat + 0 + c2 := by
                                intro c2 hc2
                                cases hnc : needCharge <;> cases hdec : decide (e'.target ≤ curL') <;>
                                  simp [hnc, hdec] at hc2 ⊢ <;> omega
                              cases hterm : phBlk.term with
                              | jump e'' =>
                                  rw [hterm] at hck; dsimp only at hck
                                  have hst_j := step_jump (p := q) (F := G) (B := phBlk)
                                    (fr := { fn, label := e'.target, pos := phBlk.body.size, env := ρ₂Ph, dsts := [] })
                                    (rest := rest₂) (mem := mem) (ctx := ctx) hG hph rfl hterm
                                  rcases checkEdge_sound hp hF hG hFP hsrc hdef hftgt hevals₁ hbp₁ fuel
                                      tgtEnvPh allFacts e'.target phBlk.body.size (needCharge && !decide (e'.target ≤ curL'))
                                      e'' ρ₂Ph ρ₂Ph htgtPh hfacts hck hst_j with
                                    ⟨c2, ρ₂', bp', hbp', hst3, hc2, htop'⟩ | hfail
                                  · rw [hbp_eq] at hbp'
                                    exact .inl ⟨_, ρ₂', bp', hbp', hst12.trans hst3, hcharge_add c2 hc2, htop'⟩
                                  · exact .inr (fails_of_star_fails hst12 hfail)
                              | br gc gw ga gb gt gf =>
                                  rw [hterm] at hck; dsimp only at hck
                                  cases hea : evalTgtArg tgtEnvPh ga with
                                  | none => rw [hea] at hck; cases hck
                                  | some ea =>
                                      cases heb : evalTgtArg tgtEnvPh gb with
                                      | none => rw [hea, heb] at hck; cases hck
                                      | some eb =>
                                          rw [hea, heb] at hck; dsimp only at hck
                                          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound htgtPh hea
                                          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound htgtPh heb
                                          have hst_br := step_br (p := q) (F := G) (B := phBlk)
                                            (fr := { fn, label := e'.target, pos := phBlk.body.size, env := ρ₂Ph, dsts := [] })
                                            (rest := rest₂) (mem := mem) (ctx := ctx) hG hph rfl hterm hva hvb
                                          by_cases hgf : isFailEdge G gf = true
                                          · simp only [hgf, ↓reduceIte] at hck
                                            cases hcond : gc.holds gw va vb with
                                            | false =>
                                                rw [hcond] at hst_br
                                                exact .inr (fails_of_star_fails hst12 (isFailEdge_fails hG hgf hst_br))
                                            | true =>
                                                rw [hcond] at hst_br
                                                have hfacts' : FactsHold ρ₁₀ ctx snaps
                                                    (if ea.norm.isMemFree && eb.norm.isMemFree
                                                     then { cond := gc, width := gw, lhs := ea.norm, rhs := eb.norm, result := true } :: allFacts
                                                     else allFacts) := by
                                                  simpa [addFact] using addFact_holds hfacts heva hevb hcond
                                                rcases checkEdge_sound hp hF hG hFP hsrc hdef hftgt hevals₁ hbp₁ fuel
                                                    tgtEnvPh _ e'.target phBlk.body.size (needCharge && !decide (e'.target ≤ curL'))
                                                    gt ρ₂Ph ρ₂Ph htgtPh hfacts' hck hst_br with
                                                  ⟨c2, ρ₂', bp', hbp', hst3, hc2, htop'⟩ | hfail
                                                · rw [hbp_eq] at hbp'
                                                  exact .inl ⟨_, ρ₂', bp', hbp', hst12.trans hst3, hcharge_add c2 hc2, htop'⟩
                                                · exact .inr (fails_of_star_fails hst12 hfail)
                                          · simp only [hgf, Bool.false_eq_true, ↓reduceIte] at hck
                                            by_cases hgt : isFailEdge G gt = true
                                            · simp only [hgt, ↓reduceIte] at hck
                                              cases hcond : gc.holds gw va vb with
                                              | true =>
                                                  rw [hcond] at hst_br
                                                  exact .inr (fails_of_star_fails hst12 (isFailEdge_fails hG hgt hst_br))
                                              | false =>
                                                  rw [hcond] at hst_br
                                                  have hfacts' : FactsHold ρ₁₀ ctx snaps
                                                      (if ea.norm.isMemFree && eb.norm.isMemFree
                                                       then { cond := gc, width := gw, lhs := ea.norm, rhs := eb.norm, result := false } :: allFacts
                                                       else allFacts) := by
                                                    simpa [addFact] using addFact_holds hfacts heva hevb hcond
                                                  rcases checkEdge_sound hp hF hG hFP hsrc hdef hftgt hevals₁ hbp₁ fuel
                                                      tgtEnvPh _ e'.target phBlk.body.size (needCharge && !decide (e'.target ≤ curL'))
                                                      gf ρ₂Ph ρ₂Ph htgtPh hfacts' hck hst_br with
                                                    ⟨c2, ρ₂', bp', hbp', hst3, hc2, htop'⟩ | hfail
                                                  · rw [hbp_eq] at hbp'
                                                    exact .inl ⟨_, ρ₂', bp', hbp', hst12.trans hst3, hcharge_add c2 hc2, htop'⟩
                                                  · exact .inr (fails_of_star_fails hst12 hfail)
                                            · simp [hgt] at hck
                              | _ => rw [hterm] at hck; cases hck

private theorem checkCondRelationDirect_sound {ρ₁₀ : Env} {ctx : Word} {snaps : MemSnaps}
    {facts : List PFact} (hfacts : FactsHold ρ₁₀ ctx snaps facts)
    {c1 c2 : Cond} {w1 w2 : Width} {a1 b1 a2 b2 : SymExpr} {va1 vb1 va2 vb2 : Word} {neg : Bool}
    (hrel : checkCondRelationDirect facts c1 w1 a1 b1 c2 w2 a2 b2 = some neg)
    (ha1 : a1.eval ρ₁₀ ctx snaps = some va1) (hb1 : b1.eval ρ₁₀ ctx snaps = some vb1)
    (ha2 : a2.eval ρ₁₀ ctx snaps = some va2) (hb2 : b2.eval ρ₁₀ ctx snaps = some vb2) :
    c2.holds w2 va2 vb2 = if neg then !(c1.holds w1 va1 vb1) else c1.holds w1 va1 vb1 := by
  unfold checkCondRelationDirect at hrel
  by_cases hw : (w1 != w2) = true
  · simp [hw] at hrel
  · have hweq : w1 = w2 := by simpa [bne] using hw
    subst hweq
    simp only [hw, Bool.false_eq_true, ↓reduceIte] at hrel
    by_cases h1 : (exprEquivFacts facts a1 a2 && exprEquivFacts facts b1 b2) = true
    · simp only [h1, ↓reduceIte] at hrel
      simp only [Bool.and_eq_true] at h1
      have ha_eq := exprEquivFacts_sound hfacts h1.1 ha1 ha2
      have hb_eq := exprEquivFacts_sound hfacts h1.2 hb1 hb2
      subst ha_eq hb_eq
      by_cases hc : (c1 == c2) = true
      · have hc' : c1 = c2 := by simpa using hc
        subst hc'; simp only [hc, ↓reduceIte, Option.some.injEq] at hrel; subst hrel; rfl
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hrel
        by_cases hcn : (c1 == condNegate c2) = true
        · have hcn' : c1 = condNegate c2 := by simpa using hcn
          subst hcn'; simp only [hcn, ↓reduceIte, Option.some.injEq] at hrel; subst hrel
          simp [condNegate_holds]
        · simp [hcn] at hrel
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hrel
      by_cases h2 : (exprEquivFacts facts a1 b2 && exprEquivFacts facts b1 a2) = true
      · simp only [h2, ↓reduceIte] at hrel
        simp only [Bool.and_eq_true] at h2
        have ha_eq := exprEquivFacts_sound hfacts h2.1 ha1 hb2
        have hb_eq := exprEquivFacts_sound hfacts h2.2 hb1 ha2
        subst ha_eq hb_eq
        by_cases hc : (c1 == condSwap c2) = true
        · have hc' : c1 = condSwap c2 := by simpa using hc
          subst hc'; simp only [hc, ↓reduceIte, Option.some.injEq] at hrel; subst hrel
          rw [condSwap_holds]; rfl
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hrel
          by_cases hcn : (c1 == condNegate (condSwap c2)) = true
          · have hcn' : c1 = condNegate (condSwap c2) := by simpa using hcn
            subst hcn'; simp only [hcn, ↓reduceIte, Option.some.injEq] at hrel; subst hrel
            simp [condNegate_holds, condSwap_holds]
          · simp [hcn] at hrel
      · simp [h2] at hrel

private theorem checkCondRelation_sound {ρ₁₀ : Env} {ctx : Word} {snaps : MemSnaps}
    {facts : List PFact} (hfacts : FactsHold ρ₁₀ ctx snaps facts)
    {c1 c2 : Cond} {w1 w2 : Width} {a1 b1 a2 b2 : SymExpr} {va1 vb1 va2 vb2 : Word} {neg : Bool}
    (hrel : checkCondRelation facts c1 w1 a1 b1 c2 w2 a2 b2 = some neg)
    (ha1 : a1.eval ρ₁₀ ctx snaps = some va1) (hb1 : b1.eval ρ₁₀ ctx snaps = some vb1)
    (ha2 : a2.eval ρ₁₀ ctx snaps = some va2) (hb2 : b2.eval ρ₁₀ ctx snaps = some vb2) :
    c2.holds w2 va2 vb2 = if neg then !(c1.holds w1 va1 vb1) else c1.holds w1 va1 vb1 := by
  have hstep : ∀ {c1' : Cond} {w1' : Width} {a1' b1' : SymExpr} {va1' vb1' : Word},
      a1'.eval ρ₁₀ ctx snaps = some va1' → b1'.eval ρ₁₀ ctx snaps = some vb1' →
      (match checkCondRelationDirect facts c1' w1' a1' b1' c2 w2 a2 b2 with
       | some neg => some neg
       | none =>
           match unwrapOddBit2 facts c1' w1' a1' b1' with
           | some (co, wo, ao, bo) => checkCondRelationDirect facts co wo ao bo c2 w2 a2 b2
           | none => none) = some neg →
      c2.holds w2 va2 vb2 = if neg then !(c1'.holds w1' va1' vb1') else c1'.holds w1' va1' vb1' := by
    intro c1' w1' a1' b1' va1' vb1' ha1' hb1' hs
    cases hd : checkCondRelationDirect facts c1' w1' a1' b1' c2 w2 a2 b2 with
    | some n =>
        rw [hd] at hs; cases hs
        exact checkCondRelationDirect_sound hfacts hd ha1' hb1' ha2 hb2
    | none =>
        rw [hd] at hs
        cases hu : unwrapOddBit2 facts c1' w1' a1' b1' with
        | none => rw [hu] at hs; cases hs
        | some res =>
            rcases res with ⟨co, wo, ao, bo⟩
            rw [hu] at hs
            obtain ⟨vao, vbo, hao, hbo, heq⟩ := unwrapOddBit2_sound hfacts hu ha1' hb1'
            have hdir := checkCondRelationDirect_sound hfacts hs hao hbo ha2 hb2
            rw [heq] at hdir; exact hdir
  unfold checkCondRelation at hrel
  dsimp only at hrel
  split at hrel
  · rename_i n hn; cases hrel
    exact hstep ha1 hb1 hn
  · cases hu : unwrapSelectCond c1 w1 a1 b1 with
    | none => rw [hu] at hrel; cases hrel
    | some res =>
        rcases res with ⟨cs, ws, as_, bs⟩
        rw [hu] at hrel
        obtain ⟨vas, vbs, has, hbs, heq⟩ := unwrapSelectCond_sound hu ha1 hb1
        have hst := hstep has hbs hrel
        rw [heq] at hst; exact hst

private theorem checkOvfCondEquiv_sound {ρ₁₀ : Env} {ctx : Word} {snaps : MemSnaps}
    {facts : List PFact} (hfacts : FactsHold ρ₁₀ ctx snaps facts)
    {o1 o2 : Ovf} {ea1 eb1 ea2 eb2 : SymExpr} {va1 vb1 va2 vb2 : Word}
    (hck : checkOvfCondEquiv facts o1 ea1 eb1 o2 ea2 eb2 = true)
    (ha1 : ea1.eval ρ₁₀ ctx snaps = some va1) (hb1 : eb1.eval ρ₁₀ ctx snaps = some vb1)
    (ha2 : ea2.eval ρ₁₀ ctx snaps = some va2) (hb2 : eb2.eval ρ₁₀ ctx snaps = some vb2) :
    o1 = o2 ∧ (o1.eval va1 vb1).2 = (o2.eval va2 vb2).2 := by
  unfold checkOvfCondEquiv at hck
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hck
  obtain ⟨rfl, hcases⟩ := hck
  refine ⟨rfl, ?_⟩
  rcases hcases with ⟨heqa, heqb⟩ | ⟨⟨⟨rfl, hpa⟩, hpb⟩, hpair⟩
  · have ha_eq := exprEquivFacts_sound hfacts heqa ha1 ha2
    have hb_eq := exprEquivFacts_sound hfacts heqb hb1 hb2
    rw [ha_eq, hb_eq]
  · have hev1 : va1 &&& 1 = 0 := by have h := parityOf_sound hfacts ha1; rw [hpa] at h; exact h
    have hev2 : vb1 &&& 1 = 0 := by have h := parityOf_sound hfacts hb1; rw [hpb] at h; exact h
    rcases hpair with ⟨heqa, heqb⟩ | ⟨heqa, heqb⟩
    · have ha_eq := exprEquivFacts_sound hfacts heqa (mkAdd64_sound ha1 rfl) ha2
      have hb_eq := exprEquivFacts_sound hfacts heqb hb1 hb2
      rw [← ha_eq, ← hb_eq]
      exact (addC_even_ovf_eq hev1 hev2).symm
    · have ha_eq := exprEquivFacts_sound hfacts heqa ha1 ha2
      have hb_eq := exprEquivFacts_sound hfacts heqb (mkAdd64_sound hb1 rfl) hb2
      rw [← ha_eq, ← hb_eq]
      have hcomm : ∀ x y : Word, (Ovf.addC.eval x y).2 = (Ovf.addC.eval y x).2 := by
        intro x y; simp only [Ovf.eval, UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
        have hx : x.toNat < 2 ^ 64 := x.toNat_lt_size
        have hy : y.toNat < 2 ^ 64 := y.toNat_lt_size
        by_cases h : x.toNat + y.toNat < 2 ^ 64
        · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
          simp only [decide_eq_decide]; omega
        · have hm1 : (x.toNat + y.toNat) % 2 ^ 64 = x.toNat + y.toNat - 2 ^ 64 := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          have hm2 : (y.toNat + x.toNat) % 2 ^ 64 = y.toNat + x.toNat - 2 ^ 64 := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [hm1, hm2]; simp only [decide_eq_decide]; omega
      rw [hcomm va1 (vb1 + 1), addC_even_ovf_eq hev2 hev1, hcomm vb1 va1]

/-! ## Helper: entering a callee function preserves `TopFrameRel` -/

private theorem enter_rel {p q : Program} {plan : ProgPlan}
    (hp : checkProgramWithPlan p q plan = true)
    {g : FunId} {vals : List Word} {callee₁ : Frame} {mem : X86.Memory} {ctx : Word}
    (he₁ : enter p g vals = some callee₁) :
    ∃ callee₂, enter q g vals = some callee₂ ∧
      TopFrameRel p q plan ctx mem callee₁ mem callee₂ := by
  simp only [enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at he₁
  obtain ⟨F, hF, ρ, hbp, rfl⟩ := he₁
  rcases checkProgramWithPlan_func hp hF with ⟨hG, _⟩ | ⟨G, fplan, hG, hFP, hfunc⟩
  · exact ⟨{ fn := g, label := 0, pos := 0, env := ρ, dsts := [] },
      by simp [enter, hG, hbp], .inr ⟨rfl, rfl, by rw [hF, hG]⟩⟩
  · obtain ⟨hpar, _, fb0, gb0, bp0, hfb0, hgb0, hbp0, htgt0, hentry⟩ := checkFuncWithPlan_entry hfunc
    have hbp2 : bindParams {} G.params vals = some ρ := by rw [hpar]; exact hbp
    have hinv := checkEntryInv_sound (ctx := ctx) hentry hbp
    have htop := topFrameRel_atBlock (mem := mem) hp hF hG hFP hbp0 hinv
    rw [htgt0] at htop
    exact ⟨{ fn := g, label := 0, pos := 0, env := ρ, dsts := [] },
      by simp [enter, hG, hbp2], htop⟩

/-! ## Master forward simulation theorem (`checkProgramWithPlan_forward`) -/

private theorem checkSeg_sync {p q : Program} {plan : ProgPlan}
    {ctx : Word} {mem₁ mem₂ : X86.Memory} {fr₁ fr₂ : Frame} {rest₂ : List Frame}
    (htop : TopFrameData p q plan ctx mem₁ fr₁ mem₂ fr₂)
    (hrem : htop.rem₁ = []) :
    ∃ ρ₂' snaps,
      Sem.Star (semStep q) { mem := mem₂, ctx, stack := fr₂ :: rest₂ } 0
        (atState mem₁ ctx fr₁.fn htop.bp.target (htop.pre₂.length + htop.seg₂.length) ρ₂' rest₂) ∧
      SegInv htop.st htop.ρ₁₀ mem₂ fr₁.env mem₁ ρ₂' mem₁ ctx snaps := by
  have hchk := htop.hCheckSeg
  rw [hrem, List.append_nil] at hchk
  obtain ⟨ρ₂', snaps, hx2, hseg⟩ := checkSeg_sound htop.hInv hchk htop.hDone₁
  have hst := star_stmts (p := q) (F := htop.G) (B := htop.B₂) (fn := fr₁.fn) (L := htop.bp.target)
    (dsts := []) (rest := rest₂) (pre := htop.pre₂) (ss := htop.seg₂) (post := callsTail htop.calls₂)
    htop.hG htop.hB₂ htop.hBody₂ htop.hNoCall₂ hx2
  have hfr2_eq : fr₂ = { fn := fr₁.fn, label := htop.bp.target, pos := htop.pre₂.length, env := fr₂.env, dsts := [] } := by
    cases fr₂; simp only [Frame.mk.injEq]
    exact ⟨htop.fnEq, htop.hL', htop.hPos₂, trivial, htop.dsts2⟩
  rw [← hfr2_eq] at hst
  exact ⟨ρ₂', snaps, hst, hseg⟩

private theorem star_congr_left {q : Program} {s s' t : State} {c : Nat}
    (heq : s = s') (h : Sem.Star (semStep q) s' c t) : Sem.Star (semStep q) s c t :=
  heq ▸ h

private theorem takeEdge_not_nonstuck {F : Func} {s : State} {fr : Frame} {rest : List Frame}
    {ρ : Env} {e : Edge} {r : Sem.Result (List Word × X86.Memory)}
    (hfin : Sem.Final (takeEdge F s fr rest ρ e).toSem r) (hne : r ≠ .stuck) : False := by
  unfold takeEdge at hfin
  cases hev : evalArgs ρ e.args with
  | none => rw [hev] at hfin; dsimp only [Step.toSem] at hfin; cases hfin; exact absurd rfl hne
  | some vals =>
      cases hblk : F.blocks[e.target]? with
      | none => rw [hev, hblk] at hfin; dsimp only [Step.toSem] at hfin; cases hfin; exact absurd rfl hne
      | some target =>
          rw [hev, hblk] at hfin; dsimp only at hfin
          cases hbp : bindParams ρ target.params vals with
          | none => rw [hbp] at hfin; dsimp only [Step.toSem] at hfin; cases hfin; exact absurd rfl hne
          | some ρ' => rw [hbp] at hfin; dsimp only [Step.toSem] at hfin; cases hfin

private theorem resumeCaller_rel {p q : Program} {plan : ProgPlan}
    {mem : X86.Memory} {ctx : Word} {caller₁ caller₂ : Frame} {vals : List Word} {ρc₁ : Env}
    (hcal : CallerFrameRel p q plan ctx caller₁ caller₂)
    (hbp1 : bindParams caller₁.env caller₁.dsts vals = some ρc₁) :
    ∃ ρc₂, bindParams caller₂.env caller₂.dsts vals = some ρc₂ ∧
      TopFrameRel p q plan ctx mem
        { fn := caller₁.fn, label := caller₁.label, pos := caller₁.pos, env := ρc₁, dsts := [] }
        mem
        { fn := caller₂.fn, label := caller₂.label, pos := caller₂.pos, env := ρc₂, dsts := [] } := by
  rcases hcal with ⟨⟨hcal⟩⟩ | ⟨rfl, hfnSame⟩
  · have hlen_v := bindParams_length_eq hbp1
    obtain ⟨ρc₂, hbp2⟩ := bindParams_exists (ρ := caller₂.env) (ps := caller₂.dsts) (vs := vals)
      (by rw [hcal.dstsEq]; exact hlen_v)
    have hinv_res := hcal.hResume vals ρc₁ ρc₂ hbp1 hbp2
    exact ⟨ρc₂, hbp2, .inl
      ⟨{ fnEq := hcal.fnEq, dsts1 := rfl, dsts2 := rfl
         F := hcal.F, G := hcal.G, fplan := hcal.fplan, bp := hcal.bp
         B₁ := hcal.B₁, B₂ := hcal.B₂
         hF := hcal.hF, hG := hcal.hG, hFP := hcal.hFP, hBP := hcal.hBP
         hL' := hcal.hL', hB₁ := hcal.hB₁, hB₂ := hcal.hB₂
         pre₁ := hcal.pre₁, done₁ := [], rem₁ := hcal.seg₁, calls₁ := hcal.calls₁
         pre₂ := hcal.pre₂, seg₂ := hcal.seg₂, calls₂ := hcal.calls₂
         inv := hcal.postInv, afterInvs := hcal.afterInvs
         hBody₁ := by simpa using hcal.hBody₁
         hBody₂ := hcal.hBody₂
         hNoCall₁ := by simpa using hcal.hNoCall₁
         hNoCall₂ := hcal.hNoCall₂
         hCallsNoCall₁ := hcal.hCallsNoCall₁
         hCallsNoCall₂ := hcal.hCallsNoCall₂
         hPos₁ := by simpa using hcal.hPos₁
         hPos₂ := hcal.hPos₂
         ρ₁₀ := ρc₁, hInv := hinv_res, hDone₁ := rfl
         st := hcal.st, hCheckSeg := by simpa using hcal.hCheckSeg
         hCheckRest := hcal.hCheckRest }⟩⟩
  · exact ⟨ρc₁, hbp1, .inr ⟨rfl, rfl, hfnSame⟩⟩

private theorem takeEdge_same_rest {F : Func} {mem : X86.Memory} {ctx : Word} {fr : Frame}
    {rest₁ rest₂ : List Frame} {ρ : Env} {e : Edge} {s₁' : State} {b : Bool}
    (hte : takeEdge F { mem, ctx, stack := fr :: rest₁ } fr rest₁ ρ e = .next s₁' b) :
    ∃ nextFr, s₁' = { mem, ctx, stack := nextFr :: rest₁ } ∧ nextFr.fn = fr.fn ∧
      takeEdge F { mem, ctx, stack := fr :: rest₂ } fr rest₂ ρ e =
        .next { mem, ctx, stack := nextFr :: rest₂ } b := by
  unfold takeEdge at hte ⊢
  cases hev : evalArgs ρ e.args with
  | none => rw [hev] at hte; cases hte
  | some vs =>
      cases hblk : F.blocks[e.target]? with
      | none => rw [hev, hblk] at hte; cases hte
      | some tgt =>
          rw [hev, hblk] at hte; dsimp only at hte
          cases hbp : bindParams ρ tgt.params vs with
          | none => rw [hbp] at hte; cases hte
          | some ρ' =>
              rw [hbp] at hte; simp only [Step.next.injEq] at hte
              obtain ⟨rfl, rfl⟩ := hte
              exact ⟨{ fn := fr.fn, label := e.target, pos := 0, env := ρ', dsts := fr.dsts },
                rfl, rfl, by simp [hbp]⟩

/-- `step` at a block terminator (`fr.pos` past the body), as a `match` on `B.term`. -/
private theorem step_at_term' {p : Program} {F : Func} {B : Block} {mem : X86.Memory} {ctx : Word}
    {fr : Frame} {rest : List Frame}
    (hF : p.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B)
    (hlt : ¬ fr.pos < B.body.size) :
    step p { mem, ctx, stack := fr :: rest } =
      match B.term with
      | .jump e => takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env e
      | .br c w a b' t f =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
              takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env
                (if c.holds w va vb then t else f)
          | _, _ => .stuck
      | .brOvf o x a b' ok ovf =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
              let (r, carry) := o.eval va vb
              takeEdge F { mem, ctx, stack := fr :: rest } fr rest
                (fr.env.insert x r) (if carry then ovf else ok)
          | _, _ => .stuck
      | .ret ras =>
          match evalArgs fr.env ras with
          | none => .stuck
          | some vals =>
              match rest with
              | [] => .done vals mem
              | c :: rest' =>
                  match bindParams c.env c.dsts vals with
                  | some ρ => .next { mem, ctx, stack := { c with env := ρ, dsts := [] } :: rest' } false
                  | none => .stuck
      | .tail g tas =>
          match evalArgs fr.env tas >>= enter p g with
          | some calleeF => .next { mem, ctx, stack := calleeF :: rest } true
          | none => .stuck
      | .fail r => .fail r
      | .trap => .trap := by
  unfold step; dsimp only; rw [hF]; dsimp only; rw [hB]; simp only [hlt, ↓reduceDIte]
  cases B.term with
  | jump _ | fail _ | trap => rfl
  | br _ _ a b' _ _ | brOvf _ _ a b' _ _ =>
      cases a.eval fr.env <;> cases b'.eval fr.env <;> rfl
  | ret ras =>
      cases evalArgs fr.env ras with
      | none => rfl
      | some vals =>
          cases rest with
          | nil => rfl
          | cons c rest' => cases bindParams c.env c.dsts vals <;> rfl
  | tail g tas =>
      cases evalArgs fr.env tas >>= enter p g <;> rfl

/-- **Forward diagram for `checkProgramWithPlan`**: every `next` step and non-stuck
`final` step of `p` is matched by `q` (or `q` fails with a resource error). -/
theorem checkProgramWithPlan_forward {p q : Program} {plan : ProgPlan}
    (hp : checkProgramWithPlan p q plan = true) :
    Sem.Forward (semStep p) (semStep q) Eq (StateRel p q plan) where
  next := by
    intro s₁ s₁' s₂ b hrel hstep
    obtain ⟨hctx, hstack⟩ := hrel
    cases hs1 : s₁.stack with
    | nil => rw [hs1] at hstack; cases hstack
    | cons fr₁ rest₁ =>
        cases hs2 : s₂.stack with
        | nil => rw [hs1, hs2] at hstack; cases hstack
        | cons fr₂ rest₂ =>
            rw [hs1, hs2] at hstack
            obtain ⟨htopRel, hcallers⟩ := hstack
            have hstep1 : step p s₁ = .next s₁' b := semStep_next.1 hstep
            have hs1_eq : s₁ = { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ } := by
              cases s₁; cases hs1; rfl
            have hs2_eq : s₂ = { mem := s₂.mem, ctx := s₁.ctx, stack := fr₂ :: rest₂ } := by
              cases s₂; cases hs2; cases hctx; rfl
            rcases htopRel with ⟨⟨htop⟩⟩ | ⟨hmemEq, hfrEq, hfnSame⟩
            rotate_left
            · -- Identical unchanged function (`p.funcs[fr₁.fn]? = q.funcs[fr₁.fn]?`)
              rw [hs1_eq] at hstep1
              have hs2_eq' : s₂ = { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₂ } := by
                rw [hs2_eq, ← hmemEq, ← hfrEq]
              unfold step at hstep1; dsimp only at hstep1
              cases hF : p.funcs[fr₁.fn]? with
              | none => rw [hF] at hstep1; cases hstep1
              | some F =>
                  have hG : q.funcs[fr₁.fn]? = some F := hfnSame.symm.trans hF
                  rw [hF] at hstep1; dsimp only at hstep1
                  cases hB : F.blocks[fr₁.label]? with
                  | none => rw [hB] at hstep1; cases hstep1
                  | some B =>
                      rw [hB] at hstep1; dsimp only at hstep1
                      by_cases hlt : fr₁.pos < B.body.size
                      · simp only [hlt, ↓reduceDIte] at hstep1
                        cases hst : B.body[fr₁.pos] with
                        | assign x r | limb r1 r2 op | store w m a =>
                            rw [hst] at hstep1; dsimp only at hstep1; rw [← hst] at hstep1
                            cases hex : (B.body[fr₁.pos]).exec fr₁.env s₁.mem s₁.ctx with
                            | none => rw [hex] at hstep1; cases hstep1
                            | some res =>
                                obtain ⟨ρ', mem'⟩ := res
                                rw [hex] at hstep1; simp only [Step.next.injEq] at hstep1
                                obtain ⟨rfl, rfl⟩ := hstep1
                                have hstep2 : step q s₂ = .next { mem := mem', ctx := s₁.ctx, stack := { fr₁ with pos := fr₁.pos + 1, env := ρ' } :: rest₂ } false := by
                                  rw [hs2_eq']; unfold step; simp only [hG, hB, hlt, ↓reduceDIte]
                                  rw [hst]; dsimp only; rw [← hst, hex]
                                exact .inl ⟨0, _, star_of_step hstep2, Nat.le_refl _, rfl, .inr ⟨rfl, rfl, hfnSame⟩, hcallers⟩
                        | call rs g as =>
                            rw [hst] at hstep1; dsimp only at hstep1
                            cases hev : evalArgs fr₁.env as with
                            | none => rw [hev] at hstep1; cases hstep1
                            | some vals =>
                                rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                                cases hent1 : enter p g vals with
                                | none => rw [hent1] at hstep1; cases hstep1
                                | some callee₁ =>
                                    rw [hent1] at hstep1; simp only [Step.next.injEq] at hstep1
                                    obtain ⟨rfl, rfl⟩ := hstep1
                                    obtain ⟨callee₂, hent2, htop_c⟩ := enter_rel hp (mem := s₁.mem) (ctx := s₁.ctx) hent1
                                    have hstep2 : step q s₂ = .next { mem := s₁.mem, ctx := s₁.ctx, stack := callee₂ :: { fr₁ with pos := fr₁.pos + 1, dsts := rs } :: rest₂ } true := by
                                      rw [hs2_eq']; unfold step; simp only [hG, hB, hlt, ↓reduceDIte, hst, hev, Option.bind_eq_bind, Option.bind_some, hent2]
                                    exact .inl ⟨1, _, star_of_step hstep2, Nat.le_refl _, rfl, htop_c, .cons (.inr ⟨rfl, hfnSame⟩) hcallers⟩
                      · simp only [hlt, ↓reduceDIte] at hstep1
                        have hstep2_term := (congrArg (step q) hs2_eq').trans
                          (step_at_term' (p := q) (F := F) (B := B) (mem := s₁.mem) (ctx := s₁.ctx)
                            (fr := fr₁) (rest := rest₂) hG hB hlt)
                        cases ht : B.term with
                        | jump e =>
                            rw [ht] at hstep1 hstep2_term; dsimp only at hstep1 hstep2_term
                            obtain ⟨nFr, rfl, hfnN, hte2⟩ := takeEdge_same_rest (rest₂ := rest₂) hstep1
                            exact .inl ⟨b.toNat, _, star_of_step (hstep2_term.trans hte2), Nat.le_refl _, rfl,
                              .inr ⟨rfl, rfl, by rw [hfnN]; exact hfnSame⟩, hcallers⟩
                        | br cond w a b' t f =>
                            rw [ht] at hstep1 hstep2_term; dsimp only at hstep1 hstep2_term
                            cases ha : a.eval fr₁.env with
                            | none => rw [ha] at hstep1; cases hstep1
                            | some va =>
                                cases hb : b'.eval fr₁.env with
                                | none => rw [ha, hb] at hstep1; cases hstep1
                                | some vb =>
                                    rw [ha, hb] at hstep1 hstep2_term; dsimp only at hstep1 hstep2_term
                                    obtain ⟨nFr, rfl, hfnN, hte2⟩ := takeEdge_same_rest (rest₂ := rest₂) hstep1
                                    exact .inl ⟨b.toNat, _, star_of_step (hstep2_term.trans hte2), Nat.le_refl _, rfl,
                                      .inr ⟨rfl, rfl, by rw [hfnN]; exact hfnSame⟩, hcallers⟩
                        | brOvf op dst a b' ok ovf =>
                            rw [ht] at hstep1 hstep2_term; dsimp only at hstep1 hstep2_term
                            cases ha : a.eval fr₁.env with
                            | none => rw [ha] at hstep1; cases hstep1
                            | some va =>
                                cases hb : b'.eval fr₁.env with
                                | none => rw [ha, hb] at hstep1; cases hstep1
                                | some vb =>
                                    rw [ha, hb] at hstep1 hstep2_term; dsimp only at hstep1 hstep2_term
                                    obtain ⟨nFr, rfl, hfnN, hte2⟩ := takeEdge_same_rest (rest₂ := rest₂) hstep1
                                    exact .inl ⟨b.toNat, _, star_of_step (hstep2_term.trans hte2), Nat.le_refl _, rfl,
                                      .inr ⟨rfl, rfl, by rw [hfnN]; exact hfnSame⟩, hcallers⟩
                        | ret args =>
                            rw [ht] at hstep1 hstep2_term; dsimp only at hstep1 hstep2_term
                            cases hev : evalArgs fr₁.env args with
                            | none => rw [hev] at hstep1; cases hstep1
                            | some vs =>
                                rw [hev] at hstep1 hstep2_term; dsimp only at hstep1 hstep2_term
                                cases rest₁ with
                                | nil => cases hstep1
                                | cons c₁ r₁ =>
                                    cases hcallers with
                                    | cons hcal hcallers' =>
                                        rename_i c₂ r₂
                                        dsimp only at hstep1 hstep2_term
                                        cases hbp1 : bindParams c₁.env c₁.dsts vs with
                                        | none => rw [hbp1] at hstep1; cases hstep1
                                        | some ρc₁ =>
                                            rw [hbp1] at hstep1; simp only [Step.next.injEq] at hstep1
                                            obtain ⟨rfl, rfl⟩ := hstep1
                                            obtain ⟨ρc₂, hbp2, htop_res⟩ := resumeCaller_rel (mem := s₁.mem) hcal hbp1
                                            rw [hbp2] at hstep2_term
                                            exact .inl ⟨0, _, star_of_step hstep2_term, Nat.le_refl _, rfl, htop_res, hcallers'⟩
                        | tail g args =>
                            rw [ht] at hstep1 hstep2_term; dsimp only at hstep1 hstep2_term
                            cases hev : evalArgs fr₁.env args with
                            | none => rw [hev] at hstep1; cases hstep1
                            | some vs =>
                                rw [hev] at hstep1 hstep2_term; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1 hstep2_term
                                cases hent1 : enter p g vs with
                                | none => rw [hent1] at hstep1; cases hstep1
                                | some callee₁ =>
                                    rw [hent1] at hstep1; simp only [Step.next.injEq] at hstep1
                                    obtain ⟨rfl, rfl⟩ := hstep1
                                    obtain ⟨callee₂, hent2, htop_c⟩ := enter_rel hp (mem := s₁.mem) (ctx := s₁.ctx) hent1
                                    rw [hent2] at hstep2_term
                                    exact .inl ⟨1, _, star_of_step hstep2_term, Nat.le_refl _, rfl, htop_c, hcallers⟩
                        | fail _ => rw [ht] at hstep1; cases hstep1
                        | trap => rw [ht] at hstep1; cases hstep1
            -- Planned function (`htop : TopFrameData`): case split on remaining statements
            cases hrem : htop.rem₁ with
            | cons s rem₁' =>
                -- Case A: `fr₁` steps a local non-call statement; `fr₂` takes 0 steps!
                have hpos_lt : fr₁.pos < htop.B₁.body.size := by
                  have := congrArg List.length htop.hBody₁
                  simp only [Array.length_toList, List.length_append, hrem, List.length_cons] at this
                  have := htop.hPos₁; omega
                have hget : htop.B₁.body[fr₁.pos] = s := by
                  have hopt : htop.B₁.body.toList[fr₁.pos]? = some s := by
                    rw [htop.hBody₁, hrem, htop.hPos₁]
                    simp [List.append_assoc]
                  simp only [Array.getElem?_toList, Array.getElem?_eq_some_iff] at hopt
                  exact hopt.2
                have hnc_s : s.isCall = false := htop.hNoCall₁ s (by simp [hrem])
                rw [hs1_eq] at hstep1
                unfold step at hstep1
                simp only [htop.hF, htop.hB₁, hpos_lt, ↓reduceDIte, hget] at hstep1
                cases hsc : s with
                | call _ _ _ => rw [hsc] at hnc_s; cases hnc_s
                | assign _ _ | limb _ _ _ | store _ _ _ =>
                    rw [hsc] at hstep1; dsimp only at hstep1; rw [← hsc] at hstep1
                    cases hex : s.exec fr₁.env s₁.mem s₁.ctx with
                    | none => rw [hex] at hstep1; cases hstep1
                    | some res =>
                        obtain ⟨ρ₁', mem₁'⟩ := res
                        rw [hex] at hstep1
                        simp only [Step.next.injEq] at hstep1
                        obtain ⟨rfl, rfl⟩ := hstep1
                        have hdone' : execList htop.ρ₁₀ s₂.mem s₁.ctx (htop.done₁ ++ [s]) = some (ρ₁', mem₁') :=
                          execList_snoc htop.hDone₁ hex
                        have hconcat : (htop.done₁ ++ [s]) ++ rem₁' = htop.done₁ ++ htop.rem₁ := by
                          rw [hrem, List.append_assoc]; rfl
                        refine .inl ⟨0, s₂, .refl _, Nat.le_refl _, hctx, ?_⟩
                        rw [hs2]
                        refine ⟨?_, hcallers⟩
                        exact .inl
                          ⟨{ htop with
                             done₁ := htop.done₁ ++ [s]
                             rem₁ := rem₁'
                             hBody₁ := by rw [hconcat]; exact htop.hBody₁
                             hNoCall₁ := by rw [hconcat]; exact htop.hNoCall₁
                             hPos₁ := by simp [htop.hPos₁, Nat.add_assoc]
                             hDone₁ := hdone'
                             hCheckSeg := by rw [hconcat]; exact htop.hCheckSeg }⟩
            | nil =>
                -- Sync target frame `fr₂` across `seg₂` in 0 charges!
                obtain ⟨ρ₂', snaps, hstar_seg, hseg⟩ := checkSeg_sync (rest₂ := rest₂) htop hrem
                cases hcalls1 : htop.calls₁ with
                | cons c₁ restCalls1 =>
                    -- Case B: `fr₁` is at `.call c₁.rs c₁.fn c₁.args`!
                    have hrest_chk := htop.hCheckRest
                    rw [hcalls1] at hrest_chk
                    cases hcalls2 : htop.calls₂ with
                    | nil => rw [hcalls2] at hrest_chk; cases hrest_chk
                    | cons c₂ restCalls2 =>
                        cases hinvs : htop.afterInvs with
                        | nil => rw [hcalls2, hinvs] at hrest_chk; cases hrest_chk
                        | cons postInv restInvs =>
                            rw [hcalls2, hinvs] at hrest_chk
                            simp only [checkCallsAndTerm, Bool.and_eq_true, beq_iff_eq] at hrest_chk
                            obtain ⟨⟨⟨⟨hfn_eq, hrs_eq⟩, hargs_eq⟩, hafter_chk⟩, hnext_chk⟩ := hrest_chk
                            cases hcs_next : checkSeg postInv c₁.after c₂.after with
                            | none => rw [hcs_next] at hnext_chk; cases hnext_chk
                            | some stNext =>
                                rw [hcs_next] at hnext_chk
                                -- Decode source `.call` step
                                have hpos1_lt : fr₁.pos < htop.B₁.body.size := by
                                  have := congrArg List.length htop.hBody₁
                                  simp only [Array.length_toList, List.length_append, hrem, List.append_nil,
                                    hcalls1, callsTail, List.length_cons] at this
                                  have := htop.hPos₁; omega
                                have hget1 : htop.B₁.body[fr₁.pos] = .call c₁.rs c₁.fn c₁.args := by
                                  have hopt : htop.B₁.body.toList[fr₁.pos]? = some (.call c₁.rs c₁.fn c₁.args) := by
                                    rw [htop.hBody₁, hrem, List.append_nil, hcalls1, callsTail, htop.hPos₁]
                                    simp [List.append_assoc]
                                  simp only [Array.getElem?_toList, Array.getElem?_eq_some_iff] at hopt
                                  exact hopt.2
                                rw [hs1_eq] at hstep1
                                unfold step at hstep1
                                simp only [htop.hF, htop.hB₁, hpos1_lt, ↓reduceDIte, hget1,
                                  Option.bind_eq_bind] at hstep1
                                cases hev1 : evalArgs fr₁.env c₁.args with
                                | none => rw [hev1] at hstep1; cases hstep1
                                | some vals =>
                                    rw [hev1] at hstep1
                                    simp only [Option.bind_some] at hstep1
                                    cases hent1 : enter p c₁.fn vals with
                                    | none => rw [hent1] at hstep1; cases hstep1
                                    | some callee₁ =>
                                        rw [hent1] at hstep1
                                        simp only [Step.next.injEq] at hstep1
                                        obtain ⟨rfl, rfl⟩ := hstep1
                                        have hev2 := checkArgsEquiv_sound hseg hargs_eq hev1
                                        obtain ⟨callee₂, hent2, htop_callee⟩ := enter_rel hp (mem := s₁.mem) (ctx := s₁.ctx) hent1
                                        -- Step target `.call c₂.rs c₂.fn c₂.args`
                                        have hpos2_lt : htop.pre₂.length + htop.seg₂.length < htop.B₂.body.size := by
                                          have := congrArg List.length htop.hBody₂
                                          simp only [Array.length_toList, List.length_append, hcalls2,
                                            callsTail, List.length_cons] at this
                                          omega
                                        have hget2 : htop.B₂.body[htop.pre₂.length + htop.seg₂.length] = .call c₂.rs c₂.fn c₂.args := by
                                          have hopt : htop.B₂.body.toList[htop.pre₂.length + htop.seg₂.length]? =
                                              some (.call c₂.rs c₂.fn c₂.args) := by
                                            rw [htop.hBody₂, hcalls2, callsTail]
                                            simp [List.append_assoc]
                                          simp only [Array.getElem?_toList, Array.getElem?_eq_some_iff] at hopt
                                          exact hopt.2
                                        have hst_call := step_call (p := q) (F := htop.G) (B := htop.B₂)
                                          (fr := { fn := fr₁.fn, label := htop.bp.target, pos := htop.pre₂.length + htop.seg₂.length, env := ρ₂', dsts := [] })
                                          (rest := rest₂) (mem := s₁.mem) (ctx := s₁.ctx)
                                          htop.hG htop.hB₂ hpos2_lt hget2 hev2 (by rw [← hfn_eq]; exact hent2)
                                        have hstar_all := (star_congr_left hs2_eq hstar_seg).trans (star_of_step hst_call)
                                        have hcaller_new : CallerFrameRel p q plan s₁.ctx
                                            { fr₁ with pos := fr₁.pos + 1, dsts := c₁.rs }
                                            { fn := fr₁.fn, label := htop.bp.target,
                                              pos := htop.pre₂.length + htop.seg₂.length + 1,
                                              env := ρ₂', dsts := c₂.rs } := .inl
                                          ⟨{ fnEq := rfl, dstsEq := hrs_eq.symm
                                             F := htop.F, G := htop.G, fplan := htop.fplan, bp := htop.bp
                                             B₁ := htop.B₁, B₂ := htop.B₂
                                             hF := htop.hF, hG := htop.hG, hFP := htop.hFP, hBP := htop.hBP
                                             hL' := rfl, hB₁ := htop.hB₁, hB₂ := htop.hB₂
                                             pre₁ := htop.pre₁ ++ htop.done₁ ++ [.call c₁.rs c₁.fn c₁.args]
                                             seg₁ := c₁.after, calls₁ := restCalls1
                                             pre₂ := htop.pre₂ ++ htop.seg₂ ++ [.call c₂.rs c₂.fn c₂.args]
                                             seg₂ := c₂.after, calls₂ := restCalls2
                                             postInv, afterInvs := restInvs
                                             hBody₁ := by
                                               have hb := htop.hBody₁
                                               rw [hrem, List.append_nil, hcalls1, callsTail, reconBody_eq_append] at hb
                                               simpa [List.append_assoc] using hb
                                             hBody₂ := by
                                               have hb := htop.hBody₂
                                               rw [hcalls2, callsTail, reconBody_eq_append] at hb
                                               simpa [List.append_assoc] using hb
                                             hNoCall₁ := htop.hCallsNoCall₁ c₁ (by rw [hcalls1]; simp)
                                             hNoCall₂ := htop.hCallsNoCall₂ c₂ (by rw [hcalls2]; simp)
                                             hCallsNoCall₁ := fun c hc => htop.hCallsNoCall₁ c (by rw [hcalls1]; simp [hc])
                                             hCallsNoCall₂ := fun c hc => htop.hCallsNoCall₂ c (by rw [hcalls2]; simp [hc])
                                             hPos₁ := by simp [htop.hPos₁, Nat.add_assoc]
                                             hPos₂ := by simp [Nat.add_assoc]
                                             hResume := fun vals' ρa ρb hba hbb =>
                                               checkAfterCall_sound hseg hafter_chk hba (by rw [hrs_eq]; exact hbb)
                                             st := stNext, hCheckSeg := hcs_next, hCheckRest := hnext_chk }⟩
                                        exact .inl ⟨0 + 1, _, hstar_all, Nat.le_refl _, rfl,
                                          htop_callee, .cons hcaller_new hcallers⟩
                | nil =>
                    -- Case C: `fr₁` is at `htop.B₁.term`!
                    have hrest_chk := htop.hCheckRest
                    rw [hcalls1] at hrest_chk
                    cases hcalls2 : htop.calls₂ with
                    | cons _ _ => rw [hcalls2] at hrest_chk; cases hrest_chk
                    | nil =>
                        cases hinvs : htop.afterInvs with
                        | cons _ _ => rw [hcalls2, hinvs] at hrest_chk; cases hrest_chk
                        | nil =>
                            rw [hcalls2, hinvs] at hrest_chk
                            simp only [checkCallsAndTerm] at hrest_chk
                            have hpos1_eq : fr₁.pos = htop.B₁.body.size := by
                              have := congrArg List.length htop.hBody₁
                              simp only [Array.length_toList, List.length_append, hrem, List.append_nil,
                                hcalls1, callsTail] at this
                              rw [htop.hPos₁, this]
                            have hpos2_eq : htop.pre₂.length + htop.seg₂.length = htop.B₂.body.size := by
                              have := congrArg List.length htop.hBody₂
                              simp only [Array.length_toList, List.length_append, hcalls2, callsTail,
                                List.length_nil, Nat.add_zero] at this
                              exact this.symm
                            rw [hs1_eq, step_term htop.hF htop.hB₁ hpos1_eq] at hstep1
                            rw [hpos2_eq] at hstar_seg
                            have hstar_seg' : Sem.Star (semStep q) s₂ 0
                                (atState s₁.mem s₁.ctx fr₁.fn htop.bp.target htop.B₂.body.size ρ₂' rest₂) :=
                              star_congr_left hs2_eq hstar_seg
                            -- Helper to finish edge transitions via `checkEdge_sound`
                            have finishEdge : ∀ (e1 : Edge) (ρ1Next : Env) (srcEnv1 : Src.NatMap SymExpr)
                                (srcDef1 : Src.NatSet) (tgtEnv1 : Src.NatMap SymExpr) (fs1 : List PFact)
                                (e2 : Edge) (ρ2Next : Env),
                                (∀ x v, ρ1Next[x]? = some v → (srcLookup srcEnv1 x).eval htop.ρ₁₀ s₁.ctx snaps = some v) →
                                (∀ x, srcDef1.contains x = true → ρ1Next[x]?.isSome = true) →
                                (∀ y ey, tgtEnv1.get? y = some ey → ∃ v, ρ2Next[y]? = some v ∧ ey.eval htop.ρ₁₀ s₁.ctx snaps = some v) →
                                FactsHold htop.ρ₁₀ s₁.ctx snaps fs1 →
                                takeEdge htop.F { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ1Next e1 = .next s₁' b →
                                step q (atState s₁.mem s₁.ctx fr₁.fn htop.bp.target htop.B₂.body.size ρ₂' rest₂) =
                                  takeEdge htop.G (atState s₁.mem s₁.ctx fr₁.fn htop.bp.target htop.B₂.body.size ρ₂' rest₂)
                                    { fn := fr₁.fn, label := htop.bp.target, pos := htop.B₂.body.size, env := ρ₂', dsts := [] } rest₂ ρ2Next e2 →
                                checkEdge htop.F htop.G htop.fplan srcEnv1 srcDef1 tgtEnv1 fs1 htop.bp.target
                                  (decide (e1.target ≤ fr₁.label)) e1 e2 maxEdgeHops = true →
                                (∃ c s₂', Sem.Star (semStep q) s₂ c s₂' ∧ b.toNat ≤ c ∧ StateRel p q plan s₁' s₂') ∨
                                  Sem.Fails (semStep q) s₂ := by
                              intro e1 ρ1Next srcEnv1 srcDef1 tgtEnv1 fs1 e2 ρ2Next hsrc1 hdef1 htgt1 hfs1 hte1 hst2 hce
                              unfold takeEdge at hte1
                              cases hev1 : evalArgs ρ1Next e1.args with
                              | none => rw [hev1] at hte1; cases hte1
                              | some vals1 =>
                                  cases hftgt : htop.F.blocks[e1.target]? with
                                  | none => rw [hev1, hftgt] at hte1; cases hte1
                                  | some fTgt =>
                                      rw [hev1, hftgt] at hte1; dsimp only at hte1
                                      cases hbp1 : bindParams ρ1Next fTgt.params vals1 with
                                      | none => rw [hbp1] at hte1; cases hte1
                                      | some ρ1' =>
                                          rw [hbp1] at hte1
                                          simp only [Step.next.injEq] at hte1
                                          obtain ⟨rfl, rfl⟩ := hte1
                                          rcases checkEdge_sound hp htop.hF htop.hG htop.hFP hsrc1 hdef1 hftgt hev1 hbp1
                                              maxEdgeHops tgtEnv1 fs1 htop.bp.target htop.B₂.body.size
                                              (decide (e1.target ≤ fr₁.label)) e2 ρ₂' ρ2Next htgt1 hfs1 hce hst2 with
                                            ⟨c2, ρ2', bp', _, hst_edge, hc2, htop'⟩ | hfail
                                          · have hfr1' : { fr₁ with label := e1.target, pos := 0, env := ρ1' } =
                                                { fn := fr₁.fn, label := e1.target, pos := 0, env := ρ1', dsts := [] } := by
                                              cases fr₁; simp only [Frame.mk.injEq]; exact ⟨trivial, trivial, trivial, trivial, htop.dsts1⟩
                                            rw [hfr1']
                                            exact .inl ⟨0 + c2, _, hstar_seg'.trans hst_edge, by omega, rfl, htop', hcallers⟩
                                          · exact .inr (fails_of_star_fails hstar_seg' hfail)
                            -- Dispatch on `(htop.B₁.term, htop.B₂.term)`
                            cases ht1 : htop.B₁.term <;> cases ht2 : htop.B₂.term <;>
                              rw [ht1, ht2] at hrest_chk <;> try (simp [checkTerm] at hrest_chk; done)
                            · -- jump vs jump
                              rename_i e1 e2
                              simp only [ht1] at hstep1
                              simp only [checkTerm] at hrest_chk
                              have hst2 := step_jump (p := q) (F := htop.G) (B := htop.B₂)
                                (fr := { fn := fr₁.fn, label := htop.bp.target, pos := htop.B₂.body.size, env := ρ₂', dsts := [] })
                                (rest := rest₂) (mem := s₁.mem) (ctx := s₁.ctx) htop.hG htop.hB₂ rfl ht2
                              exact finishEdge e1 fr₁.env htop.st.srcEnv htop.st.srcDef htop.st.tgtEnv htop.st.facts
                                e2 ρ₂' hseg.srcEnvEval hseg.srcDefOk hseg.tgtEnvEval hseg.factsHold hstep1 hst2 hrest_chk
                            · -- jump vs br (hoisted `.fail` guard in existing preheader)
                              rename_i e1 gc gw ga gb gt gf
                              simp only [ht1] at hstep1
                              simp only [checkTerm] at hrest_chk
                              cases hea : evalTgtArg htop.st.tgtEnv ga with
                              | none => rw [hea] at hrest_chk; cases hrest_chk
                              | some ea =>
                                  cases heb : evalTgtArg htop.st.tgtEnv gb with
                                  | none => rw [hea, heb] at hrest_chk; cases hrest_chk
                                  | some eb =>
                                      rw [hea, heb] at hrest_chk
                                      obtain ⟨va, hva, heva⟩ := evalTgtArg_sound hseg.tgtEnvEval hea
                                      obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound hseg.tgtEnvEval heb
                                      have hst2 := step_br (p := q) (F := htop.G) (B := htop.B₂)
                                        (fr := { fn := fr₁.fn, label := htop.bp.target, pos := htop.B₂.body.size, env := ρ₂', dsts := [] })
                                        (rest := rest₂) (mem := s₁.mem) (ctx := s₁.ctx) htop.hG htop.hB₂ rfl ht2 hva hvb
                                      by_cases hgf : isFailEdge htop.G gf = true
                                      · simp only [hgf, ↓reduceIte] at hrest_chk
                                        cases hcond : gc.holds gw va vb with
                                        | false =>
                                            rw [hcond] at hst2
                                            exact .inr (fails_of_star_fails hstar_seg' (isFailEdge_fails htop.hG hgf hst2))
                                        | true =>
                                            rw [hcond] at hst2
                                            exact finishEdge e1 fr₁.env htop.st.srcEnv htop.st.srcDef htop.st.tgtEnv
                                              (addFact htop.st.facts gc gw ea eb true) gt ρ₂'
                                              hseg.srcEnvEval hseg.srcDefOk hseg.tgtEnvEval
                                              (addFact_holds hseg.factsHold heva hevb hcond) hstep1 hst2 hrest_chk
                                      · simp only [hgf, Bool.false_eq_true, ↓reduceIte] at hrest_chk
                                        by_cases hgt : isFailEdge htop.G gt = true
                                        · simp only [hgt, ↓reduceIte] at hrest_chk
                                          cases hcond : gc.holds gw va vb with
                                          | true =>
                                              rw [hcond] at hst2
                                              exact .inr (fails_of_star_fails hstar_seg' (isFailEdge_fails htop.hG hgt hst2))
                                          | false =>
                                              rw [hcond] at hst2
                                              exact finishEdge e1 fr₁.env htop.st.srcEnv htop.st.srcDef htop.st.tgtEnv
                                                (addFact htop.st.facts gc gw ea eb false) gf ρ₂'
                                                hseg.srcEnvEval hseg.srcDefOk hseg.tgtEnvEval
                                                (addFact_holds hseg.factsHold heva hevb hcond) hstep1 hst2 hrest_chk
                                        · simp [hgt] at hrest_chk
                            · -- br vs jump (folded branch)
                              rename_i c1 w1 a1 b1 t1 f1 e2
                              simp only [ht1] at hstep1
                              cases hva : a1.eval fr₁.env with
                              | none => rw [hva] at hstep1; cases hstep1
                              | some va1 =>
                                  cases hvb : b1.eval fr₁.env with
                                  | none => rw [hva, hvb] at hstep1; cases hstep1
                                  | some vb1 =>
                                      rw [hva, hvb] at hstep1; dsimp only at hstep1
                                      have hea1 := SymExpr.norm_sound (argToSym_eval hseg.srcEnvEval hva)
                                      have heb1 := SymExpr.norm_sound (argToSym_eval hseg.srcEnvEval hvb)
                                      have hst2 := step_jump (p := q) (F := htop.G) (B := htop.B₂)
                                        (fr := { fn := fr₁.fn, label := htop.bp.target, pos := htop.B₂.body.size, env := ρ₂', dsts := [] })
                                        (rest := rest₂) (mem := s₁.mem) (ctx := s₁.ctx) htop.hG htop.hB₂ rfl ht2
                                      simp only [checkTerm] at hrest_chk
                                      cases hcf : condFromFacts htop.st.facts c1 w1
                                          (argToSym (srcLookup htop.st.srcEnv) a1).norm
                                          (argToSym (srcLookup htop.st.srcEnv) b1).norm with
                                      | some r =>
                                          have hr := condFromFacts_sound hseg.factsHold hcf hea1 heb1
                                          rw [hr] at hstep1
                                          cases r <;> rw [hcf] at hrest_chk
                                          · exact finishEdge f1 fr₁.env htop.st.srcEnv htop.st.srcDef htop.st.tgtEnv htop.st.facts
                                              e2 ρ₂' hseg.srcEnvEval hseg.srcDefOk hseg.tgtEnvEval hseg.factsHold hstep1 hst2 hrest_chk
                                          · exact finishEdge t1 fr₁.env htop.st.srcEnv htop.st.srcDef htop.st.tgtEnv htop.st.facts
                                              e2 ρ₂' hseg.srcEnvEval hseg.srcDefOk hseg.tgtEnvEval hseg.factsHold hstep1 hst2 hrest_chk
                                      | none =>
                                          rw [hcf] at hrest_chk
                                          by_cases htf : (t1 == f1) = true
                                          · have htf' : t1 = f1 := by simpa using htf
                                            simp only [htf, ↓reduceIte] at hrest_chk
                                            rw [← htf', ite_self] at hstep1
                                            exact finishEdge t1 fr₁.env htop.st.srcEnv htop.st.srcDef htop.st.tgtEnv htop.st.facts
                                              e2 ρ₂' hseg.srcEnvEval hseg.srcDefOk hseg.tgtEnvEval hseg.factsHold hstep1 hst2 hrest_chk
                                          · simp [htf] at hrest_chk
                            · -- br vs br
                              rename_i c1 w1 a1 b1 t1 f1 c2 w2 a2 b2 t2 f2
                              simp only [ht1] at hstep1
                              cases hva1 : a1.eval fr₁.env with
                              | none => rw [hva1] at hstep1; cases hstep1
                              | some va1 =>
                                  cases hvb1 : b1.eval fr₁.env with
                                  | none => rw [hva1, hvb1] at hstep1; cases hstep1
                                  | some vb1 =>
                                      rw [hva1, hvb1] at hstep1; dsimp only at hstep1
                                      simp only [checkTerm] at hrest_chk
                                      cases hea2 : evalTgtArg htop.st.tgtEnv a2 with
                                      | none => rw [hea2] at hrest_chk; cases hrest_chk
                                      | some ea2 =>
                                          cases heb2 : evalTgtArg htop.st.tgtEnv b2 with
                                          | none => rw [hea2, heb2] at hrest_chk; cases hrest_chk
                                          | some eb2 =>
                                              rw [hea2, heb2] at hrest_chk; dsimp only at hrest_chk
                                              obtain ⟨va2, hva2, heva2⟩ := evalTgtArg_sound hseg.tgtEnvEval hea2
                                              obtain ⟨vb2, hvb2, hevb2⟩ := evalTgtArg_sound hseg.tgtEnvEval heb2
                                              have hea1 := SymExpr.norm_sound (argToSym_eval hseg.srcEnvEval hva1)
                                              have heb1 := SymExpr.norm_sound (argToSym_eval hseg.srcEnvEval hvb1)
                                              have hst2 := step_br (p := q) (F := htop.G) (B := htop.B₂)
                                                (fr := { fn := fr₁.fn, label := htop.bp.target, pos := htop.B₂.body.size, env := ρ₂', dsts := [] })
                                                (rest := rest₂) (mem := s₁.mem) (ctx := s₁.ctx) htop.hG htop.hB₂ rfl ht2 hva2 hvb2
                                              cases hcrel : checkCondRelation htop.st.facts c1 w1
                                                  (argToSym (srcLookup htop.st.srcEnv) a1).norm
                                                  (argToSym (srcLookup htop.st.srcEnv) b1).norm c2 w2 ea2 eb2 with
                                              | none => rw [hcrel] at hrest_chk; cases hrest_chk
                                              | some neg =>
                                                  rw [hcrel] at hrest_chk
                                                  have hc2_eq := checkCondRelation_sound hseg.factsHold hcrel hea1 heb1 heva2 hevb2
                                                  cases neg <;> simp only [Bool.and_eq_true] at hrest_chk
                                                  · -- same polarity
                                                    cases hcond : c1.holds w1 va1 vb1 with
                                                    | true =>
                                                        rw [hcond] at hstep1 hc2_eq; simp only [Bool.false_eq_true, ↓reduceIte] at hc2_eq; rw [hc2_eq] at hst2
                                                        exact finishEdge t1 fr₁.env htop.st.srcEnv htop.st.srcDef htop.st.tgtEnv
                                                          (addFact (addFact htop.st.facts c1 w1 _ _ true) c2 w2 ea2 eb2 true) t2 ρ₂'
                                                          hseg.srcEnvEval hseg.srcDefOk hseg.tgtEnvEval
                                                          (addFact_holds (addFact_holds hseg.factsHold hea1 heb1 hcond) heva2 hevb2 hc2_eq)
                                                          hstep1 hst2 hrest_chk.1
                                                    | false =>
                                                        rw [hcond] at hstep1 hc2_eq; simp only [Bool.false_eq_true, ↓reduceIte] at hc2_eq; rw [hc2_eq] at hst2
                                                        exact finishEdge f1 fr₁.env htop.st.srcEnv htop.st.srcDef htop.st.tgtEnv
                                                          (addFact (addFact htop.st.facts c1 w1 _ _ false) c2 w2 ea2 eb2 false) f2 ρ₂'
                                                          hseg.srcEnvEval hseg.srcDefOk hseg.tgtEnvEval
                                                          (addFact_holds (addFact_holds hseg.factsHold hea1 heb1 hcond) heva2 hevb2 hc2_eq)
                                                          hstep1 hst2 hrest_chk.2
                                                  · -- negated polarity
                                                    cases hcond : c1.holds w1 va1 vb1 with
                                                    | true =>
                                                        rw [hcond] at hstep1 hc2_eq; simp only [↓reduceIte, Bool.not_true] at hc2_eq; rw [hc2_eq] at hst2
                                                        exact finishEdge t1 fr₁.env htop.st.srcEnv htop.st.srcDef htop.st.tgtEnv
                                                          (addFact (addFact htop.st.facts c1 w1 _ _ true) c2 w2 ea2 eb2 false) f2 ρ₂'
                                                          hseg.srcEnvEval hseg.srcDefOk hseg.tgtEnvEval
                                                          (addFact_holds (addFact_holds hseg.factsHold hea1 heb1 hcond) heva2 hevb2 hc2_eq)
                                                          hstep1 hst2 hrest_chk.1
                                                    | false =>
                                                        rw [hcond] at hstep1 hc2_eq; simp only [↓reduceIte, Bool.not_false] at hc2_eq; rw [hc2_eq] at hst2
                                                        exact finishEdge f1 fr₁.env htop.st.srcEnv htop.st.srcDef htop.st.tgtEnv
                                                          (addFact (addFact htop.st.facts c1 w1 _ _ false) c2 w2 ea2 eb2 true) t2 ρ₂'
                                                          hseg.srcEnvEval hseg.srcDefOk hseg.tgtEnvEval
                                                          (addFact_holds (addFact_holds hseg.factsHold hea1 heb1 hcond) heva2 hevb2 hc2_eq)
                                                          hstep1 hst2 hrest_chk.2
                            · -- brOvf vs jump (folded overflow check)
                              rename_i o1 x1 a1 b1 ok1 ovf1 e2
                              simp only [ht1] at hstep1
                              cases hva1 : a1.eval fr₁.env with
                              | none => rw [hva1] at hstep1; cases hstep1
                              | some va1 =>
                                  cases hvb1 : b1.eval fr₁.env with
                                  | none => rw [hva1, hvb1] at hstep1; cases hstep1
                                  | some vb1 =>
                                      rw [hva1, hvb1] at hstep1
                                      have hea1 := SymExpr.norm_sound (argToSym_eval hseg.srcEnvEval hva1)
                                      have heb1 := SymExpr.norm_sound (argToSym_eval hseg.srcEnvEval hvb1)
                                      have hres1 := ovfToSym_eval (o := o1) hea1 heb1
                                      have hsrc' : ∀ x v, (fr₁.env.insert x1 (o1.eval va1 vb1).1)[x]? = some v →
                                          (srcLookup (htop.st.srcEnv.insert x1 (ovfToSym o1
                                            (argToSym (srcLookup htop.st.srcEnv) a1).norm
                                            (argToSym (srcLookup htop.st.srcEnv) b1).norm)) x).eval htop.ρ₁₀ s₁.ctx snaps = some v := by
                                        intro x v hx
                                        rw [env_insert_get] at hx
                                        unfold srcLookup Src.NatMap.getD
                                        rw [Src.NatMap.get?_insert]
                                        by_cases hxx : x = x1
                                        · subst hxx; simp only [↓reduceIte, Option.some.injEq] at hx; subst hx
                                          simp only [↓reduceIte, Option.getD_some]; exact hres1
                                        · have hx1x : x1 ≠ x := Ne.symm hxx
                                          simp only [hx1x, ↓reduceIte] at hx; simp only [hxx, ↓reduceIte]
                                          exact hseg.srcEnvEval x v hx
                                      have hdef' : ∀ x, (htop.st.srcDef.insert x1).contains x = true →
                                          (fr₁.env.insert x1 (o1.eval va1 vb1).1)[x]?.isSome = true := by
                                        intro x hx
                                        rw [natSet_contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
                                        rw [env_insert_get]
                                        rcases hx with rfl | hx
                                        · simp
                                        · split
                                          · rfl
                                          · exact hseg.srcDefOk x hx
                                      have hst2 := step_jump (p := q) (F := htop.G) (B := htop.B₂)
                                        (fr := { fn := fr₁.fn, label := htop.bp.target, pos := htop.B₂.body.size, env := ρ₂', dsts := [] })
                                        (rest := rest₂) (mem := s₁.mem) (ctx := s₁.ctx) htop.hG htop.hB₂ rfl ht2
                                      simp only [checkTerm] at hrest_chk
                                      cases hof : ovfFromFacts htop.st.facts o1
                                          (argToSym (srcLookup htop.st.srcEnv) a1).norm
                                          (argToSym (srcLookup htop.st.srcEnv) b1).norm with
                                      | some r =>
                                          have hr := ovfFromFacts_sound hseg.factsHold hof hea1 heb1
                                          dsimp only at hstep1; rw [hr] at hstep1
                                          cases r <;> rw [hof] at hrest_chk
                                          · exact finishEdge ok1 _ _ _ htop.st.tgtEnv htop.st.facts e2 ρ₂'
                                              hsrc' hdef' hseg.tgtEnvEval hseg.factsHold hstep1 hst2 hrest_chk
                                          · exact finishEdge ovf1 _ _ _ htop.st.tgtEnv htop.st.facts e2 ρ₂'
                                              hsrc' hdef' hseg.tgtEnvEval hseg.factsHold hstep1 hst2 hrest_chk
                                      | none =>
                                          rw [hof] at hrest_chk
                                          by_cases hoo : (ok1 == ovf1) = true
                                          · have hoo' : ok1 = ovf1 := by simpa using hoo
                                            simp only [hoo, ↓reduceIte] at hrest_chk
                                            dsimp only at hstep1; rw [← hoo', ite_self] at hstep1
                                            exact finishEdge ok1 _ _ _ htop.st.tgtEnv htop.st.facts e2 ρ₂'
                                              hsrc' hdef' hseg.tgtEnvEval hseg.factsHold hstep1 hst2 hrest_chk
                                          · simp [hoo] at hrest_chk
                            · -- brOvf vs brOvf
                              rename_i o1 x1 a1 b1 ok1 ovf1 o2 x2 a2 b2 ok2 ovf2
                              simp only [ht1] at hstep1
                              cases hva1 : a1.eval fr₁.env with
                              | none => rw [hva1] at hstep1; cases hstep1
                              | some va1 =>
                                  cases hvb1 : b1.eval fr₁.env with
                                  | none => rw [hva1, hvb1] at hstep1; cases hstep1
                                  | some vb1 =>
                                      rw [hva1, hvb1] at hstep1; dsimp only at hstep1
                                      simp only [checkTerm] at hrest_chk
                                      cases hea2 : evalTgtArg htop.st.tgtEnv a2 with
                                      | none => rw [hea2] at hrest_chk; cases hrest_chk
                                      | some ea2 =>
                                          cases heb2 : evalTgtArg htop.st.tgtEnv b2 with
                                          | none => rw [hea2, heb2] at hrest_chk; cases hrest_chk
                                          | some eb2 =>
                                              rw [hea2, heb2] at hrest_chk; dsimp only at hrest_chk
                                              simp only [Bool.and_eq_true] at hrest_chk
                                              obtain ⟨hovf_eq, hok_chk, hovf_chk⟩ := hrest_chk
                                              obtain ⟨va2, hva2, heva2⟩ := evalTgtArg_sound hseg.tgtEnvEval hea2
                                              obtain ⟨vb2, hvb2, hevb2⟩ := evalTgtArg_sound hseg.tgtEnvEval heb2
                                              have hea1 := SymExpr.norm_sound (argToSym_eval hseg.srcEnvEval hva1)
                                              have heb1 := SymExpr.norm_sound (argToSym_eval hseg.srcEnvEval hvb1)
                                              obtain ⟨rfl, hcarry_eq⟩ := checkOvfCondEquiv_sound hseg.factsHold hovf_eq hea1 heb1 heva2 hevb2
                                              have hres1 := ovfToSym_eval (o := o1) hea1 heb1
                                              have hres2 := ovfToSym_eval (o := o1) (SymExpr.norm_sound heva2) (SymExpr.norm_sound hevb2)
                                              have hsrc' : ∀ x v, (fr₁.env.insert x1 (o1.eval va1 vb1).1)[x]? = some v →
                                                  (srcLookup (htop.st.srcEnv.insert x1 (ovfToSym o1
                                                    (argToSym (srcLookup htop.st.srcEnv) a1).norm
                                                    (argToSym (srcLookup htop.st.srcEnv) b1).norm)) x).eval htop.ρ₁₀ s₁.ctx snaps = some v := by
                                                intro x v hx
                                                rw [env_insert_get] at hx; unfold srcLookup Src.NatMap.getD; rw [Src.NatMap.get?_insert]
                                                by_cases hxx : x = x1
                                                · subst hxx; simp only [↓reduceIte, Option.some.injEq] at hx; subst hx
                                                  simp only [↓reduceIte, Option.getD_some]; exact hres1
                                                · have hx1x : x1 ≠ x := Ne.symm hxx
                                                  simp only [hx1x, ↓reduceIte] at hx; simp only [hxx, ↓reduceIte]
                                                  exact hseg.srcEnvEval x v hx
                                              have hdef' : ∀ x, (htop.st.srcDef.insert x1).contains x = true →
                                                  (fr₁.env.insert x1 (o1.eval va1 vb1).1)[x]?.isSome = true := by
                                                intro x hx
                                                rw [natSet_contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
                                                rw [env_insert_get]
                                                rcases hx with rfl | hx
                                                · simp
                                                · split
                                                  · rfl
                                                  · exact hseg.srcDefOk x hx
                                              have htgt' : ∀ y ey, (htop.st.tgtEnv.insert x2 (ovfToSym o1 ea2.norm eb2.norm)).get? y = some ey →
                                                  ∃ v, (ρ₂'.insert x2 (o1.eval va2 vb2).1)[y]? = some v ∧ ey.eval htop.ρ₁₀ s₁.ctx snaps = some v := by
                                                intro y ey hy
                                                rw [Src.NatMap.get?_insert] at hy; rw [env_insert_get]
                                                by_cases hyx : y = x2
                                                · subst hyx; simp only [↓reduceIte, Option.some.injEq] at hy; subst hy
                                                  exact ⟨_, by simp, hres2⟩
                                                · simp only [hyx, ↓reduceIte] at hy
                                                  have hx2y : x2 ≠ y := Ne.symm hyx
                                                  simp only [hx2y, ↓reduceIte]; exact hseg.tgtEnvEval y ey hy
                                              have hst2 := step_brOvf (p := q) (F := htop.G) (B := htop.B₂)
                                                (fr := { fn := fr₁.fn, label := htop.bp.target, pos := htop.B₂.body.size, env := ρ₂', dsts := [] })
                                                (rest := rest₂) (mem := s₁.mem) (ctx := s₁.ctx) htop.hG htop.hB₂ rfl ht2 hva2 hvb2
                                              rw [← hcarry_eq] at hst2
                                              cases hcarry : (o1.eval va1 vb1).2 with
                                              | false =>
                                                  rw [hcarry] at hstep1 hst2
                                                  exact finishEdge ok1 _ _ _ _ htop.st.facts ok2 _
                                                    hsrc' hdef' htgt' hseg.factsHold hstep1 hst2 hok_chk
                                              | true =>
                                                  rw [hcarry] at hstep1 hst2
                                                  exact finishEdge ovf1 _ _ _ _ htop.st.facts ovf2 _
                                                    hsrc' hdef' htgt' hseg.factsHold hstep1 hst2 hovf_chk
                            · -- ret vs ret (returning to a caller frame)
                              rename_i as1 as2
                              simp only [ht1] at hstep1
                              simp only [checkTerm] at hrest_chk
                              cases hev1 : evalArgs fr₁.env as1 with
                              | none => rw [hev1] at hstep1; cases hstep1
                              | some vals =>
                                  rw [hev1] at hstep1; dsimp only at hstep1
                                  cases rest₁ with
                                  | nil => cases hstep1
                                  | cons caller₁ rest₁' =>
                                      cases hcallers with
                                      | cons hcal hcallers' =>
                                          rename_i caller₂ rest₂'
                                          dsimp only at hstep1
                                          cases hbp1 : bindParams caller₁.env caller₁.dsts vals with
                                          | none => rw [hbp1] at hstep1; cases hstep1
                                          | some ρc₁ =>
                                              rw [hbp1] at hstep1
                                              simp only [Step.next.injEq] at hstep1
                                              obtain ⟨rfl, rfl⟩ := hstep1
                                              have hev2 := checkArgsEquiv_sound hseg hrest_chk hev1
                                              obtain ⟨ρc₂, hbp2, htop_res⟩ := resumeCaller_rel (mem := s₁.mem) hcal hbp1
                                              have hst_ret := step_ret_caller (p := q) (F := htop.G) (B := htop.B₂)
                                                (fr := { fn := fr₁.fn, label := htop.bp.target, pos := htop.B₂.body.size, env := ρ₂', dsts := [] })
                                                (caller := caller₂) (rest' := rest₂') (mem := s₁.mem) (ctx := s₁.ctx)
                                                htop.hG htop.hB₂ rfl ht2 hev2 hbp2
                                              have hstar_all := hstar_seg'.trans (star_of_step hst_ret)
                                              exact .inl ⟨0 + 0, _, hstar_all, Nat.le_refl _, rfl, htop_res, hcallers'⟩
                            · -- tail vs tail
                              rename_i g1 as1 g2 as2
                              simp only [ht1] at hstep1
                              simp only [checkTerm, Bool.and_eq_true, beq_iff_eq] at hrest_chk
                              obtain ⟨hg_eq, hargs_chk⟩ := hrest_chk
                              cases hev1 : evalArgs fr₁.env as1 with
                              | none => rw [hev1] at hstep1; cases hstep1
                              | some vals =>
                                  rw [hev1] at hstep1
                                  simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                                  cases hent1 : enter p g1 vals with
                                  | none => rw [hent1] at hstep1; cases hstep1
                                  | some callee₁ =>
                                      rw [hent1] at hstep1
                                      simp only [Step.next.injEq] at hstep1
                                      obtain ⟨rfl, rfl⟩ := hstep1
                                      have hev2 := checkArgsEquiv_sound hseg hargs_chk hev1
                                      obtain ⟨callee₂, hent2, htop_callee⟩ := enter_rel hp (mem := s₁.mem) (ctx := s₁.ctx) hent1
                                      have hst_tail := step_tail (p := q) (F := htop.G) (B := htop.B₂)
                                        (fr := { fn := fr₁.fn, label := htop.bp.target, pos := htop.B₂.body.size, env := ρ₂', dsts := [] })
                                        (rest := rest₂) (mem := s₁.mem) (ctx := s₁.ctx)
                                        htop.hG htop.hB₂ rfl ht2 hev2 (by rw [← hg_eq]; exact hent2)
                                      exact .inl ⟨0 + 1, _, hstar_seg'.trans (star_of_step hst_tail), Nat.le_refl _,
                                        rfl, htop_callee, hcallers⟩
                            · -- fail vs fail (not a `.next` step!)
                              simp [ht1] at hstep1
                            · -- trap vs trap (not a `.next` step!)
                              simp [ht1] at hstep1
  final := by
    intro s₁ s₂ r hrel hfin hne_stuck
    obtain ⟨hctx, hstack⟩ := hrel
    cases hs1 : s₁.stack with
    | nil => rw [hs1] at hstack; cases hstack
    | cons fr₁ rest₁ =>
        cases hs2 : s₂.stack with
        | nil => rw [hs1, hs2] at hstack; cases hstack
        | cons fr₂ rest₂ =>
            rw [hs1, hs2] at hstack
            obtain ⟨htopRel, hcallers⟩ := hstack
            have hs1_eq : s₁ = { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ } := by
              cases s₁; cases hs1; rfl
            have hs2_eq : s₂ = { mem := s₂.mem, ctx := s₁.ctx, stack := fr₂ :: rest₂ } := by
              cases s₂; cases hs2; cases hctx; rfl
            rcases htopRel with ⟨⟨htop⟩⟩ | ⟨hmemEq, hfrEq, hfnSame⟩
            rotate_left
            · -- Identical unchanged function final step
              have hst1 : semStep p s₁ = (step p { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ }).toSem := by
                rw [← hs1_eq]; rfl
              have hs2_eq' : s₂ = { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₂ } := by
                rw [hs2_eq, ← hmemEq, ← hfrEq]
              unfold step at hst1; dsimp only at hst1
              cases hF : p.funcs[fr₁.fn]? with
              | none => rw [hF] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
              | some F =>
                  have hG : q.funcs[fr₁.fn]? = some F := hfnSame.symm.trans hF
                  rw [hF] at hst1; dsimp only at hst1
                  cases hB : F.blocks[fr₁.label]? with
                  | none => rw [hB] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
                  | some B =>
                      rw [hB] at hst1; dsimp only at hst1
                      by_cases hlt : fr₁.pos < B.body.size
                      · simp only [hlt, ↓reduceDIte] at hst1
                        cases hst : B.body[fr₁.pos] with
                        | assign _ _ | limb _ _ _ | store _ _ _ =>
                            rw [hst] at hst1; dsimp only at hst1; rw [← hst] at hst1
                            cases hex : (B.body[fr₁.pos]).exec fr₁.env s₁.mem s₁.ctx with
                            | some _ => rw [hex] at hst1; rw [hst1] at hfin; cases hfin
                            | none => rw [hex] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
                        | call _ g as =>
                            rw [hst] at hst1; dsimp only at hst1
                            cases hbind : (evalArgs fr₁.env as >>= enter p g) with
                            | some _ => rw [hbind] at hst1; rw [hst1] at hfin; cases hfin
                            | none => rw [hbind] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
                      · simp only [hlt, ↓reduceDIte] at hst1
                        have hst2 : semStep q s₂ = IxCC.Lir.Step.toSem _ :=
                          congrArg IxCC.Lir.Step.toSem ((congrArg (step q) hs2_eq').trans
                            (step_at_term' (p := q) (F := F) (B := B) (mem := s₁.mem) (ctx := s₁.ctx)
                              (fr := fr₁) (rest := rest₂) hG hB hlt))
                        cases ht : B.term with
                        | ret args =>
                            rw [ht] at hst1 hst2; dsimp only at hst1 hst2
                            cases hev : evalArgs fr₁.env args with
                            | none => rw [hev] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
                            | some vs =>
                                rw [hev] at hst1 hst2; dsimp only at hst1 hst2
                                cases rest₁ with
                                | cons c₁ r₁ =>
                                    dsimp only at hst1
                                    cases hbp : bindParams c₁.env c₁.dsts vs with
                                    | some _ => rw [hbp] at hst1; rw [hst1] at hfin; cases hfin
                                    | none => rw [hbp] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
                                | nil =>
                                    cases hcallers
                                    rw [hst1] at hfin; cases hfin
                                    exact .inl ⟨0, s₂, .ok (vs, s₁.mem), .refl _, by rw [hst2]; exact .done, .ok rfl⟩
                        | fail res =>
                            rw [ht] at hst1 hst2; rw [hst1] at hfin; cases hfin
                            exact .inl ⟨0, s₂, .resource res, .refl _, by rw [hst2]; exact .fail, .resource res⟩
                        | trap =>
                            rw [ht] at hst1 hst2; rw [hst1] at hfin; cases hfin
                            exact .inl ⟨0, s₂, .trap, .refl _, by rw [hst2]; exact .trap, .trap⟩
                        | jump e =>
                            rw [ht] at hst1; dsimp only at hst1; rw [hst1] at hfin
                            exact absurd hfin (fun h => takeEdge_not_nonstuck h hne_stuck)
                        | br _ _ a b' _ _ =>
                            rw [ht] at hst1; dsimp only at hst1
                            cases ha : a.eval fr₁.env with
                            | none => rw [ha] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
                            | some _ =>
                                cases hb : b'.eval fr₁.env with
                                | none => rw [ha, hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
                                | some _ =>
                                    rw [ha, hb] at hst1; dsimp only at hst1; rw [hst1] at hfin
                                    exact absurd hfin (fun h => takeEdge_not_nonstuck h hne_stuck)
                        | brOvf _ _ a b' _ _ =>
                            rw [ht] at hst1; dsimp only at hst1
                            cases ha : a.eval fr₁.env with
                            | none => rw [ha] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
                            | some _ =>
                                cases hb : b'.eval fr₁.env with
                                | none => rw [ha, hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
                                | some _ =>
                                    rw [ha, hb] at hst1; dsimp only at hst1; rw [hst1] at hfin
                                    exact absurd hfin (fun h => takeEdge_not_nonstuck h hne_stuck)
                        | tail g as =>
                            rw [ht] at hst1; dsimp only at hst1
                            cases hbind : (evalArgs fr₁.env as >>= enter p g) with
                            | some _ => rw [hbind] at hst1; rw [hst1] at hfin; cases hfin
                            | none => rw [hbind] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
            -- Planned function (`htop : TopFrameData`): a non-stuck final step CANNOT happen while `fr₁.pos < B₁.body.size`!
            have hrem_nil : htop.rem₁ = [] := by
              cases hrem : htop.rem₁ with
              | nil => rfl
              | cons s rem₁' =>
                  have hpos_lt : fr₁.pos < htop.B₁.body.size := by
                    have := congrArg List.length htop.hBody₁
                    simp only [Array.length_toList, List.length_append, hrem, List.length_cons] at this
                    have := htop.hPos₁; omega
                  have hget : htop.B₁.body[fr₁.pos] = s := by
                    have hopt : htop.B₁.body.toList[fr₁.pos]? = some s := by
                      rw [htop.hBody₁, hrem, htop.hPos₁]; simp [List.append_assoc]
                    simp only [Array.getElem?_toList, Array.getElem?_eq_some_iff] at hopt; exact hopt.2
                  have hnc_s : s.isCall = false := htop.hNoCall₁ s (by simp [hrem])
                  have hst1 : semStep p s₁ = (step p { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ }).toSem := by
                    rw [← hs1_eq]; rfl
                  unfold step at hst1
                  simp only [htop.hF, htop.hB₁, hpos_lt, ↓reduceDIte, hget] at hst1
                  cases hsc : s with
                  | call _ _ _ => rw [hsc] at hnc_s; cases hnc_s
                  | assign _ _ | limb _ _ _ | store _ _ _ =>
                      rw [hsc] at hst1; dsimp only at hst1; rw [← hsc] at hst1
                      cases hex : s.exec fr₁.env s₁.mem s₁.ctx with
                      | some res => rw [hex] at hst1; rw [hst1] at hfin; cases hfin
                      | none => rw [hex] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
            have hcalls_nil : htop.calls₁ = [] := by
              cases hcalls1 : htop.calls₁ with
              | nil => rfl
              | cons c₁ restCalls1 =>
                  have hpos_lt : fr₁.pos < htop.B₁.body.size := by
                    have := congrArg List.length htop.hBody₁
                    simp only [Array.length_toList, List.length_append, hrem_nil, List.append_nil,
                      hcalls1, callsTail, List.length_cons] at this
                    have := htop.hPos₁; omega
                  have hget : htop.B₁.body[fr₁.pos] = .call c₁.rs c₁.fn c₁.args := by
                    have hopt : htop.B₁.body.toList[fr₁.pos]? = some (.call c₁.rs c₁.fn c₁.args) := by
                      rw [htop.hBody₁, hrem_nil, List.append_nil, hcalls1, callsTail, htop.hPos₁]
                      simp [List.append_assoc]
                    simp only [Array.getElem?_toList, Array.getElem?_eq_some_iff] at hopt; exact hopt.2
                  have hst1 : semStep p s₁ = (step p { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ }).toSem := by
                    rw [← hs1_eq]; rfl
                  unfold step at hst1
                  simp only [htop.hF, htop.hB₁, hpos_lt, ↓reduceDIte, hget] at hst1
                  cases hbind : (evalArgs fr₁.env c₁.args >>= enter p c₁.fn) with
                  | some _ => rw [hbind] at hst1; rw [hst1] at hfin; cases hfin
                  | none => rw [hbind] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne_stuck
            -- Sync `fr₂` to terminator in 0 charges!
            obtain ⟨ρ₂', snaps, hstar_seg, hseg⟩ := checkSeg_sync (rest₂ := rest₂) htop hrem_nil
            have hrest_chk := htop.hCheckRest
            rw [hcalls_nil] at hrest_chk
            cases hcalls2 : htop.calls₂ with
            | cons _ _ => rw [hcalls2] at hrest_chk; cases hrest_chk
            | nil =>
                cases hinvs : htop.afterInvs with
                | cons _ _ => rw [hcalls2, hinvs] at hrest_chk; cases hrest_chk
                | nil =>
                    rw [hcalls2, hinvs] at hrest_chk
                    simp only [checkCallsAndTerm] at hrest_chk
                    have hpos1_eq : fr₁.pos = htop.B₁.body.size := by
                      have := congrArg List.length htop.hBody₁
                      simp only [Array.length_toList, List.length_append, hrem_nil, List.append_nil,
                        hcalls_nil, callsTail] at this
                      rw [htop.hPos₁, this]
                    have hpos2_eq : htop.pre₂.length + htop.seg₂.length = htop.B₂.body.size := by
                      have := congrArg List.length htop.hBody₂
                      simp only [Array.length_toList, List.length_append, hcalls2, callsTail,
                        List.length_nil, Nat.add_zero] at this
                      exact this.symm
                    rw [hpos2_eq] at hstar_seg
                    have hstar_seg' : Sem.Star (semStep q) s₂ 0
                        (atState s₁.mem s₁.ctx fr₁.fn htop.bp.target htop.B₂.body.size ρ₂' rest₂) :=
                      star_congr_left hs2_eq hstar_seg
                    -- Decode `hfin` at terminator
                    have hst_term := step_term (p := p) (F := htop.F) (B := htop.B₁) (fr := fr₁) (rest := rest₁)
                      (mem := s₁.mem) (ctx := s₁.ctx) htop.hF htop.hB₁ hpos1_eq
                    have hst1_sem : semStep p s₁ = (step p { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ }).toSem := by
                      rw [← hs1_eq]; rfl
                    rw [hst_term] at hst1_sem
                    cases ht1 : htop.B₁.term with
                    | ret as1 =>
                        rw [ht1] at hst1_sem hrest_chk; dsimp only at hst1_sem
                        cases ht2 : htop.B₂.term <;> rw [ht2] at hrest_chk <;> try cases hrest_chk
                        rename_i as2
                        simp only [checkTerm] at hrest_chk
                        cases hev1 : evalArgs fr₁.env as1 with
                        | none => rw [hev1] at hst1_sem; rw [hst1_sem] at hfin; cases hfin; exact absurd rfl hne_stuck
                        | some vals =>
                            rw [hev1] at hst1_sem; dsimp only at hst1_sem
                            cases rest₁ with
                            | cons caller₁ rest₁' =>
                                dsimp only at hst1_sem
                                cases hbp1 : bindParams caller₁.env caller₁.dsts vals with
                                | some _ => rw [hbp1] at hst1_sem; rw [hst1_sem] at hfin; cases hfin
                                | none => rw [hbp1] at hst1_sem; rw [hst1_sem] at hfin; cases hfin; exact absurd rfl hne_stuck
                            | nil =>
                                cases hcallers
                                rw [hst1_sem] at hfin
                                cases hfin
                                have hev2 := checkArgsEquiv_sound hseg hrest_chk hev1
                                have hdone2 := step_ret_done (p := q) (F := htop.G) (B := htop.B₂)
                                  (fr := { fn := fr₁.fn, label := htop.bp.target, pos := htop.B₂.body.size, env := ρ₂', dsts := [] })
                                  (mem := s₁.mem) (ctx := s₁.ctx) htop.hG htop.hB₂ rfl ht2 hev2
                                exact .inl ⟨0, _, .ok (vals, s₁.mem), hstar_seg',
                                  by rw [semStep_done.2 hdone2]; exact .done, .ok rfl⟩
                    | fail res1 =>
                        rw [ht1] at hst1_sem hrest_chk; dsimp only at hst1_sem
                        cases ht2 : htop.B₂.term <;> rw [ht2] at hrest_chk <;> try cases hrest_chk
                        rename_i res2
                        simp only [checkTerm, beq_iff_eq] at hrest_chk; subst hrest_chk
                        rw [hst1_sem] at hfin; cases hfin
                        have hfl2 := step_fail (p := q) (F := htop.G) (B := htop.B₂)
                          (fr := { fn := fr₁.fn, label := htop.bp.target, pos := htop.B₂.body.size, env := ρ₂', dsts := [] })
                          (rest := rest₂) (mem := s₁.mem) (ctx := s₁.ctx) htop.hG htop.hB₂ rfl ht2
                        exact .inl ⟨0, _, .resource res1, hstar_seg',
                          by rw [semStep_fail.2 hfl2]; exact .fail, .resource res1⟩
                    | trap =>
                        rw [ht1] at hst1_sem hrest_chk; dsimp only at hst1_sem
                        cases ht2 : htop.B₂.term <;> rw [ht2] at hrest_chk <;> try cases hrest_chk
                        rw [hst1_sem] at hfin; cases hfin
                        have htr2 := step_trap (p := q) (F := htop.G) (B := htop.B₂)
                          (fr := { fn := fr₁.fn, label := htop.bp.target, pos := htop.B₂.body.size, env := ρ₂', dsts := [] })
                          (rest := rest₂) (mem := s₁.mem) (ctx := s₁.ctx) htop.hG htop.hB₂ rfl ht2
                        exact .inl ⟨0, _, .trap, hstar_seg',
                          by rw [semStep_trap.2 htr2]; exact .trap, .trap⟩
                    | jump e1 =>
                        rw [ht1] at hst1_sem; dsimp only at hst1_sem
                        rw [hst1_sem] at hfin
                        exact False.elim (takeEdge_not_nonstuck hfin hne_stuck)
                    | br c1 w1 a1 b1 t1 f1 =>
                        rw [ht1] at hst1_sem; dsimp only at hst1_sem
                        cases ha1 : a1.eval fr₁.env <;> cases hb1 : b1.eval fr₁.env <;>
                          rw [ha1, hb1] at hst1_sem <;> dsimp only at hst1_sem
                        · rw [hst1_sem] at hfin; cases hfin; exact absurd rfl hne_stuck
                        · rw [hst1_sem] at hfin; cases hfin; exact absurd rfl hne_stuck
                        · rw [hst1_sem] at hfin; cases hfin; exact absurd rfl hne_stuck
                        · rw [hst1_sem] at hfin; exact False.elim (takeEdge_not_nonstuck hfin hne_stuck)
                    | brOvf o1 x1 a1 b1 ok1 ovf1 =>
                        rw [ht1] at hst1_sem; dsimp only at hst1_sem
                        cases ha1 : a1.eval fr₁.env <;> cases hb1 : b1.eval fr₁.env <;>
                          rw [ha1, hb1] at hst1_sem <;> dsimp only at hst1_sem
                        · rw [hst1_sem] at hfin; cases hfin; exact absurd rfl hne_stuck
                        · rw [hst1_sem] at hfin; cases hfin; exact absurd rfl hne_stuck
                        · rw [hst1_sem] at hfin; cases hfin; exact absurd rfl hne_stuck
                        · rw [hst1_sem] at hfin; exact False.elim (takeEdge_not_nonstuck hfin hne_stuck)
                    | tail g1 as1 =>
                        rw [ht1] at hst1_sem; dsimp only at hst1_sem
                        cases hbind : (evalArgs fr₁.env as1 >>= enter p g1) with
                        | some _ => rw [hbind] at hst1_sem; rw [hst1_sem] at hfin; cases hfin
                        | none => rw [hbind] at hst1_sem; rw [hst1_sem] at hfin; cases hfin; exact absurd rfl hne_stuck

/-! ## Public simulation & refinement theorems -/

/-- **Trusted validator clocked simulation (`Sem.Sim Eq id`)** for any accepted `plan`. -/
theorem checkProgramWithPlan_sim {p q : Program} {plan : ProgPlan}
    (hp : checkProgramWithPlan p q plan = true)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id (fun k => eval p k args mem ctx) (fun k => eval q k args mem ctx) := by
  cases hinit1 : State.initial p args mem ctx with
  | none =>
      refine ⟨fun k _ => ⟨0, by simp [eval, hinit1]; exact .stuck⟩,
        fun k hk => by simp [eval, hinit1] at hk⟩
  | some s₁ =>
      have hmain : q.main = p.main := by
        unfold checkProgramWithPlan at hp
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        exact hp.1.1.1
      simp only [State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hinit1
      obtain ⟨fr₁, hent₁, rfl⟩ := hinit1
      obtain ⟨fr₂, hent₂, htop⟩ := enter_rel hp (mem := mem) (ctx := ctx) hent₁
      have hinit2 : State.initial q args mem ctx = some { mem, ctx, stack := [fr₂] } := by
        simp [State.initial, hmain, hent₂]
      have hrel : StateRel p q plan { mem, ctx, stack := [fr₁] } { mem, ctx, stack := [fr₂] } :=
        ⟨rfl, htop, .nil⟩
      exact (checkProgramWithPlan_forward hp).sim hrel
        (runs_eval (by simp [State.initial, hent₁]))
        (runs_eval hinit2)

/-- **Validator clocked simulation (`Lir.Opt.check_sim`)**: every program pair
accepted by `Lir.Opt.check` is simulated with exact value/memory equality and
identity clock map. -/
theorem check_sim {p q : Program} (h : check p q = true)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id (fun k => eval p k args mem ctx) (fun k => eval q k args mem ctx) :=
  checkProgramWithPlan_sim h args mem ctx

/-- **Validator behaviour refinement (`Lir.Opt.check_refines`)**: every program
pair accepted by `Lir.Opt.check` refines original `Lir.eval` behaviours
(termination with identical return words & memory, divergence, traps, and
resource failures). -/
theorem check_refines {p q : Program} (h : check p q = true)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Behaviour.Refines Eq
      (Sem.behaviour fun k => eval p k args mem ctx)
      (Sem.behaviour fun k => eval q k args mem ctx) :=
  (check_sim h args mem ctx).refines (eval_mono p args mem ctx) (eval_mono q args mem ctx)

/-- `Lir.Opt.runLocal` preserves `Lir.Program.wellFormed`. -/
theorem runLocal_wellFormed {p : Program} (hwf : p.wellFormed = true) :
    (Lir.Opt.runLocal p).wellFormed = true := by
  unfold Lir.Opt.runLocal
  dsimp only
  split
  · rename_i hcond
    rw [Bool.and_eq_true, Bool.or_eq_true, hwf] at hcond
    rcases hcond.2 with h | h
    · cases h
    · exact h
  · exact hwf

/-- **Clocked simulation for `Lir.Opt.runLocal`** (`Sem.Sim Eq id`). -/
theorem runLocal_sim (p : Program) (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id (fun k => eval p k args mem ctx) (fun k => eval (Lir.Opt.runLocal p) k args mem ctx) := by
  unfold Lir.Opt.runLocal
  dsimp only
  split
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    exact check_sim hcond.1 args mem ctx
  · exact ⟨fun k _ => ⟨k, Sem.Result.Refines.refl (fun _ => rfl)⟩, fun k hk => .inl hk⟩

/-- `Lir.Opt.runLocalAt` preserves `Lir.Program.wellFormed`. -/
theorem runLocalAt_wellFormed {p : Program} {fi : FunId} (hwf : p.wellFormed = true) :
    (Lir.Opt.runLocalAt p fi).wellFormed = true := by
  unfold Lir.Opt.runLocalAt
  cases p.funcs[fi]? with
  | none => exact hwf
  | some F =>
      dsimp only
      split
      · exact hwf
      · split
        · rename_i hcond
          rw [Bool.and_eq_true, Bool.or_eq_true, hwf] at hcond
          rcases hcond.2 with h | h
          · cases h
          · exact h
        · exact hwf

/-- **Clocked simulation for `Lir.Opt.runLocalAt`** (`Sem.Sim Eq id`). -/
theorem runLocalAt_sim (p : Program) (fi : FunId)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id (fun k => eval p k args mem ctx)
      (fun k => eval (Lir.Opt.runLocalAt p fi) k args mem ctx) := by
  unfold Lir.Opt.runLocalAt
  cases p.funcs[fi]? with
  | none => exact Sem.Sim.refl (fun _ => rfl) _
  | some F =>
      dsimp only
      split
      · exact Sem.Sim.refl (fun _ => rfl) _
      · split
        · rename_i hcond
          rw [Bool.and_eq_true] at hcond
          exact checkProgramWithPlan_sim hcond.1 args mem ctx
        · exact Sem.Sim.refl (fun _ => rfl) _

/-! ## Composing structural passes (`Inline`, `Unroll`, `IfConv`) with `runLocalAt` -/

private theorem sim_clock_le {α : Type} {f g : Nat → Nat}
    {c₁ c₂ : Nat → Sem.Result α}
    (h₁ : Sem.ClockMono c₁) (hfg : ∀ k, f k ≤ g k)
    (h : Sem.Sim Eq f c₁ c₂) : Sem.Sim Eq g c₁ c₂ where
  forward := h.forward
  timeout k hk := by
    apply h.timeout k
    cases hfk : c₁ (f k) with
    | timeout => rfl
    | _ =>
        have hne : c₁ (f k) ≠ .timeout := by rw [hfk]; intro hc; cases hc
        have heq := h₁ (hfg k) hne
        rw [hk] at heq
        exact absurd heq.symm hne

private theorem sim_refl_clock {α : Type} {f : Nat → Nat} {c : Nat → Sem.Result α}
    (h : Sem.ClockMono c) (hf : ∀ k, k ≤ f k) : Sem.Sim Eq f c c :=
  sim_clock_le h hf (Sem.Sim.refl (fun _ => rfl) c)

private theorem inlineClock_ge : ∀ n k, k ≤ inlineClock n k
  | 0, _ => Nat.le_refl _
  | n + 1, k => by simp only [inlineClock]; have := inlineClock_ge n k; omega

private theorem unrollClock_ge : ∀ n k, k ≤ unrollClock n k
  | 0, _ => Nat.le_refl _
  | n + 1, k => by simp only [unrollClock]; have := unrollClock_ge n k; omega

theorem inlineTailLoop_wellFormed : ∀ (fuel : Nat) {p : Program},
    p.wellFormed = true → (inlineTailLoop fuel p).wellFormed = true
  | 0, _, hwf => hwf
  | fuel + 1, p, hwf => by
      unfold inlineTailLoop
      split
      · exact hwf
      · rename_i fi blk _
        dsimp only
        split
        · exact inlineTailLoop_wellFormed fuel (runLocalAt_wellFormed (inlineTailSiteChecked_wellFormed hwf))
        · exact hwf

theorem inlineTailLoop_sim : ∀ (fuel : Nat) (p : Program)
    (args : List Word) (mem : X86.Memory) (ctx : Word),
    Sem.Sim Eq (inlineClock fuel)
      (fun k => eval p k args mem ctx)
      (fun k => eval (inlineTailLoop fuel p) k args mem ctx)
  | 0, p, args, mem, ctx => Sem.Sim.refl (fun _ => rfl) _
  | fuel + 1, p, args, mem, ctx => by
      unfold inlineTailLoop
      split
      · exact sim_refl_clock (eval_mono p args mem ctx) (inlineClock_ge (fuel + 1))
      · rename_i fi blk _
        dsimp only
        split
        · have h1 := inlineTailSiteChecked_sim p fi blk args mem ctx
          have h2 := runLocalAt_sim (inlineTailSiteChecked p fi blk).1 fi args mem ctx
          have h3 := inlineTailLoop_sim fuel (runLocalAt (inlineTailSiteChecked p fi blk).1 fi) args mem ctx
          exact sim_clock_le (eval_mono p args mem ctx) (fun k => by simp only [inlineClock, id]; exact Nat.le_refl _)
            (sim_eq_comp (eval_mono _ args mem ctx) h1 (sim_eq_comp (eval_mono _ args mem ctx) h2 h3))
        · exact sim_refl_clock (eval_mono p args mem ctx) (inlineClock_ge (fuel + 1))

theorem inlineHelpersLoop_wellFormed : ∀ (fuel : Nat) {p : Program},
    p.wellFormed = true → (inlineHelpersLoop fuel p).wellFormed = true
  | 0, _, hwf => hwf
  | fuel + 1, p, hwf => by
      unfold inlineHelpersLoop
      split
      · exact hwf
      · rename_i fi blk pos _
        dsimp only
        split
        · exact inlineHelpersLoop_wellFormed fuel (runLocalAt_wellFormed (inlineCallSiteChecked_wellFormed hwf))
        · exact hwf

theorem inlineHelpersLoop_sim : ∀ (fuel : Nat) (p : Program)
    (args : List Word) (mem : X86.Memory) (ctx : Word),
    Sem.Sim Eq (inlineClock fuel)
      (fun k => eval p k args mem ctx)
      (fun k => eval (inlineHelpersLoop fuel p) k args mem ctx)
  | 0, p, args, mem, ctx => Sem.Sim.refl (fun _ => rfl) _
  | fuel + 1, p, args, mem, ctx => by
      unfold inlineHelpersLoop
      split
      · exact sim_refl_clock (eval_mono p args mem ctx) (inlineClock_ge (fuel + 1))
      · rename_i fi blk pos _
        dsimp only
        split
        · have h1 := inlineCallSiteChecked_sim p fi blk pos args mem ctx
          have h2 := runLocalAt_sim (inlineCallSiteChecked p fi blk pos).1 fi args mem ctx
          have h3 := inlineHelpersLoop_sim fuel (runLocalAt (inlineCallSiteChecked p fi blk pos).1 fi) args mem ctx
          exact sim_clock_le (eval_mono p args mem ctx) (fun k => by simp only [inlineClock, id]; exact Nat.le_refl _)
            (sim_eq_comp (eval_mono _ args mem ctx) h1 (sim_eq_comp (eval_mono _ args mem ctx) h2 h3))
        · exact sim_refl_clock (eval_mono p args mem ctx) (inlineClock_ge (fuel + 1))

theorem versionOddLoop_wellFormed : ∀ (fuel : Nat) (doneFns : Src.NatSet) {p : Program},
    p.wellFormed = true → (versionOddLoop fuel doneFns p).wellFormed = true
  | 0, _, _, hwf => hwf
  | fuel + 1, doneFns, p, hwf => by
      unfold versionOddLoop
      split
      · exact hwf
      · rename_i fi h idxs outers _
        dsimp only
        split
        · exact versionOddLoop_wellFormed fuel (doneFns.insert fi)
            (runLocalAt_wellFormed (versionOddLoopSiteChecked_wellFormed hwf))
        · exact hwf

theorem versionOddLoop_sim : ∀ (fuel : Nat) (doneFns : Src.NatSet) (p : Program)
    (args : List Word) (mem : X86.Memory) (ctx : Word),
    Sem.Sim Eq id
      (fun k => eval p k args mem ctx)
      (fun k => eval (versionOddLoop fuel doneFns p) k args mem ctx)
  | 0, _, p, args, mem, ctx => Sem.Sim.refl (fun _ => rfl) _
  | fuel + 1, doneFns, p, args, mem, ctx => by
      unfold versionOddLoop
      split
      · exact Sem.Sim.refl (fun _ => rfl) _
      · rename_i fi h idxs outers _
        dsimp only
        split
        · have h1 := versionOddLoopSiteChecked_sim p fi h idxs outers args mem ctx
          have h2 := runLocalAt_sim (versionOddLoopSiteChecked p fi h idxs outers).1 fi args mem ctx
          have h3 := versionOddLoop_sim fuel (doneFns.insert fi)
            (runLocalAt (versionOddLoopSiteChecked p fi h idxs outers).1 fi) args mem ctx
          exact sim_eq_comp (eval_mono _ args mem ctx) h1
            (sim_eq_comp (eval_mono _ args mem ctx) h2 h3)
        · exact Sem.Sim.refl (fun _ => rfl) _

theorem ifConvDiamondStep_wellFormed {p : Program} {fi : FunId} {b : Label}
    (hwf : p.wellFormed = true) : (ifConvDiamondStep p fi b).1.wellFormed = true := by
  unfold ifConvDiamondStep
  cases h : ifConvDiamondSite p fi b with
  | none => exact hwf
  | some q0 =>
      dsimp only
      split
      · rename_i hcond; simp only [hwf, Bool.not_true, Bool.false_or] at hcond; exact hcond
      · exact hwf

theorem ifConvDiamondStep_sim (p : Program) (fi : FunId) (b : Label)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id
      (fun k => eval p k args mem ctx)
      (fun k => eval (ifConvDiamondStep p fi b).1 k args mem ctx) := by
  unfold ifConvDiamondStep
  cases h : ifConvDiamondSite p fi b with
  | none => exact Sem.Sim.refl (fun _ => rfl) _
  | some q0 =>
      dsimp only
      split
      · exact sim_eq_comp (eval_mono _ args mem ctx)
          (ifConvDiamondSite_sim h args mem ctx) (runLocalAt_sim q0 fi args mem ctx)
      · exact Sem.Sim.refl (fun _ => rfl) _

theorem ifConvLoop_wellFormed : ∀ (fuel : Nat) {p : Program},
    p.wellFormed = true → (ifConvLoop fuel p).wellFormed = true
  | 0, _, hwf => hwf
  | fuel + 1, p, hwf => by
      unfold ifConvLoop
      split
      · exact hwf
      · rename_i fi b _
        dsimp only
        split
        · exact ifConvLoop_wellFormed fuel (ifConvDiamondStep_wellFormed hwf)
        · exact hwf

theorem ifConvLoop_sim : ∀ (fuel : Nat) (p : Program)
    (args : List Word) (mem : X86.Memory) (ctx : Word),
    Sem.Sim Eq id
      (fun k => eval p k args mem ctx)
      (fun k => eval (ifConvLoop fuel p) k args mem ctx)
  | 0, p, args, mem, ctx => Sem.Sim.refl (fun _ => rfl) _
  | fuel + 1, p, args, mem, ctx => by
      unfold ifConvLoop
      split
      · exact Sem.Sim.refl (fun _ => rfl) _
      · rename_i fi b _
        dsimp only
        split
        · have h1 := ifConvDiamondStep_sim p fi b args mem ctx
          have h2 := ifConvLoop_sim fuel (ifConvDiamondStep p fi b).1 args mem ctx
          exact sim_eq_comp (eval_mono _ args mem ctx) h1 h2
        · exact Sem.Sim.refl (fun _ => rfl) _

theorem inlineSelfLoop_wellFormed : ∀ (fuel : Nat) {p : Program},
    p.wellFormed = true → (inlineSelfLoop fuel p).wellFormed = true
  | 0, _, hwf => hwf
  | fuel + 1, p, hwf => by
      unfold inlineSelfLoop
      split
      · exact hwf
      · rename_i fi blk pos _
        dsimp only
        split
        · exact inlineSelfLoop_wellFormed fuel (runLocalAt_wellFormed (inlineCallSiteChecked_wellFormed hwf))
        · exact hwf

theorem inlineSelfLoop_sim : ∀ (fuel : Nat) (p : Program)
    (args : List Word) (mem : X86.Memory) (ctx : Word),
    Sem.Sim Eq (inlineClock fuel)
      (fun k => eval p k args mem ctx)
      (fun k => eval (inlineSelfLoop fuel p) k args mem ctx)
  | 0, p, args, mem, ctx => Sem.Sim.refl (fun _ => rfl) _
  | fuel + 1, p, args, mem, ctx => by
      unfold inlineSelfLoop
      split
      · exact sim_refl_clock (eval_mono p args mem ctx) (inlineClock_ge (fuel + 1))
      · rename_i fi blk pos _
        dsimp only
        split
        · have h1 := inlineCallSiteChecked_sim p fi blk pos args mem ctx
          have h2 := runLocalAt_sim (inlineCallSiteChecked p fi blk pos).1 fi args mem ctx
          have h3 := inlineSelfLoop_sim fuel (runLocalAt (inlineCallSiteChecked p fi blk pos).1 fi) args mem ctx
          exact sim_clock_le (eval_mono p args mem ctx) (fun k => by simp only [inlineClock, id]; exact Nat.le_refl _)
            (sim_eq_comp (eval_mono _ args mem ctx) h1 (sim_eq_comp (eval_mono _ args mem ctx) h2 h3))
        · exact sim_refl_clock (eval_mono p args mem ctx) (inlineClock_ge (fuel + 1))

theorem unrollLoop_wellFormed : ∀ (fuel : Nat) (doneFns : Src.NatSet) {p : Program},
    p.wellFormed = true → (unrollLoop fuel doneFns p).wellFormed = true
  | 0, _, _, hwf => hwf
  | fuel + 1, doneFns, p, hwf => by
      unfold unrollLoop
      split
      · exact hwf
      · rename_i fi h U _
        split
        · dsimp only
          split
          · exact unrollLoop_wellFormed fuel (doneFns.insert fi)
              (runLocalAt_wellFormed (unrollLoopSiteChecked_wellFormed hwf))
          · exact hwf
        · exact hwf

theorem unrollLoop_sim : ∀ (fuel : Nat) (doneFns : Src.NatSet) (p : Program)
    (args : List Word) (mem : X86.Memory) (ctx : Word),
    Sem.Sim Eq (unrollClock fuel)
      (fun k => eval p k args mem ctx)
      (fun k => eval (unrollLoop fuel doneFns p) k args mem ctx)
  | 0, _, p, args, mem, ctx => Sem.Sim.refl (fun _ => rfl) _
  | fuel + 1, doneFns, p, args, mem, ctx => by
      unfold unrollLoop
      split
      · exact sim_refl_clock (eval_mono p args mem ctx) (unrollClock_ge (fuel + 1))
      · rename_i fi h U _
        split
        · rename_i hU
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hU
          obtain ⟨hU1, hU4⟩ := hU
          dsimp only
          split
          · have h1' := unrollLoopSiteChecked_sim p fi h U hU1 args mem ctx
            have h1 : Sem.Sim Eq (fun k => 4 * k + 3)
                (fun k => eval p k args mem ctx)
                (fun k => eval (unrollLoopSiteChecked p fi h U).1 k args mem ctx) :=
              sim_clock_le (eval_mono p args mem ctx)
                (fun k => by have := Nat.mul_le_mul_right k hU4; omega) h1'
            have h2 := runLocalAt_sim (unrollLoopSiteChecked p fi h U).1 fi args mem ctx
            have h3 := unrollLoop_sim fuel (doneFns.insert fi)
              (runLocalAt (unrollLoopSiteChecked p fi h U).1 fi) args mem ctx
            exact sim_clock_le (eval_mono p args mem ctx) (fun k => by simp only [unrollClock, id]; exact Nat.le_refl _)
              (sim_eq_comp (eval_mono _ args mem ctx) h1 (sim_eq_comp (eval_mono _ args mem ctx) h2 h3))
          · exact sim_refl_clock (eval_mono p args mem ctx) (unrollClock_ge (fuel + 1))
        · exact sim_refl_clock (eval_mono p args mem ctx) (unrollClock_ge (fuel + 1))

/-- `Lir.Opt.run` preserves `Lir.Program.wellFormed`. -/
theorem run_wellFormed {p : Program} (hwf : p.wellFormed = true) :
    (Lir.Opt.run p).wellFormed = true := by
  unfold Lir.Opt.run
  exact unrollLoop_wellFormed _ _ (inlineSelfLoop_wellFormed _
    (ifConvLoop_wellFormed _ (versionOddLoop_wellFormed _ _
      (inlineHelpersLoop_wellFormed _ (inlineTailLoop_wellFormed _ (runLocal_wellFormed hwf))))))

/-- **End-to-end clocked simulation for `Lir.Opt.run`** (with composed clock map `runClock`). -/
theorem run_sim (p : Program) (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq runClock (fun k => eval p k args mem ctx) (fun k => eval (Lir.Opt.run p) k args mem ctx) := by
  unfold Lir.Opt.run
  dsimp only
  let p1 := runLocal p
  let p2 := inlineTailLoop tailInlineFuel p1
  let p3 := inlineHelpersLoop helperInlineFuel p2
  let p4 := versionOddLoop versionOddFuel .leaf p3
  let p5 := ifConvLoop ifConvFuel p4
  let p6 := inlineSelfLoop selfInlineFuel p5
  have h1 := runLocal_sim p args mem ctx
  have h2 := inlineTailLoop_sim tailInlineFuel p1 args mem ctx
  have h3 := inlineHelpersLoop_sim helperInlineFuel p2 args mem ctx
  have h4 := versionOddLoop_sim versionOddFuel .leaf p3 args mem ctx
  have h5 := ifConvLoop_sim ifConvFuel p4 args mem ctx
  have h6 := inlineSelfLoop_sim selfInlineFuel p5 args mem ctx
  have h7 := unrollLoop_sim unrollFuel .leaf p6 args mem ctx
  exact sim_clock_le (eval_mono p args mem ctx) (fun k => by simp only [runClock, id]; exact Nat.le_refl _)
    (sim_eq_comp (eval_mono _ args mem ctx) h1
      (sim_eq_comp (eval_mono _ args mem ctx) h2
        (sim_eq_comp (eval_mono _ args mem ctx) h3
          (sim_eq_comp (eval_mono _ args mem ctx) h4
            (sim_eq_comp (eval_mono _ args mem ctx) h5
              (sim_eq_comp (eval_mono _ args mem ctx) h6 h7))))))

/-- **End-to-end behaviour refinement for `Lir.Opt.run`.** -/
theorem run_refines (p : Program) (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Behaviour.Refines Eq
      (Sem.behaviour fun k => eval p k args mem ctx)
      (Sem.behaviour fun k => eval (Lir.Opt.run p) k args mem ctx) :=
  (run_sim p args mem ctx).refines (eval_mono p args mem ctx) (eval_mono (Lir.Opt.run p) args mem ctx)

/-- External certificate replay preserves `wellFormed` and refines `Lir.eval`. -/
theorem validateCert_wellFormed {p cert q : Program} (h : validateCert p cert = .ok q) :
    q.wellFormed = true ∧ check p q = true := by
  unfold validateCert at h
  split at h
  · cases h
  · rename_i hck
    have hck' : check p cert = true := by simpa using hck
    cases hwf : cert.check with
    | error _ => rw [hwf] at h; cases h
    | ok u =>
        rw [hwf] at h; cases h
        exact ⟨by simp [Program.wellFormed, hwf, Except.toBool], hck'⟩

theorem validateCert_sim {p cert q : Program} (h : validateCert p cert = .ok q)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id (fun k => eval p k args mem ctx) (fun k => eval q k args mem ctx) :=
  check_sim (validateCert_wellFormed h).2 args mem ctx

theorem validateCert_refines {p cert q : Program} (h : validateCert p cert = .ok q)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Behaviour.Refines Eq
      (Sem.behaviour fun k => eval p k args mem ctx)
      (Sem.behaviour fun k => eval q k args mem ctx) :=
  check_refines (validateCert_wellFormed h).2 args mem ctx

end IxCC.Lir.Opt
