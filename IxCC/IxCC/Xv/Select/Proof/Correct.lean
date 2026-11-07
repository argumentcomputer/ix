import IxCC.Xv.Select.Proof.XvSteps
import IxCC.Lir.Proof.Relabel
import IxCC.Xv.Validate.Proof.Diagram
import IxCC.Xv.Validate.Proof.Fuel
import IxCC.Sem.TracedSim

/-!
# Selection is correct (`Select.correct`)

A selected Xv program runs in lock-step with its Lir program: each Lir step
is matched by Xv steps spending the same charge, and each final Lir step
other than a stuck one by free Xv steps and the same final step
(`select_lockstep`). Hence, on every input and at every clock, the Xv run
has the Lir run's outcome unless that is stuck (`select_eval_eq`), a
clocked simulation with the identity clock map (`select_sim`), refinement
of behaviours (`select_correct`), and its traced form (`select_tsim`). The
same holds of the statistics-counting `Select.run`.

**The relation.** Related states share memory and context; their stacks
are related frame by frame (`FrameRel`): the same function, label and
result registers; the Xv position is the Lir position's offset in the
selected block (`off`, the lengths of the earlier statements' segments);
the Xv environment holds the Lir environment's values at every register
below the function's first fresh one outside its folded registers
(`EnvRel`); and the running frame's pending values hold (`PendInv`), a
suspended frame's after its call's results bind.

**Steps.** A statement other than a call runs its segment (a consumed
statement's is empty, and its register is folded, so the relation does not
constrain it); a call runs its segment's prefix and the call; a terminator
runs its prefix and the terminator, whose edges carry the Lir edges'
arguments into blocks with the same parameters.
-/

namespace IxCC.Xv.Select.Proof

open IxCC.Lir (VReg Word Env Frame State)
open IxCC.Xv.Select

/-! ## Offsets, avoided registers, environments -/

/-- The Xv position of Lir position `i` in a selected block. -/
def off (segs : List (List (Inst VReg))) (i : Nat) : Nat := (segs.take i).flatten.length

theorem off_succ {segs : List (List (Inst VReg))} {i : Nat} {seg : List (Inst VReg)} (h : segs[i]? = some seg) :
    off segs (i + 1) = off segs i + seg.length := by
  simp only [off]
  rw [List.take_add_one, h]
  simp

theorem body_split {segs : List (List (Inst VReg))} {pre : List (Inst VReg)} {i : Nat} {seg : List (Inst VReg)}
    (h : segs[i]? = some seg) :
    segs.flatten ++ pre = (segs.take i).flatten ++ seg ++ ((segs.drop (i + 1)).flatten ++ pre) := by
  have : segs = segs.take i ++ seg :: segs.drop (i + 1) := by
    have hlt : i < segs.length := (List.getElem?_eq_some_iff.1 h).1
    have he : segs[i] = seg := (List.getElem?_eq_some_iff.1 h).2
    conv => lhs; rw [← List.take_append_drop i segs]
    rw [List.drop_eq_getElem_cons hlt, he]
  conv => lhs; rw [this]
  simp

theorem off_len {segs : List (List (Inst VReg))} {n : Nat} (h : segs.length = n) : off segs n = segs.flatten.length := by
  simp [off, ← h]

/-- Xv's environment holds Lir's values below `N` outside `D`. -/
def EnvRel (N : Nat) (D : List VReg) (ρ σ : Env) : Prop :=
  ∀ u, u < N → u ∉ D → ∀ v, ρ[u]? = some v → σ[u]? = some v

theorem avoids_body {D : List VReg} {xb : Block VReg} (h : xb.avoids D = true) {i : Inst VReg}
    (hi : i ∈ xb.body.toList) : ∀ u ∈ i.uses, u ∉ D := by
  simp only [Block.avoids, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  intro u hu hD
  have := h.1 i hi u hu
  have : D.contains u = true := List.contains_iff_mem.2 hD
  simp_all

theorem avoids_term {D : List VReg} {xb : Block VReg} (h : xb.avoids D = true) :
    ∀ u ∈ xb.term.uses ++ xb.term.edgeUses, u ∉ D := by
  simp only [Block.avoids, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  intro u hu hD
  have := h.2 u hu
  have : D.contains u = true := List.contains_iff_mem.2 hD
  simp_all

/-- The registers instructions of the block read are related. -/
theorem EnvRel.agree {N : Nat} {D : List VReg} {ρ σ : Env} (h : EnvRel N D ρ σ) {S : List VReg}
    (hS : ∀ u ∈ S, u ∉ D) : Agree N S ρ σ :=
  fun u hu hN v hv => h u hN (hS u hu) v hv

theorem readsOf_avoid {D : List VReg} {xb : Block VReg} (h : xb.avoids D = true) {is : List (Inst VReg)}
    (hs : ∀ i ∈ is, i ∈ xb.body.toList) : ∀ u ∈ readsOf is, u ∉ D := by
  intro u hu
  simp only [readsOf, List.mem_flatMap] at hu
  obtain ⟨i, hi, hu⟩ := hu
  exact avoids_body h (hs i hi) u hu


/-! ## Binding, edges and calls -/

theorem bindParams_rel :
    ∀ {xs : List VReg} {vals : List Word} {ρ σ ρ' : Env}, Lir.bindParams ρ xs vals = some ρ' →
      ∃ σ', Lir.bindParams σ xs vals = some σ' ∧
        ∀ u, (u ∈ xs → σ'[u]? = ρ'[u]?) ∧ (u ∉ xs → σ'[u]? = σ[u]? ∧ ρ'[u]? = ρ[u]?)
  | [], [], ρ, σ, ρ', h => by
      simp only [Lir.bindParams, Option.some.injEq] at h
      subst h
      exact ⟨σ, rfl, fun u => ⟨fun h => by simp at h, fun _ => ⟨rfl, rfl⟩⟩⟩
  | [], _ :: _, _, _, _, h => by simp [Lir.bindParams] at h
  | _ :: _, [], _, _, _, h => by simp [Lir.bindParams] at h
  | x :: xs, v :: vs, ρ, σ, ρ', h => by
      simp only [Lir.bindParams] at h ⊢
      obtain ⟨σ', hb, hu⟩ := bindParams_rel (σ := σ.insert x v) h
      refine ⟨σ', hb, fun u => ⟨fun hm => ?_, fun hm => ?_⟩⟩
      · by_cases hxs : u ∈ xs
        · exact (hu u).1 hxs
        · rcases List.mem_cons.1 hm with hux | hux
          · subst hux
            obtain ⟨h₁, h₂⟩ := (hu u).2 hxs
            rw [h₁, h₂]
            simp
          · exact absurd hux hxs
      · simp only [List.mem_cons, not_or] at hm
        obtain ⟨h₁, h₂⟩ := (hu u).2 hm.2
        rw [h₁, h₂, insert_ne (Ne.symm hm.1), insert_ne (Ne.symm hm.1)]
        exact ⟨rfl, rfl⟩

theorem EnvRel.bind {N : Nat} {D : List VReg} {ρ σ ρ' : Env} {xs : List VReg} {vals : List Word}
    (h : EnvRel N D ρ σ) (hb : Lir.bindParams ρ xs vals = some ρ') :
    ∃ σ', Lir.bindParams σ xs vals = some σ' ∧ EnvRel N D ρ' σ' := by
  obtain ⟨σ', hb', hu⟩ := bindParams_rel (σ := σ) hb
  refine ⟨σ', hb', fun u hN hD v hv => ?_⟩
  by_cases hm : u ∈ xs
  · rw [(hu u).1 hm]; exact hv
  · obtain ⟨h₁, h₂⟩ := (hu u).2 hm
    rw [h₁]; rw [h₂] at hv; exact h u hN hD v hv

theorem EnvRel.insert {N : Nat} {D : List VReg} {ρ σ : Env} (h : EnvRel N D ρ σ) (x : VReg) (v : Word) :
    EnvRel N D (ρ.insert x v) (σ.insert x v) := by
  intro u hN hD w hw
  by_cases hx : x = u
  · subst hx; simpa using hw
  · rw [insert_ne hx] at hw ⊢; exact h u hN hD w hw

theorem EnvRel.above {N n : Nat} {D : List VReg} {ρ σ σ' : Env} (h : EnvRel N D ρ σ)
    (hab : ∀ u, u < n → σ'[u]? = σ[u]?) (hN : N ≤ n) : EnvRel N D ρ σ' :=
  fun u hu hD v hv => by rw [hab u (Nat.lt_of_lt_of_le hu hN)]; exact h u hu hD v hv

theorem takeEdge_inv {F : Lir.Func} {s : State} {fr : Frame} {rest : List Frame} {ρ : Env} {e : Lir.Edge}
    {s₁ : State} {b : Bool} (h : Lir.takeEdge F s fr rest ρ e = .next s₁ b) :
    ∃ vals tb ρ', Lir.evalArgs ρ e.args = some vals ∧ F.blocks[e.target]? = some tb ∧
      Lir.bindParams ρ tb.params vals = some ρ' ∧
      s₁ = { s with stack := { fr with label := e.target, pos := 0, env := ρ' } :: rest } ∧
      b = decide (e.target ≤ fr.label) := by
  unfold Lir.takeEdge at h
  split at h
  · rename_i vals tb hv ht
    split at h
    · rename_i ρ' hp
      simp only [Lir.Step.next.injEq] at h
      exact ⟨vals, tb, ρ', hv, ht, hp, h.1.symm, h.2.symm⟩
    · cases h
  · cases h

theorem xv_takeEdge {xf : Func VReg} {s : State} {fr : Frame} {rest : List Frame} {σ σ' : Env} {e : Edge VReg}
    {vals : List Word} {xtb : Block VReg} (hr : readAll σ e.args = some vals) (ht : xf.blocks[e.target]? = some xtb)
    (hp : Lir.bindParams σ xtb.params vals = some σ') :
    Xv.takeEdge xf s fr rest σ e =
      .next { s with stack := { fr with label := e.target, pos := 0, env := σ' } :: rest } (decide (e.target ≤ fr.label)) := by
  unfold Xv.takeEdge
  simp only [hr, ht, hp]

theorem enter_rel {p : Lir.Program} {q : VProgram} (hps : ProgSel p q) {g : Lir.FunId} {vals : List Word}
    {callee : Frame} (he : Lir.enter p g vals = some callee) : Xv.enter q g vals = some callee := by
  simp only [Lir.enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at he
  obtain ⟨f, hf, ρ, hρ, rfl⟩ := he
  obtain ⟨xf, D, hxf, hfs⟩ := hps.func g f hf
  simp [Xv.enter, hxf, hfs.params, hρ]

/-! ## The relation -/

/-- The pending facts of a frame: at the running frame, in the current
memory; at a suspended frame, after its call's results bind. -/
def PendRel (c : Ctx) : Bool → Frame → X86.Memory → Word → Prop
  | true, fr, mem, ctx => PendInv c fr.pos fr.env mem ctx
  | false, fr, _, ctx => ∀ ρ' mem', (∀ u, u ∉ fr.dsts → ρ'[u]? = fr.env[u]?) → PendInv c fr.pos ρ' mem' ctx

/-- A frame's block, selected, at a Lir position and its Xv position. -/
def BlockAt (fn : Lir.FunId) (f : Lir.Func) (xf : Func VReg) (D : List VReg) (l : Lir.Label) (pos xpos : Nat)
    (pend : Ctx → Prop) : Prop :=
  ∀ b, f.blocks[l]? = some b → ∃ xb segs pre C, xf.blocks[l]? = some xb ∧ xb.params = b.params ∧
    BlockSel (blockCtx fn (useCounts f) l b.body.toList) (maxVReg f + 1) b.term segs pre xb.term C ∧
    xb.body.toList = segs.flatten ++ pre ∧ (∀ u ∈ consumedDefs b.body.toList C, u ∈ D) ∧ xb.avoids D = true ∧
    pos ≤ b.body.size ∧ xpos = off segs pos ∧ pend (blockCtx fn (useCounts f) l b.body.toList)

/-- A Lir frame and its Xv frame. -/
def FrameRel (p : Lir.Program) (q : VProgram) (mem : X86.Memory) (ctx : Word) (top : Bool) (fr fr' : Frame) : Prop :=
  fr'.fn = fr.fn ∧ fr'.label = fr.label ∧ fr'.dsts = fr.dsts ∧
  ∃ f xf D, p.funcs[fr.fn]? = some f ∧ q.funcs[fr.fn]? = some xf ∧ FuncSel fr.fn f xf D ∧
    EnvRel (maxVReg f + 1) D fr.env fr'.env ∧
    BlockAt fr.fn f xf D fr.label fr.pos fr'.pos (fun c => PendRel c top fr mem ctx)

/-- Two lists related pointwise. -/
inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → Forall2 R as bs → Forall2 R (a :: as) (b :: bs)

/-- Lir and Xv stacks: the running frames, then the suspended ones. -/
def StackRel (p : Lir.Program) (q : VProgram) (mem : X86.Memory) (ctx : Word) : List Frame → List Frame → Prop
  | [], [] => True
  | fr :: rest, fr' :: rest' => FrameRel p q mem ctx true fr fr' ∧ Forall2 (FrameRel p q mem ctx false) rest rest'
  | _, _ => False

/-- Related Lir and Xv states. -/
def StateRel (p : Lir.Program) (q : VProgram) (s s' : State) : Prop :=
  s'.mem = s.mem ∧ s'.ctx = s.ctx ∧ StackRel p q s.mem s.ctx s.stack s'.stack

theorem FrameRel.susp {p : Lir.Program} {q : VProgram} {mem mem' : X86.Memory} {ctx : Word} {fr fr' : Frame}
    (h : FrameRel p q mem ctx false fr fr') : FrameRel p q mem' ctx false fr fr' := h

theorem forall₂_susp {p : Lir.Program} {q : VProgram} {mem mem' : X86.Memory} {ctx : Word} :
    ∀ {rest rest' : List Frame}, Forall2 (FrameRel p q mem ctx false) rest rest' →
      Forall2 (FrameRel p q mem' ctx false) rest rest'
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons h hs => .cons h.susp (forall₂_susp hs)

/-- A function's entry frame is related to itself. -/
theorem entry_rel {p : Lir.Program} {q : VProgram} (hps : ProgSel p q) {g : Lir.FunId} {vals : List Word}
    {callee : Frame} (he : Lir.enter p g vals = some callee) (mem : X86.Memory) (ctx : Word) :
    FrameRel p q mem ctx true callee callee := by
  have he' := he
  simp only [Lir.enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at he'
  obtain ⟨f, hf, ρ, hρ, rfl⟩ := he'
  obtain ⟨xf, D, hxf, hfs⟩ := hps.func g f hf
  refine ⟨rfl, rfl, rfl, f, xf, D, hf, hxf, hfs, fun u _ _ v hv => hv, fun b hb => ?_⟩
  obtain ⟨xb, segs, pre, C, hxb, hpar, hbs, hbody, hD, hav⟩ := hfs.block 0 b hb
  exact ⟨xb, segs, pre, C, hxb, hpar, hbs, hbody, hD, hav, Nat.zero_le _, by simp [off], PendInv.zero _ _ _ _⟩


/-! ## Registers of a block -/

theorem stmt_low {F : Lir.Func} {l : Nat} {B : Lir.Block} (hB : F.blocks[l]? = some B) {i : Nat} {s : Lir.Stmt}
    (hs : B.body.toList[i]? = some s) :
    (∀ u ∈ s.uses, u < maxVReg F + 1) ∧ (∀ u ∈ s.defs, u < maxVReg F + 1) := by
  have hmem : s ∈ B.body.toList := List.mem_of_getElem? hs
  refine ⟨fun u hu => maxVReg_block hB ?_, fun u hu => maxVReg_block hB ?_⟩
  · simp only [blockRegs, List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inl (.inr ⟨s, hmem, .inl hu⟩)))
  · simp only [blockRegs, List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inl (.inr ⟨s, hmem, .inr hu⟩)))

theorem term_low {F : Lir.Func} {l : Nat} {B : Lir.Block} (hB : F.blocks[l]? = some B) :
    (∀ u ∈ B.term.uses, u < maxVReg F + 1) ∧ (∀ u ∈ B.term.defs, u < maxVReg F + 1) ∧
      (∀ u ∈ B.term.edgeUses, u < maxVReg F + 1) := by
  refine ⟨fun u hu => maxVReg_block hB ?_, fun u hu => maxVReg_block hB ?_, fun u hu => maxVReg_block hB ?_⟩ <;>
    simp only [blockRegs, List.mem_append]
  · exact .inl (.inl (.inr hu))
  · exact .inl (.inr hu)
  · exact .inr hu

theorem params_low {F : Lir.Func} {l : Nat} {B : Lir.Block} (hB : F.blocks[l]? = some B) :
    ∀ u ∈ B.params, u < maxVReg F + 1 := fun u hu => maxVReg_block hB (by
  simp only [blockRegs, List.mem_append]
  exact .inl (.inl (.inl (.inl hu))))

theorem consumed_dead {body : List Lir.Stmt} {C : List Nat} {D : List VReg}
    (hD : ∀ u ∈ consumedDefs body C, u ∈ D) {i : Nat} (hi : i ∈ C) {y : VReg} {r : Lir.Rhs}
    (hs : body[i]? = some (.assign y r)) : y ∈ D :=
  hD y (List.mem_flatMap.2 ⟨i, hi, by simp [hs, Lir.Stmt.defs]⟩)

/-! ## A statement other than a call -/

theorem stmt_next {p : Lir.Program} {q : VProgram} {mem mem' : X86.Memory} {ctx : Word} {fr fr' : Frame}
    {rest rest' : List Frame} {F : Lir.Func} {B : Lir.Block} {ρ' : Env}
    (hfr : FrameRel p q mem ctx true fr fr') (hrest : Forall2 (FrameRel p q mem ctx false) rest rest')
    (hF : p.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B) (hp : fr.pos < B.body.size)
    (hnc : B.body[fr.pos].isCall = false) (hx : B.body[fr.pos].exec fr.env mem ctx = some (ρ', mem')) :
    ∃ s₂', Sem.Star (Xv.step q) { mem, ctx, stack := fr' :: rest' } 0 s₂' ∧
      StateRel p q { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := ρ' } :: rest } s₂' := by
  obtain ⟨hfn, hl, hd, f, xf, D, hf, hxf, hfs, henv, hblk⟩ := hfr
  rw [hF] at hf
  cases hf
  obtain ⟨xb, segs, pre, C, hxb, hpar, hbs, hbody, hD, hav, hpos, hxpos, hpend⟩ := hblk B hB
  have hs : (blockCtx fr.fn (useCounts F) fr.label B.body.toList).body[fr.pos]? = some B.body[fr.pos] := by
    simp [blockCtx]
  have hs' : B.body.toList[fr.pos]? = some B.body[fr.pos] := by simp
  obtain ⟨hsu, hsd⟩ := stmt_low hB hs'
  have hxf' : q.funcs[fr'.fn]? = some xf := by rw [hfn]; exact hxf
  have hxb' : xf.blocks[fr'.label]? = some xb := by rw [hl]; exact hxb
  by_cases hC : fr.pos ∈ C
  · -- a consumed statement: an assignment of a folded register, nothing in Xv
    obtain ⟨y, r, hdy⟩ := hbs.cons fr.pos hC
    have hsy : B.body[fr.pos] = .assign y r := by
      have := defSites_spec (body := B.body.toList) hdy
      rw [hs'] at this
      exact Option.some.inj this
    have hseg := hbs.skip fr.pos (by simpa [blockCtx] using hp) hC
    have hyD : y ∈ D := consumed_dead hD hC (by rw [hs', hsy])
    rw [hsy] at hx
    simp only [Lir.Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨v, hv, rfl, rfl⟩ := hx
    refine ⟨_, .refl _, rfl, rfl, ⟨hfn, hl, hd, F, xf, D, hF, hxf, hfs, ?_, ?_⟩, hrest⟩
    · intro u hu hD' w hw
      rw [insert_ne (t := y) (fun h => hD' (by rw [← h]; exact hyD))] at hw
      exact henv u hu hD' w hw
    · intro b hb
      rw [hB] at hb
      cases hb
      refine ⟨xb, segs, pre, C, hxb, hpar, hbs, hbody, hD, hav, hp, ?_, ?_⟩
      · rw [off_succ hseg, hxpos]; rfl
      · exact PendInv.step (blockCtx_ok _ _ _ _) hs (by rw [hsy]; simp [Lir.Stmt.exec, hv]) hpend
  · -- a selected statement: its segment runs
    obtain ⟨sti, sti', seg, hle, hseg, hsel⟩ := hbs.stmt fr.pos _ hs hC
    have hok := selectStmt_ok (c := { blockCtx fr.fn (useCounts F) fr.label B.body.toList with site := some fr.pos })
      rfl hnc hsel
    have hsplit := body_split (pre := pre) hseg
    have hsub : ∀ i ∈ seg, i ∈ xb.body.toList := fun i hi => by rw [hbody, hsplit]; simp [hi]
    obtain ⟨σ', hex, hregs⟩ := hok.2 (maxVReg F + 1) fr.env fr'.env ρ' mem mem' ctx
      (ctxLow_block hB fr.fn (useCounts F) fr.label) hle hsu hsd hx
      (PendInv.pend (c' := { blockCtx fr.fn (useCounts F) fr.label B.body.toList with site := some fr.pos })
        (blockCtx_ok _ _ _ _) rfl rfl rfl hok.1 hpend)
      (henv.agree (readsOf_avoid hav hsub))
    have hstar := xv_star_seq (rest := rest') hxf' hxb' seg (segs.take fr.pos).flatten
      ((segs.drop (fr.pos + 1)).flatten ++ pre) fr' mem mem' σ' rfl rfl (by rw [hbody, hsplit])
      (by rw [hxpos]; rfl) hex
    refine ⟨_, hstar, rfl, rfl, ⟨by simp [hfn], by simp [hl], by simp [hd], F, xf, D, hF, hxf, hfs, ?_, ?_⟩,
      forall₂_susp hrest⟩
    · intro u hu hD' w hw
      obtain ⟨hother, -⟩ := exec_other hx
      have hu' : u < sti.next := Nat.lt_of_lt_of_le hu hle
      by_cases hm : u ∈ B.body[fr.pos].defs
      · simp only
        rw [(hregs u hu').1 hm]; exact hw
      · simp only
        rw [(hregs u hu').2 hm]
        rw [hother u hm] at hw
        exact henv u hu hD' w hw
    · intro b hb
      rw [hB] at hb
      cases hb
      refine ⟨xb, segs, pre, C, hxb, hpar, hbs, hbody, hD, hav, hp, ?_, ?_⟩
      · show _ = off segs (fr.pos + 1)
        rw [off_succ hseg]; rfl
      · exact PendInv.step (blockCtx_ok _ _ _ _) hs hx hpend


/-! ## A call -/

theorem call_next {p : Lir.Program} {q : VProgram} (hps : ProgSel p q) {mem : X86.Memory} {ctx : Word}
    {fr fr' : Frame} {rest rest' : List Frame} {F : Lir.Func} {B : Lir.Block} {rs : List VReg} {g : Lir.FunId}
    {as : List Lir.Arg} {vs : List Word} {callee : Frame}
    (hfr : FrameRel p q mem ctx true fr fr') (hrest : Forall2 (FrameRel p q mem ctx false) rest rest')
    (hF : p.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B) (hp : fr.pos < B.body.size)
    (hcall : B.body[fr.pos] = .call rs g as) (hvs : Lir.evalArgs fr.env as = some vs)
    (he : Lir.enter p g vs = some callee) :
    ∃ s₂', Sem.Star (Xv.step q) { mem, ctx, stack := fr' :: rest' } 1 s₂' ∧
      StateRel p q { mem, ctx, stack := callee :: { fr with pos := fr.pos + 1, dsts := rs } :: rest } s₂' := by
  obtain ⟨hfn, hl, hd, f, xf, D, hf, hxf, hfs, henv, hblk⟩ := hfr
  rw [hF] at hf
  cases hf
  obtain ⟨xb, segs, pre, C, hxb, hpar, hbs, hbody, hD, hav, hpos, hxpos, hpend⟩ := hblk B hB
  have hs : (blockCtx fr.fn (useCounts F) fr.label B.body.toList).body[fr.pos]? = some (.call rs g as) := by
    rw [← hcall]; simp [blockCtx, hp]
  have hs' : B.body.toList[fr.pos]? = some (.call rs g as) := by rw [← hcall]; simp [hp]
  obtain ⟨hsu, -⟩ := stmt_low hB hs'
  have hxf' : q.funcs[fr'.fn]? = some xf := by rw [hfn]; exact hxf
  have hxb' : xf.blocks[fr'.label]? = some xb := by rw [hl]; exact hxb
  have hC : fr.pos ∉ C := by
    intro hC
    obtain ⟨y, r, hdy⟩ := hbs.cons fr.pos hC
    have := defSites_spec (body := B.body.toList) hdy
    rw [hs'] at this
    cases this
  obtain ⟨sti, sti', seg, hle, hseg, hsel⟩ := hbs.stmt fr.pos _ hs hC
  obtain ⟨xvs, prec, rfl, hn, hc, hr, hu, hv⟩ := selectCall_spec hsel
  have hsplit := body_split (pre := pre) hseg
  have hsub : ∀ i ∈ prec ++ [.call g xvs rs], i ∈ xb.body.toList := fun i hi => by
    rw [hbody, hsplit]; simp only [List.mem_append] at hi ⊢; exact .inl (.inr hi)
  have hag := henv.agree (readsOf_avoid hav hsub)
  have hvs' : Lir.evalArgs fr'.env as = some vs :=
    hag.args (fun u hu' => by simp [hr, Inst.uses, hu u hu']) (fun u hu' => hsu u (by simpa [Lir.Stmt.uses] using hu'))
      hvs
  obtain ⟨σ₁, he₁, hr₁, hab₁⟩ := hv fr'.env mem ctx vs
    (fun u hu' => Nat.lt_of_lt_of_le (hsu u (by simpa [Lir.Stmt.uses] using hu')) hle) hvs'
  have hstar := xv_star_seq (rest := rest') hxf' hxb' prec (segs.take fr.pos).flatten
    (.call g xvs rs :: ((segs.drop (fr.pos + 1)).flatten ++ pre)) fr' mem mem σ₁ rfl rfl
    (by rw [hbody, hsplit]; simp) (by rw [hxpos]; rfl) he₁
  have hcallx := xv_step_call (rest := rest') (mem := mem) (ctx := ctx) (g := g) (vs := xvs) (rs := rs)
    (fr := { fr' with pos := (segs.take fr.pos).flatten.length + prec.length, env := σ₁ }) hxf' hxb'
    (by rw [hbody, hsplit]; simp) hr₁ (enter_rel hps he)
  refine ⟨{ mem, ctx, stack := callee ::
      { fr' with pos := (segs.take fr.pos).flatten.length + prec.length + 1, env := σ₁, dsts := rs } :: rest' },
    by simpa using hstar.trans (Sem.Star.single hcallx), rfl, rfl, entry_rel hps he mem ctx, .cons ?_ hrest⟩
  refine ⟨by simp [hfn], by simp [hl], rfl, F, xf, D, hF, hxf, hfs, henv.above hab₁ (Nat.le_trans (Nat.le_refl _) hle),
    fun b hb => ?_⟩
  rw [hB] at hb
  cases hb
  refine ⟨xb, segs, pre, C, hxb, hpar, hbs, hbody, hD, hav, hp, ?_, ?_⟩
  · show _ = off segs (fr.pos + 1)
    rw [off_succ hseg]
    simp [off]
    omega
  · exact PendInv.call (blockCtx_ok _ _ _ _) hs hpend


/-! ## Terminators -/

/-- At a block's terminator: the Xv frame stands at the terminator's prefix,
which, with the terminator, does what the Lir terminator does. -/
theorem term_setup {p : Lir.Program} {q : VProgram} {mem : X86.Memory} {ctx : Word} {fr fr' : Frame}
    {F : Lir.Func} {B : Lir.Block} (hfr : FrameRel p q mem ctx true fr fr') (hF : p.funcs[fr.fn]? = some F)
    (hB : F.blocks[fr.label]? = some B) (hp : ¬ fr.pos < B.body.size) :
    ∃ (xf : Func VReg) (D : List VReg) (xb : Block VReg) (segs : List (List (Inst VReg))) (pre : List (Inst VReg))
      (n : Nat), q.funcs[fr'.fn]? = some xf ∧ xf.blocks[fr'.label]? = some xb ∧ FuncSel fr.fn F xf D ∧
      EnvRel (maxVReg F + 1) D fr.env fr'.env ∧ xb.body.toList = segs.flatten ++ pre ∧
      fr'.pos = segs.flatten.length ∧ maxVReg F + 1 ≤ n ∧ TermRun B.term pre xb.term fr.env fr'.env mem ctx n := by
  obtain ⟨hfn, hl, hd, f, xf, D, hf, hxf, hfs, henv, hblk⟩ := hfr
  rw [hF] at hf
  cases hf
  obtain ⟨xb, segs, pre, C, hxb, hpar, hbs, hbody, hD, hav, hpos, hxpos, hpend⟩ := hblk B hB
  have hpn : fr.pos = B.body.size := by omega
  obtain ⟨stT, stT', hle, hT⟩ := hbs.term
  have hok := selectTerm_ok hT
  obtain ⟨htu, htd, hte⟩ := term_low hB
  have hsub : ∀ i ∈ pre, i ∈ xb.body.toList := fun i hi => by rw [hbody]; simp [hi]
  refine ⟨xf, D, xb, segs, pre, stT.next, by rw [hfn]; exact hxf, by rw [hl]; exact hxb, hfs, henv, hbody, ?_, hle,
    hok.2 (maxVReg F + 1) fr.env fr'.env mem ctx (ctxLow_block hB _ _ _) hle htu htd hte
      (PendInv.pend (blockCtx_ok _ _ _ _) rfl rfl rfl hok.1 (by simpa [PendRel, Ctx.pos, blockCtx, hpn] using hpend)) ?_⟩
  · rw [hxpos, hpn, off_len (by rw [hbs.len]; simp [blockCtx])]
  · refine henv.agree fun u hu => ?_
    simp only [List.mem_append] at hu
    rcases hu with (hu | hu) | hu
    · exact readsOf_avoid hav hsub u hu
    · exact avoids_term hav u (List.mem_append_left _ hu)
    · exact avoids_term hav u (List.mem_append_right _ hu)

/-- The Xv run of a terminator's prefix. -/
theorem pre_star {q : VProgram} {mem : X86.Memory} {ctx : Word} {fr' : Frame} {rest' : List Frame} {xf : Func VReg}
    {xb : Block VReg} {segs : List (List (Inst VReg))} {pre : List (Inst VReg)} {σ' : Env}
    (hxf : q.funcs[fr'.fn]? = some xf) (hxb : xf.blocks[fr'.label]? = some xb)
    (hbody : xb.body.toList = segs.flatten ++ pre) (hpos : fr'.pos = segs.flatten.length)
    (hex : execSeq fr'.env mem ctx pre = some (σ', mem)) :
    Sem.Star (Xv.step q) { mem, ctx, stack := fr' :: rest' } 0
      { mem, ctx, stack := { fr' with pos := xb.body.size, env := σ' } :: rest' } := by
  have := xv_star_seq (rest := rest') hxf hxb pre segs.flatten [] fr' mem mem σ' rfl rfl (by simp [hbody]) hpos hex
  have hsz : segs.flatten.length + pre.length = xb.body.size := by
    rw [← Array.length_toList, hbody]; simp
  rwa [hsz] at this

/-- A related frame entering a block of its function. -/
theorem enter_block {p : Lir.Program} {q : VProgram} {mem : X86.Memory} {ctx : Word} {fr : Frame}
    {F : Lir.Func} {xf : Func VReg} {D : List VReg} (hF : p.funcs[fr.fn]? = some F) (hxf : q.funcs[fr.fn]? = some xf)
    (hfs : FuncSel fr.fn F xf D) {l : Lir.Label} {tb : Lir.Block} (htb : F.blocks[l]? = some tb) {ρ σ : Env}
    (henv : EnvRel (maxVReg F + 1) D ρ σ) {fr₁ fr₁' : Frame} (h₁ : fr₁ = { fr with label := l, pos := 0, env := ρ })
    (h₁' : fr₁'.fn = fr.fn ∧ fr₁'.label = l ∧ fr₁'.pos = 0 ∧ fr₁'.env = σ ∧ fr₁'.dsts = fr.dsts) :
    FrameRel p q mem ctx true fr₁ fr₁' := by
  subst h₁
  obtain ⟨h1, h2, h3, h4, h5⟩ := h₁'
  refine ⟨h1, h2, h5, F, xf, D, hF, hxf, hfs, by rw [h4]; exact henv, fun b hb => ?_⟩
  obtain ⟨xb, segs, pre, C, hxb, hpar, hbs, hbody, hD, hav⟩ := hfs.block l b hb
  exact ⟨xb, segs, pre, C, hxb, hpar, hbs, hbody, hD, hav, Nat.zero_le _, by rw [h3]; simp [off],
    PendInv.zero _ _ _ _⟩

/-- An edge taken from related frames to related frames. -/
theorem edge_next {p : Lir.Program} {q : VProgram} {mem : X86.Memory} {ctx : Word} {fr fr' : Frame}
    {rest rest' : List Frame} {F : Lir.Func} {xf : Func VReg} {D : List VReg} {s₁ : State} {b : Bool}
    {ρ σ : Env} {e : Lir.Edge} {e' : Edge VReg} (hF : p.funcs[fr.fn]? = some F) (hxf : q.funcs[fr.fn]? = some xf)
    (hfs : FuncSel fr.fn F xf D) (hfn : fr'.fn = fr.fn) (hl : fr'.label = fr.label) (hd : fr'.dsts = fr.dsts)
    (henv : EnvRel (maxVReg F + 1) D ρ σ) (hedge : EdgeRel e e' ρ σ)
    (hrest : Forall2 (FrameRel p q mem ctx false) rest rest')
    (h : Lir.takeEdge F { mem, ctx, stack := fr :: rest } fr rest ρ e = .next s₁ b) :
    ∃ s₂', Xv.takeEdge xf { mem, ctx, stack := fr' :: rest' } fr' rest' σ e' = .next s₂' b ∧ StateRel p q s₁ s₂' := by
  obtain ⟨vals, tb, ρ₁, hv, htb, hbp, rfl, rfl⟩ := takeEdge_inv h
  obtain ⟨σ₁, hbp', henv₁⟩ := henv.bind hbp
  obtain ⟨xtb, segs, pre, C, hxtb, hpar, -⟩ := hfs.block e.target tb htb
  have hr : readAll σ e'.args = some vals := hedge.2 vals hv
  have he' : e'.target = e.target := hedge.1
  refine ⟨{ mem, ctx, stack := { fr' with label := e'.target, pos := 0, env := σ₁ } :: rest' }, ?_, rfl, rfl,
    ?_, hrest⟩
  · rw [xv_takeEdge hr (by rw [he']; exact hxtb) (by rw [hpar]; exact hbp'), he', hl]
  · exact enter_block hF hxf hfs htb henv₁ rfl ⟨by simp [hfn], by simp [he'], rfl, rfl, by simp [hd]⟩


/-- The Xv step at a terminator, the terminator given. -/
theorem xv_term_eq {q : VProgram} {mem : X86.Memory} {ctx : Word} {fr : Frame} {rest : List Frame}
    {xf : Func VReg} {xb : Block VReg} {t : Term VReg} (hf : q.funcs[fr.fn]? = some xf)
    (hb : xf.blocks[fr.label]? = some xb) (hpos : fr.pos = xb.body.size) (ht : xb.term = t) :
    Xv.step q { mem, ctx, stack := fr :: rest } =
      match (generalizing := false) t with
      | .jmp e => takeEdge xf { mem, ctx, stack := fr :: rest } fr rest fr.env e
      | .jcc p' pargs defs c tt ff =>
          match execJcc p' pargs defs c fr.env mem ctx with
          | some (ρ, mem', taken) => takeEdge xf { mem := mem', ctx, stack := fr :: rest } fr rest ρ (if taken then tt else ff)
          | none => .stuck
      | .ret vs =>
          match readAll fr.env vs with
          | none => .stuck
          | some vals =>
              match rest with
              | [] => .done (vals, mem)
              | caller :: rest' =>
                  match Lir.bindParams caller.env caller.dsts vals with
                  | some ρ => .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest' } false
                  | none => .stuck
      | .tail g args =>
          match readAll fr.env args >>= Xv.enter q g with
          | some callee => .next { mem, ctx, stack := callee :: rest } true
          | none => .stuck
      | .fail r => .fail r
      | .trap => .trap := by
  have h := xv_step_term (rest := rest) (mem := mem) (ctx := ctx) hf hb hpos
  rw [ht] at h
  exact h

/-- Selection's lock-step diagram. -/
theorem select_lockstep {p : Lir.Program} {q : VProgram} (hps : ProgSel p q) :
    Xv.Validate.LockStep (Lir.semStep p) (Xv.step q) (StateRel p q) where
  next := by
    intro s₁ s₁' s₂ b hm hs
    obtain ⟨mem, ctx, stack⟩ := s₁
    obtain ⟨mem₂, ctx₂, stack₂⟩ := s₂
    obtain ⟨hmem, hctx, hstk⟩ := hm
    simp only at hmem hctx hstk
    subst mem₂ ctx₂
    cases stack with
    | nil => simp [Lir.semStep, Lir.step, Lir.Step.toSem] at hs
    | cons fr rest =>
      cases stack₂ with
      | nil => exact absurd hstk (by simp [StackRel])
      | cons fr' rest' =>
        obtain ⟨hfr, hrest⟩ := hstk
        obtain ⟨F, B, hF, hB, hcase⟩ := Lir.step_next_cases (Lir.semStep_next.1 hs)
        rcases hcase with ⟨hp, ⟨rs, g, as, vs, callee, hcall, hvs, he, rfl, rfl⟩ | ⟨ρ', mem', hnc, hx, rfl, rfl⟩⟩ |
          ⟨hp, hterm⟩
        · exact call_next hps hfr hrest hF hB hp hcall hvs he
        · exact stmt_next hfr hrest hF hB hp hnc hx
        · obtain ⟨xf, D, xb, segs, pre, n, hxf, hxb, hfs, henv, hbody, hpos, hn, hrun⟩ := term_setup hfr hF hB hp
          obtain ⟨hfn, hl, hd, -⟩ := hfr
          have hxf₀ : q.funcs[fr.fn]? = some xf := by rw [← hfn]; exact hxf
          rcases hterm with ⟨e, ht, hte⟩ | ⟨c, w, a, b', tt, ff, va, vb, ht, ha, hb, hte⟩ |
            ⟨o, x, a, b', ok, ovf, va, vb, ht, ha, hb, hte⟩ | ⟨as, vals, caller, rest₂, ρc, ht, hv, rfl, hbp, rfl, rfl⟩ |
            ⟨g, as, vs, callee, ht, hv, he, rfl, rfl⟩
          · -- jump
            rw [ht] at hrun
            obtain ⟨e', hxt, σ', hex, hab, hedge⟩ := hrun
            have hpre := pre_star (rest' := rest') hxf hxb hbody hpos hex
            have hstep := xv_term_eq (rest := rest') (mem := mem) (ctx := ctx)
              (fr := { fr' with pos := xb.body.size, env := σ' }) hxf hxb rfl hxt
            simp only at hstep
            obtain ⟨s₂', hte', hrel⟩ := edge_next (fr' := { fr' with pos := xb.body.size, env := σ' }) hF hxf₀ hfs
              hfn hl hd (henv.above hab hn) hedge hrest hte
            rw [hte'] at hstep
            exact ⟨s₂', by simpa using hpre.trans (Sem.Star.single hstep), hrel⟩
          · -- br
            rw [ht] at hrun
            obtain ⟨p', pargs, cond, tt', ff', hxt, hrun⟩ := hrun
            obtain ⟨σ', hex, hab, hj, htt, hff⟩ := hrun va vb ha hb
            have hpre := pre_star (rest' := rest') hxf hxb hbody hpos hex
            have hstep := xv_term_eq (rest := rest') (mem := mem) (ctx := ctx)
              (fr := { fr' with pos := xb.body.size, env := σ' }) hxf hxb rfl hxt
            simp only [hj] at hstep
            obtain ⟨s₂', hte', hrel⟩ := edge_next (fr' := { fr' with pos := xb.body.size, env := σ' })
              (e' := if c.holds w va vb then tt' else ff') hF hxf₀ hfs hfn hl hd (henv.above hab hn)
              (by split <;> assumption) hrest hte
            rw [hte'] at hstep
            exact ⟨s₂', by simpa using hpre.trans (Sem.Star.single hstep), hrel⟩
          · -- brOvf
            rw [ht] at hrun
            obtain ⟨p', pargs, ok', ovf', hxt, hrun⟩ := hrun
            obtain ⟨σ', hex, hab, hj, hok, hovf⟩ := hrun va vb ha hb
            have hpre := pre_star (rest' := rest') hxf hxb hbody hpos hex
            have hstep := xv_term_eq (rest := rest') (mem := mem) (ctx := ctx)
              (fr := { fr' with pos := xb.body.size, env := σ' }) hxf hxb rfl hxt
            simp only [hj] at hstep
            obtain ⟨s₂', hte', hrel⟩ := edge_next (fr' := { fr' with pos := xb.body.size, env := σ' })
              (e' := if (o.eval va vb).2 then ovf' else ok') hF hxf₀ hfs hfn hl hd ((henv.above hab hn).insert x _)
              (by split <;> assumption) hrest hte
            rw [hte'] at hstep
            exact ⟨s₂', by simpa using hpre.trans (Sem.Star.single hstep), hrel⟩
          · -- ret to a caller
            rw [ht] at hrun
            obtain ⟨vs, hxt, σ', hex, hab, hvals⟩ := hrun
            cases hrest with
            | cons hc hrest₂ =>
              rename_i caller' rest₂'
              obtain ⟨hcfn, hcl, hcd, cF, cxf, cD, hcF, hcxf, hcfs, hcenv, hcblk⟩ := hc
              obtain ⟨σc, hbp', hcenv'⟩ := hcenv.bind hbp
              have hpre := pre_star (rest' := caller' :: rest₂') hxf hxb hbody hpos hex
              have hstep := xv_term_eq (rest := caller' :: rest₂') (mem := mem) (ctx := ctx)
                (fr := { fr' with pos := xb.body.size, env := σ' }) hxf hxb rfl hxt
              simp only [hvals vals hv, hcd, hbp'] at hstep
              refine ⟨{ mem, ctx, stack := { caller' with env := σc, dsts := [] } :: rest₂' },
                by simpa using hpre.trans (Sem.Star.single hstep), rfl, rfl,
                ⟨hcfn, hcl, rfl, cF, cxf, cD, hcF, hcxf, hcfs, hcenv', fun cb hcb => ?_⟩, hrest₂⟩
              obtain ⟨xb', segs', pre', C', hxb', hpar', hbs', hbody', hD', hav', hpos', hxpos', hpend'⟩ := hcblk cb hcb
              refine ⟨xb', segs', pre', C', hxb', hpar', hbs', hbody', hD', hav', hpos', hxpos', ?_⟩
              exact hpend' ρc mem (fun u hu => Xv.Validate.bindParams_other hbp hu)
          · -- tail
            rw [ht] at hrun
            obtain ⟨xvs, hxt, σ', hex, hab, hvals⟩ := hrun
            have hpre := pre_star (rest' := rest') hxf hxb hbody hpos hex
            have hstep := xv_term_eq (rest := rest') (mem := mem) (ctx := ctx)
              (fr := { fr' with pos := xb.body.size, env := σ' }) hxf hxb rfl hxt
            simp [hvals vs hv, enter_rel hps he] at hstep
            exact ⟨{ mem, ctx, stack := callee :: rest' }, by simpa using hpre.trans (Sem.Star.single hstep), rfl, rfl,
              entry_rel hps he mem ctx, hrest⟩
  final := by
    intro s₁ s₂ r hm hf hr
    obtain ⟨mem, ctx, stack⟩ := s₁
    obtain ⟨mem₂, ctx₂, stack₂⟩ := s₂
    obtain ⟨hmem, hctx, hstk⟩ := hm
    simp only at hmem hctx hstk
    subst mem₂ ctx₂
    cases stack with
    | nil =>
      simp only [Lir.semStep, Lir.step, Lir.Step.toSem] at hf
      cases hf
      exact absurd rfl hr
    | cons fr rest =>
      cases stack₂ with
      | nil => exact absurd hstk (by simp [StackRel])
      | cons fr' rest' =>
        obtain ⟨hfr, hrest⟩ := hstk
        obtain ⟨F, B, hF, hB, hp, hcase⟩ := Lir.step_final_cases hf hr
        obtain ⟨xf, D, xb, segs, pre, n, hxf, hxb, hfs, henv, hbody, hpos, hn, hrun⟩ := term_setup hfr hF hB hp
        rcases hcase with ⟨as, vals, ht, hv, rfl, rfl⟩ | ⟨fl, ht, rfl⟩ | ⟨ht, rfl⟩
        · rw [ht] at hrun
          obtain ⟨vs, hxt, σ', hex, hab, hvals⟩ := hrun
          cases hrest
          have hpre := pre_star (rest' := []) hxf hxb hbody hpos hex
          have hstep := xv_term_eq (rest := []) (mem := mem) (ctx := ctx)
            (fr := { fr' with pos := xb.body.size, env := σ' }) hxf hxb rfl hxt
          simp only [hvals vals hv] at hstep
          exact ⟨_, hpre, by rw [hstep]; exact .done⟩
        · rw [ht] at hrun
          obtain ⟨hxt, rfl⟩ := hrun
          have hstep := xv_term_eq (rest := rest') (mem := mem) (ctx := ctx) (fr := fr') hxf hxb
            (by rw [hpos, ← Array.length_toList, hbody]; simp) hxt
          exact ⟨_, .refl _, by rw [hstep]; exact .fail⟩
        · rw [ht] at hrun
          obtain ⟨hxt, rfl⟩ := hrun
          have hstep := xv_term_eq (rest := rest') (mem := mem) (ctx := ctx) (fr := fr') hxf hxb
            (by rw [hpos, ← Array.length_toList, hbody]; simp) hxt
          exact ⟨_, .refl _, by rw [hstep]; exact .trap⟩


/-! ## Whole programs -/

/-- The initial states are the same state, related to itself. -/
theorem initial_rel {p : Lir.Program} {q : VProgram} (hps : ProgSel p q) {args : List Word} {mem : X86.Memory}
    {ctx : Word} {s : State} (h : Lir.State.initial p args mem ctx = some s) :
    Xv.State.initial q args mem ctx = some s ∧ StateRel p q s s := by
  simp only [Lir.State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨fr, he, rfl⟩ := h
  refine ⟨by simp [Xv.State.initial, hps.main, enter_rel hps he], rfl, rfl, entry_rel hps he mem ctx, .nil⟩

/-- Per clock: the selected program has the Lir program's outcome unless
that is stuck, timeouts included. -/
theorem prog_eval_eq {p : Lir.Program} {q : VProgram} (hps : ProgSel p q) {k : Nat} {args : List Word}
    {mem : X86.Memory} {ctx : Word} (hk : Lir.eval p k args mem ctx ≠ .stuck) :
    Xv.eval q k args mem ctx = Lir.eval p k args mem ctx := by
  cases hi : Lir.State.initial p args mem ctx with
  | none => exact absurd (by simp [Lir.eval, hi]) hk
  | some s =>
    obtain ⟨hi', hm⟩ := initial_rel hps hi
    exact (select_lockstep hps).eq hm (Lir.runs_eval hi) (Xv.runs_eval hi') hk

theorem prog_sim {p : Lir.Program} {q : VProgram} (hps : ProgSel p q) (args : List Word) (mem : X86.Memory)
    (ctx : Word) : Sem.Sim Eq id (fun k => Lir.eval p k args mem ctx) (fun k => Xv.eval q k args mem ctx) := by
  cases hi : Lir.State.initial p args mem ctx with
  | none =>
    have hs : ∀ k, Lir.eval p k args mem ctx = .stuck := fun k => by simp [Lir.eval, hi]
    exact { forward := fun k _ => ⟨0, (hs k) ▸ .stuck⟩,
            timeout := fun k hk => absurd ((hs k).symm.trans hk) (by simp) }
  | some s =>
    obtain ⟨hi', hm⟩ := initial_rel hps hi
    exact (select_lockstep hps).sim hm (Lir.runs_eval hi) (Xv.runs_eval hi')

end IxCC.Xv.Select.Proof

namespace IxCC.Xv.Select

open IxCC.Lir (Word)
open IxCC.Xv.Select.Proof

/-- **Selection is correct, per clock** (`Select.select`, the recheck path):
on every input and at every clock, the selected program's outcome is the
Lir program's unless that is stuck, timeouts included. -/
theorem eval_eq {p : Lir.Program} {q : VProgram} (h : select p = .ok q) {k : Nat} {args : List Word}
    {mem : X86.Memory} {ctx : Word} (hk : Lir.eval p k args mem ctx ≠ .stuck) :
    Xv.eval q k args mem ctx = Lir.eval p k args mem ctx :=
  prog_eval_eq (select_spec h) hk

/-- A clocked simulation with the identity clock map and equal values. -/
theorem sim {p : Lir.Program} {q : VProgram} (h : select p = .ok q) (args : List Word) (mem : X86.Memory)
    (ctx : Word) : Sem.Sim Eq id (fun k => Lir.eval p k args mem ctx) (fun k => Xv.eval q k args mem ctx) :=
  prog_sim (select_spec h) args mem ctx

/-- **`Select.correct`**: a selected program refines its Lir program. On
every input, each behaviour of the Lir program other than a stuck one (a
result, divergence, a trap, a resource failure) is the Xv program's. -/
theorem correct {p : Lir.Program} {q : VProgram} (h : select p = .ok q) (args : List Word) (mem : X86.Memory)
    (ctx : Word) :
    Sem.Behaviour.Refines Eq (Sem.behaviour fun k => Lir.eval p k args mem ctx)
      (Sem.behaviour fun k => Xv.eval q k args mem ctx) :=
  (sim h args mem ctx).refines (Lir.eval_mono p args mem ctx) (Xv.eval_mono q args mem ctx)

/-- The traced form of `Select.sim`, for every environment and event type. -/
theorem tsim {Env E : Type} {p : Lir.Program} {q : VProgram} (h : select p = .ok q) (args : List Word)
    (mem : X86.Memory) (ctx : Word) :
    Sem.TSim (Env := Env) (E := E) Eq id (fun _ k => Sem.Traced.lift (Lir.eval p k args mem ctx))
      (fun _ k => Sem.Traced.lift (Xv.eval q k args mem ctx)) :=
  Sem.TSim.ofPure (sim h args mem ctx)

/-- `Select.run` (with the firing statistics) is correct per clock. -/
theorem run_eval_eq {p : Lir.Program} {q : VProgram} {fired : Std.TreeMap String Nat compare}
    (h : run p = .ok (q, fired)) {k : Nat} {args : List Word} {mem : X86.Memory} {ctx : Word}
    (hk : Lir.eval p k args mem ctx ≠ .stuck) : Xv.eval q k args mem ctx = Lir.eval p k args mem ctx :=
  prog_eval_eq (run_spec h) hk

theorem run_sim {p : Lir.Program} {q : VProgram} {fired : Std.TreeMap String Nat compare}
    (h : run p = .ok (q, fired)) (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id (fun k => Lir.eval p k args mem ctx) (fun k => Xv.eval q k args mem ctx) :=
  prog_sim (run_spec h) args mem ctx

/-- `Select.run` refines its Lir program. -/
theorem run_correct {p : Lir.Program} {q : VProgram} {fired : Std.TreeMap String Nat compare}
    (h : run p = .ok (q, fired)) (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Behaviour.Refines Eq (Sem.behaviour fun k => Lir.eval p k args mem ctx)
      (Sem.behaviour fun k => Xv.eval q k args mem ctx) :=
  (run_sim h args mem ctx).refines (Lir.eval_mono p args mem ctx) (Xv.eval_mono q args mem ctx)

end IxCC.Xv.Select
