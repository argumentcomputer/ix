import IxCC.Xv.Stacking.Proof.Call

/-!
# What a call needs

A function's facts (`Func.facts`) count its incoming arguments from its
parameters (`facts_inArgs`), record that it calls (`facts_calls`), and
bound the outgoing cells it names (`facts_outArgs`). A callee starts with
its register arguments in the convention's registers (`entryRegs_get`), its
stacked call is a `call` to its first block (`inst_call`), and its prologue
runs as checked steps (`prologue_steps`).
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-! ## Facts kept and gained -/

section
variable (P : Facts → Prop) (hloc : ∀ a l, P a → P (a.noteLoc l)) (hdef : ∀ a l, P a → P (a.noteDef l))
  (hcall : ∀ a, P a → P { a with calls := true })
include hloc hdef hcall

theorem inst_keep (a : Facts) (i : Inst Loc) (h : P a) : P (a.inst i) := by
  have h₁ := foldl_keeps P Facts.noteLoc hloc i.uses a h
  have h₂ := foldl_keeps P Facts.noteDef hdef i.defs _ h₁
  unfold Facts.inst
  cases i <;> first | exact h₂ | exact hcall _ h₂

theorem term_keep (a : Facts) (t : Term Loc) (h : P a) : P (a.term t) := by
  unfold Facts.term
  exact foldl_keeps P Facts.noteDef hdef _ _ (foldl_keeps P Facts.noteLoc hloc _ _ h)

theorem block_keep (a : Facts) (b : Block Loc) (h : P a) : P (a.block b) := by
  unfold Facts.block
  exact term_keep P hloc hdef hcall _ _ (foldl_keeps P Facts.inst (fun a i h => inst_keep P hloc hdef hcall a i h) _ _
    (foldl_keeps P Facts.noteDef hdef _ _ h))

/-- A fact every step keeps holds of a function if it holds initially. -/
theorem facts_keep (f : Func Loc) (h : P { inArgs := f.params.length - Xl.nArgRegs }) : P f.facts := by
  unfold Func.facts
  exact foldl_keeps P Facts.block (fun a b h => block_keep P hloc hdef hcall a b h) _ _ h

/-- A fact some instruction gains and every step keeps holds of the function. -/
theorem facts_gets (f : Func Loc) {b : Block Loc} (hb : b ∈ f.blocks.toList) {i : Inst Loc} (hi : i ∈ b.body.toList)
    (hgain : ∀ a : Facts, P (a.inst i)) : P f.facts := by
  unfold Func.facts
  refine foldl_gets P Facts.block (fun a b h => block_keep P hloc hdef hcall a b h) (fun a => ?_) _ _ hb
  unfold Facts.block
  exact term_keep P hloc hdef hcall _ _ (foldl_gets P Facts.inst (fun a i h => inst_keep P hloc hdef hcall a i h)
    hgain _ _ hi)

end

theorem facts_inArgs (f : Func Loc) : f.facts.inArgs = f.params.length - Xl.nArgRegs :=
  facts_keep (fun a => a.inArgs = f.params.length - Xl.nArgRegs)
    (fun a l h => by cases l <;> simpa [Facts.noteLoc] using h)
    (fun a l h => by
      cases l with
      | reg r => simp only [Facts.noteDef]; split <;> simpa using h
      | _ => simpa [Facts.noteDef, Facts.noteLoc] using h)
    (fun a h => h) f rfl

theorem facts_calls {f : Func Loc} {b : Block Loc} (hb : b ∈ f.blocks.toList) {g : Lir.FunId} {args rets : List Loc}
    (hi : Inst.call g args rets ∈ b.body.toList) : f.facts.calls = true :=
  facts_gets (fun a => a.calls = true)
    (fun a l h => by cases l <;> simpa [Facts.noteLoc] using h)
    (fun a l h => by
      cases l with
      | reg r => simp only [Facts.noteDef]; split <;> simpa using h
      | _ => simpa [Facts.noteDef, Facts.noteLoc] using h)
    (fun a _ => rfl) f hb hi (fun a => rfl)

theorem noteLoc_outArgs_le (a : Facts) (l : Loc) : a.outArgs ≤ (a.noteLoc l).outArgs := by
  cases l <;> simp [Facts.noteLoc] <;> omega

theorem facts_outArgs {f : Func Loc} {b : Block Loc} (hb : b ∈ f.blocks.toList) {i : Inst Loc}
    (hi : i ∈ b.body.toList) {k : Nat} (hk : Loc.outArg k ∈ i.uses) : k + 1 ≤ f.facts.outArgs := by
  have hmono : ∀ (a : Facts) (l : Loc), k + 1 ≤ a.outArgs → k + 1 ≤ (a.noteLoc l).outArgs := fun a l h =>
    Nat.le_trans h (noteLoc_outArgs_le a l)
  have hmonoDef : ∀ (a : Facts) (l : Loc), k + 1 ≤ a.outArgs → k + 1 ≤ (a.noteDef l).outArgs := fun a l h => by
    cases l with
    | reg r => simp only [Facts.noteDef]; split <;> simpa using h
    | _ => exact hmono a _ h
  refine facts_gets (fun a => k + 1 ≤ a.outArgs) hmono hmonoDef (fun a h => h) f hb hi (fun a => ?_)
  have h₁ : k + 1 ≤ (i.uses.foldl Facts.noteLoc a).outArgs :=
    foldl_gets (fun a : Facts => k + 1 ≤ a.outArgs) Facts.noteLoc hmono
      (fun a => by simp [Facts.noteLoc]; omega) _ _ hk
  have h₂ := foldl_keeps (fun a : Facts => k + 1 ≤ a.outArgs) Facts.noteDef hmonoDef i.defs _ h₁
  unfold Facts.inst
  cases i <;> exact h₂

/-! ## Entry registers -/

theorem foldl_set_get {rs : Xl.Regs} (hs : rs.size = 16) :
    ∀ (L : List (GPR × Word)) {r : GPR} {v : Word},
      (L.foldl (fun rs (p : GPR × Word) => rs.set p.1 (some p.2)) rs).get r = some v →
        (r, v) ∈ L ∨ rs.get r = some v
  | [], _, _, h => .inr h
  | (q, w) :: L, r, v, h => by
      rcases foldl_set_get (by rw [Xl.Regs.size_set, hs]) L h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · rw [Xl.Regs.get_set _ hs] at h
        split at h
        · rename_i e; subst e; cases h; exact .inl List.mem_cons_self
        · exact .inr h

theorem foldl_set_size {rs : Xl.Regs} (hs : rs.size = 16) :
    ∀ (L : List (GPR × Word)), (L.foldl (fun rs (p : GPR × Word) => rs.set p.1 (some p.2)) rs).size = 16
  | [] => hs
  | _ :: L => foldl_set_size (by rw [Xl.Regs.size_set, hs]) L

theorem entryRegs_size (vals : List Word) : (Xl.entryRegs vals).size = 16 :=
  foldl_set_size Xl.Regs.empty_size _

/-- A callee's registers: each argument register holds its argument. -/
theorem entryRegs_get {vals : List Word} {r : GPR} {v : Word} (h : (Xl.entryRegs vals).get r = some v) :
    ∃ i : Nat, Lir.Conv.argRegs[i]? = some r ∧ vals[i]? = some v := by
  rcases foldl_set_get Xl.Regs.empty_size _ h with h | h
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
    rw [List.getElem?_zip_eq_some] at hi
    exact ⟨i, hi.1, hi.2⟩
  · rw [Xl.Regs.get_empty] at h; cases h

/-! ## Reading arguments -/

theorem readAll_get {regs : Xl.Regs} {fr : Xl.Frame} :
    ∀ {ls : List Loc} {vs : List Word}, Xl.readAll regs fr ls = some vs →
      vs.length = ls.length ∧ ∀ (i : Nat) (l : Loc), ls[i]? = some l → ∃ v, vs[i]? = some v ∧ Xl.read regs fr l = some v
  | [], vs, h => by
      simp only [Xl.readAll, List.mapM_nil, pure, Option.some.injEq] at h
      subst h; exact ⟨rfl, fun _ _ h => by simp at h⟩
  | l :: ls, vs, h => by
      simp only [Xl.readAll, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v, hv, vs', hvs', rfl⟩ := h
      obtain ⟨hlen, hget⟩ := readAll_get (ls := ls) hvs'
      refine ⟨by simp [hlen], fun i l' hl' => ?_⟩
      cases i with
      | zero => simp at hl'; subst hl'; exact ⟨v, rfl, hv⟩
      | succ i => exact hget i l' (by simpa using hl')

theorem conventionArgs_get {args : List Loc} (h : Xl.conventionArgs args = true) {i : Nat} (hi : i < args.length) :
    args[i]? = some (Xl.argLoc i) := by
  simp only [Xl.conventionArgs, beq_iff_eq] at h
  rw [h]
  simp [hi]

theorem argLoc_reg {i : Nat} {r : GPR} (h : Lir.Conv.argRegs[i]? = some r) : Xl.argLoc i = .reg r := by
  simp [Xl.argLoc, h]

theorem argLoc_out {i : Nat} (h : Xl.nArgRegs ≤ i) : Xl.argLoc i = .outArg (i - Xl.nArgRegs) := by
  have : Lir.Conv.argRegs[i]? = none := List.getElem?_eq_none (by simpa [Xl.nArgRegs] using h)
  simp [Xl.argLoc, this]

theorem nArgRegs_eq : Xl.nArgRegs = 7 := rfl

/-! ## The stacked call -/

/-- A call's stacked code: a `call` to the callee's first block. -/
theorem inst_call {c : FnCtx} {g : Lir.FunId} {args rets : List Loc} {code : List Instr}
    (h : c.inst (.call g args rets) = .ok code) :
    ∃ entry arity, c.funcs.get? g = some (entry, arity) ∧ args.length = arity ∧
      code = [.call (UInt32.ofNat entry)] := by
  cases hg : c.funcs.get? g with
  | none =>
    rw [Std.TreeMap.get?_eq_getElem?] at hg
    simp [FnCtx.inst, FnCtx.callee, hg, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h
    split at h <;> simp at h
  | some ea =>
    obtain ⟨entry, arity⟩ := ea
    refine ⟨entry, arity, rfl, ?_⟩
    rw [Std.TreeMap.get?_eq_getElem?] at hg
    simp [FnCtx.inst, FnCtx.callee, hg, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h
    split at h
    · split at h
      · rename_i hl
        simp only [Except.ok.injEq] at h
        exact ⟨hl, h.symm⟩
      · simp at h
    · simp at h

/-! ## Frames and return slots -/

/-- Writes below every live return slot keep them. -/
theorem disjoint_below {frames : List ReturnFrame} {addr : Word} {count : Nat} {B : Nat}
    (hf : ∀ frame ∈ frames, ∀ i < 8, B ≤ (frame.returnSlot + UInt64.ofNat i).toNat)
    (ha : ∀ j < count, (addr + UInt64.ofNat j).toNat < B) : FramesDisjoint frames addr count := by
  intro frame hfr i hi j hj e
  have h₁ := hf frame hfr i hi
  have h₂ := ha j hj
  rw [e] at h₁
  omega

/-! ## The prologue -/

theorem saved_ne_rsp {l : FrameLayout} {a : Facts} (hs : l.Sound a) {r : GPR} (hr : r ∈ l.saved) : r ≠ .rsp := by
  have := (hs.savesExact r).1 hr
  simp only [saves, List.mem_filter] at this
  intro e; subst e
  simp [calleeSaved] at this

theorem saveOff_mem {l : FrameLayout} {r : GPR} {o : Nat} (h : (r, o) ∈ l.saveOff) : r ∈ l.saved :=
  List.mem_map.2 ⟨(r, o), h, rfl⟩

theorem frameless_saveOff {l : FrameLayout} {a : Facts} (hs : l.Sound a) (hz : l.size = 0) : l.saveOff = [] := by
  cases hl : l.saveOff with
  | nil => rfl
  | cons p ps =>
    have := (save_range hs (r := p.1) (o := p.2) (by rw [hl]; exact List.mem_cons_self)).2.2
    omega

theorem prologue_map (l : FrameLayout) :
    (l.saveOff.map fun (r, o) => Instr.store .w64 (rspAt o) r) =
      l.saveOff.map fun p => Instr.store .w64 (rspAt p.2) p.1 := by
  congr 1

theorem setReg_self (core : Core) (r : GPR) : core.setReg r (core.readReg r) = core := by
  obtain ⟨regs, mem⟩ := core
  simp only [Core.setReg, Core.readReg, Core.mk.injEq, and_true]
  funext q
  by_cases h : q = r <;> simp [Registers.set, h]

/-- The prologue from `rsp = Q`: `sub rsp, size`, then a store per saved
register, as checked steps. -/
theorem prologue_steps {cs : Checked} {blk : BlockId} {l : FrameLayout} {a : Facts} (hs : l.Sound a)
    {returns : List ReturnFrame} {holes : Holes} {core : Core} {Q : Word}
    (hseg : Straight.Segment cs blk 0 (prologue l)) (hfits : (prologue l).length < UInt32.size)
    (hQ : core.readReg .rsp = Q) (hQn : l.size ≤ Q.toNat)
    (hw : ∀ x, (Q - UInt64.ofNat l.size).toNat ≤ x.toNat → x.toNat < Q.toNat → core.memory.writable x = true)
    (hdis : ∀ frame ∈ returns, ∀ i < 8, Q.toNat ≤ (frame.returnSlot + UInt64.ofNat i).toNat) :
    ∃ mem' holes', SafeSteps Runtime.rejecting cs (prologue l).length holes (inFrame core blk 0 returns) holes'
        (inFrame { core.setReg .rsp (Q - UInt64.ofNat l.size) with memory := mem' } blk (prologue l).length returns) ∧
      mem'.readable = core.memory.readable ∧ mem'.writable = core.memory.writable ∧
      (∀ x, ¬((Q - UInt64.ofNat l.size).toNat ≤ x.toNat ∧ x.toNat < Q.toNat) → mem'.bytes x = core.memory.bytes x) ∧
      (∀ r o, (r, o) ∈ l.saveOff → mem'.read64 (Q - UInt64.ofNat l.size + UInt64.ofNat o) = core.readReg r) ∧
      (∀ x, holes' x → holes x) ∧
      (∀ r o, (r, o) ∈ l.saveOff → ReadableData holes' (Q - UInt64.ofNat l.size + UInt64.ofNat o) 8) := by
  have hbd := hs.bounded
  have hQs : (Q - UInt64.ofNat l.size).toNat = Q.toNat - l.size := by
    rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size, maxFrame, slack] at *; omega)]
      exact hQn), UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size, maxFrame, slack] at *; omega)]
  -- A save cell's bytes
  have hcellB : ∀ r o, (r, o) ∈ l.saveOff → ∀ i < 8,
      (Q - UInt64.ofNat l.size + UInt64.ofNat o + UInt64.ofNat i).toNat = Q.toNat - l.size + o + i := by
    intro r o hro i hi
    have hsr := save_range hs hro
    have hq : Q.toNat < 2 ^ 64 := Q.toBitVec.isLt
    have h1 : (Q - UInt64.ofNat l.size + UInt64.ofNat o).toNat = Q.toNat - l.size + o := by
      rw [addr_toNat (by rw [hQs]; omega), hQs]
    rw [addr_toNat (by rw [h1]; omega), h1]
  by_cases hz : l.size = 0
  · have hso := frameless_saveOff hs hz
    have hpro : prologue l = [] := by simp [prologue, hz, hso]
    refine ⟨core.memory, holes, ?_, rfl, rfl, fun _ _ => rfl, fun r o h => by simp [hso] at h, fun _ h => h,
      fun r o h => by simp [hso] at h⟩
    have hcore : ({ core.setReg .rsp (Q - UInt64.ofNat l.size) with memory := core.memory } : Core) = core := by
      rw [hz, show UInt64.ofNat 0 = 0 from rfl, UInt64.sub_zero, ← hQ, setReg_self]
    rw [hcore, hpro]
    exact SafeSteps.refl _ _
  · have hpro : prologue l = subRsp l.size :: l.saveOff.map fun p => Instr.store .w64 (rspAt p.2) p.1 := by
      simp only [prologue, beq_iff_eq, hz, ↓reduceIte, List.singleton_append, prologue_map]
    rw [hpro] at hseg hfits ⊢
    have hseg' : Straight.Segment cs blk 0
        ([subRsp l.size] ++ l.saveOff.map fun p => Instr.store .w64 (rspAt p.2) p.1) := hseg
    have hsize : l.size < 2 ^ 31 := by simp only [maxFrame, slack] at hbd; omega
    have hsub := seg_safe_reg hseg'.left (by simp at hfits ⊢; omega) (fun _ => nofun) (fun _ => nofun) rfl
      Runtime.rejecting (holes := holes) (R := returns) (core := core)
      (core' := core.setReg .rsp (Q - UInt64.ofNat l.size)) (subRsp_footprint _ core) (by
        rw [exec_subRsp hsize]; exact congrArg _ (congrArg _ (by rw [← hQ]; rfl)))
    have hrsp₁ : (core.setReg .rsp (Q - UInt64.ofNat l.size)).readReg .rsp = Q - UInt64.ofNat l.size := by
      simp [Validate.readReg_setReg]
    have hnd : (l.saveOff.map Prod.snd).Nodup := (List.nodup_append.1 hs.distinct).2.1
    have hpw : l.saveOff.Pairwise (fun p q => ∀ i < 8, ∀ j < 8,
        (core.setReg .rsp (Q - UInt64.ofNat l.size)).readReg .rsp + UInt64.ofNat p.2 + UInt64.ofNat i ≠
          (core.setReg .rsp (Q - UInt64.ofNat l.size)).readReg .rsp + UInt64.ofNat q.2 + UInt64.ofNat j) := by
      refine (List.pairwise_map.1 hnd).imp_of_mem fun {p q} hp hq hne => ?_
      intro i hi j hj e
      rw [hrsp₁] at e
      have := congrArg UInt64.toNat e
      rw [hcellB p.1 p.2 hp i hi, hcellB q.1 q.2 hq j hj] at this
      have h1 := save_range hs hp
      have h2 := save_range hs hq
      omega
    obtain ⟨mem', holes', hst, hr', hw', hb', hv', hh', hd'⟩ := stores_steps l.saveOff (off := 0 + 1)
      (holes := holes) (core := core.setReg .rsp (Q - UInt64.ofNat l.size)) hseg'.right
      (by simp at hfits ⊢; omega)
      (fun p hp => by have := save_range hs hp; simp only [maxFrame, slack] at hbd; omega)
      (fun p hp i hi => by
        rw [hrsp₁]
        have hb := hcellB p.1 p.2 hp i hi
        have hsr := save_range hs hp
        exact hw _ (by rw [hb, hQs]; omega) (by rw [hb]; omega))
      (fun p hp => disjoint_below (B := Q.toNat) hdis (fun j hj => by
        rw [hrsp₁, hcellB p.1 p.2 hp j hj]; have := save_range hs hp; omega)) hpw
    refine ⟨mem', holes', ?_, by rw [hr']; rfl, by rw [hw']; rfl, fun x hx => ?_, fun r o hro => ?_,
      hh', fun r o hro => ?_⟩
    · have := hsub.append hst
      simpa [Nat.add_comm] using this
    · rw [hb' x (fun p hp i hi e => hx (by
        have hb := hcellB p.1 p.2 hp i hi
        have hsr := save_range hs hp
        rw [hrsp₁] at e
        rw [e, hb, hQs]; omega))]
      rfl
    · have := hv' (r, o) hro
      rw [hrsp₁] at this
      rw [this, Validate.readReg_setReg, if_neg (saved_ne_rsp hs (saveOff_mem hro))]
    · have := hd' (r, o) hro
      rwa [hrsp₁] at this

end IxCC.Xv.Stacking.Proof
