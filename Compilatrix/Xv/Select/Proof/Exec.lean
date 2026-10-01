import Compilatrix.Xv.Select.Proof.Place
import Compilatrix.Xv.Select.Driver
import Compilatrix.Lir.Proof.Steps
import Compilatrix.X86.Width

/-!
# Running Xv instructions

What the instructions selection emits compute, as equations on
`Xv.Inst.exec`: each row runs on the values of its operands (its placement
puts each in its own register, `execBound_run`), so an instruction's
outcome is the row's semantics applied to the operands' values, written to
its definitions. One lemma per row family, stated over operand values.
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (VReg Word Env)
open X86 (GPR)

/-! ## Sequences -/

/-- Run instructions other than calls in order (the steps Xv takes through a
selected statement). -/
def execSeq (ρ : Env) (mem : X86.Memory) (ctx : Word) : List (Inst VReg) → Option (Env × X86.Memory)
  | [] => some (ρ, mem)
  | i :: is => do
      let (ρ', mem') ← i.exec ρ mem ctx
      execSeq ρ' mem' ctx is

@[simp] theorem execSeq_nil (ρ : Env) (mem : X86.Memory) (ctx : Word) : execSeq ρ mem ctx [] = some (ρ, mem) := rfl

theorem execSeq_cons {ρ : Env} {mem : X86.Memory} {ctx : Word} {i : Inst VReg} {is : List (Inst VReg)}
    {ρ' : Env} {mem' : X86.Memory} (h : i.exec ρ mem ctx = some (ρ', mem')) :
    execSeq ρ mem ctx (i :: is) = execSeq ρ' mem' ctx is := by
  simp [execSeq, h]

theorem execSeq_append {ρ : Env} {mem : X86.Memory} {ctx : Word} :
    ∀ {is js : List (Inst VReg)} {ρ' : Env} {mem' : X86.Memory}, execSeq ρ mem ctx is = some (ρ', mem') →
      execSeq ρ mem ctx (is ++ js) = execSeq ρ' mem' ctx js
  | [], js, ρ', mem', h => by simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | i :: is, js, ρ', mem', h => by
      simp only [execSeq, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨ρ₁, mem₁⟩, h₁, h⟩ := h
      simp only [List.cons_append, execSeq, h₁, Option.bind_eq_bind, Option.bind_some]
      exact execSeq_append h

theorem execSeq_singleton {ρ : Env} {mem : X86.Memory} {ctx : Word} {i : Inst VReg} :
    execSeq ρ mem ctx [i] = i.exec ρ mem ctx := by
  simp only [execSeq, Option.bind_eq_bind]
  cases i.exec ρ mem ctx <;> simp

/-! ## Addresses -/

/-- The address an Xv addressing mode denotes in an environment. -/
def Amode.evalV (ρ : Env) (ctx : Word) (a : Amode VReg) : Option Word := do
  let base ← match a.base with
    | none => some 0
    | some .ctx => some ctx
    | some (.r b) => ρ[b]?
  let index ← match a.index with
    | none => some 0
    | some (x, s) => (· * s.word) <$> ρ[x]?
  some (base + index + X86.signExtend32 a.disp.toUInt32)

theorem Amode.regs_length_le (a : Amode VReg) : a.regs.length ≤ 2 := by
  rcases a with ⟨base, index, disp⟩
  rcases base with _ | (_ | _) <;> rcases index with _ | ⟨_, _⟩ <;> simp [Amode.regs]

/-- An assigned address placed by the Xv placer evaluates to the address of
its operands' values. -/
theorem Amode.evalV_toMem {ρ : Env} {ctx : Word} {am : Amode (VReg × GPR)} {m : X86.MemAddr} {core : X86.Core}
    (h : (am.map Prod.snd).toMem some = some m) (hctx : core.readReg .r15 = ctx)
    (hv : ∀ q ∈ am.regs, ρ[q.1]? = some (core.readReg q.2)) :
    (am.map Prod.fst).evalV ρ ctx = some (m.eval core) := by
  rw [Amode.eval_toMem h]
  rcases am with ⟨base, index, disp⟩
  rcases base with _ | (q | _) <;> rcases index with _ | ⟨q', s⟩ <;>
    simp [Amode.evalV, Amode.map, Base.map, Amode.baseVal, Amode.indexVal, hctx, Amode.regs] at hv ⊢ <;>
    simp [hv]

/-! ## Inverting an assignment -/

section Invert

variable {s : X86.Slot} {i : X86.Implicit}

@[simp] theorem Bound.map_fst_eq_input_r {b : Bound (VReg × GPR)} {a : VReg} :
    b.map Prod.fst = .input s (.r a) ↔ ∃ r, b = .input s (.r (a, r)) := by
  constructor
  · intro h; rcases b with ⟨_, (⟨_, _⟩ | _ | _)⟩ | _ | _ | _ | _ | _ | _ <;> simp_all [Bound.map, XArg.map]
  · rintro ⟨r, rfl⟩; rfl

@[simp] theorem Bound.map_fst_eq_input_i {b : Bound (VReg × GPR)} {w : Word} :
    b.map Prod.fst = .input s (.i w) ↔ b = .input s (.i w) := by
  constructor
  · intro h; rcases b with ⟨_, (⟨_, _⟩ | _ | _)⟩ | _ | _ | _ | _ | _ | _ <;> simp_all [Bound.map, XArg.map]
  · rintro rfl; rfl

@[simp] theorem Bound.map_fst_eq_input_m {b : Bound (VReg × GPR)} {am : Amode VReg} :
    b.map Prod.fst = .input s (.m am) ↔ ∃ amR, b = .input s (.m amR) ∧ amR.map Prod.fst = am := by
  constructor
  · intro h; rcases b with ⟨_, (⟨_, _⟩ | _ | _)⟩ | _ | _ | _ | _ | _ | _ <;> simp_all [Bound.map, XArg.map]
  · rintro ⟨amR, rfl, rfl⟩; rfl

@[simp] theorem Bound.map_fst_eq_output {b : Bound (VReg × GPR)} {x : VReg} :
    b.map Prod.fst = .output s x ↔ ∃ r, b = .output s (x, r) := by
  constructor
  · intro h; rcases b with ⟨_, (⟨_, _⟩ | _ | _)⟩ | ⟨_, ⟨_, _⟩⟩ | _ | _ | _ | _ | _ <;> simp_all [Bound.map, XArg.map]
  · rintro ⟨r, rfl⟩; rfl

@[simp] theorem Bound.map_fst_eq_tied {b : Bound (VReg × GPR)} {a x : VReg} :
    b.map Prod.fst = .tied s a x ↔ ∃ ra rx, b = .tied s (a, ra) (x, rx) := by
  constructor
  · intro h; rcases b with ⟨_, (⟨_, _⟩ | _ | _)⟩ | _ | ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩ | _ | _ | _ | _ <;>
      simp_all [Bound.map, XArg.map]
  · rintro ⟨ra, rx, rfl⟩; rfl

@[simp] theorem Bound.map_fst_eq_memory {b : Bound (VReg × GPR)} {am : Amode VReg} :
    b.map Prod.fst = .memory s am ↔ ∃ amR, b = .memory s amR ∧ amR.map Prod.fst = am := by
  constructor
  · intro h; rcases b with ⟨_, (⟨_, _⟩ | _ | _)⟩ | _ | _ | _ | _ | _ | _ <;> simp_all [Bound.map, XArg.map]
  · rintro ⟨amR, rfl, rfl⟩; rfl

@[simp] theorem Bound.map_fst_eq_fixedUse {b : Bound (VReg × GPR)} {a : VReg} :
    b.map Prod.fst = .fixedUse i a ↔ ∃ r, b = .fixedUse i (a, r) := by
  constructor
  · intro h; rcases b with ⟨_, (⟨_, _⟩ | _ | _)⟩ | _ | _ | _ | ⟨_, ⟨_, _⟩⟩ | _ | _ <;> simp_all [Bound.map, XArg.map]
  · rintro ⟨r, rfl⟩; rfl

@[simp] theorem Bound.map_fst_eq_fixedDef {b : Bound (VReg × GPR)} {x : VReg} :
    b.map Prod.fst = .fixedDef i x ↔ ∃ r, b = .fixedDef i (x, r) := by
  constructor
  · intro h; rcases b with ⟨_, (⟨_, _⟩ | _ | _)⟩ | _ | _ | _ | _ | ⟨_, ⟨_, _⟩⟩ | _ <;> simp_all [Bound.map, XArg.map]
  · rintro ⟨r, rfl⟩; rfl

@[simp] theorem Bound.map_fst_eq_fixedTied {b : Bound (VReg × GPR)} {a x : VReg} :
    b.map Prod.fst = .fixedTied i a x ↔ ∃ ra rx, b = .fixedTied i (a, ra) (x, rx) := by
  constructor
  · intro h; rcases b with ⟨_, (⟨_, _⟩ | _ | _)⟩ | _ | _ | _ | _ | _ | ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩ <;>
      simp_all [Bound.map, XArg.map]
  · rintro ⟨ra, rx, rfl⟩; rfl

end Invert

/-! ## One row -/

/-- An Xv row whose operands are defined runs on an assignment's core: the
row's outcome there, read back. -/
theorem bound_run {ρ : Env} {mem : X86.Memory} {ctx : Word} {o : X86.Op} {bs : List (Bound VReg)}
    (hneed : (bs.map Bound.need).sum ≤ (scratch.filter (!(bs.filterMap Bound.fixed?).contains ·)).length)
    (hdef : ∀ x ∈ bs.flatMap Bound.uses, ∃ w, ρ[x]? = some w)
    (hfix : (bs.filterMap Bound.fixedUse?).Nodup) (hfr : ∀ b ∈ bs, b.fixed? ≠ some .r15) :
    ∃ (bR : List (Bound (VReg × GPR))) (margs : List X86.Arg) (core : X86.Core),
      bR.map (Bound.map Prod.fst) = bs ∧ (∀ b ∈ bR, b.Assigned) ∧
      slotArgs some some (bR.map (Bound.map Prod.snd)) = some margs ∧
      core.memory = mem ∧ core.readReg .r15 = ctx ∧ (bR.flatMap Bound.taken).Nodup ∧
      (∀ b ∈ bR, ∀ r ∈ b.taken, r ∈ scratch ∧ r ∉ bs.filterMap Bound.fixed?) ∧
      (∀ q ∈ bR.flatMap Bound.uses, ρ[q.1]? = some (core.readReg q.2)) ∧
      (∀ b ∈ bR, ∀ q ∈ b.outputs, core.readReg q.2 = 0) ∧
      execBound [(o, bs)] ρ mem ctx = (execRow o margs core {}).map fun r =>
        (readBack r.1 ρ ((bR.flatMap Bound.defs).map fun q => (q.1, q.2)), r.1.memory, r.2) := by
  obtain ⟨aps, margs, core, hmap, hass, hargs, hmem, hctx, htk, htkm, huse, hout, hrun⟩ :=
    execBound_run (parts := [(o, bs)]) (ρ := ρ) (mem := mem) (ctx := ctx)
      (by simpa [fixedRegs] using hneed) (by simpa using hdef) (by simpa using hfix)
  obtain ⟨⟨o', bR⟩, rfl⟩ : ∃ ap, aps = [ap] := by
    cases aps with
    | nil => simp at hmap
    | cons ap rest => cases rest with
      | nil => exact ⟨ap, rfl⟩
      | cons _ _ => simp at hmap
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hmap
  obtain ⟨rfl, rfl⟩ := hmap
  simp only [List.mapM_cons, List.mapM_nil, APart.args, Option.map_eq_map, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.map_eq_some_iff] at hargs
  obtain ⟨⟨_, margs'⟩, ⟨margs'', hsl, he⟩, hrest⟩ := hargs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨_, h₁, h₂⟩ := hrest
  simp only [pure, Option.some.injEq] at h₁ h₂
  subst h₁; subst h₂
  refine ⟨bR, margs'', core, rfl, fun b hb => hass (o', bR) (by simp) b hb, hsl, hmem, hctx,
    by simpa using htk, ?_, ?_, by simpa using hout, ?_⟩
  · intro b hb r hr
    have := htkm b (by simp [hb]) r hr
    simpa [fixedRegs] using this
  · intro q hq
    obtain ⟨b, hb, hqb⟩ := List.mem_flatMap.1 hq
    refine huse q (by simp [hq]) ?_
    by_cases hfu : q ∈ b.freeUses
    · have hqt : q.2 ∈ b.taken := by
        rw [Bound.taken_eq]; exact List.mem_map_of_mem (List.mem_append_left _ hfu)
      exact fun e => r15_not_mem_scratch (e ▸ (htkm b (by simp [hb]) q.2 hqt).1)
    · obtain ⟨i, hi, hqi⟩ := Bound.uses_fixed (hass (o', bR) (by simp) b hb) hqb hfu
      rw [hqi]
      intro e
      subst e
      exact hfr (b.map Prod.fst) (List.mem_map_of_mem hb) (by rw [Bound.fixed?_map, hi])
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hrun
    rw [hrun]
    simp only [execRows, List.foldlM_cons, List.foldlM_nil]
    cases execRow o' margs'' core {} <;> simp [pure]

/-- An `op` instruction runs its bound row. -/
theorem exec_op {ρ ρ' : Env} {mem mem' : X86.Memory} {ctx : Word} {o : X86.Op} {defs : List VReg}
    {args : List (XArg VReg)} {bs : List (Bound VReg)} {f : X86.ByteEval.Flags} (hb : bindRow o defs args = some bs)
    (h : execBound [(o, bs)] ρ mem ctx = some (ρ', mem', f)) :
    Inst.exec ρ mem ctx (.op o defs args) = some (ρ', mem') := by
  simp [Inst.exec, hb, h]

/-- `bound_run` for an `op` instruction, with its bound operands computed by
`bindRow` (pass `rfl`). -/
theorem op_run {ρ : Env} {mem : X86.Memory} {ctx : Word} {o : X86.Op} {defs : List VReg}
    {args : List (XArg VReg)} {bs : List (Bound VReg)} (hb : bindRow o defs args = some bs)
    (hneed : (bs.map Bound.need).sum ≤ (scratch.filter (!(bs.filterMap Bound.fixed?).contains ·)).length)
    (hdef : ∀ x ∈ bs.flatMap Bound.uses, ∃ w, ρ[x]? = some w)
    (hfix : (bs.filterMap Bound.fixedUse?).Nodup) (hfr : ∀ b ∈ bs, b.fixed? ≠ some .r15) :
    ∃ (bR : List (Bound (VReg × GPR))) (margs : List X86.Arg) (core : X86.Core),
      bR.map (Bound.map Prod.fst) = bs ∧ (∀ b ∈ bR, b.Assigned) ∧
      slotArgs some some (bR.map (Bound.map Prod.snd)) = some margs ∧
      core.memory = mem ∧ core.readReg .r15 = ctx ∧ (bR.flatMap Bound.taken).Nodup ∧
      (∀ b ∈ bR, ∀ r ∈ b.taken, r ∈ scratch ∧ r ∉ bs.filterMap Bound.fixed?) ∧
      (∀ q ∈ bR.flatMap Bound.uses, ρ[q.1]? = some (core.readReg q.2)) ∧
      (∀ b ∈ bR, ∀ q ∈ b.outputs, core.readReg q.2 = 0) ∧
      Inst.exec ρ mem ctx (.op o defs args) = (execRow o margs core {}).map fun r =>
        (readBack r.1 ρ ((bR.flatMap Bound.defs).map fun q => (q.1, q.2)), r.1.memory) := by
  obtain ⟨bR, margs, core, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, hrun⟩ := bound_run (o := o) hneed hdef hfix hfr
  refine ⟨bR, margs, core, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, ?_⟩
  simp only [Inst.exec, hb, Option.bind_eq_bind, Option.bind_some, hrun]
  cases execRow o margs core {} <;> simp [pure]

/-- A `jcc` producer runs its bound row; the branch tests its flags. -/
theorem execJcc_of {ρ ρ' : Env} {mem mem' : X86.Memory} {ctx : Word} {p : X86.Op} {defs : List VReg}
    {args : List (XArg VReg)} {bs : List (Bound VReg)} {f : X86.ByteEval.Flags} {c : X86.Condition} {t : Bool}
    (hb : bindRow p defs args = some bs) (h : execBound [(p, bs)] ρ mem ctx = some (ρ', mem', f))
    (ht : jccTaken c f = some t) : execJcc p args defs c ρ mem ctx = some (ρ', mem', t) := by
  simp [execJcc, hb, h, ht]

/-! ## Operand values -/

/-- The value of a row argument in an environment and memory, read at a
width. -/
def XArg.valIn (ρ : Env) (mem : X86.Memory) (ctx : Word) (w : X86.Width) : XArg VReg → Option Word
  | .r x => ρ[x]?
  | .m am => (am.evalV ρ ctx).bind fun a => (mem.read? w a).toOption
  | .i k => some k

theorem Amode.evalV_defined {ρ : Env} {ctx : Word} {am : Amode VReg} {a : Word} (h : am.evalV ρ ctx = some a) :
    ∀ x ∈ am.regs, ∃ w, ρ[x]? = some w := by
  rcases am with ⟨base, index, disp⟩
  rcases base with _ | (b | _) <;> rcases index with _ | ⟨i, s⟩ <;>
    simp [Amode.evalV, Amode.regs, Option.bind_eq_some_iff] at h ⊢ <;>
    first
    | (obtain ⟨_, ⟨w, hw, _⟩, _⟩ := h; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw, _⟩ := h; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw, _, ⟨w', hw', _⟩, _⟩ := h; exact ⟨⟨w, hw⟩, ⟨w', hw'⟩⟩)

theorem XArg.valIn_defined {ρ : Env} {mem : X86.Memory} {ctx : Word} {w : X86.Width} {a : XArg VReg} {v : Word}
    (h : a.valIn ρ mem ctx w = some v) : ∀ x ∈ a.regs, ∃ w, ρ[x]? = some w := by
  cases a with
  | r x => simp [XArg.valIn, XArg.regs] at h ⊢; exact ⟨v, h⟩
  | m am =>
      simp only [XArg.valIn, Option.bind_eq_some_iff] at h
      obtain ⟨a, ha, -⟩ := h
      exact Amode.evalV_defined ha
  | i k => simp [XArg.regs]


/-! ## Placed arguments load their values -/

theorem load_r {ρ : Env} {core : X86.Core} {w : X86.Width} {q : VReg × GPR} {v : Word}
    (huse : ρ[q.1]? = some (core.readReg q.2)) (hv : ρ[q.1]? = some v) :
    (X86.Arg.reg q.2).load core w = .ok v := by
  rw [hv] at huse
  simp [X86.Arg.load, Option.some.inj huse]

theorem load_m {ρ : Env} {mem : X86.Memory} {ctx : Word} {core : X86.Core} {w : X86.Width}
    {amR : Amode (VReg × GPR)} {m : X86.MemAddr} {addr v : Word}
    (hm : (amR.map Prod.snd).toMem some = some m) (hmem : core.memory = mem) (hctx : core.readReg .r15 = ctx)
    (huse : ∀ q ∈ amR.regs, ρ[q.1]? = some (core.readReg q.2))
    (ha : (amR.map Prod.fst).evalV ρ ctx = some addr) (hv : mem.read? w addr = .ok v) :
    (X86.Arg.mem m).load core w = .ok v ∧ m.eval core = addr := by
  have he := Amode.evalV_toMem hm hctx huse
  rw [ha] at he
  have : m.eval core = addr := (Option.some.inj he).symm
  simp [X86.Arg.load, hmem, this, hv]

/-! ## Row families -/

open Compilatrix.Xv.Validate (mergeWrite readReg_writeReg readReg_setReg)

theorem merge_allSet (before computed : X86.ByteEval.Flags) :
    X86.ByteEval.Flags.merge X86.Table.allSet before computed = computed := by
  obtain ⟨c, z, s, o⟩ := computed
  rfl

/-- The simp set that runs a table row on registers. -/
macro "row_simp" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp [execRow, X86.Op.exec, X86.Op.run, X86.Op.inputs, X86.readSlots, X86.Arg.load, X86.Arg.address,
    X86.Op.stage, X86.writeSlots, X86.Arg.store, X86.readImplicits, X86.writeImplicits, X86.desc,
    X86.Table.arithDesc, X86.Table.movDesc, X86.Table.movzxDesc, X86.Table.leaDesc, X86.Table.imulDesc,
    X86.Table.testDesc, X86.Table.shiftDesc, X86.Table.divDesc, X86.Table.cmovDesc, X86.Table.setccDesc,
    X86.Table.cmovSem, X86.Table.setccSem, X86.Table.rmSlot, X86.Table.regSlot,
    X86.Table.immSlot, X86.Table.Arith.sem, X86.Table.Arith.role, X86.Table.aluSem, X86.Table.cmpSem,
    X86.Table.moveSem, X86.Table.zeroExtendSem, X86.Table.mulSem, X86.Table.testSem, X86.Table.shiftSem,
    X86.Table.divSem, X86.Table.addArith, X86.Table.orArith, X86.Table.andArith, X86.Table.subArith,
    X86.Table.xorArith, X86.Table.cmpArith, X86.AluOp.mnemonic, bind, Except.bind, Except.mapError,
    Functor.map, Except.map, pure, Except.pure, merge_allSet,
    readReg_writeReg, readReg_setReg, X86.Encode.truncate64, readBack, Bound.defs, mergeWrite, X86.Role.reads,
    X86.Role.writes, List.filterMap_cons, List.filterMap_nil, $xs,*])

/-- The prefix of a family proof: run the bound row, and the bound
operands' shapes. -/
macro "bound_start" : tactic => `(tactic|
  first
  | skip)

theorem exec_zero (ρ : Env) (mem : X86.Memory) (ctx : Word) (x : VReg) :
    Inst.exec ρ mem ctx (.zero x) = some (ρ.insert x 0, mem) := by
  simp [Inst.exec, execRows, execRow, X86.Op.exec, X86.Op.run, X86.Op.inputs, X86.readSlots, X86.Arg.load,
    X86.Op.stage, X86.writeSlots, X86.Arg.store, X86.writeImplicits, X86.readImplicits, X86.desc, zeroRow,
    X86.Table.arithDesc, X86.Table.xorArith, X86.Table.rmSlot, X86.Table.regSlot, X86.Table.Arith.sem,
    X86.Table.Arith.role, X86.Table.aluSem, X86.AluOp.eval, bind, Except.bind, Except.mapError, Functor.map,
    Except.map, pure, Except.pure, X86.Core.readReg, X86.Core.writeReg, X86.Core.setReg, X86.Width.truncate,
    X86.Registers.set]

theorem exec_move {ρ : Env} {mem : X86.Memory} {ctx : Word} {x a : VReg} {v : Word} (ha : ρ[a]? = some v) :
    Inst.exec ρ mem ctx (.move x a) = some (ρ.insert x v, mem) := by
  simp [Inst.exec, ha]

/-- `mov r, imm` (`OI` at 32 or 64 bits) and `mov r/m64, imm32` (`MI`):
`x := c` at the width. -/
theorem exec_movImm {w : X86.Width} {form : X86.OpEn}
    (hwf : (w = .w32 ∧ form = .OI) ∨ (w = .w64 ∧ form = .OI) ∨ (w = .w64 ∧ form = .MI))
    {ρ : Env} {mem : X86.Memory} {ctx : Word} (x : VReg) (c : Word) :
    Inst.exec ρ mem ctx (.op { mn := .mov, w, form } [x] [.i c]) = some (ρ.insert x (w.truncate c), mem) := by
  have key : ∀ {s₁ s₂ : X86.Slot}, bindRow { mn := .mov, w, form } [x] [.i c] = some [.output s₁ x, .input s₂ (.i c)] →
      s₁.role = .write → s₁.width = w → (s₂.role = .read) →
      Inst.exec ρ mem ctx (.op { mn := .mov, w, form } [x] [.i c]) = some (ρ.insert x (w.truncate c), mem) := by
    intro s₁ s₂ hb hr₁ hw₁ hr₂
    obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, hout, hrun⟩ :=
      op_run (ρ := ρ) (mem := mem) (ctx := ctx) hb (by simp [Bound.need, Bound.fixed?, scratch, XArg.regs])
        (by simp [Bound.uses, XArg.regs]) List.nodup_nil (by simp [Bound.fixed?])
    simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_output, Bound.map_fst_eq_input_i] at hmap
    obtain ⟨_, _, rfl, ⟨rx, rfl⟩, _, _, rfl, rfl, rfl⟩ := hmap
    simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons] at hsl
    subst hsl
    rw [hrun]
    rcases hwf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      row_simp [hmem, X86.Table.moveImm, X86.Table.fullImm, X86.Table.ImmKind.argKind, hr₁, hw₁, hr₂]
  rcases hwf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact key rfl rfl rfl rfl

theorem aluBind (op : X86.AluOp) (w : X86.Width) (form : X86.OpEn) (defs : List VReg) (args : List (XArg VReg)) :
    bindRow { mn := op.mnemonic, w, form } defs args = bindRow { mn := .add, w, form } defs args := by
  cases op <;> cases form <;> rfl


/-- `op r/m, r` (an ALU row at width 32 or 64, tied to `a`): `x := a op b`. -/
theorem exec_aluR (op : X86.AluOp) {w : X86.Width} (hw : w = .w32 ∨ w = .w64) {ρ : Env} {mem : X86.Memory}
    {ctx : Word} {x a b : VReg} {va vb : Word} (ha : ρ[a]? = some va) (hb : ρ[b]? = some vb) :
    Inst.exec ρ mem ctx (.op { mn := op.mnemonic, w, form := .MR } [x] [.r a, .r b]) =
      some (ρ.insert x (w.truncate (op.eval va vb)), mem) := by
  have hbind : bindRow { mn := op.mnemonic, w, form := .MR } [x] [.r a, .r b] =
      some [.tied (X86.Table.rmSlot w .readWrite) a x, .input (X86.Table.regSlot w .read) (.r b)] :=
    (aluBind op w .MR _ _).trans rfl
  obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, -, hrun⟩ :=
    op_run (ρ := ρ) (mem := mem) (ctx := ctx) hbind
      (by simp [Bound.need, Bound.fixed?, XArg.regs, scratch]) (by simp [Bound.uses, XArg.regs, ha, hb])
      List.nodup_nil (by simp [Bound.fixed?])
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_tied, Bound.map_fst_eq_input_r] at hmap
  obtain ⟨_, _, rfl, ⟨ra, rx, rfl⟩, _, _, rfl, ⟨rb, rfl⟩, rfl⟩ := hmap
  have hrx : ra = rx := hass (.tied _ (a, ra) (x, rx)) List.mem_cons_self
  subst hrx
  simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons] at hsl
  subst hsl
  have hra := huse (a, ra) (by simp [Bound.uses])
  have hrb := huse (b, rb) (by simp [Bound.uses, XArg.regs])
  rw [ha] at hra; rw [hb] at hrb
  simp only [Option.some.injEq] at hra hrb
  rw [hrun]
  rcases hw with rfl | rfl <;> cases op <;> row_simp [← hra, ← hrb, hmem]

/-- `op r/m, imm8` or `op r/m, imm32` (an ALU row at width 32 or 64, tied):
`x := a op c`. -/
theorem exec_aluI (op : X86.AluOp) {w : X86.Width} (hw : w = .w32 ∨ w = .w64) {form : X86.OpEn}
    (hf : form = .MI8 ∨ form = .MI) {ρ : Env} {mem : X86.Memory}
    {ctx : Word} {x a : VReg} {va : Word} (c : Word) (ha : ρ[a]? = some va) :
    Inst.exec ρ mem ctx (.op { mn := op.mnemonic, w, form } [x] [.r a, .i c]) =
      some (ρ.insert x (w.truncate (op.eval va c)), mem) := by
  have key : ∀ {s₂ : X86.Slot}, bindRow { mn := op.mnemonic, w, form } [x] [.r a, .i c] =
      some [.tied (X86.Table.rmSlot w .readWrite) a x, .input s₂ (.i c)] → s₂.role = .read →
      Inst.exec ρ mem ctx (.op { mn := op.mnemonic, w, form } [x] [.r a, .i c]) =
        some (ρ.insert x (w.truncate (op.eval va c)), mem) := by
    intro s₂ hbind hr₂
    obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, -, hrun⟩ :=
      op_run (ρ := ρ) (mem := mem) (ctx := ctx) hbind
        (by simp [Bound.need, Bound.fixed?, XArg.regs, scratch]) (by simp [Bound.uses, XArg.regs, ha])
        List.nodup_nil (by simp [Bound.fixed?])
    simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_tied, Bound.map_fst_eq_input_i] at hmap
    obtain ⟨_, _, rfl, ⟨ra, rx, rfl⟩, _, _, rfl, rfl, rfl⟩ := hmap
    have hrx : ra = rx := hass (.tied _ (a, ra) (x, rx)) List.mem_cons_self
    subst hrx
    simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons] at hsl
    subst hsl
    have hra := huse (a, ra) (by simp [Bound.uses])
    rw [ha] at hra
    simp only [Option.some.injEq] at hra
    rw [hrun]
    rcases hf with rfl | rfl <;> rcases hw with rfl | rfl <;> cases op <;> row_simp [← hra, hmem, hr₂]
  rcases hf with rfl | rfl
  · exact key ((aluBind op w .MI8 _ _).trans rfl) rfl
  · exact key ((aluBind op w .MI _ _).trans rfl) rfl

/-- `op r, m` (an ALU row at width 32 or 64, tied to `a`, reading memory):
`x := a op [m]`. -/
theorem exec_aluM (op : X86.AluOp) {w : X86.Width} (hw : w = .w32 ∨ w = .w64) {ρ : Env} {mem : X86.Memory}
    {ctx : Word} {x a : VReg} {am : Amode VReg} {va addr vm : Word} (ha : ρ[a]? = some va)
    (hm : am.evalV ρ ctx = some addr) (hv : mem.read? w addr = .ok vm) :
    Inst.exec ρ mem ctx (.op { mn := op.mnemonic, w, form := .RM } [x] [.r a, .m am]) =
      some (ρ.insert x (w.truncate (op.eval va vm)), mem) := by
  have hbind : bindRow { mn := op.mnemonic, w, form := .RM } [x] [.r a, .m am] =
      some [.tied (X86.Table.regSlot w .readWrite) a x, .input (X86.Table.rmSlot w .read) (.m am)] :=
    (aluBind op w .RM _ _).trans rfl
  obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, -, hrun⟩ :=
    op_run (ρ := ρ) (mem := mem) (ctx := ctx) hbind
      (by have := Amode.regs_length_le am; simp [Bound.need, Bound.fixed?, XArg.regs, scratch]; omega)
      (by
        have hd := Amode.evalV_defined hm
        simp only [Bound.uses, XArg.regs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
          List.mem_singleton]
        rintro y (rfl | hy)
        · exact ⟨va, ha⟩
        · exact hd y hy)
      List.nodup_nil (by simp [Bound.fixed?])
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_tied, Bound.map_fst_eq_input_m] at hmap
  obtain ⟨_, _, rfl, ⟨ra, rx, rfl⟩, _, _, rfl, ⟨amR, rfl, rfl⟩, rfl⟩ := hmap
  have hrx : ra = rx := hass (.tied _ (a, ra) (x, rx)) List.mem_cons_self
  subst hrx
  cases htm : (amR.map Prod.snd).toMem some with
  | none => simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons, htm] at hsl
  | some m =>
    simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons, htm] at hsl
    subst hsl
    have hra := huse (a, ra) (by simp [Bound.uses])
    rw [ha] at hra
    simp only [Option.some.injEq] at hra
    obtain ⟨-, hev⟩ := load_m htm hmem hctx (fun q hq => huse q (by simp [Bound.uses, XArg.regs, hq])) hm hv
    rw [hrun]
    rcases hw with rfl | rfl <;> cases op <;> row_simp [← hra, hmem, hev, hv]

/-- The register-operand prefix of a family proof on an `output, input`
row (`mov`, `movzx`): the assignment's shape and values. -/
theorem out_in_reg {ρ : Env} {mem : X86.Memory} {ctx : Word} {o : X86.Op} {x y : VReg} {vy : Word}
    {s₁ s₂ : X86.Slot} (hb : bindRow o [x] [.r y] = some [.output s₁ x, .input s₂ (.r y)])
    (hy : ρ[y]? = some vy) :
    ∃ rx ry core, core.memory = mem ∧ core.readReg ry = vy ∧
      Inst.exec ρ mem ctx (.op o [x] [.r y]) = (execRow o [.reg rx, .reg ry] core {}).map fun r =>
        (readBack r.1 ρ [(x, rx)], r.1.memory) := by
  obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, -, hrun⟩ :=
    op_run (ρ := ρ) (mem := mem) (ctx := ctx) hb
      (by simp [Bound.need, Bound.fixed?, XArg.regs, scratch]) (by simp [Bound.uses, XArg.regs, hy])
      List.nodup_nil (by simp [Bound.fixed?])
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_output, Bound.map_fst_eq_input_r] at hmap
  obtain ⟨_, _, rfl, ⟨rx, rfl⟩, _, _, rfl, ⟨ry, rfl⟩, rfl⟩ := hmap
  simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons] at hsl
  subst hsl
  have hry := huse (y, ry) (by simp [Bound.uses, XArg.regs])
  rw [hy] at hry
  exact ⟨rx, ry, core, hmem, (Option.some.inj hry).symm, by rw [hrun]; simp [Bound.defs, readBack]⟩

/-- The memory-operand prefix of a family proof on an `output, input` row
(loads, `lea`). -/
theorem out_in_mem {ρ : Env} {mem : X86.Memory} {ctx : Word} {o : X86.Op} {x : VReg} {am : Amode VReg}
    {addr : Word} {s₁ s₂ : X86.Slot} (hb : bindRow o [x] [.m am] = some [.output s₁ x, .input s₂ (.m am)])
    (hm : am.evalV ρ ctx = some addr) :
    ∃ rx m core, core.memory = mem ∧ m.eval core = addr ∧
      Inst.exec ρ mem ctx (.op o [x] [.m am]) = (execRow o [.reg rx, .mem m] core {}).map fun r =>
        (readBack r.1 ρ [(x, rx)], r.1.memory) := by
  obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, -, hrun⟩ :=
    op_run (ρ := ρ) (mem := mem) (ctx := ctx) hb
      (by have := Amode.regs_length_le am; simp [Bound.need, Bound.fixed?, XArg.regs, scratch]; omega)
      (by simpa [Bound.uses, XArg.regs] using Amode.evalV_defined hm)
      List.nodup_nil (by simp [Bound.fixed?])
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_output, Bound.map_fst_eq_input_m] at hmap
  obtain ⟨_, _, rfl, ⟨rx, rfl⟩, _, _, rfl, ⟨amR, rfl, rfl⟩, rfl⟩ := hmap
  cases htm : (amR.map Prod.snd).toMem some with
  | none => simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons, htm] at hsl
  | some m =>
    simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons, htm] at hsl
    subst hsl
    have he := Amode.evalV_toMem htm hctx (fun q hq => huse q (by simp [Bound.uses, XArg.regs, hq]))
    rw [hm] at he
    exact ⟨rx, m, core, hmem, (Option.some.inj he).symm, by rw [hrun]; simp [Bound.defs, readBack]⟩

/-- `movzx r32, r/m8` or `r/m16` on a register: `x := src.truncate y`. -/
theorem exec_movzxR {src : X86.Width} (hs : src = .w8 ∨ src = .w16) {ρ : Env} {mem : X86.Memory} {ctx : Word}
    {x y : VReg} {vy : Word} (hy : ρ[y]? = some vy) :
    Inst.exec ρ mem ctx (.op { mn := .movzx, w := .w32, form := .RM, src } [x] [.r y]) =
      some (ρ.insert x (src.truncate vy), mem) := by
  obtain ⟨rx, ry, core, hmem, hry, h⟩ := out_in_reg (o := { mn := .movzx, w := .w32, form := .RM, src }) (ctx := ctx) (mem := mem) (x := x) (s₁ := X86.Table.regSlot .w32 .write)
    (s₂ := X86.Table.rmSlot src .read) rfl hy
  rw [h]
  rcases hs with rfl | rfl <;> row_simp [hmem, hry, X86.Width.truncate, X86.Width.mask] <;>
    · rw [UInt64.and_assoc]; rfl

/-- `mov r32, r/m32` on a register: `x := w32.truncate y`. -/
theorem exec_mov32R {ρ : Env} {mem : X86.Memory} {ctx : Word} {x y : VReg} {vy : Word} (hy : ρ[y]? = some vy) :
    Inst.exec ρ mem ctx (.op { mn := .mov, w := .w32, form := .RM } [x] [.r y]) =
      some (ρ.insert x (X86.Width.w32.truncate vy), mem) := by
  obtain ⟨rx, ry, core, hmem, hry, h⟩ := out_in_reg (o := { mn := .mov, w := .w32, form := .RM }) (ctx := ctx) (mem := mem) (x := x) (s₁ := X86.Table.regSlot .w32 .write)
    (s₂ := X86.Table.rmSlot .w32 .read) rfl hy
  rw [h]
  row_simp [hmem, hry]

/-- `mov r, m` at width 32 or 64: `x := [m]`. -/
theorem exec_movLoad {w : X86.Width} (hw : w = .w32 ∨ w = .w64) {ρ : Env} {mem : X86.Memory} {ctx : Word}
    {x : VReg} {am : Amode VReg} {addr v : Word} (hm : am.evalV ρ ctx = some addr) (hv : mem.read? w addr = .ok v) :
    Inst.exec ρ mem ctx (.op { mn := .mov, w, form := .RM } [x] [.m am]) = some (ρ.insert x (w.truncate v), mem) := by
  obtain ⟨rx, m, core, hmem, hev, h⟩ := out_in_mem (o := { mn := .mov, w, form := .RM }) (ctx := ctx) (mem := mem)
    (x := x) (s₁ := X86.Table.regSlot w .write) (s₂ := X86.Table.rmSlot w .read) rfl hm
  rw [h]
  rcases hw with rfl | rfl <;> row_simp [hmem, hev, hv]

/-- `movzx r32, m8` or `m16`: `x := [m]` zero-extended. -/
theorem exec_movzxLoad {src : X86.Width} (hs : src = .w8 ∨ src = .w16) {ρ : Env} {mem : X86.Memory} {ctx : Word}
    {x : VReg} {am : Amode VReg} {addr v : Word} (hm : am.evalV ρ ctx = some addr) (hv : mem.read? src addr = .ok v) :
    Inst.exec ρ mem ctx (.op { mn := .movzx, w := .w32, form := .RM, src } [x] [.m am]) =
      some (ρ.insert x (src.truncate v), mem) := by
  obtain ⟨rx, m, core, hmem, hev, h⟩ := out_in_mem (o := { mn := .movzx, w := .w32, form := .RM, src }) (ctx := ctx) (mem := mem) (x := x)
    (s₁ := X86.Table.regSlot .w32 .write) (s₂ := X86.Table.rmSlot src .read) rfl hm
  rw [h]
  rcases hs with rfl | rfl <;> row_simp [hmem, hev, hv, X86.Width.truncate, X86.Width.mask] <;>
    · rw [UInt64.and_assoc]; rfl

/-- `lea r64, m`: `x := m`'s address. -/
theorem exec_lea {ρ : Env} {mem : X86.Memory} {ctx : Word} {x : VReg} {am : Amode VReg} {addr : Word}
    (hm : am.evalV ρ ctx = some addr) :
    Inst.exec ρ mem ctx (.op { mn := .lea, w := .w64, form := .RM } [x] [.m am]) = some (ρ.insert x addr, mem) := by
  obtain ⟨rx, m, core, hmem, hev, h⟩ := out_in_mem (o := { mn := .lea, w := .w64, form := .RM }) (ctx := ctx) (mem := mem) (x := x)
    (s₁ := X86.Table.regSlot .w64 .write) (s₂ := ⟨[.mem], .w64, .address⟩) rfl hm
  rw [h]
  row_simp [hmem, hev]


/-! ## Tied rows (`imul`, shifts) -/

/-- A tied row with a register or immediate second operand: the
assignment's shape and values. -/
theorem tied_in {ρ : Env} {mem : X86.Memory} {ctx : Word} {o : X86.Op} {x a : VReg} {b : XArg VReg} {va : Word}
    {s₁ s₂ : X86.Slot} (hb : bindRow o [x] [.r a, b] = some [.tied s₁ a x, .input s₂ b])
    (ha : ρ[a]? = some va) (hbm : ∀ am, b ≠ .m am) (hbd : ∀ y ∈ b.regs, ∃ w, ρ[y]? = some w) :
    ∃ ra arg core, core.memory = mem ∧ core.readReg ra = va ∧
      (∀ y vy, b = .r y → ρ[y]? = some vy → ∃ ry, arg = .reg ry ∧ core.readReg ry = vy) ∧
      (∀ c, b = .i c → arg = .imm c) ∧
      Inst.exec ρ mem ctx (.op o [x] [.r a, b]) = (execRow o [.reg ra, arg] core {}).map fun r =>
        (readBack r.1 ρ [(x, ra)], r.1.memory) := by
  obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, -, hrun⟩ :=
    op_run (ρ := ρ) (mem := mem) (ctx := ctx) hb
      (by
        cases b with
        | m am => exact absurd rfl (hbm am)
        | _ => simp [Bound.need, Bound.fixed?, XArg.regs, scratch])
      (by
        simp only [Bound.uses, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
          List.mem_singleton]
        rintro y (rfl | hy)
        · exact ⟨va, ha⟩
        · exact hbd y hy)
      List.nodup_nil (by simp [Bound.fixed?])
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_tied] at hmap
  obtain ⟨_, _, rfl, ⟨ra, rx, rfl⟩, b', _, rfl, hb', rfl⟩ := hmap
  have hrx : ra = rx := hass (.tied _ (a, ra) (x, rx)) List.mem_cons_self
  subst hrx
  have hra := huse (a, ra) (by simp [Bound.uses])
  rw [ha] at hra
  cases b with
  | m am => exact absurd rfl (hbm am)
  | r y =>
    simp only [Bound.map_fst_eq_input_r] at hb'
    obtain ⟨ry, rfl⟩ := hb'
    simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons] at hsl
    subst hsl
    have hry := huse (y, ry) (by simp [Bound.uses, XArg.regs])
    refine ⟨ra, .reg ry, core, hmem, (Option.some.inj hra).symm, ?_, by simp, by rw [hrun]; simp [Bound.defs, readBack]⟩
    intro y' vy e hy
    cases e
    rw [hy] at hry
    exact ⟨ry, rfl, (Option.some.inj hry).symm⟩
  | i c =>
    simp only [Bound.map_fst_eq_input_i] at hb'
    subst hb'
    simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons] at hsl
    subst hsl
    refine ⟨ra, .imm c, core, hmem, (Option.some.inj hra).symm, by simp, by simp, by rw [hrun]; simp [Bound.defs, readBack]⟩

/-- A tied row reading memory as its second operand. -/
theorem tied_in_mem {ρ : Env} {mem : X86.Memory} {ctx : Word} {o : X86.Op} {x a : VReg} {am : Amode VReg}
    {va addr : Word} {s₁ s₂ : X86.Slot} (hb : bindRow o [x] [.r a, .m am] = some [.tied s₁ a x, .input s₂ (.m am)])
    (ha : ρ[a]? = some va) (hm : am.evalV ρ ctx = some addr) :
    ∃ ra m core, core.memory = mem ∧ core.readReg ra = va ∧ m.eval core = addr ∧
      Inst.exec ρ mem ctx (.op o [x] [.r a, .m am]) = (execRow o [.reg ra, .mem m] core {}).map fun r =>
        (readBack r.1 ρ [(x, ra)], r.1.memory) := by
  obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, -, hrun⟩ :=
    op_run (ρ := ρ) (mem := mem) (ctx := ctx) hb
      (by have := Amode.regs_length_le am; simp [Bound.need, Bound.fixed?, XArg.regs, scratch]; omega)
      (by
        have hd := Amode.evalV_defined hm
        simp only [Bound.uses, XArg.regs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
          List.mem_singleton]
        rintro y (rfl | hy)
        · exact ⟨va, ha⟩
        · exact hd y hy)
      List.nodup_nil (by simp [Bound.fixed?])
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_tied, Bound.map_fst_eq_input_m] at hmap
  obtain ⟨_, _, rfl, ⟨ra, rx, rfl⟩, _, _, rfl, ⟨amR, rfl, rfl⟩, rfl⟩ := hmap
  have hrx : ra = rx := hass (.tied _ (a, ra) (x, rx)) List.mem_cons_self
  subst hrx
  have hra := huse (a, ra) (by simp [Bound.uses])
  rw [ha] at hra
  cases htm : (amR.map Prod.snd).toMem some with
  | none => simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons, htm] at hsl
  | some m =>
    simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons, htm] at hsl
    subst hsl
    have he := Amode.evalV_toMem htm hctx (fun q hq => huse q (by simp [Bound.uses, XArg.regs, hq]))
    rw [hm] at he
    exact ⟨ra, m, core, hmem, (Option.some.inj hra).symm, (Option.some.inj he).symm, by rw [hrun]; simp [Bound.defs, readBack]⟩

/-- `imul r, r/m` at width 32 or 64 on registers: `x := a * b`. -/
theorem exec_imulR {w : X86.Width} (hw : w = .w32 ∨ w = .w64) {ρ : Env} {mem : X86.Memory} {ctx : Word}
    {x a b : VReg} {va vb : Word} (ha : ρ[a]? = some va) (hb : ρ[b]? = some vb) :
    Inst.exec ρ mem ctx (.op { mn := .imul, w, form := .RM } [x] [.r a, .r b]) =
      some (ρ.insert x (w.truncate (va * vb)), mem) := by
  obtain ⟨ra, arg, core, hmem, hra, hr, -, h⟩ := tied_in (o := { mn := .imul, w, form := .RM }) (ctx := ctx)
    (mem := mem) (x := x) (b := .r b) (s₁ := X86.Table.regSlot w .readWrite) (s₂ := X86.Table.rmSlot w .read) rfl ha
    (by simp) (by simp [XArg.regs, hb])
  obtain ⟨rb, rfl, hrb⟩ := hr b vb rfl hb
  rw [h]
  rcases hw with rfl | rfl <;> row_simp [hmem, hra, hrb]

/-- `imul r, m` at width 32 or 64: `x := a * [m]`. -/
theorem exec_imulM {w : X86.Width} (hw : w = .w32 ∨ w = .w64) {ρ : Env} {mem : X86.Memory} {ctx : Word}
    {x a : VReg} {am : Amode VReg} {va addr vm : Word} (ha : ρ[a]? = some va) (hm : am.evalV ρ ctx = some addr)
    (hv : mem.read? w addr = .ok vm) :
    Inst.exec ρ mem ctx (.op { mn := .imul, w, form := .RM } [x] [.r a, .m am]) =
      some (ρ.insert x (w.truncate (va * vm)), mem) := by
  obtain ⟨ra, m, core, hmem, hra, hev, h⟩ := tied_in_mem (o := { mn := .imul, w, form := .RM }) (ctx := ctx)
    (mem := mem) (x := x) (s₁ := X86.Table.regSlot w .readWrite) (s₂ := X86.Table.rmSlot w .read) rfl ha hm
  rw [h]
  rcases hw with rfl | rfl <;> row_simp [hmem, hra, hev, hv]

/-- `imul r, r/m, imm8` or `imm32` at width 32 or 64: `x := a * c`. -/
theorem exec_imulI {w : X86.Width} (hw : w = .w32 ∨ w = .w64) {form : X86.OpEn} (hf : form = .RMI8 ∨ form = .RMI)
    {ρ : Env} {mem : X86.Memory} {ctx : Word} {x a : VReg} {va : Word} (c : Word) (ha : ρ[a]? = some va) :
    Inst.exec ρ mem ctx (.op { mn := .imul, w, form } [x] [.r a, .i c]) =
      some (ρ.insert x (w.truncate (va * c)), mem) := by
  have key : ∀ {s₁ s₂ s₃ : X86.Slot}, bindRow { mn := .imul, w, form } [x] [.r a, .i c] =
      some [.output s₁ x, .input s₂ (.r a), .input s₃ (.i c)] → s₁ = X86.Table.regSlot w .write →
      s₂ = X86.Table.rmSlot w .read → s₃.role = .read →
      Inst.exec ρ mem ctx (.op { mn := .imul, w, form } [x] [.r a, .i c]) =
        some (ρ.insert x (w.truncate (va * c)), mem) := by
    intro s₁ s₂ s₃ hb e₁ e₂ hr₃
    subst e₁ e₂
    obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, hout, hrun⟩ :=
      op_run (ρ := ρ) (mem := mem) (ctx := ctx) hb
        (by simp [Bound.need, Bound.fixed?, XArg.regs, scratch]) (by simp [Bound.uses, XArg.regs, ha])
        List.nodup_nil (by simp [Bound.fixed?])
    simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_output, Bound.map_fst_eq_input_r,
      Bound.map_fst_eq_input_i] at hmap
    obtain ⟨_, _, rfl, ⟨rx, rfl⟩, _, _, rfl, ⟨ra, rfl⟩, _, _, rfl, rfl, rfl⟩ := hmap
    simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons] at hsl
    subst hsl
    have hra := huse (a, ra) (by simp [Bound.uses, XArg.regs])
    rw [ha] at hra
    simp only [Option.some.injEq] at hra
    rw [hrun]
    rcases hf with rfl | rfl <;> rcases hw with rfl | rfl <;> row_simp [hmem, ← hra, hr₃]
  rcases hf with rfl | rfl
  · exact key rfl rfl rfl rfl
  · exact key rfl rfl rfl rfl

/-- The mnemonic of a shift. -/
def _root_.Compilatrix.X86.ShiftOp.mnemonic : X86.ShiftOp → X86.Mnemonic
  | .shl => .shl
  | .shr => .shr
  | .sar => .sar

/-- The value a shift leaves in its register: the shifted low `w` bits,
merged as a `w`-bit register write over `a`. -/
def shiftResult (op : X86.ShiftOp) (w : X86.Width) (va count : Word) : Word :=
  mergeWrite w va ⟨(op.apply w va (X86.shiftCount w count)).setWidth 64⟩

/-- `shl/shr/sar r/m, imm8` (tied): `x := a shifted by s`. -/
theorem exec_shiftI (op : X86.ShiftOp) (w : X86.Width) {ρ : Env} {mem : X86.Memory} {ctx : Word}
    {x a : VReg} {va : Word} (s : Word) (ha : ρ[a]? = some va) :
    Inst.exec ρ mem ctx (.op { mn := op.mnemonic, w, form := .MI } [x] [.r a, .i s]) =
      some (ρ.insert x (shiftResult op w va s), mem) := by
  have hb : bindRow { mn := op.mnemonic, w, form := .MI } [x] [.r a, .i s] =
      some [.tied (X86.Table.rmSlot w .readWrite) a x, .input (X86.Table.immSlot .imm8 w) (.i s)] := by
    cases op <;> rfl
  obtain ⟨ra, arg, core, hmem, hra, -, hi, h⟩ := tied_in (ctx := ctx) (mem := mem) hb ha (by simp) (by simp [XArg.regs])
  rw [hi s rfl] at h
  rw [h]
  cases op <;> cases w <;> row_simp [hmem, hra, shiftResult, X86.ShiftOp.mnemonic]


/-- `shl/shr/sar r/m, cl` (tied, the count in `rcx`): `x := a shifted by c`. -/
theorem exec_shiftC (op : X86.ShiftOp) (w : X86.Width) {ρ : Env} {mem : X86.Memory} {ctx : Word}
    {x a c : VReg} {va vc : Word} (ha : ρ[a]? = some va) (hc : ρ[c]? = some vc) :
    Inst.exec ρ mem ctx (.op { mn := op.mnemonic, w, form := .MC } [x] [.r a, .r c]) =
      some (ρ.insert x (shiftResult op w va vc), mem) := by
  have hb : bindRow { mn := op.mnemonic, w, form := .MC } [x] [.r a, .r c] =
      some [.tied (X86.Table.rmSlot w .readWrite) a x, .fixedUse ⟨.rcx, .w8, .read⟩ c] := by
    cases op <;> rfl
  obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, -, hrun⟩ :=
    op_run (ρ := ρ) (mem := mem) (ctx := ctx) hb
      (by simp [Bound.need, Bound.fixed?, XArg.regs, scratch]) (by simp [Bound.uses, XArg.regs, ha, hc])
      (by exact (by decide : [GPR.rcx].Nodup)) (by simp [Bound.fixed?])
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_tied, Bound.map_fst_eq_fixedUse] at hmap
  obtain ⟨_, _, rfl, ⟨ra, rx, rfl⟩, _, _, rfl, ⟨rc, rfl⟩, rfl⟩ := hmap
  have hrx : ra = rx := hass (.tied _ (a, ra) (x, rx)) List.mem_cons_self
  have hrc : rc = .rcx := hass (.fixedUse ⟨.rcx, .w8, .read⟩ (c, rc)) (by simp)
  subst hrx hrc
  simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons] at hsl
  subst hsl
  have hra := huse (a, ra) (by simp [Bound.uses])
  have hrc := huse (c, .rcx) (by simp [Bound.uses])
  rw [ha] at hra; rw [hc] at hrc
  simp only [Option.some.injEq] at hra hrc
  rw [hrun]
  cases op <;> cases w <;> row_simp [hmem, ← hra, ← hrc, shiftResult, X86.ShiftOp.mnemonic]

/-- The quotient and remainder `div` at width `w` leaves for divisor `d` and
dividend `hi:lo`. -/
def divDividend (w : X86.Width) (lo hi : Word) : Nat := (w.truncate hi).toNat * 2 ^ w.bits + (w.truncate lo).toNat

/-- `div r/m` at width 32 or 64 (`rdx:rax` by the divisor, quotient to
`rax`, remainder to `rdx`), with a divisor above the high half. -/
theorem exec_div {w : X86.Width} (hw : w = .w32 ∨ w = .w64) {ρ : Env} {mem : X86.Memory} {ctx : Word}
    {q r lo hi : VReg} {d : XArg VReg} {vd vlo vhi : Word} (hd : d.valIn ρ mem ctx w = some vd)
    (hdi : ∀ k, d ≠ .i k) (hlo : ρ[lo]? = some vlo) (hhi : ρ[hi]? = some vhi)
    (hnz : (w.truncate vd).toNat ≠ 0) (hlt : (w.truncate vhi).toNat < (w.truncate vd).toNat) :
    Inst.exec ρ mem ctx (.op (X86.Op.divM w) [q, r] [d, .r lo, .r hi]) =
      some ((ρ.insert q (w.truncate (UInt64.ofNat (divDividend w vlo vhi / (w.truncate vd).toNat)))).insert r
        (w.truncate (UInt64.ofNat (divDividend w vlo vhi % (w.truncate vd).toNat))), mem) := by
  have hb : bindRow (X86.Op.divM w) [q, r] [d, .r lo, .r hi] =
      some [.input (X86.Table.rmSlot w .read) d, .fixedTied ⟨.rax, w, .readWrite⟩ lo q,
        .fixedTied ⟨.rdx, w, .readWrite⟩ hi r] := by
    cases d <;> rfl
  obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, -, hrun⟩ :=
    op_run (ρ := ρ) (mem := mem) (ctx := ctx) hb
      (by
        cases d with
        | m am => have := Amode.regs_length_le am; simp [Bound.need, Bound.fixed?, XArg.regs, scratch]; omega
        | _ => simp [Bound.need, Bound.fixed?, XArg.regs, scratch])
      (by
        have hdd := XArg.valIn_defined hd
        intro y hy
        simp only [Bound.uses, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with hy | hy | hy
        · exact hdd y hy
        · subst hy; exact ⟨vlo, hlo⟩
        · subst hy; exact ⟨vhi, hhi⟩)
      (by exact (by decide : [GPR.rax, GPR.rdx].Nodup)) (by simp [Bound.fixed?])
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_fixedTied] at hmap
  obtain ⟨bd, _, rfl, hbd, _, _, rfl, ⟨rl, rq, rfl⟩, _, _, rfl, ⟨rh, rr, rfl⟩, rfl⟩ := hmap
  obtain ⟨hrl, hrq⟩ : rl = .rax ∧ rq = .rax := hass (.fixedTied ⟨.rax, w, .readWrite⟩ (lo, rl) (q, rq)) (by simp)
  obtain ⟨hrh, hrr⟩ : rh = .rdx ∧ rr = .rdx := hass (.fixedTied ⟨.rdx, w, .readWrite⟩ (hi, rh) (r, rr)) (by simp)
  subst hrl hrq hrh hrr
  have hvlo := huse (lo, .rax) (by simp [Bound.uses])
  have hvhi := huse (hi, .rdx) (by simp [Bound.uses])
  rw [hlo] at hvlo; rw [hhi] at hvhi
  simp only [Option.some.injEq] at hvlo hvhi
  -- The divisor's machine operand loads `vd`.
  obtain ⟨arg, hsl', hload⟩ : ∃ arg, margs = [arg] ∧ arg.load core w = .ok vd := by
    cases d with
    | i k => exact absurd rfl (hdi k)
    | r y =>
      simp only [Bound.map_fst_eq_input_r] at hbd
      obtain ⟨ry, rfl⟩ := hbd
      simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons] at hsl
      refine ⟨_, hsl.symm, load_r (huse (y, ry) (by simp [Bound.uses, XArg.regs])) hd⟩
    | m am =>
      simp only [Bound.map_fst_eq_input_m] at hbd
      obtain ⟨amR, rfl, rfl⟩ := hbd
      cases htm : (amR.map Prod.snd).toMem some with
      | none =>
        simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons, htm] at hsl
      | some m =>
        simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons, htm] at hsl
        simp only [XArg.valIn, Option.bind_eq_some_iff] at hd
        obtain ⟨addr, ha, hv⟩ := hd
        have hv' : mem.read? w addr = .ok vd := by
          cases h : mem.read? w addr <;> simp_all [Except.toOption]
        exact ⟨_, hsl.symm, (load_m htm hmem hctx (fun q hq => huse q (by simp [Bound.uses, XArg.regs, hq])) ha hv').1⟩
  subst hsl'
  rw [hrun]
  have hbdd : bd.defs = [] := by
    cases bd <;> simp_all [Bound.map, Bound.defs]
  have hle : ¬ (w.truncate vd).toNat ≤ (w.truncate vhi).toNat := by omega
  simp only [List.flatMap_cons, List.flatMap_nil, hbdd, List.nil_append, List.append_nil]
  simp only [execRow, X86.Op.exec, X86.Op.run, X86.Op.inputs, X86.readSlots, X86.desc, X86.Op.divM,
    X86.Table.divDesc, X86.Table.rmSlot, hload]
  rcases hw with rfl | rfl
  · row_simp [hmem, hload, ← hvlo, ← hvhi, X86.Op.divM, hnz, hle, divDividend, X86.Width.bits, hbdd]
  · simp only [X86.Encode.truncate64] at hnz hle ⊢
    row_simp [hmem, hload, ← hvlo, ← hvhi, X86.Op.divM, hnz, hle, divDividend, X86.Width.bits, hbdd]

/-! ## Stores -/

/-- A store row (`memory`, `input`): the address and the source operand. -/
theorem mem_store {ρ : Env} {mem : X86.Memory} {ctx : Word} {o : X86.Op} {am : Amode VReg} {b : XArg VReg}
    {addr : Word} {s₁ s₂ : X86.Slot} (hb : bindRow o [] [.m am, b] = some [.memory s₁ am, .input s₂ b])
    (hm : am.evalV ρ ctx = some addr) (hbm : ∀ am', b ≠ .m am') (hbd : ∀ y ∈ b.regs, ∃ w, ρ[y]? = some w) :
    ∃ m arg core, core.memory = mem ∧ m.eval core = addr ∧
      (∀ y vy, b = .r y → ρ[y]? = some vy → ∃ ry, arg = .reg ry ∧ core.readReg ry = vy) ∧
      (∀ c, b = .i c → arg = .imm c) ∧
      Inst.exec ρ mem ctx (.op o [] [.m am, b]) = (execRow o [.mem m, arg] core {}).map fun r =>
        (ρ, r.1.memory) := by
  obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, -, hrun⟩ :=
    op_run (ρ := ρ) (mem := mem) (ctx := ctx) hb
      (by
        have := Amode.regs_length_le am
        cases b with
        | m am' => exact absurd rfl (hbm am')
        | _ => simp [Bound.need, Bound.fixed?, XArg.regs, scratch]; omega)
      (by
        have hd := Amode.evalV_defined hm
        simp only [Bound.uses, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
        rintro y (hy | hy)
        · exact hd y hy
        · exact hbd y hy)
      List.nodup_nil (by simp [Bound.fixed?])
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_memory] at hmap
  obtain ⟨_, _, rfl, ⟨amR, rfl, rfl⟩, b', _, rfl, hb', rfl⟩ := hmap
  cases htm : (amR.map Prod.snd).toMem some with
  | none =>
    cases b <;> simp_all [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons,
      List.mapM_cons, htm]
  | some m =>
    have he := Amode.evalV_toMem htm hctx (fun q hq => huse q (by simp [Bound.uses, hq]))
    rw [hm] at he
    cases b with
    | m am' => exact absurd rfl (hbm am')
    | r y =>
      simp only [Bound.map_fst_eq_input_r] at hb'
      obtain ⟨ry, rfl⟩ := hb'
      simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons, htm] at hsl
      subst hsl
      have hry := huse (y, ry) (by simp [Bound.uses, XArg.regs])
      refine ⟨m, .reg ry, core, hmem, (Option.some.inj he).symm, ?_, by simp, by rw [hrun]; simp [Bound.defs, readBack]⟩
      intro y' vy e hy
      cases e
      rw [hy] at hry
      exact ⟨ry, rfl, (Option.some.inj hry).symm⟩
    | i c =>
      simp only [Bound.map_fst_eq_input_i] at hb'
      subst hb'
      simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, XArg.map, List.filter_cons, List.mapM_cons, htm] at hsl
      subst hsl
      exact ⟨m, .imm c, core, hmem, (Option.some.inj he).symm, by simp, by simp, by rw [hrun]; simp [Bound.defs, readBack]⟩

/-- `mov m, r` at width `w`: store the low `w` bits of `y`. -/
theorem exec_storeR (w : X86.Width) {ρ : Env} {mem mem' : X86.Memory} {ctx : Word} {am : Amode VReg} {y : VReg}
    {addr vy : Word} (hm : am.evalV ρ ctx = some addr) (hy : ρ[y]? = some vy) (hw : mem.write? w addr vy = .ok mem') :
    Inst.exec ρ mem ctx (.op { mn := .mov, w, form := .MR } [] [.m am, .r y]) = some (ρ, mem') := by
  obtain ⟨m, arg, core, hmem, hev, hr, -, h⟩ := mem_store (o := { mn := .mov, w, form := .MR }) (ctx := ctx) (am := am) (b := .r y)
    (s₁ := X86.Table.rmSlot w .write) (s₂ := X86.Table.regSlot w .read) rfl hm (by simp) (by simp [XArg.regs, hy])
  obtain ⟨ry, rfl, hry⟩ := hr y vy rfl hy
  rw [h]
  cases w <;> row_simp [hmem, hev, hry, hw]

/-- `mov m, imm` at width `w` (the row's full immediate): store `c`. -/
theorem exec_storeI (w : X86.Width) {ρ : Env} {mem mem' : X86.Memory} {ctx : Word} {am : Amode VReg}
    {addr : Word} (c : Word) (hm : am.evalV ρ ctx = some addr) (hw : mem.write? w addr c = .ok mem') :
    Inst.exec ρ mem ctx (.op { mn := .mov, w, form := .MI } [] [.m am, .i c]) = some (ρ, mem') := by
  obtain ⟨m, arg, core, hmem, hev, -, hi, h⟩ := mem_store (o := { mn := .mov, w, form := .MI }) (ctx := ctx) (am := am) (b := .i c)
    (s₁ := X86.Table.rmSlot w .write) (s₂ := X86.Table.immSlot (X86.Table.ImmKind.argKind (X86.Table.fullImm w)) w)
    rfl hm (by simp) (by simp [XArg.regs])
  rw [hi c rfl] at h
  rw [h]
  cases w <;> row_simp [hmem, hev, hw]


/-! ## Flag producers, fused pairs and branches -/

/-- Restricting flags to what a condition reads keeps its test. -/
theorem test_restrict (f : X86.ByteEval.Flags) (c : X86.Condition) :
    (f.restrict c.reads).test c = f.test c := by
  obtain ⟨cf, zf, sf, of⟩ := f
  cases c <;> rfl

/-- The `jcc` row takes the branch its condition's test gives. -/
theorem jccTaken_eq {f : X86.ByteEval.Flags} {c : X86.Condition} {b : Bool} (h : f.test c = some b) :
    jccTaken c f = some b := by
  have h' := test_restrict f c
  rw [h] at h'
  simp [jccTaken, X86.desc, X86.Op.jccRel32, X86.Table.jccDesc, X86.Table.jccSem, h']

/-- The rows that produce a branch's or a fused pair's flags without
writing anything: `cmp` and `test`. -/
inductive Prod where
  | cmp
  | test
  deriving DecidableEq

/-- The flags a producer sets from its operands' values. -/
def Prod.flags : Prod → X86.Width → Word → Word → X86.ByteEval.Flags
  | .cmp, w, a, b => X86.ByteEval.aluFlags .sub w a b
  | .test, w, a, b => X86.ByteEval.aluFlags .and w a b

def Prod.mnemonic : Prod → X86.Mnemonic
  | .cmp => .cmp
  | .test => .test

/-- The forms of a producer row: `r/m, r` and `r/m, imm` (and `r/m, imm8` for
`cmp`). -/
def Prod.FormOk : Prod → X86.OpEn → Prop
  | .cmp, form => form = .MR ∨ form = .MI8 ∨ form = .MI
  | .test, form => form = .MR ∨ form = .MI

/-- A producer row binds its two operands as reads. -/
theorem Prod.bind (k : Prod) {w : X86.Width} {form : X86.OpEn} (hf : k.FormOk form) (a₁ a₂ : XArg VReg) :
    ∃ s₁ s₂ : X86.Slot, s₁.role = .read ∧ s₂.role = .read ∧ s₁.width = w ∧ s₂.width = w ∧
      bindRow { mn := k.mnemonic, w, form } [] [a₁, a₂] = some [.input s₁ a₁, .input s₂ a₂] := by
  cases k <;> simp only [Prod.FormOk] at hf
  · rcases hf with rfl | rfl | rfl <;> exact ⟨_, _, rfl, rfl, rfl, rfl, by cases a₁ <;> rfl⟩
  · rcases hf with rfl | rfl <;> exact ⟨_, _, rfl, rfl, rfl, rfl, by cases a₁ <;> rfl⟩

/-- A producer row runs on its operands' values, leaving the core and
setting its flags. -/
theorem Prod.exec (k : Prod) {w : X86.Width} {form : X86.OpEn} (hf : k.FormOk form) {arg₁ arg₂ : X86.Arg}
    {core : X86.Core} {v₁ v₂ : Word} (h₁ : arg₁.load core w = .ok v₁) (h₂ : arg₂.load core w = .ok v₂) :
    execRow { mn := k.mnemonic, w, form } [arg₁, arg₂] core {} = some (core, k.flags w v₁ v₂) := by
  cases k <;> simp only [Prod.FormOk] at hf
  · rcases hf with rfl | rfl | rfl <;>
    · simp only [execRow, X86.Op.exec, X86.Op.run, X86.Op.inputs, X86.readSlots, X86.desc, Prod.mnemonic,
        X86.Table.arithDesc, X86.Table.cmpArith, X86.Table.Arith.role, X86.Table.rmSlot, X86.Table.regSlot,
        X86.Table.immSlot, h₁, h₂]
      row_simp [Prod.flags, X86.Table.cmpArith, X86.Table.Arith.sem]
  · rcases hf with rfl | rfl <;>
    · simp only [execRow, X86.Op.exec, X86.Op.run, X86.Op.inputs, X86.readSlots, X86.desc, Prod.mnemonic,
        X86.Table.testDesc, X86.Table.rmSlot, X86.Table.regSlot, X86.Table.immSlot, h₁, h₂]
      row_simp [Prod.flags]

/-- A placed input argument loads its value. -/
theorem input_loads {ρ : Env} {mem : X86.Memory} {ctx : Word} {core : X86.Core} {w : X86.Width}
    {bR : Bound (VReg × GPR)} {s : X86.Slot} {a : XArg VReg} {arg : X86.Arg} {v : Word}
    (hb : bR.map Prod.fst = .input s a) (hm : (bR.map Prod.snd).machine some some = some arg)
    (hmem : core.memory = mem) (hctx : core.readReg .r15 = ctx)
    (huse : ∀ q ∈ bR.uses, ρ[q.1]? = some (core.readReg q.2)) (hv : a.valIn ρ mem ctx w = some v) :
    arg.load core w = .ok v := by
  cases a with
  | r y =>
    simp only [Bound.map_fst_eq_input_r] at hb
    obtain ⟨ry, rfl⟩ := hb
    simp [Bound.map, Bound.machine, XArg.map] at hm
    subst hm
    exact load_r (huse (y, ry) (by simp [Bound.uses, XArg.regs])) hv
  | m am =>
    simp only [Bound.map_fst_eq_input_m] at hb
    obtain ⟨amR, rfl, rfl⟩ := hb
    cases htm : (amR.map Prod.snd).toMem some with
    | none => simp [Bound.map, XArg.map, Bound.machine, htm] at hm
    | some m =>
    simp [Bound.map, XArg.map, Bound.machine, htm] at hm
    subst hm
    simp only [XArg.valIn, Option.bind_eq_some_iff] at hv
    obtain ⟨addr, ha, hv⟩ := hv
    have hv' : mem.read? w addr = .ok v := by
      cases h : mem.read? w addr <;> simp_all [Except.toOption]
    exact (load_m htm hmem hctx (fun q hq => huse q (by simp [Bound.uses, XArg.regs, hq])) ha hv').1
  | i k =>
    simp only [Bound.map_fst_eq_input_i] at hb
    subst hb
    simp [Bound.map, Bound.machine, XArg.map] at hm
    subst hm
    simp [XArg.valIn] at hv
    simp [X86.Arg.load, hv]

theorem need_input_le {s : X86.Slot} {a : XArg VReg} : (Bound.input s a).need ≤ 2 := by
  cases a with
  | m am => exact Amode.regs_length_le am
  | _ => simp [Bound.need, XArg.regs]

/-- A two-part Xv row run (a fused pair): `bound_run` for both parts at
once. -/
theorem parts2_run {ρ : Env} {mem : X86.Memory} {ctx : Word} {p c : X86.Op} {pb cb : List (Bound VReg)}
    (hneed : ((pb ++ cb).map Bound.need).sum ≤ 13) (hfx : (pb ++ cb).filterMap Bound.fixed? = [])
    (hdef : ∀ x ∈ (pb ++ cb).flatMap Bound.uses, ∃ w, ρ[x]? = some w) :
    ∃ (pR cR : List (Bound (VReg × GPR))) (pargs cargs : List X86.Arg) (core : X86.Core),
      pR.map (Bound.map Prod.fst) = pb ∧ cR.map (Bound.map Prod.fst) = cb ∧ (∀ b ∈ pR ++ cR, b.Assigned) ∧
      slotArgs some some (pR.map (Bound.map Prod.snd)) = some pargs ∧
      slotArgs some some (cR.map (Bound.map Prod.snd)) = some cargs ∧
      core.memory = mem ∧ core.readReg .r15 = ctx ∧ ((pR ++ cR).flatMap Bound.taken).Nodup ∧
      (∀ q ∈ (pR ++ cR).flatMap Bound.uses, ρ[q.1]? = some (core.readReg q.2)) ∧
      (∀ b ∈ pR ++ cR, ∀ q ∈ b.outputs, core.readReg q.2 = 0) ∧
      execBound [(p, pb), (c, cb)] ρ mem ctx = ((execRow p pargs core {}).bind fun r => execRow c cargs r.1 r.2).map
        fun r => (readBack r.1 ρ (((pR ++ cR).flatMap Bound.defs).map fun q => (q.1, q.2)), r.1.memory, r.2) := by
  obtain ⟨aps, margs, core, hmap, hass, hargs, hmem, hctx, htk, htkm, huse, hout, hrun⟩ :=
    execBound_run (parts := [(p, pb), (c, cb)]) (ρ := ρ) (mem := mem) (ctx := ctx)
      (by
        have : fixedRegs [(p, pb), (c, cb)] = [] := by
          simpa [fixedRegs, List.filterMap_append] using hfx
        rw [this]
        simpa [scratch] using hneed)
      (by simpa using hdef)
      (by
        have : ((pb ++ cb).filterMap Bound.fixedUse?) = [] := by
          rw [List.filterMap_eq_nil_iff]
          intro b hb
          have : b.fixed? = none := by
            rw [List.filterMap_eq_nil_iff] at hfx
            exact hfx b hb
          cases b <;> simp_all [Bound.fixed?, Bound.fixedUse?]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [this]
        exact List.nodup_nil)
  obtain ⟨⟨p', pR⟩, ⟨c', cR⟩, rfl⟩ : ∃ a₁ a₂, aps = [a₁, a₂] := by
    rcases aps with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, rest⟩⟩⟩ <;> simp at hmap
    exact ⟨a₁, a₂, rfl⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hmap
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hmap
  simp only [List.mapM_cons, List.mapM_nil, APart.args, Option.map_eq_map, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.map_eq_some_iff] at hargs
  obtain ⟨⟨_, pa⟩, ⟨pargs, hpsl, hpe⟩, hrest⟩ := hargs
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨rfl, rfl⟩ := hpe
  obtain ⟨_, ⟨⟨_, ca⟩, ⟨cargs, hcsl, hce⟩, hrest'⟩, hrest⟩ := hrest
  simp only [Prod.mk.injEq] at hce
  obtain ⟨rfl, rfl⟩ := hce
  obtain ⟨_, h₁, h₂⟩ := hrest'
  simp only [pure, Option.some.injEq] at h₁ h₂
  subst h₁; subst h₂
  simp only [pure, Option.some.injEq] at hrest
  subst hrest
  refine ⟨pR, cR, pargs, cargs, core, rfl, rfl, ?_, hpsl, hcsl, hmem, hctx, by simpa using htk, ?_, ?_, ?_⟩
  · intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact hass (p', pR) (by simp) b hb
    · exact hass (c', cR) (by simp) b hb
  · intro q hq
    refine huse q (by simpa using hq) ?_
    obtain ⟨b, hb, hqb⟩ := List.mem_flatMap.1 hq
    have hbm : b ∈ [(p', pR), (c', cR)].flatMap (·.2) := by simpa using hb
    by_cases hfu : q ∈ b.freeUses
    · have hqt : q.2 ∈ b.taken := by
        rw [Bound.taken_eq]; exact List.mem_map_of_mem (List.mem_append_left _ hfu)
      exact fun e => r15_not_mem_scratch (e ▸ (htkm b hbm q.2 hqt).1)
    · have hab : b.Assigned := by
        rcases List.mem_append.1 hb with hb | hb
        · exact hass (p', pR) (by simp) b hb
        · exact hass (c', cR) (by simp) b hb
      obtain ⟨i, hi, -⟩ := Bound.uses_fixed hab hqb hfu
      exfalso
      have : (b.map Prod.fst).fixed? = some i := by rw [Bound.fixed?_map, hi]
      rw [List.filterMap_eq_nil_iff] at hfx
      have := hfx (b.map Prod.fst) (by
        rcases List.mem_append.1 hb with hb | hb
        · exact List.mem_append_left _ (List.mem_map_of_mem hb)
        · exact List.mem_append_right _ (List.mem_map_of_mem hb))
      simp_all
  · intro b hb q hq
    exact hout b (by simpa using hb) q hq
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hrun
    rw [hrun]
    simp only [execRows, List.foldlM_cons, List.foldlM_nil]
    cases execRow p' pargs core {} with
    | none => rfl
    | some r => cases execRow c' cargs r.1 r.2 <;> simp [pure]


/-- Slot arguments of two slot bounds. -/
theorem slotArgs_two {b₁ b₂ : Bound GPR} {margs : List X86.Arg} (h₁ : b₁.isSlot = true) (h₂ : b₂.isSlot = true)
    (h : slotArgs some some [b₁, b₂] = some margs) :
    ∃ a₁ a₂, margs = [a₁, a₂] ∧ b₁.machine some some = some a₁ ∧ b₂.machine some some = some a₂ := by
  rw [slotArgs_cons, if_pos h₁, slotArgs_cons, if_pos h₂] at h
  cases e₁ : b₁.machine some some <;> cases e₂ : b₂.machine some some <;> simp_all [slotArgs]

/-- An ALU row (width 32 or 64, tied to `a`, second operand a register, an
immediate or memory): `x := a op b` and the row's flags. -/
theorem bound_alu (op : X86.AluOp) {w : X86.Width} (hw : w = .w32 ∨ w = .w64) {form : X86.OpEn}
    {s₁ s₂ : X86.Slot}
    (hrow : (form = .MR ∧ s₁ = X86.Table.rmSlot w .readWrite ∧ s₂ = X86.Table.regSlot w .read) ∨
      (form = .MI8 ∧ s₁ = X86.Table.rmSlot w .readWrite ∧ s₂ = X86.Table.immSlot .imm8 w) ∨
      (form = .MI ∧ s₁ = X86.Table.rmSlot w .readWrite ∧
        s₂ = X86.Table.immSlot (X86.Table.ImmKind.argKind (X86.Table.fullImm w)) w) ∨
      (form = .RM ∧ s₁ = X86.Table.regSlot w .readWrite ∧ s₂ = X86.Table.rmSlot w .read))
    {ρ : Env} {mem : X86.Memory} {ctx : Word} {x a : VReg} {b : XArg VReg} {va vb : Word}
    (ha : ρ[a]? = some va) (hb : b.valIn ρ mem ctx w = some vb) :
    execBound [({ mn := op.mnemonic, w, form }, [.tied s₁ a x, .input s₂ b])] ρ mem ctx =
      some (ρ.insert x (w.truncate (op.eval va vb)), mem, X86.ByteEval.aluFlags op w va vb) := by
  obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, -, hrun⟩ :=
    bound_run (o := { mn := op.mnemonic, w, form }) (ρ := ρ) (mem := mem) (ctx := ctx)
      (bs := [.tied s₁ a x, .input s₂ b])
      (by have := need_input_le (s := s₂) (a := b); simp [Bound.need, Bound.fixed?, scratch] at this ⊢; omega)
      (by
        have hd := XArg.valIn_defined hb
        intro y hy
        simp only [Bound.uses, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | hy
        · exact ⟨va, ha⟩
        · exact hd y hy)
      List.nodup_nil (by simp [Bound.fixed?])
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_tied] at hmap
  obtain ⟨_, _, rfl, ⟨ra, rx, rfl⟩, bb, _, rfl, hbb, rfl⟩ := hmap
  have hrx : ra = rx := hass (.tied _ (a, ra) (x, rx)) List.mem_cons_self
  subst hrx
  have hsl' : slotArgs some some [Bound.tied s₁ ra ra, bb.map Prod.snd] = some margs := hsl
  have hbs : (bb.map Prod.snd).isSlot = true := by
    rw [Bound.isSlot_map]
    have : (bb.map Prod.fst).isSlot = true := by rw [hbb]; rfl
    rwa [Bound.isSlot_map] at this
  obtain ⟨a₁, a₂, rfl, hm₁, hm₂⟩ := slotArgs_two rfl hbs hsl'
  simp [Bound.machine] at hm₁
  subst hm₁
  have hra := huse (a, ra) (by simp [Bound.uses])
  rw [ha] at hra
  have hld := input_loads hbb hm₂ hmem hctx (fun q hq => huse q (by simp [hq])) hb
  rw [hrun]
  have hdefs : (bb.defs) = [] := by
    have : (bb.map Prod.fst).defs = [] := by rw [hbb]; rfl
    rw [Bound.defs_map] at this
    simpa using this
  simp only [List.flatMap_cons, List.flatMap_nil, hdefs, List.append_nil]
  rcases hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  rcases hw with rfl | rfl <;> cases op <;>
  · simp only [execRow, X86.Op.exec, X86.Op.run, X86.Op.inputs, X86.readSlots, X86.Table.rmSlot,
      X86.Table.regSlot, X86.Table.immSlot, X86.desc, X86.AluOp.mnemonic, X86.Table.arithDesc,
      X86.Table.Arith.role, X86.Table.addArith, X86.Table.subArith, X86.Table.andArith, X86.Table.orArith,
      X86.Table.xorArith, hld]
    row_simp [hmem, (Option.some.inj hra).symm, Bound.defs]

/-- A branch on a flag producer (`cmp`, `test`) with operands' values
`v₁`, `v₂`: the environment and memory unchanged, taken as the condition
holds on the producer's flags. -/
theorem execJcc_prod (k : Prod) {w : X86.Width} {form : X86.OpEn} (hf : k.FormOk form) {ρ : Env}
    {mem : X86.Memory} {ctx : Word} {a₁ a₂ : XArg VReg} {v₁ v₂ : Word} (h₁ : a₁.valIn ρ mem ctx w = some v₁)
    (h₂ : a₂.valIn ρ mem ctx w = some v₂) {cond : X86.Condition} {b : Bool}
    (hb : (k.flags w v₁ v₂).test cond = some b) :
    execJcc { mn := k.mnemonic, w, form } [a₁, a₂] [] cond ρ mem ctx = some (ρ, mem, b) := by
  obtain ⟨s₁, s₂, hr₁, hr₂, hw₁, hw₂, hbind⟩ := k.bind (w := w) hf a₁ a₂
  refine execJcc_of hbind ?_ (jccTaken_eq hb)
  obtain ⟨bR, margs, core, hmap, hass, hsl, hmem, hctx, htk, htkm, huse, -, hrun⟩ :=
    bound_run (o := { mn := k.mnemonic, w, form }) (ρ := ρ) (mem := mem) (ctx := ctx)
      (bs := [.input s₁ a₁, .input s₂ a₂])
      (by
        have := need_input_le (s := s₁) (a := a₁); have := need_input_le (s := s₂) (a := a₂)
        simp [Bound.need, Bound.fixed?, scratch] at *; omega)
      (by
        have hd₁ := XArg.valIn_defined h₁; have hd₂ := XArg.valIn_defined h₂
        intro y hy
        simp only [Bound.uses, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hy
        rcases hy with hy | hy
        · exact hd₁ y hy
        · exact hd₂ y hy)
      List.nodup_nil (by simp [Bound.fixed?])
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at hmap
  obtain ⟨b₁, _, rfl, hb₁, b₂, _, rfl, hb₂, rfl⟩ := hmap
  have hs : ∀ (bb : Bound (VReg × GPR)) (s : X86.Slot) (a : XArg VReg), bb.map Prod.fst = .input s a →
      (bb.map Prod.snd).isSlot = true := by
    intro bb s a h
    rw [Bound.isSlot_map]
    have : (bb.map Prod.fst).isSlot = true := by rw [h]; rfl
    rwa [Bound.isSlot_map] at this
  have hdefs : ∀ (bb : Bound (VReg × GPR)) (s : X86.Slot) (a : XArg VReg), bb.map Prod.fst = .input s a →
      bb.defs = [] := by
    intro bb s a h
    have : (bb.map Prod.fst).defs = [] := by rw [h]; rfl
    rw [Bound.defs_map] at this
    simpa using this
  obtain ⟨arg₁, arg₂, rfl, hm₁, hm₂⟩ := slotArgs_two (hs b₁ _ _ hb₁) (hs b₂ _ _ hb₂) hsl
  have hl₁ := input_loads hb₁ hm₁ hmem hctx (fun q hq => huse q (by simp [hq])) (hw₁ ▸ h₁)
  have hl₂ := input_loads hb₂ hm₂ hmem hctx (fun q hq => huse q (by simp [hq])) (hw₂ ▸ h₂)
  rw [hw₁] at hl₁; rw [hw₂] at hl₂
  rw [hrun, k.exec hf hl₁ hl₂]
  simp [hdefs b₁ _ _ hb₁, hdefs b₂ _ _ hb₂, readBack, hmem]


theorem input_isSlot {bb : Bound (VReg × GPR)} {s : X86.Slot} {a : XArg VReg} (h : bb.map Prod.fst = .input s a) :
    (bb.map Prod.snd).isSlot = true := by
  rw [Bound.isSlot_map]
  have : (bb.map Prod.fst).isSlot = true := by rw [h]; rfl
  rwa [Bound.isSlot_map] at this

theorem input_defs {bb : Bound (VReg × GPR)} {s : X86.Slot} {a : XArg VReg} (h : bb.map Prod.fst = .input s a) :
    bb.defs = [] := by
  have : (bb.map Prod.fst).defs = [] := by rw [h]; rfl
  rw [Bound.defs_map] at this
  simpa using this

/-- The producer half of a fused pair: its two input operands load their
values, and the row sets its flags. -/
theorem fused_prod (k : Prod) {w : X86.Width} {form : X86.OpEn} (hf : k.FormOk form) {ρ : Env}
    {mem : X86.Memory} {ctx : Word} {a₁ a₂ : XArg VReg} {v₁ v₂ : Word} {core : X86.Core}
    {pR : List (Bound (VReg × GPR))} {pargs : List X86.Arg} {s₁ s₂ : X86.Slot} (hw₁ : s₁.width = w) (hw₂ : s₂.width = w)
    (hmap : pR.map (Bound.map Prod.fst) = [.input s₁ a₁, .input s₂ a₂])
    (hsl : slotArgs some some (pR.map (Bound.map Prod.snd)) = some pargs)
    (hmem : core.memory = mem) (hctx : core.readReg .r15 = ctx)
    (huse : ∀ q ∈ pR.flatMap Bound.uses, ρ[q.1]? = some (core.readReg q.2))
    (h₁ : a₁.valIn ρ mem ctx w = some v₁) (h₂ : a₂.valIn ρ mem ctx w = some v₂) :
    execRow { mn := k.mnemonic, w, form } pargs core {} = some (core, k.flags w v₁ v₂) ∧
      pR.flatMap Bound.defs = [] := by
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at hmap
  obtain ⟨b₁, _, rfl, hb₁, b₂, _, rfl, hb₂, rfl⟩ := hmap
  obtain ⟨arg₁, arg₂, rfl, hm₁, hm₂⟩ := slotArgs_two (input_isSlot hb₁) (input_isSlot hb₂) hsl
  have hl₁ := input_loads hb₁ hm₁ hmem hctx (fun q hq => huse q (by simp [hq])) (hw₁ ▸ h₁)
  have hl₂ := input_loads hb₂ hm₂ hmem hctx (fun q hq => huse q (by simp [hq])) (hw₂ ▸ h₂)
  rw [hw₁] at hl₁; rw [hw₂] at hl₂
  exact ⟨k.exec hf hl₁ hl₂, by simp [input_defs hb₁, input_defs hb₂]⟩

/-- A fused compare and `cmovcc` (64-bit, tied to `f`): `x := if c then t
else f` on the producer's flags. -/
theorem exec_fusedCmov (k : Prod) {w : X86.Width} {form : X86.OpEn} (hf : k.FormOk form) {ρ : Env}
    {mem : X86.Memory} {ctx : Word} {a₁ a₂ : XArg VReg} {v₁ v₂ : Word} (h₁ : a₁.valIn ρ mem ctx w = some v₁)
    (h₂ : a₂.valIn ρ mem ctx w = some v₂) {cond : X86.Condition} {b : Bool}
    (hb : (k.flags w v₁ v₂).test cond = some b) {x f : VReg} {t : XArg VReg} {vf vt : Word}
    (hfv : ρ[f]? = some vf) (htv : t.valIn ρ mem ctx .w64 = some vt) (hti : ∀ c, t ≠ .i c) :
    Inst.exec ρ mem ctx (.fused { mn := k.mnemonic, w, form } [a₁, a₂] (X86.Op.cmovRM cond .w64) [x] [.r f, t]) =
      some (ρ.insert x (if b then vt else vf), mem) := by
  obtain ⟨s₁, s₂, hr₁, hr₂, hw₁, hw₂, hpb⟩ := k.bind (w := w) hf a₁ a₂
  have hcb : bindRow (X86.Op.cmovRM cond .w64) [x] [.r f, t] =
      some [.tied (X86.Table.regSlot .w64 .readWrite) f x, .input (X86.Table.rmSlot .w64 .read) t] := by
    cases t <;> rfl
  obtain ⟨pR, cR, pargs, cargs, core, hpm, hcm, hass, hpsl, hcsl, hmem, hctx, htk, huse, -, hrun⟩ :=
    parts2_run (ρ := ρ) (mem := mem) (ctx := ctx) (p := { mn := k.mnemonic, w, form })
      (c := X86.Op.cmovRM cond .w64) (pb := [.input s₁ a₁, .input s₂ a₂])
      (cb := [.tied (X86.Table.regSlot .w64 .readWrite) f x, .input (X86.Table.rmSlot .w64 .read) t])
      (by
        have := need_input_le (s := s₁) (a := a₁); have := need_input_le (s := s₂) (a := a₂)
        have := need_input_le (s := X86.Table.rmSlot .w64 .read) (a := t)
        simp [Bound.need] at *; omega)
      (by simp [Bound.fixed?])
      (by
        have hd₁ := XArg.valIn_defined h₁; have hd₂ := XArg.valIn_defined h₂; have hdt := XArg.valIn_defined htv
        intro y hy
        simp only [Bound.uses, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with hy | hy | rfl | hy
        · exact hd₁ y hy
        · exact hd₂ y hy
        · exact ⟨vf, hfv⟩
        · exact hdt y hy)
  have hpu : ∀ q ∈ pR.flatMap Bound.uses, ρ[q.1]? = some (core.readReg q.2) :=
    fun q hq => huse q (by simp only [List.flatMap_append, List.mem_append]; exact .inl hq)
  obtain ⟨hpx, hpd⟩ := fused_prod k hf hw₁ hw₂ hpm hpsl hmem hctx hpu h₁ h₂
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_tied] at hcm
  obtain ⟨_, _, rfl, ⟨rf, rx, rfl⟩, bt, _, rfl, hbt, rfl⟩ := hcm
  have hrx : rf = rx := hass (.tied (X86.Table.regSlot .w64 .readWrite) (f, rf) (x, rx)) (by simp)
  subst hrx
  obtain ⟨a₁', a₂', rfl, hm₁, hm₂⟩ := slotArgs_two rfl (input_isSlot hbt) hcsl
  simp [Bound.machine, Bound.map] at hm₁
  subst hm₁
  have hrf := huse (f, rf) (by simp [Bound.uses])
  rw [hfv] at hrf
  have hlt := input_loads hbt hm₂ hmem hctx (fun q hq => huse q (by simp [hq])) htv
  have hb' := test_restrict (k.flags w v₁ v₂) cond
  rw [hb] at hb'
  rw [Inst.exec, hpb, hcb]
  simp only [Option.bind_eq_bind, Option.bind_some, hrun, hpx]
  simp only [List.flatMap_append, hpd, List.flatMap_cons, List.flatMap_nil, input_defs hbt, List.nil_append,
    List.append_nil]
  simp only [execRow, X86.Op.exec, X86.Op.run, X86.Op.inputs, X86.readSlots, X86.desc, X86.Op.cmovRM,
    X86.Table.cmovDesc, X86.Table.regSlot, X86.Table.rmSlot, hlt]
  row_simp [hmem, (Option.some.inj hrf).symm, X86.Table.cmovSem, hb', hpd, input_defs hbt]

/-- A fused compare and `setcc` (its destination zeroed first): `x := 1`
if the condition holds on the producer's flags, else `0`. -/
theorem exec_fusedSetcc (k : Prod) {w : X86.Width} {form : X86.OpEn} (hf : k.FormOk form) {ρ : Env}
    {mem : X86.Memory} {ctx : Word} {a₁ a₂ : XArg VReg} {v₁ v₂ : Word} (h₁ : a₁.valIn ρ mem ctx w = some v₁)
    (h₂ : a₂.valIn ρ mem ctx w = some v₂) {cond : X86.Condition} {b : Bool}
    (hb : (k.flags w v₁ v₂).test cond = some b) (x : VReg) :
    Inst.exec ρ mem ctx (.fused { mn := k.mnemonic, w, form } [a₁, a₂] (X86.Op.setccM cond) [x] []) =
      some (ρ.insert x (if b then 1 else 0), mem) := by
  obtain ⟨s₁, s₂, hr₁, hr₂, hw₁, hw₂, hpb⟩ := k.bind (w := w) hf a₁ a₂
  have hcb : bindRow (X86.Op.setccM cond) [x] [] = some [.output (X86.Table.rmSlot .w8 .write) x] := rfl
  obtain ⟨pR, cR, pargs, cargs, core, hpm, hcm, hass, hpsl, hcsl, hmem, hctx, htk, huse, hout, hrun⟩ :=
    parts2_run (ρ := ρ) (mem := mem) (ctx := ctx) (p := { mn := k.mnemonic, w, form })
      (c := X86.Op.setccM cond) (pb := [.input s₁ a₁, .input s₂ a₂])
      (cb := [.output (X86.Table.rmSlot .w8 .write) x])
      (by
        have := need_input_le (s := s₁) (a := a₁); have := need_input_le (s := s₂) (a := a₂)
        simp [Bound.need] at *; omega)
      (by simp [Bound.fixed?])
      (by
        have hd₁ := XArg.valIn_defined h₁; have hd₂ := XArg.valIn_defined h₂
        intro y hy
        simp only [Bound.uses, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.mem_append, List.not_mem_nil, or_false] at hy
        rcases hy with hy | hy
        · exact hd₁ y hy
        · exact hd₂ y hy)
  have hpu : ∀ q ∈ pR.flatMap Bound.uses, ρ[q.1]? = some (core.readReg q.2) :=
    fun q hq => huse q (by simp only [List.flatMap_append, List.mem_append]; exact .inl hq)
  obtain ⟨hpx, hpd⟩ := fused_prod k hf hw₁ hw₂ hpm hpsl hmem hctx hpu h₁ h₂
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff, Bound.map_fst_eq_output] at hcm
  obtain ⟨_, _, rfl, ⟨rx, rfl⟩, rfl⟩ := hcm
  simp [slotArgs, Bound.isSlot, Bound.map, Bound.machine, List.filter_cons, List.mapM_cons] at hcsl
  subst hcsl
  have hz := hout (.output (X86.Table.rmSlot .w8 .write) (x, rx)) (by simp) (x, rx) (by simp [Bound.outputs])
  have hb' := test_restrict (k.flags w v₁ v₂) cond
  rw [hb] at hb'
  rw [Inst.exec, hpb, hcb]
  simp only [Option.bind_eq_bind, Option.bind_some, hrun, hpx]
  row_simp [hmem, X86.Op.setccM, X86.Table.setccDesc, X86.Table.setccSem, hb', hpd, hz, X86.Width.truncate,
    X86.Width.mask]
  cases b <;> rfl

end Compilatrix.Xv
