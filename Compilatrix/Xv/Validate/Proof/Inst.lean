import Compilatrix.Xv.Validate.Proof.RowChecks

/-!
# One instruction

The validator's transfer for one instruction is sound for its Xl image
(05 §5's per-instruction step of `Validate.sound`): if the abstract state
agrees with the Xv environment and the Xl locations before, and Xv runs the
instruction, then Xl runs the substituted instruction with the same memory
and the new abstract state agrees afterwards (`stepInst_sound`, calls
aside, which `Proof.Sound` handles with frames). An edit is a move whose
source holds a known value (`stepEdit_sound`), and a `jcc` producer runs
with the same flags (`stepJcc_sound`).
-/

namespace Compilatrix.Xv.Validate

open Compilatrix.Lir (VReg Word Env Operand Kind Pos Con)
open Compilatrix.Xv.Xl (placeL xlLocs xlNamed xlCells xlFree xlTable WriteOk)
open Compilatrix.Xv

/-- The Xl locations as a valuation. -/
abbrev XlVal (regs : Xl.Regs) (fr : Xl.Frame) : Loc → Option Word := Xl.read regs fr

@[simp] theorem kind_use_beq_use : (Kind.use == Kind.use) = true := rfl
@[simp] theorem kind_use_beq_define : (Kind.use == Kind.define) = false := rfl
@[simp] theorem kind_define_beq_use : (Kind.define == Kind.use) = false := rfl
@[simp] theorem kind_define_beq_define : (Kind.define == Kind.define) = true := rfl

/-! ## Generic operands -/

theorem stepOperands_ok {c : Ctx} {a a' : AState} {ops : List (Operand VReg)} {ls : List Loc}
    {row : Bool} (h : stepOperands c a ops ls row = .ok a') :
    ops.length = ls.length ∧ operandCode c (ops.zip ls) row = none ∧
      usesHold a (ops.zip ls) = true ∧ a' = a.define (defsOfPairs (ops.zip ls)) [] := by
  unfold stepOperands at h
  cases h1 : (ops.length == ls.length) <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw, reduceCtorEq] at h
  cases h2 : operandCode c (ops.zip ls) row <;> simp only [h2] at h
  · cases h3 : usesHold a (ops.zip ls) <;>
      simp only [h3, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw, reduceCtorEq, Except.ok.injEq, Bool.not_true, Bool.not_false] at h
    exact ⟨by simpa using h1, rfl, rfl, h.symm⟩
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

theorem zip_pairs (ops : List (Operand (VReg × Loc))) :
    (ops.map (opMap Prod.fst)).zip (ops.map (·.v.2)) = pairsOf ops := List.zip_map'

theorem defsOfPairs_pairs {bs : List (Bound (VReg × Loc))} {z : Bool} :
    defsOfPairs (pairsOf (boundOperands bs z)) = bs.flatMap Bound.defs := by
  unfold defsOfPairs
  rw [defsOf_pairs, ← boundDefs_v z 0]
  unfold pairsOf
  rw [List.map_map]
  rfl

/-- An instruction's rows under the validator's operand checks. -/
theorem rows_sound {c : Ctx} {a a' : AState} {parts : List (X86.Op × List (Bound (VReg × Loc)))} {z : Bool}
    (hv : stepOperands c a ((boundOperands (parts.flatMap Prod.snd) z).map (opMap Prod.fst))
      ((boundOperands (parts.flatMap Prod.snd) z).map (·.v.2)) true = .ok a')
    (hshape : ∀ q ∈ parts, ∃ defs args, bindRow q.1 defs args = some q.2)
    (hstack : ∀ q ∈ parts, (X86.desc q.1).stack = .none)
    (hwide : ∀ q ∈ parts, ∀ i ∈ (X86.desc q.1).implicit, i.role.reads = true ∨ Wide i.width)
    (hnarrow : ∀ q ∈ parts, ∀ b ∈ q.2, b.narrowOutput = true → z = true ∧ parts.getLast? = some q)
    (honly : ∀ q ∈ parts.dropLast, q.2.flatMap Bound.defs = [])
    {ρ ρ' : Env} {regs : Xl.Regs} {fr : Xl.Frame} {mem mem' : X86.Memory} {ctx : Word}
    {flags : X86.ByteEval.Flags}
    (hagree : a.Agree ρ (Xl.read regs fr)) (hsize : regs.size = 16) (hin : fr.inArgs.size = c.stackParams)
    (hxv : execBound (parts.map fun q => (q.1, q.2.map (Bound.map Prod.fst))) ρ mem ctx =
      some (ρ', mem', flags)) :
    ∃ regs' fr', Xl.execBound (parts.map fun q => (q.1, q.2.map (Bound.map Prod.snd))) regs fr mem ctx z =
        some (regs', fr', mem', flags) ∧ regs'.size = 16 ∧ Xl.Frame.SameCtl fr fr' ∧
      a'.Agree ρ' (Xl.read regs' fr') := by
  obtain ⟨-, hcode, hholds, rfl⟩ := stepOperands_ok hv
  rw [zip_pairs] at hcode hholds ⊢
  have hops := operandCode_none hcode
  have hf := rowFacts_of_checks hin hshape hstack hwide hnarrow honly hops
  have hagree' : ∀ u ∈ (parts.flatMap Prod.snd).flatMap Bound.uses,
      ∃ w, ρ[u.1]? = some w ∧ Xl.read regs fr u.2 = some w := by
    intro u hu
    obtain ⟨o, -, rfl, hp⟩ := use_pair (z := z) hu
    have := List.all_eq_true.1 hholds _ hp
    exact hagree.holds (by simpa using this)
  obtain ⟨regs', fr', hxl, hs, hctl, hdefs, hρ, hℓ⟩ := execBound_sim hf hsize hagree' hxv
  refine ⟨regs', fr', hxl, hs, hctl, ?_⟩
  rw [defsOfPairs_pairs]
  exact hagree.define (fun v l h => hdefs (v, l) h) hρ (fun l hl _ => hℓ l hl)

/-! ## Pairing an instruction with its locations -/

theorem Inst.map_eq_op {pi : Inst (VReg × Loc)} {o : X86.Op} {defs : List VReg} {args : List (XArg VReg)}
    (h : pi.map Prod.fst = .op o defs args) :
    ∃ pd pa, pi = .op o pd pa ∧ pd.map Prod.fst = defs ∧ pa.map (XArg.map Prod.fst) = args := by
  cases pi <;> simp [Inst.map] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem Inst.map_eq_fused {pi : Inst (VReg × Loc)} {p c : X86.Op} {defs : List VReg}
    {pargs cargs : List (XArg VReg)} (h : pi.map Prod.fst = .fused p pargs c defs cargs) :
    ∃ ppa pd pca, pi = .fused p ppa c pd pca ∧ ppa.map (XArg.map Prod.fst) = pargs ∧
      pd.map Prod.fst = defs ∧ pca.map (XArg.map Prod.fst) = cargs := by
  cases pi <;> simp [Inst.map] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩

theorem bindRow_pair {o : X86.Op} {pd : List (VReg × Loc)} {pa : List (XArg (VReg × Loc))}
    {bs : List (Bound VReg)} (h : bindRow o (pd.map Prod.fst) (pa.map (XArg.map Prod.fst)) = some bs) :
    ∃ pbs, bindRow o pd pa = some pbs ∧ bs = pbs.map (Bound.map Prod.fst) := by
  rw [bindRow_map] at h
  cases hb : bindRow o pd pa with
  | none => rw [hb] at h; simp at h
  | some pbs => rw [hb] at h; simp at h; exact ⟨pbs, rfl, h.symm⟩

theorem locs_of_pair {i : Inst VReg} {ls : List Loc} {pi : Inst (VReg × Loc)}
    (hsub : i.substitute ls = some (pi.map Prod.snd)) (hc : pi.consumed = i.consumed.zip ls) :
    pi.consumed.map Prod.snd = ls := by
  rw [hc]
  exact List.map_snd_zip (by rw [(Inst.substitute_consumed hsub).2]; exact Nat.le_refl _)

theorem unless_ok {b : Bool} {e : Code} {k : Except Code AState} {a' : AState}
    (h : ((unless b do throw e) >>= fun _ => k : Except Code AState) = .ok a') : b = true ∧ k = .ok a' := by
  cases b <;> simp_all [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]

/-! ## Row instructions -/

theorem rowShape_facts {o : X86.Op} {defs : List VReg} {args : List (XArg VReg)} {z : Bool}
    (h : rowShapeOk o defs args z = true) :
    (X86.desc o).stack = .none ∧
      (∀ i ∈ (X86.desc o).implicit, i.role.reads = true ∨ Wide i.width) ∧
      (∀ bs, bindRow o defs args = some bs → z = false → ∀ b ∈ bs, b.narrowOutput = false) := by
  unfold rowShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hstk, hw⟩, hn⟩ := h
  refine ⟨hstk, fun i hi => ?_, fun bs hbs hz b hb => ?_⟩
  · rcases hw i hi with (h | h) | h
    · exact .inl h
    · exact .inr (.inl (by simpa using h))
    · exact .inr (.inr (by simpa using h))
  · rw [hbs, hz] at hn
    simp only [Bool.false_or, Bool.not_eq_eq_eq_not, Bool.not_true] at hn
    simpa using List.any_eq_false.1 hn b hb

/-- A one-row instruction (`op`, or a `jcc` producer) under the validator's
checks. -/
theorem single_sound {c : Ctx} {a a' : AState} {o : X86.Op} {defs : List VReg}
    {args : List (XArg VReg)} {ls : List Loc} {defs' : List Loc} {args' : List (XArg Loc)}
    (hshape : rowShapeOk o defs args false = true)
    (hv : stepOperands c a (Inst.op o defs args).operands ls true = .ok a')
    (hsub : (Inst.op o defs args).substitute ls = some (.op o defs' args'))
    {bs : List (Bound VReg)} (hbs : bindRow o defs args = some bs)
    {ρ ρ' : Env} {regs : Xl.Regs} {fr : Xl.Frame} {mem mem' : X86.Memory} {ctx : Word}
    {flags : X86.ByteEval.Flags}
    (hagree : a.Agree ρ (Xl.read regs fr)) (hsize : regs.size = 16) (hin : fr.inArgs.size = c.stackParams)
    (hrun : execBound [(o, bs)] ρ mem ctx = some (ρ', mem', flags)) :
    ∃ bs', bindRow o defs' args' = some bs' ∧ ∃ regs' fr',
      Xl.execBound [(o, bs')] regs fr mem ctx = some (regs', fr', mem', flags) ∧ regs'.size = 16 ∧
      Xl.Frame.SameCtl fr fr' ∧ a'.Agree ρ' (Xl.read regs' fr') := by
  obtain ⟨pi, hfst, hsnd, hcons⟩ := Inst.pair_of_substitute hsub
  obtain ⟨pd, pa, rfl, rfl, rfl⟩ := Inst.map_eq_op hfst
  simp only [Inst.map, Inst.op.injEq, true_and] at hsnd
  obtain ⟨rfl, rfl⟩ := hsnd
  obtain ⟨pbs, hpbs, rfl⟩ := bindRow_pair hbs
  have hls : ls = (boundOperands pbs false).map (·.v.2) := by
    have := locs_of_pair (pi := .op o pd pa) hsub hcons
    rw [← this]
    simp only [Inst.consumed, ← boundOperands_v hpbs false, List.map_map]
    rfl
  have hops : (Inst.op o (pd.map Prod.fst) (pa.map (XArg.map Prod.fst))).operands =
      (boundOperands pbs false).map (opMap Prod.fst) := by
    simp [Inst.operands, bindRow_map, hpbs, boundOperands_map]
  rw [hops, hls] at hv
  obtain ⟨hstk, hw, hn⟩ := rowShape_facts hshape
  have hn' : ∀ b ∈ pbs, b.narrowOutput = false := fun b hb => by
    have := hn _ (by rw [bindRow_map, hpbs]; rfl) rfl (b.map Prod.fst) (List.mem_map_of_mem hb)
    simpa using this
  obtain ⟨regs', fr', hxl, hs, hctl, hag⟩ := rows_sound (parts := [(o, pbs)]) (z := false)
    (by simpa using hv) (by simp; exact ⟨pd, pa, hpbs⟩) (by simpa using hstk)
    (by simpa using hw)
    (by
      simp only [List.mem_singleton, forall_eq]
      intro b hb hnb
      rw [hn' b hb] at hnb
      cases hnb)
    (by simp) hagree hsize hin (by simpa using hrun)
  refine ⟨pbs.map (Bound.map Prod.snd), by rw [bindRow_map, hpbs]; rfl, regs', fr', ?_, hs, hctl, hag⟩
  simpa using hxl

theorem op_sound {c : Ctx} {a a' : AState} {o : X86.Op} {defs : List VReg} {args : List (XArg VReg)}
    {ls : List Loc} {x : Inst Loc}
    (hv : stepInst c a (.op o defs args) ls = .ok a') (hsub : (Inst.op o defs args).substitute ls = some x)
    {ρ ρ' : Env} {regs : Xl.Regs} {fr : Xl.Frame} {mem mem' : X86.Memory} {ctx : Word}
    (hagree : a.Agree ρ (Xl.read regs fr)) (hsize : regs.size = 16) (hin : fr.inArgs.size = c.stackParams)
    (hxv : (Inst.op o defs args).exec ρ mem ctx = some (ρ', mem')) :
    ∃ regs' fr', Xl.execInst regs fr mem ctx x = some (regs', fr', mem') ∧ regs'.size = 16 ∧
      Xl.Frame.SameCtl fr fr' ∧ a'.Agree ρ' (Xl.read regs' fr') := by
  simp only [stepInst] at hv
  have hshapeRow : rowShapeOk o defs args false = true := by
    cases h : rowShapeOk o defs args false
    · simp [h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hv
    · rfl
  simp only [hshapeRow, ↓reduceIte] at hv
  simp only [Inst.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hxv
  obtain ⟨bs, hbs, ⟨ρ₁, mem₁, fl⟩, hrun, he⟩ := hxv
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨pi, hfst, hsnd, -⟩ := Inst.pair_of_substitute hsub
  obtain ⟨pd, pa, rfl, -, -⟩ := Inst.map_eq_op hfst
  subst hsnd
  obtain ⟨bs', hbs', regs', fr', hxl, hs, hctl, hag⟩ :=
    single_sound hshapeRow hv hsub hbs hagree hsize hin hrun
  refine ⟨regs', fr', ?_, hs, hctl, hag⟩
  simp only [Inst.map, Xl.execInst, Option.bind_eq_bind] at hbs' ⊢
  rw [hbs', Option.bind_some, hxl]
  rfl

theorem fused_sound {c : Ctx} {a a' : AState} {p q : X86.Op} {defs : List VReg}
    {pargs qargs : List (XArg VReg)} {ls : List Loc} {x : Inst Loc}
    (hv : stepInst c a (.fused p pargs q defs qargs) ls = .ok a')
    (hsub : (Inst.fused p pargs q defs qargs).substitute ls = some x)
    {ρ ρ' : Env} {regs : Xl.Regs} {fr : Xl.Frame} {mem mem' : X86.Memory} {ctx : Word}
    (hagree : a.Agree ρ (Xl.read regs fr)) (hsize : regs.size = 16) (hin : fr.inArgs.size = c.stackParams)
    (hxv : (Inst.fused p pargs q defs qargs).exec ρ mem ctx = some (ρ', mem')) :
    ∃ regs' fr', Xl.execInst regs fr mem ctx x = some (regs', fr', mem') ∧ regs'.size = 16 ∧
      Xl.Frame.SameCtl fr fr' ∧ a'.Agree ρ' (Xl.read regs' fr') := by
  simp only [stepInst] at hv
  have hshapeRow : (rowShapeOk p [] pargs false && rowShapeOk q defs qargs true) = true := by
    cases h : (rowShapeOk p [] pargs false && rowShapeOk q defs qargs true)
    · simp [h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hv
    · rfl
  simp only [hshapeRow, ↓reduceIte] at hv
  rw [Bool.and_eq_true] at hshapeRow
  simp only [Inst.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hxv
  obtain ⟨pb, hpb, cb, hcb, ⟨ρ₁, mem₁, fl⟩, hrun, he⟩ := hxv
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨pi, hfst, hsnd, hcons⟩ := Inst.pair_of_substitute hsub
  obtain ⟨ppa, pd, pqa, rfl, rfl, rfl, rfl⟩ := Inst.map_eq_fused hfst
  subst hsnd
  obtain ⟨ppb, hppb, rfl⟩ := bindRow_pair (pd := ([] : List (VReg × Loc))) hpb
  obtain ⟨pqb, hpqb, rfl⟩ := bindRow_pair hcb
  have hls : ls = (boundOperands (ppb ++ pqb) true).map (·.v.2) := by
    have := locs_of_pair hsub hcons
    rw [← this]
    have r₁ := bindRow_regs hppb
    have r₂ := bindRow_regs hpqb
    have e₁ : (boundUses (ppb ++ pqb)).map (fun x => x.v.2) =
        ((ppb ++ pqb).flatMap Bound.uses).map Prod.snd := by
      rw [← boundUses_v, List.map_map]; rfl
    have e₂ : (boundDefs true 0 (ppb ++ pqb)).map (fun x => x.v.2) =
        ((ppb ++ pqb).flatMap Bound.defs).map Prod.snd := by
      rw [← boundDefs_v true 0, List.map_map]; rfl
    simp only [Inst.consumed, boundOperands, List.map_append]
    rw [e₁, e₂]
    simp [List.flatMap_append, r₁.1, r₁.2, r₂.1, r₂.2]
  have hops : (Inst.fused p (ppa.map (XArg.map Prod.fst)) q (pd.map Prod.fst)
      (pqa.map (XArg.map Prod.fst))).operands = (boundOperands (ppb ++ pqb) true).map (opMap Prod.fst) := by
    have e₁ := bindRow_map Prod.fst p [] ppa
    simp only [List.map_nil] at e₁
    simp [Inst.operands, e₁, hppb, bindRow_map, hpqb, ← boundOperands_map, List.map_append]
  rw [hops, hls] at hv
  obtain ⟨hstk₁, hw₁, hn₁⟩ := rowShape_facts hshapeRow.1
  obtain ⟨hstk₂, hw₂, -⟩ := rowShape_facts hshapeRow.2
  have hn₁' : ∀ b ∈ ppb, b.narrowOutput = false := fun b hb => by
    have e₁ := bindRow_map Prod.fst p [] ppa
    simp only [List.map_nil] at e₁
    have := hn₁ _ (by rw [e₁, hppb]; rfl) rfl (b.map Prod.fst) (List.mem_map_of_mem hb)
    simpa using this
  have hnod : ppb.flatMap Bound.defs = [] := by
    have := (bindRow_regs hppb).2
    exact this
  obtain ⟨regs', fr', hxl, hs, hctl, hag⟩ := rows_sound (parts := [(p, ppb), (q, pqb)]) (z := true)
    (by simpa using hv)
    (by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      exact ⟨⟨[], ppa, hppb⟩, ⟨pd, pqa, hpqb⟩⟩)
    (by simp [hstk₁, hstk₂])
    (by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      exact ⟨hw₁, hw₂⟩)
    (by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      refine ⟨fun b hb hnb => ?_, fun b _ _ => by simp⟩
      rw [hn₁' b hb] at hnb
      cases hnb)
    (by simpa [List.flatMap_eq_nil_iff] using hnod) hagree hsize hin (by simpa using hrun)
  refine ⟨regs', fr', ?_, hs, hctl, hag⟩
  have e₂ := bindRow_map Prod.snd p [] ppa
  simp only [List.map_nil] at e₂
  simp only [Inst.map, Xl.execInst, Option.bind_eq_bind, List.map_nil]
  rw [e₂, hppb, bindRow_map, hpqb]
  simp only [Option.map_some, Option.bind_some]
  simp only [List.map_cons, List.map_nil] at hxl
  rw [hxl]
  rfl

theorem move_sound {c : Ctx} {a a' : AState} {dst src : VReg} {ls : List Loc} {x : Inst Loc}
    (hv : stepInst c a (.move dst src) ls = .ok a') (hsub : (Inst.move dst src).substitute ls = some x)
    {ρ ρ' : Env} {regs : Xl.Regs} {fr : Xl.Frame} {mem mem' : X86.Memory} {ctx : Word}
    (hagree : a.Agree ρ (Xl.read regs fr)) (hsize : regs.size = 16) (hin : fr.inArgs.size = c.stackParams)
    (hxv : (Inst.move dst src).exec ρ mem ctx = some (ρ', mem')) :
    ∃ regs' fr', Xl.execInst regs fr mem ctx x = some (regs', fr', mem') ∧ regs'.size = 16 ∧
      Xl.Frame.SameCtl fr fr' ∧ a'.Agree ρ' (Xl.read regs' fr') := by
  rcases ls with _ | ⟨ls₁, _ | ⟨ld, _ | ⟨_, _⟩⟩⟩ <;> simp [Inst.substitute] at hsub
  subst hsub
  have hv' : stepOperands c a (Inst.move dst src).operands [ls₁, ld] false = .ok a' := by
    simp only [stepInst] at hv
    cases h : (ls₁.isCell && ld.isCell)
    · simpa [h] using hv
    · simp [h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hv
  obtain ⟨-, hcode, hholds, rfl⟩ := stepOperands_ok hv'
  have hf := operandCode_none hcode
  simp only [Inst.operands, List.zip_cons_cons, List.zip_nil_right] at hf hholds ⊢
  have hsrc : a.holds ls₁ src = true := by
    simpa [usesHold, usesOf, useAt, defAt] using hholds
  obtain ⟨w, hw, hr⟩ := hagree.holds hsrc
  simp only [Inst.exec, Option.bind_eq_bind, hw, Option.bind_some, pure, Option.some.injEq,
    Prod.mk.injEq] at hxv
  obtain ⟨rfl, rfl⟩ := hxv
  have hloc := hf.loc (defAt .any dst, ld) (by simp)
  have hok : WriteOk fr ld := by
    cases ld with
    | reg r => simp only [WriteOk]; simp only [locCode, allocatable] at hloc; cases h : Xl.reserved r <;> simp_all
    | slot i => trivial
    | inArg i => simp only [locCode] at hloc; simp only [WriteOk, hin]; split at hloc <;> simp_all
    | outArg i => simp [locCode] at hloc
  obtain ⟨regs', fr', hwr⟩ := Xl.write_ok (regs := regs) hok w
  obtain ⟨hread, hother, hctl, hs⟩ := Xl.write_spec hsize hwr
  refine ⟨regs', fr', by simp [Xl.execInst, hr, hwr], hs, hctl, ?_⟩
  simp only [defsOfPairs, defsOf, List.filter_cons, useAt, defAt, List.filter_nil]
  simp only [kind_use_beq_define, kind_define_beq_define, Bool.false_eq_true, ↓reduceIte, List.map_cons,
    List.map_nil]
  refine hagree.define (fun v l h => ?_) (fun v hv => ?_) (fun l hl _ => ?_)
  ·
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨w, by simp, hread⟩
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hv
    rw [Std.HashMap.getElem?_insert]
    have : (dst == v) = false := by simpa [beq_iff_eq] using fun e => hv e.symm
    simp [this]
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hl
    exact hother l hl

theorem zeroRow_run (core : X86.Core) (r : X86.GPR) :
    ∃ core' f, execRows [(zeroRow, [.reg r, .reg r])] core = some (core', f) ∧
      core'.readReg r = 0 ∧ core'.memory = core.memory := by
  have hstack : (X86.desc zeroRow).stack = .none := rfl
  simp only [execRows, List.foldlM_cons, List.foldlM_nil, execRow, X86.Op.exec, run_eq hstack]
  simp [zeroRow, X86.desc, X86.Table.arithDesc, X86.Table.xorArith, X86.Table.Arith.sem,
    X86.Table.Arith.role, X86.Table.aluSem, X86.readSlots, X86.writeSlots, X86.Table.rmSlot,
    X86.Table.regSlot, X86.Arg.load, X86.Arg.store, readReg_writeReg, mergeWrite, X86.Width.truncate,
    bind, Except.bind, pure, Except.pure, X86.AluOp.eval]

theorem zero_sound {c : Ctx} {a a' : AState} {y : VReg} {ls : List Loc} {x : Inst Loc}
    (hv : stepInst c a (.zero y) ls = .ok a') (hsub : (Inst.zero y).substitute ls = some x)
    {ρ ρ' : Env} {regs : Xl.Regs} {fr : Xl.Frame} {mem mem' : X86.Memory} {ctx : Word}
    (hagree : a.Agree ρ (Xl.read regs fr)) (hsize : regs.size = 16)
    (hxv : (Inst.zero y).exec ρ mem ctx = some (ρ', mem')) :
    ∃ regs' fr', Xl.execInst regs fr mem ctx x = some (regs', fr', mem') ∧ regs'.size = 16 ∧
      Xl.Frame.SameCtl fr fr' ∧ a'.Agree ρ' (Xl.read regs' fr') := by
  rcases ls with _ | ⟨l, _ | ⟨_, _⟩⟩ <;> simp [Inst.substitute] at hsub
  subst hsub
  have hv' : stepOperands c a (Inst.zero y).operands [l] false = .ok a' := hv
  obtain ⟨-, hcode, -, rfl⟩ := stepOperands_ok hv'
  have hf := operandCode_none hcode
  simp only [Inst.operands, List.zip_cons_cons, List.zip_nil_right] at hf ⊢
  have hcon := hf.con (defAt .reg y, l) (by simp)
  have hloc := hf.loc (defAt .reg y, l) (by simp)
  simp only [defAt] at hcon
  cases l with
  | reg r =>
    have hres : Xl.reserved r = false := by
      simp only [locCode, allocatable] at hloc; cases h : Xl.reserved r <;> simp_all
    obtain ⟨core₁, f₁, hrun₁, hr₁, hm₁⟩ := zeroRow_run { registers := fun _ => 0, memory := mem } .rax
    obtain ⟨core₂, f₂, hrun₂, hr₂, hm₂⟩ :=
      zeroRow_run { registers := fun q => (regs.get q).getD 0, memory := mem } r
    simp only [Inst.exec, hrun₁, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq,
      Prod.mk.injEq] at hxv
    obtain ⟨rfl, rfl⟩ := hxv
    refine ⟨regs.set r (some (core₂.readReg r)), fr, ?_, by rw [Xl.Regs.size_set, hsize],
      Xl.Frame.SameCtl.refl _, ?_⟩
    · simp [Xl.execInst, hres, hrun₂, hm₁, hm₂, guard]
    · simp only [defsOfPairs, defsOf, List.filter_cons, List.filter_nil, defAt, kind_define_beq_define,
        ↓reduceIte,
        List.map_cons, List.map_nil]
      refine hagree.define (fun v l h => ?_) (fun v hv => ?_) (fun l hl _ => ?_)
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨0, by simp [hr₁], ?_⟩
        rw [Xl.read_reg hres, Xl.Regs.get_set _ hsize, ite_eq_left rfl, hr₂]
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hv
        rw [Std.HashMap.getElem?_insert]
        have : (y == v) = false := by simpa [beq_iff_eq] using fun e => hv e.symm
        simp [this]
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hl
        cases l with
        | reg r' =>
          have hne : r' ≠ r := fun e => hl (e ▸ rfl)
          simp [Xl.read, Xl.Regs.get_set _ hsize, hne]
        | _ => rfl
  | _ => simp [conOk] at hcon

/-! ## Edits -/

theorem stepEdit_sound {c : Ctx} {a a' : AState} {dst src : Loc}
    (hv : stepEdit c a (.move dst src) = .ok a')
    {ρ : Env} {regs : Xl.Regs} {fr : Xl.Frame} {mem : X86.Memory} {ctx : Word}
    (hagree : a.Agree ρ (Xl.read regs fr)) (hsize : regs.size = 16) (hin : fr.inArgs.size = c.stackParams) :
    ∃ regs' fr', Xl.execInst regs fr mem ctx (.move dst src) = some (regs', fr', mem) ∧ regs'.size = 16 ∧
      Xl.Frame.SameCtl fr fr' ∧ a'.Agree ρ (Xl.read regs' fr') := by
  simp only [stepEdit, bind, Except.bind] at hv
  cases hd : editLocCode c dst with
  | some code => simp [hd, throw, throwThe, MonadExceptOf.throw] at hv
  | none =>
  cases hs : editLocCode c src with
  | some code => simp [hd, hs, throw, throwThe, MonadExceptOf.throw] at hv
  | none =>
  cases hcell : (dst.isCell && src.isCell)
  · cases hk : (a.get src).isEmpty
    · simp only [hd, hs, hcell, hk, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at hv
      subst hv
      obtain ⟨v, hvm⟩ : ∃ v, v ∈ a.get src := by
        cases h : a.get src with
        | nil => rw [h] at hk; simp at hk
        | cons v vs => exact ⟨v, by simp⟩
      obtain ⟨w, -, hr⟩ := hagree src v hvm
      have hok : WriteOk fr dst := by
        cases dst with
        | reg r =>
          simp only [WriteOk]
          simp only [editLocCode, locCode, allocatable] at hd
          cases h : Xl.reserved r <;> simp_all
        | slot i => trivial
        | inArg i =>
          simp only [editLocCode, locCode] at hd
          simp only [WriteOk, hin]
          split at hd <;> simp_all
        | outArg i => trivial
      obtain ⟨regs', fr', hwr⟩ := Xl.write_ok (regs := regs) hok w
      obtain ⟨hread, hother, hctl, hsz⟩ := Xl.write_spec hsize hwr
      refine ⟨regs', fr', by simp [Xl.execInst, hr, hwr], hsz, hctl, ?_⟩
      exact hagree.stepMove (by rw [hread, hr]) hother
    · simp [hd, hs, hcell, hk, throw, throwThe, MonadExceptOf.throw] at hv
  · simp [hd, hs, hcell, throw, throwThe, MonadExceptOf.throw] at hv

/-! ## Conditional branches -/

theorem jcc_substitute {p : X86.Op} {pargs : List (XArg VReg)} {defs : List VReg} {cond : X86.Condition}
    {t f : Edge VReg} {ls : List Loc} {t' : Term Loc}
    (h : (Term.jcc p pargs defs cond t f).substitute ls [[], []] = some t') :
    ∃ pargs' defs', t' = .jcc p pargs' defs' cond ⟨t.target, []⟩ ⟨f.target, []⟩ ∧
      (Inst.op p defs pargs).substitute ls = some (.op p defs' pargs') := by
  simp only [Term.substitute, Term.edges, List.length_cons, List.length_nil, beq_self_eq_true,
    ↓reduceIte, pure, Option.bind_eq_bind, Option.bind_some, List.zip_cons_cons, List.zip_nil_right,
    List.map_cons, List.map_nil] at h
  simp only [Inst.substitute, Option.bind_eq_bind]
  cases hs : substituteArgs pargs ls with
  | none => simp [hs] at h
  | some r =>
    obtain ⟨pargs', rest⟩ := r
    by_cases hl : rest.length = defs.length
    · simp [hs, hl, guard] at h ⊢
      exact ⟨pargs', rest, h.symm, rfl, rfl⟩
    · simp [hs, hl, guard, failure] at h

theorem jcc_sound {c : Ctx} {a a' : AState} {p : X86.Op} {pargs : List (XArg VReg)} {defs : List VReg}
    {cond : X86.Condition} {t f : Edge VReg} {ls : List Loc} {defs' : List Loc} {pargs' : List (XArg Loc)}
    (hv : stepTerm c a (.jcc p pargs defs cond t f) ls = .ok a')
    (hsub : (Inst.op p defs pargs).substitute ls = some (.op p defs' pargs'))
    {ρ ρ' : Env} {regs : Xl.Regs} {fr : Xl.Frame} {mem mem' : X86.Memory} {ctx : Word} {taken : Bool}
    (hagree : a.Agree ρ (Xl.read regs fr)) (hsize : regs.size = 16) (hin : fr.inArgs.size = c.stackParams)
    (hxv : execJcc p pargs defs cond ρ mem ctx = some (ρ', mem', taken)) :
    ∃ bs', bindRow p defs' pargs' = some bs' ∧ ∃ regs' fr' flags,
      Xl.execBound [(p, bs')] regs fr mem ctx = some (regs', fr', mem', flags) ∧
      jccTaken cond flags = some taken ∧ regs'.size = 16 ∧ Xl.Frame.SameCtl fr fr' ∧
      a'.Agree ρ' (Xl.read regs' fr') := by
  simp only [stepTerm] at hv
  have hshapeRow : rowShapeOk p defs pargs false = true := by
    cases h : rowShapeOk p defs pargs false
    · simp [h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hv
    · rfl
  simp only [hshapeRow, ↓reduceIte] at hv
  simp only [execJcc, Option.bind_eq_bind, Option.bind_eq_some_iff] at hxv
  obtain ⟨bs, hbs, ⟨ρ₁, mem₁, fl⟩, hrun, tk, htk, he⟩ := hxv
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨bs', hbs', regs', fr', hxl, hs, hctl, hag⟩ :=
    single_sound (a' := a') hshapeRow hv hsub hbs hagree hsize hin hrun
  exact ⟨bs', hbs', regs', fr', fl, hxl, htk, hs, hctl, hag⟩

end Compilatrix.Xv.Validate

