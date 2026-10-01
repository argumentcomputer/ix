import Compilatrix.Xv.Stacking.Proof.RowXl
import Compilatrix.X86.Constructors

/-!
# Xl instructions and their stacked code

The instructions of a body besides a plain row (`op_sim`): a fused pair,
whose consumer's narrow destination the stacked code zeroes first
(`fused_sim`); a branch's producer and condition (`jccTaken_eq`); a move
(`move_sim`) and a zeroing (`zero_sim`). Each re-establishes `Agree` for
the running frame (`After`), from the machine core the instruction's code
leaves.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86
open Compilatrix.Xv.Xl (placeL xlLocs xlNamed xlCells xlFree xlTable)
open Compilatrix.Xv.Validate (Wide rowWrites implicitWrites)

/-- The frame after an instruction whose rows Xl ran to core `X` and read
back into `defs`, and the machine ran to `core'`: the machine's register
definitions hold Xl's values, its other registers are kept, each cell
definition holds Xl's word, and no other byte Xl cannot write changed. -/
theorem finish {c : FnCtx} {LB : List (Bound Loc)} {defs : List Loc} (hnd : defs.Nodup)
    (hdefsRes : ∀ r, Loc.reg r ∈ defs → Xl.reserved r = false)
    {regs : Xl.Regs} {fr : Xl.Frame} {mem : Memory} {ctx : Word} {core : Core} (ha : Agree c regs fr mem ctx core)
    {X core' : Core} {rf : Xl.Regs × Xl.Frame}
    (hrf : ((defs.map fun l => (l, placeL LB l)).map fun p => (p.1, some p.2)).foldlM (Xl.writeBack X) (regs, fr) =
      some rf)
    (hW : ∀ r, Loc.reg r ∈ defs → core'.readReg r = X.readReg r)
    (hK : ∀ r, Loc.reg r ∉ defs → core'.readReg r = core.readReg r)
    (hC : ∀ l ∈ defs, l.isCell = true → ∃ m, c.cell l = .ok m ∧
      core'.memory.read64 (m.eval core) = X.readReg (placeL LB l))
    (hB : ∀ x, mem.writable x = false →
      (∀ l ∈ defs, l.isCell = true → ∀ m, c.cell l = .ok m → ∀ i < 8, x ≠ m.eval core + UInt64.ofNat i) →
      core'.memory.bytes x = core.memory.bytes x)
    (hI : Inside X.memory core'.memory) (hp₁ : X.memory.readable = mem.readable)
    (hp₂ : X.memory.writable = mem.writable) (hp₃ : core'.memory.readable = core.memory.readable)
    (hp₄ : core'.memory.writable = core.memory.writable) :
    After c defs regs fr mem core rf.1 rf.2 X.memory ctx core' := by
  obtain ⟨hsize', hctl, hdefR, hother⟩ :=
    writeBacks_of ha.size (by simpa [List.map_map, Function.comp_def] using hnd) hrf
  have hrsp : core'.readReg .rsp = core.readReg .rsp := hK _ fun hm => by
    have := hdefsRes _ hm; simp [Xl.reserved] at this
  have h15' : core'.readReg .r15 = core.readReg .r15 := hK _ fun hm => by
    have := hdefsRes _ hm; simp [Xl.reserved] at this
  have hother' : ∀ l, l ∉ defs → Xl.read rf.1 rf.2 l = Xl.read regs fr l := fun l hl =>
    hother l (by simpa [List.map_map] using hl)
  have hdefR' : ∀ l ∈ defs, Xl.read rf.1 rf.2 l = some (X.readReg (placeL LB l)) :=
    fun l hl => hdefR (l, placeL LB l) (List.mem_map_of_mem hl)
  refine ⟨⟨hsize', fun r hr v hv => ?_, by rw [h15', ha.ctxReg], hI, fun l hl v hv => ?_,
    ha.frame.keep hrsp hp₁ hp₂ hp₃ hp₄⟩, hctl, hrsp, hp₁, hp₂, hp₃, hp₄, hK, hB, hother'⟩
  · by_cases hd : Loc.reg r ∈ defs
    · have := hdefR' _ hd
      rw [Xl.read_reg hr, Xl.placeL_reg] at this
      rw [this] at hv
      cases hv
      exact hW r hd
    · have := hother' _ hd
      rw [Xl.read_reg hr, Xl.read_reg hr, hv] at this
      rw [hK r hd]
      exact ha.regsRel r hr v this.symm
  · by_cases hd : l ∈ defs
    · rw [hdefR' l hd] at hv
      cases hv
      obtain ⟨m, hm, hm'⟩ := hC l hd hl
      exact ⟨m, hm, by rw [cell_rsp hm hrsp]; exact hm'⟩
    · rw [hother' l hd] at hv
      obtain ⟨m, hm, hm'⟩ := ha.cells l hl v hv
      refine ⟨m, hm, ?_⟩
      rw [cell_rsp hm hrsp, ← hm']
      refine read64_congr fun i hi => hB _ ((ha.frame.cell l m hm).noWrite i hi) fun l' hl' _ m' hm'' j hj => ?_
      exact (ha.frame.disjoint l' l m' m hm'' hm (fun e => hd (e ▸ hl')) j hj i hi).symm

/-! ## Footprints from registers -/

theorem eval_congr {c c' : Core} (h : ∀ r, c.readReg r = c'.readReg r) (m : MemAddr) : m.eval c = m.eval c' := by
  simp only [MemAddr.eval, h]

theorem slotReads_congr {c c' : Core} (h : ∀ r, c.readReg r = c'.readReg r) :
    ∀ (ss : List Slot) (as : List Arg), slotReads c ss as = slotReads c' ss as
  | [], _ => by simp [slotReads]
  | _ :: _, [] => rfl
  | s :: ss, a :: as => by
      simp only [slotReads, slotReads_congr h ss as]
      cases a <;> simp [Arg.access, eval_congr h]

theorem slotWrites_congr {c c' : Core} (h : ∀ r, c.readReg r = c'.readReg r) :
    ∀ (ss : List Slot) (as : List Arg), slotWrites c ss as = slotWrites c' ss as
  | [], _ => by simp [slotWrites]
  | _ :: _, [] => rfl
  | s :: ss, a :: as => by
      simp only [slotWrites, slotWrites_congr h ss as]
      cases a <;> simp [Arg.access, eval_congr h]

/-- A row's footprint is read off the registers. -/
theorem Foot.congr {c : FnCtx} {o : Op} {xs : List Arg} {mem : Memory} {core core' : Core} {U D : List Loc}
    (hf : Foot c o xs mem core U D) (h : ∀ r, core'.readReg r = core.readReg r) : Foot c o xs mem core' U D := by
  have hr : Op.reads o xs core' = Op.reads o xs core := by
    simp only [Op.reads, Op.pops, slotReads_congr h, h]
  have hw : Op.writes o xs core' = Op.writes o xs core := by
    simp only [Op.writes, Op.pushes, slotWrites_congr h, h]
  refine ⟨fun acc hacc => ?_, fun acc hacc => ?_, fun l hl hc m hm => ?_⟩
  · rw [hr] at hacc
    rcases hf.reads acc hacc with h' | ⟨hb, l, hlU, hl, m, hm, ha⟩
    · exact .inl h'
    · exact .inr ⟨hb, l, hlU, hl, m, hm, by rw [ha]; exact (eval_congr h m).symm⟩
  · rw [hw] at hacc
    rcases hf.writes acc hacc with h' | ⟨hb, l, hl, m, hm, ha⟩
    · exact .inl h'
    · exact .inr ⟨hb, l, hl, m, hm, by rw [ha]; exact (eval_congr h m).symm⟩
  · rw [hw, eval_congr h m]; exact hf.defs l hl hc m hm

/-- A location's agreement survives cores that keep what it reads: its
register, or its cell's bytes, `rsp` and the register Xl lends it. -/
theorem LocAgree.keep {c : FnCtx} {LB : List (Bound Loc)} {c₁ c₂ c₁' c₂' : Core} {u : Loc}
    (h : LocAgree c LB c₁ c₂ u)
    (hr : ∀ r, u = .reg r → c₁'.readReg r = c₁.readReg r ∧ c₂'.readReg r = c₂.readReg r)
    (hl : u.isCell = true → c₁'.readReg (placeL LB u) = c₁.readReg (placeL LB u))
    (hsp : c₂'.readReg .rsp = c₂.readReg .rsp)
    (hp₁ : c₁'.memory.readable = c₁.memory.readable) (hp₂ : c₁'.memory.writable = c₁.memory.writable)
    (hp₃ : c₂'.memory.readable = c₂.memory.readable) (hp₄ : c₂'.memory.writable = c₂.memory.writable)
    (hb : ∀ m, c.cell u = .ok m → ∀ i < 8,
      c₂'.memory.bytes (m.eval c₂ + UInt64.ofNat i) = c₂.memory.bytes (m.eval c₂ + UInt64.ofNat i)) :
    LocAgree c LB c₁' c₂' u := by
  cases u with
  | reg r =>
    change c₁'.readReg r = c₂'.readReg r
    obtain ⟨h₁, h₂⟩ := hr r rfl
    rw [h₁, h₂]; exact h
  | _ =>
    obtain ⟨m, hm, hc, hv⟩ := h
    have he : m.eval c₂' = m.eval c₂ := cell_rsp hm hsp
    refine ⟨m, hm, by rw [he]; exact hc.perm hp₁ hp₂ hp₃ hp₄, ?_⟩
    rw [he, hl rfl, read64_congr (hb m hm), hv]

/-! ## A fused pair -/

/-- A fused pair: when Xl runs `fused p pargs q defs cargs`, the stacked
code, having zeroed the consumer's narrow destinations `zs` (`core_z`),
runs its `.fused`, and the frame agrees again. -/
theorem fused_sim {c : FnCtx} {p q : Op} {pargs cargs : List (XArg Loc)} {defs : List Loc}
    {pb qb : List (Bound Loc)} (hpb : bindRow p [] pargs = some pb) (hqb : bindRow q defs cargs = some qb)
    {pxs qxs : List Arg} (hpx : c.rowArgs pb = .ok pxs) (hqx : c.rowArgs qb = .ok qxs)
    (hps : rowShape p pb pxs false = true) (hqs : rowShape q qb qxs true = true)
    {zs : List GPR} (hzs : (qb.filter Bound.narrowOutput).flatMap Bound.defs = zs.map Loc.reg)
    {regs : Xl.Regs} {fr : Xl.Frame} {mem : Memory} {ctx : Word} {core : Core} (ha : Agree c regs fr mem ctx core)
    {core_z : Core} (hz₁ : ∀ r ∈ zs, core_z.readReg r = 0) (hz₂ : ∀ r, r ∉ zs → core_z.readReg r = core.readReg r)
    (hz₃ : core_z.memory = core.memory)
    {regs' : Xl.Regs} {fr' : Xl.Frame} {mem' : Memory} {flags : ByteEval.Flags}
    (h : Xl.execBound [(p, pb), (q, qb)] regs fr mem ctx true = some (regs', fr', mem', flags)) :
    ∃ core₁ fl₁ core', p.exec pxs core_z {} = .ok (core₁, fl₁) ∧ q.exec qxs core₁ fl₁ = .ok (core', flags) ∧
      After c (qb.flatMap Bound.defs) regs fr mem core regs' fr' mem' ctx core' ∧
      Foot c p pxs mem core_z (pb.flatMap Bound.uses) [] ∧
      Foot c q qxs mem core_z (qb.flatMap Bound.uses) (qb.flatMap Bound.defs) ∧ (desc p).stack = .none ∧ (desc q).stack = .none := by
  rw [Xl.execBound_eq] at h
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Option.bind_eq_some_iff] at h
  obtain ⟨_, hg₁, _, hg₂, _, hg₃, vs, hread, _, hg₅, margs, hmargs, cf, hrows, rf, hrf, hfin⟩ := h
  have hplace : (pb ++ qb).all Xl.Bound.placeable = true := optGuard_some hg₁
  have hnamed := optGuard_some hg₂
  have hcells : (xlCells (pb ++ qb)).length ≤ (xlFree (pb ++ qb)).length := optGuard_some hg₃
  have hzero : Xl.zeroedRegs [(p, pb), (q, qb)] true = zs := by
    simp only [Xl.zeroedRegs, ↓reduceIte, List.getLast?_cons_cons, List.getLast?_singleton, Option.map_some,
      Option.getD_some, hzs, List.filterMap_map]
    simp [Function.comp_def, Xl.Loc.reg?]
  rw [hzero] at hg₅ hrows
  have hzu : ∀ r ∈ zs, Loc.reg r ∉ (pb ++ qb).flatMap Bound.uses := fun r hr hu => by
    have := List.all_eq_true.1 (optGuard_some hg₅) r hr
    simp only [Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at this
    exact this _ hu rfl
  have hall := List.all_eq_true.1 hplace
  have hpdefs : pb.flatMap Bound.defs = [] := (bindRow_regs hpb).2
  have hzdefs : ∀ r ∈ zs, Loc.reg r ∈ qb.flatMap Bound.defs := fun r hr => by
    have : Loc.reg r ∈ (qb.filter Bound.narrowOutput).flatMap Bound.defs := by rw [hzs]; exact List.mem_map_of_mem hr
    obtain ⟨b, hb, hd⟩ := List.mem_flatMap.1 this
    exact List.mem_flatMap.2 ⟨b, (List.mem_filter.1 hb).1, hd⟩
  have hlocU : ∀ u ∈ (pb ++ qb).flatMap Bound.uses, u ∈ xlLocs (pb ++ qb) := fun u hu => by
    obtain ⟨b, hb, hu⟩ := List.mem_flatMap.1 hu
    exact List.mem_flatMap.2 ⟨b, hb, Xl.Bound.mem_locs.2 (List.mem_append_left _ hu)⟩
  have hlocD : ∀ l ∈ (pb ++ qb).flatMap Bound.defs, l ∈ xlLocs (pb ++ qb) := fun l hl => by
    obtain ⟨b, hb, hl⟩ := List.mem_flatMap.1 hl
    exact List.mem_flatMap.2 ⟨b, hb, Xl.Bound.mem_locs.2 (List.mem_append_right _ hl)⟩
  have hdefsQ : (pb ++ qb).flatMap Bound.defs = qb.flatMap Bound.defs := by
    rw [List.flatMap_append, hpdefs, List.nil_append]
  have hresN : ∀ r, r ∈ xlNamed (pb ++ qb) → Xl.reserved r = false := fun r hr => by
    simpa using List.all_eq_true.1 hnamed r hr
  have hzNamed : ∀ r ∈ zs, r ∈ xlNamed (pb ++ qb) := fun r hr =>
    Xl.mem_xlNamed.2 (hlocD _ (by rw [hdefsQ]; exact hzdefs r hr))
  have hzRes : ∀ r ∈ zs, Xl.reserved r = false := fun r hr => hresN r (hzNamed r hr)
  have hz15 : GPR.r15 ∉ zs := fun h => by have := hzRes _ h; simp [Xl.reserved] at this
  have hzsp : GPR.rsp ∉ zs := fun h => by have := hzRes _ h; simp [Xl.reserved] at this
  have hdefsRes : ∀ r, Loc.reg r ∈ qb.flatMap Bound.defs → Xl.reserved r = false := fun r hr =>
    hresN r (Xl.mem_xlNamed.2 (hlocD _ (by rw [hdefsQ]; exact hr)))
  have huseRes : ∀ u ∈ (pb ++ qb).flatMap Bound.uses, ∀ r, u = .reg r → Xl.reserved r = false :=
    fun u hu r e => hresN r (Xl.mem_xlNamed.2 (e ▸ hlocU u hu))
  simp only [List.mapM_cons, List.mapM_nil, partArgs_eq, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.map_eq_map, Option.map_eq_some_iff, Option.pure_def, Option.bind_some, Option.some.injEq] at hmargs
  obtain ⟨_, ⟨pxs₁, hpx₁, rfl⟩, _, ⟨_, ⟨qxs₁, hqx₁, rfl⟩, rfl⟩, rfl⟩ := hmargs
  simp only [execRows, List.foldlM_cons, List.foldlM_nil, execRow, Option.bind_eq_bind] at hrows
  split at hrows
  · rename_i res₁ hexp
    simp only [Option.bind_some] at hrows
    split at hrows
    · rename_i res₂ hexq
      simp only [pure, Option.some.injEq, Option.bind_some] at hrows
      subst hrows
      simp only [Option.some.injEq, Prod.mk.injEq] at hfin
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hfin
      unfold FnCtx.rowArgs at hpx hqx
      have hpp : pb.all Xl.Bound.placeable = true :=
        List.all_eq_true.2 fun b hb => hall b (List.mem_append_left _ hb)
      have hqp : qb.all Xl.Bound.placeable = true :=
        List.all_eq_true.2 fun b hb => hall b (List.mem_append_right _ hb)
      simp only [hpp, hqp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at hpx hqx
      have hps' := hps
      simp only [rowShape, Bool.and_eq_true, Bool.or_eq_true, Bool.false_eq_true, false_or,
        Bool.not_eq_true', List.any_eq_false] at hps'
      -- The row core Xl builds, against the machine's after the zeroing
      have hagree₀ : ∀ u ∈ (pb ++ qb).flatMap Bound.uses,
          LocAgree c (pb ++ qb) ⟨Xl.rowRegisters regs fr ctx (xlTable (pb ++ qb)) zs, mem⟩ core_z u := by
        intro u hu
        obtain ⟨v, hv⟩ := readAll_some hread u hu
        have hzu' : ∀ r, u = .reg r → r ∉ zs := fun r e hr => hzu r hr (e ▸ hu)
        refine (uses_agree hcells ha hzNamed hnamed (hlocU u hu) hzu' hv).keep
          (fun r e => ⟨rfl, hz₂ r (hzu' r e)⟩) (fun _ => rfl) (hz₂ _ hzsp) rfl rfl (by rw [hz₃]) (by rw [hz₃])
          (fun m _ i _ => by rw [hz₃])
      have h15₀ : (⟨Xl.rowRegisters regs fr ctx (xlTable (pb ++ qb)) zs, mem⟩ : Core).readReg .r15 =
          core_z.readReg .r15 := by
        rw [hz₂ _ hz15, ha.ctxReg]; exact Xl.rowRegisters_r15 regs fr ctx (xlTable (pb ++ qb)) zs
      obtain ⟨core₁, hp₂, outP, hWP, hW₁P, hCWP, -, hCAP, -, hstackP⟩ :=
        part_rel (c := c) hcells hpb (fun b hb => List.mem_append_left _ hb)
          (fun b hb => hall b (List.mem_append_left _ hb)) hpx₁ hpx hps
          (fun u hu => hagree₀ u (by rw [List.flatMap_append]; exact List.mem_append_left _ hu))
          (fun u hu => huseRes u (by rw [List.flatMap_append]; exact List.mem_append_left _ hu))
          (fun d hd => by rw [hpdefs] at hd; cases hd)
          (fun b hb hn => absurd hn (by simp [hps'.2 b hb])) h15₀
          (by rw [hz₃]; exact ha.inside) hexp
      have hk₂ : ∀ r, core₁.readReg r = core_z.readReg r := fun r =>
        outP.frame₂ r fun hm => by have := (hWP r).1 hm; rw [hpdefs] at this; cases this
      have hk₁ : ∀ r, res₁.1.readReg r = Xl.rowRegisters regs fr ctx (xlTable (pb ++ qb)) zs r := fun r =>
        outP.frame₁ r fun hm => by obtain ⟨l, hl, -⟩ := (hW₁P r).1 hm; rw [hpdefs] at hl; cases hl
      have hbP : ∀ x, mem.writable x = false → core₁.memory.bytes x = core_z.memory.bytes x := fun x hx =>
        outP.bytes x hx fun a r hcw => by
          obtain ⟨l, hl, -⟩ := hCWP a r hcw; rw [hpdefs] at hl; cases hl
      have hsp₁ : core₁.readReg .rsp = core.readReg .rsp := by rw [hk₂, hz₂ _ hzsp]
      -- The second part
      have hagree₁ : ∀ u ∈ qb.flatMap Bound.uses, LocAgree c (pb ++ qb) res₁.1 core₁ u := fun u hu =>
        (hagree₀ u (by rw [List.flatMap_append]; exact List.mem_append_right _ hu)).keep
          (fun r _ => ⟨hk₁ r, hk₂ r⟩) (fun _ => hk₁ _) (hk₂ _) outP.readable₁ outP.writable₁ outP.readable₂
          outP.writable₂ (fun m hm i hi => hbP _ (by
            have := (ha.frame.cell u m hm).noWrite i hi
            rw [cell_rsp hm (hz₂ _ hzsp)]; exact this))
      have hnarrowQ : ∀ b ∈ qb, b.narrowOutput = true → ∀ d ∈ b.defs, ∀ r, d = .reg r →
          res₁.1.readReg r = core₁.readReg r := by
        intro b hb hn d hd r e
        subst e
        have hr : r ∈ zs := by
          have : Loc.reg r ∈ (qb.filter Bound.narrowOutput).flatMap Bound.defs :=
            List.mem_flatMap.2 ⟨b, List.mem_filter.2 ⟨hb, hn⟩, hd⟩
          rw [hzs] at this
          obtain ⟨r', hr', e⟩ := List.mem_map.1 this
          cases e; exact hr'
        rw [hk₁, hk₂, hz₁ r hr]
        exact Xl.rowRegisters_zeroed (fun e => hz15 (e ▸ hr)) hr
      have h15₁ : res₁.1.readReg .r15 = core₁.readReg .r15 := by rw [hk₁, hk₂]; exact h15₀
      obtain ⟨core', hq₂, outQ, hWQ, -, hCWQ, hCWofQ, hCAQ, hWDQ, hstackQ⟩ :=
        part_rel (c := c) hcells hqb (fun b hb => List.mem_append_right _ hb)
          (fun b hb => hall b (List.mem_append_right _ hb)) hqx₁ hqx hqs hagree₁
          (fun u hu => huseRes u (by rw [List.flatMap_append]; exact List.mem_append_right _ hu))
          (fun d _ _ m hm => by
            have := ha.frame.cell d m hm
            rw [cell_rsp hm hsp₁]
            exact this.perm outP.readable₁ outP.writable₁ (outP.readable₂.trans (by rw [hz₃]))
              (outP.writable₂.trans (by rw [hz₃])))
          hnarrowQ h15₁ outP.inside hexq
      have hsp' : core'.readReg .rsp = core.readReg .rsp := by
        rw [outQ.frame₂ _ fun hm => by
          have := hdefsRes _ ((hWQ _).1 hm); simp [Xl.reserved] at this]
        exact hsp₁
      rw [readback_loc hcells (fun b hb => hb) hall, hdefsQ] at hrf
      have hrf' : (((qb.flatMap Bound.defs).map fun l => (l, placeL (pb ++ qb) l)).map
          fun p => (p.1, some p.2)).foldlM (Xl.writeBack res₂.1) (regs, fr) = some rf := by
        rw [List.map_map]; exact hrf
      have hnd : (qb.flatMap Bound.defs).Nodup := by
        simp only [rowShape, Bool.and_eq_true] at hqs
        exact distinctLocs_nodup hqs.1.2
      refine ⟨core₁, res₁.2, core', hp₂, hq₂, ?_, ⟨?_, ?_, fun l hl => by cases hl⟩, ?_, hstackP, hstackQ⟩
      · refine finish hnd hdefsRes ha hrf' (fun r hr => outQ.written r ((hWQ r).2 hr)) (fun r hr => ?_)
          (fun l hl hc => ?_) (fun x hx hout => ?_) outQ.inside
          (outQ.readable₁.trans outP.readable₁) (outQ.writable₁.trans outP.writable₁)
          (outQ.readable₂.trans (outP.readable₂.trans (by rw [hz₃])))
          (outQ.writable₂.trans (outP.writable₂.trans (by rw [hz₃])))
        · have hz : r ∉ zs := fun hz => hr (hzdefs r hz)
          rw [outQ.frame₂ r fun hm => hr ((hWQ r).1 hm), hk₂, hz₂ r hz]
        · obtain ⟨m, hm, hcw⟩ := hCWofQ l hl hc
          exact ⟨m, hm, by rw [← cell_rsp hm hsp₁]; exact outQ.cell _ _ hcw⟩
        · rw [outQ.bytes x (by rw [outP.writable₁]; exact hx) fun a r hcw i hi => by
            obtain ⟨l, hl, hc, m, hm, rfl, -⟩ := hCWQ a r hcw
            rw [cell_rsp hm hsp₁]
            exact hout l hl hc m hm i hi, hbP x hx, hz₃]
      · intro acc hacc
        rcases outP.reads acc hacc with h | ⟨hb, r, hca⟩
        · exact .inl h
        · exact .inr ⟨hb, hCAP _ r hca⟩
      · intro acc hacc
        rcases outP.writes acc hacc with h | ⟨hb, r, hcw⟩
        · exact .inl h
        · obtain ⟨l, hl, -⟩ := hCWP _ r hcw; rw [hpdefs] at hl; cases hl
      · refine Foot.congr (core := core₁) ⟨fun acc hacc => ?_, fun acc hacc => ?_, hWDQ⟩ fun r => (hk₂ r).symm
        · rcases outQ.reads acc hacc with h | ⟨hb, r, hca⟩
          · exact .inl fun i hi => by rw [← outP.readable₁]; exact h i hi
          · exact .inr ⟨hb, hCAQ _ r hca⟩
        · rcases outQ.writes acc hacc with h | ⟨hb, r, hcw⟩
          · exact .inl fun i hi => by rw [← outP.writable₁]; exact h i hi
          · obtain ⟨l, -, hl, m, hm, ha, -⟩ := hCWQ _ r hcw
            exact .inr ⟨hb, l, hl, m, hm, ha⟩
    · simp at hrows
  · simp at hrows

/-! ## A branch's condition -/

/-- Xl's branch test is the machine's. -/
theorem jccTaken_eq (cond : Condition) (flags : ByteEval.Flags) : jccTaken cond flags = flags.test cond := by
  obtain ⟨cf, zf, sf, of⟩ := flags
  cases cond <;> simp only [jccTaken, desc, Op.jccRel32, Table.jccDesc, Table.jccSem, ByteEval.Flags.restrict,
    ByteEval.Flags.test, Condition.reads] <;>
    (cases cf <;> cases zf <;> cases sf <;> cases of <;> rfl)

/-! ## Single-register and single-cell definitions -/

/-- The frame after Xl writes `v` to register `d`, which the machine sets. -/
theorem after_reg {c : FnCtx} {regs : Xl.Regs} {fr : Xl.Frame} {mem : Memory} {ctx : Word} {core : Core}
    (ha : Agree c regs fr mem ctx core) {d : GPR} {v : Word} {regs' : Xl.Regs} {fr' : Xl.Frame}
    (hw : Xl.write regs fr (.reg d) v = some (regs', fr')) :
    After c [.reg d] regs fr mem core regs' fr' mem ctx (core.setReg d v) := by
  obtain ⟨hread, hother, hctl, hsize⟩ := Xl.write_spec ha.size hw
  have hd : Xl.reserved d = false := by
    cases h : Xl.reserved d
    · rfl
    · simp [Xl.write, h] at hw
  have hne : ∀ r, Xl.reserved r = true → r ≠ d := fun r hr e => by subst e; rw [hd] at hr; cases hr
  have hkeep : ∀ r, r ≠ d → (core.setReg d v).readReg r = core.readReg r := fun r hr => by
    simp [Validate.readReg_setReg, hr]
  have hrsp := hkeep _ (hne .rsp rfl)
  have hp₃ : (core.setReg d v).memory = core.memory := rfl
  refine ⟨⟨hsize, fun r hr v' hv' => ?_, by rw [hkeep _ (hne .r15 rfl), ha.ctxReg], ha.inside,
    fun l hl v' hv' => ?_, ha.frame.keep hrsp rfl rfl rfl rfl⟩, hctl, hrsp, rfl, rfl, rfl, rfl,
    fun r hr => hkeep r (fun e => hr (by simp [e])), fun x _ _ => rfl, fun y hy => hother y (by simpa using hy)⟩
  · by_cases e : r = d
    · subst e
      rw [Xl.read_reg hr] at hread
      rw [hread] at hv'
      cases hv'
      simp [Validate.readReg_setReg]
    · have := hother (.reg r) (fun h => e (by cases h; rfl))
      rw [Xl.read_reg hr, Xl.read_reg hr, hv'] at this
      rw [hkeep r e]
      exact ha.regsRel r hr v' this.symm
  · have := hother l (fun h => by subst h; simp [Loc.isCell] at hl)
    rw [this] at hv'
    obtain ⟨m, hm, hm'⟩ := ha.cells l hl v' hv'
    exact ⟨m, hm, by rw [cell_rsp hm hrsp]; exact hm'⟩

/-- The frame after Xl writes `v` to cell `l`, which the machine stores. -/
theorem after_cell {c : FnCtx} {regs : Xl.Regs} {fr : Xl.Frame} {mem : Memory} {ctx : Word} {core : Core}
    (ha : Agree c regs fr mem ctx core) {l : Loc} (hl : l.isCell = true) {m : MemAddr} (hm : c.cell l = .ok m)
    {v : Word} {regs' : Xl.Regs} {fr' : Xl.Frame} (hw : Xl.write regs fr l v = some (regs', fr')) :
    After c [l] regs fr mem core regs' fr' mem ctx { core with memory := core.memory.write .w64 (m.eval core) v } := by
  obtain ⟨hread, hother, hctl, hsize⟩ := Xl.write_spec ha.size hw
  have hc := ha.frame.cell l m hm
  have hrsp : ({ core with memory := core.memory.write .w64 (m.eval core) v } : Core).readReg .rsp =
      core.readReg .rsp := rfl
  refine ⟨⟨hsize, fun r hr v' hv' => ?_, ha.ctxReg, ha.inside.write_cell hc v,
    fun l' hl' v' hv' => ?_, ha.frame.keep hrsp rfl rfl (by simp) (by simp)⟩, hctl, hrsp, rfl, rfl,
    by simp, by simp, fun r _ => rfl, fun x hx hout => ?_, fun y hy => hother y (by simpa using hy)⟩
  · have := hother (.reg r) (fun h => by subst h; simp [Loc.isCell] at hl)
    rw [Xl.read_reg hr, Xl.read_reg hr, hv'] at this
    exact ha.regsRel r hr v' this.symm
  · by_cases e : l' = l
    · subst e
      rw [hread] at hv'
      cases hv'
      refine ⟨m, hm, ?_⟩
      rw [cell_rsp hm hrsp]
      exact Memory.read64_write64 _ _ _
    · rw [hother l' e] at hv'
      obtain ⟨m', hm', hv''⟩ := ha.cells l' hl' v' hv'
      refine ⟨m', hm', ?_⟩
      rw [cell_rsp hm' hrsp, ← hv'']
      refine read64_congr fun i hi => Memory.writeLittle_bytes_outside _ _ _ _ _ fun j hj => ?_
      exact ha.frame.disjoint l' l m' m hm' hm e i hi j hj
  · exact Memory.writeLittle_bytes_outside _ _ _ _ _ fun i hi => hout l (by simp) hl m hm i hi

/-- The frame after Xl writes a location's own value back to it. -/
theorem after_same {c : FnCtx} {regs : Xl.Regs} {fr : Xl.Frame} {mem : Memory} {ctx : Word} {core : Core}
    (ha : Agree c regs fr mem ctx core) {l : Loc} {v : Word} (hv : Xl.read regs fr l = some v)
    {regs' : Xl.Regs} {fr' : Xl.Frame} (hw : Xl.write regs fr l v = some (regs', fr')) :
    After c [l] regs fr mem core regs' fr' mem ctx core := by
  obtain ⟨hread, hother, hctl, hsize⟩ := Xl.write_spec ha.size hw
  have hsame : ∀ l', Xl.read regs' fr' l' = Xl.read regs fr l' := fun l' => by
    by_cases e : l' = l
    · subst e; rw [hread, hv]
    · exact hother l' e
  refine ⟨⟨hsize, fun r hr v' hv' => ?_, ha.ctxReg, ha.inside, fun l' hl' v' hv' => ?_, ha.frame⟩, hctl, rfl,
    rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun y _ => hsame y⟩
  · rw [← Xl.read_reg hr, hsame, Xl.read_reg hr] at hv'
    exact ha.regsRel r hr v' hv'
  · rw [hsame] at hv'
    exact ha.cells l' hl' v' hv'

/-! ## Moves and zeroing -/

theorem movRR_exec (d s : GPR) (core : Core) :
    ∃ fl, Op.exec { mn := .mov, w := .w64, form := .MR } [.reg d, .reg s] core {} =
      .ok (core.setReg d (core.readReg s), fl) := by
  simp [Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.movDesc, Table.rmSlot, Table.regSlot,
    Table.moveSem, readSlots, writeSlots, Arg.load, Arg.store, Except.mapError, Core.writeReg, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

theorem load64_exec (d : GPR) (m : MemAddr) (core : Core) {v : Word}
    (h : core.memory.read? .w64 (m.eval core) = .ok v) :
    ∃ fl, Op.exec { mn := .mov, w := .w64, form := .RM } [.reg d, .mem m.normalize] core {} =
      .ok (core.setReg d v, fl) := by
  simp [Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.movDesc, Table.rmSlot, Table.regSlot,
    Table.moveSem, readSlots, writeSlots, Arg.load, Arg.store, Except.mapError, Core.writeReg, h, bind, Except.bind,
    pure, Except.pure, MemAddr.normalize_eval]

theorem store64_exec (m : MemAddr) (s : GPR) (core : Core) {mem' : Memory}
    (h : core.memory.write? .w64 (m.eval core) (core.readReg s) = .ok mem') :
    ∃ fl, Op.exec { mn := .mov, w := .w64, form := .MR } [.mem m.normalize, .reg s] core {} =
      .ok ({ core with memory := mem' }, fl) := by
  simp [Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.movDesc, Table.rmSlot, Table.regSlot,
    Table.moveSem, readSlots, writeSlots, Arg.load, Arg.store, Except.mapError, h, bind, Except.bind, pure,
    Except.pure, MemAddr.normalize_eval]

theorem zero_exec (r : GPR) (core : Core) (flags : ByteEval.Flags) :
    ∃ fl, zeroRow.exec [.reg r, .reg r] core flags = .ok (core.setReg r 0, fl) := by
  simp [zeroRow, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.arithDesc, Table.xorArith,
    Table.Arith.sem, Table.Arith.role, Table.aluSem, Table.rmSlot, Table.regSlot, readSlots, writeSlots, Arg.load,
    Arg.store, Except.mapError, Core.writeReg, AluOp.eval, Width.truncate, bind, Except.bind, pure, Except.pure,
    UInt64.xor_self, UInt64.zero_and]

/-- The footprints of the stacked moves. -/
theorem movRR_foot (d s : GPR) (core : Core) :
    Op.reads { mn := .mov, w := .w64, form := .MR } [.reg d, .reg s] core = [] ∧
      Op.writes { mn := .mov, w := .w64, form := .MR } [.reg d, .reg s] core = [] := by
  simp [Op.reads, Op.writes, Op.pops, Op.pushes, desc, Table.movDesc, Table.rmSlot, Table.regSlot, slotReads,
    slotWrites, Arg.access]

theorem load64_foot (d : GPR) (m : MemAddr) (core : Core) :
    Op.reads { mn := .mov, w := .w64, form := .RM } [.reg d, .mem m.normalize] core = [⟨m.eval core, 8⟩] ∧
      Op.writes { mn := .mov, w := .w64, form := .RM } [.reg d, .mem m.normalize] core = [] := by
  simp [Op.reads, Op.writes, Op.pops, Op.pushes, desc, Table.movDesc, Table.rmSlot, Table.regSlot, slotReads,
    slotWrites, Arg.access, MemAddr.normalize_eval, Width.bytes]

theorem store64_foot (m : MemAddr) (s : GPR) (core : Core) :
    Op.reads { mn := .mov, w := .w64, form := .MR } [.mem m.normalize, .reg s] core = [] ∧
      Op.writes { mn := .mov, w := .w64, form := .MR } [.mem m.normalize, .reg s] core = [⟨m.eval core, 8⟩] := by
  simp [Op.reads, Op.writes, Op.pops, Op.pushes, desc, Table.movDesc, Table.rmSlot, Table.regSlot, slotReads,
    slotWrites, Arg.access, MemAddr.normalize_eval, Width.bytes]

theorem zero_foot (r : GPR) (core : Core) :
    Op.reads zeroRow [.reg r, .reg r] core = [] ∧ Op.writes zeroRow [.reg r, .reg r] core = [] := by
  simp [zeroRow, Op.reads, Op.writes, Op.pops, Op.pushes, desc, Table.arithDesc, Table.xorArith, Table.Arith.role,
    Table.rmSlot, Table.regSlot, slotReads, slotWrites, Arg.access]

theorem gpr_ok {r : GPR} {r' : GPR} (h : gpr (.reg r) = .ok r') : Xl.reserved r = false ∧ r' = r := by
  simp only [gpr] at h
  cases hr : Xl.reserved r <;> simp [hr, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h
  exact ⟨rfl, h.symm⟩

/-- What `FnCtx.move` emits for two different locations. -/
theorem move_cases {c : FnCtx} {dst src : Loc} {ins : List Instr} (h : c.move dst src = .ok ins) :
    (dst = src ∧ ins = []) ∨
    (∃ d s, dst = .reg d ∧ src = .reg s ∧ Xl.reserved d = false ∧ Xl.reserved s = false ∧
      ins = [.op { mn := .mov, w := .w64, form := .MR } [.reg d, .reg s]]) ∨
    (∃ d m, dst = .reg d ∧ src.isCell = true ∧ c.cell src = .ok m ∧ Xl.reserved d = false ∧
      ins = [.op { mn := .mov, w := .w64, form := .RM } [.reg d, .mem m.normalize]]) ∨
    (∃ s m, dst.isCell = true ∧ src = .reg s ∧ c.cell dst = .ok m ∧ Xl.reserved s = false ∧
      ins = [.op { mn := .mov, w := .w64, form := .MR } [.mem m.normalize, .reg s]]) := by
  unfold FnCtx.move at h
  by_cases he : dst = src
  · subst he
    simp only [beq_self_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    exact .inl ⟨rfl, h.symm⟩
  · have hb : (dst == src) = false := by simpa using he
    rw [hb] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    right
    cases dst with
    | reg d =>
      cases src with
      | reg s =>
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        rename_i d' hd
        split at h
        · simp at h
        rename_i s' hs
        obtain ⟨hdr, rfl⟩ := gpr_ok hd
        obtain ⟨hsr, rfl⟩ := gpr_ok hs
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact .inl ⟨_, _, rfl, rfl, hdr, hsr, by rw [← h]; rfl⟩
      | _ =>
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        rename_i d' hd
        split at h
        · simp at h
        rename_i m hm
        obtain ⟨hdr, rfl⟩ := gpr_ok hd
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact .inr (.inl ⟨_, m, rfl, rfl, hm, hdr, by rw [← h]; rfl⟩)
    | _ =>
      cases src with
      | reg s =>
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        rename_i m hm
        split at h
        · simp at h
        rename_i s' hs
        obtain ⟨hsr, rfl⟩ := gpr_ok hs
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact .inr (.inr ⟨_, m, rfl, rfl, hm, hsr, by rw [← h]; rfl⟩)
      | _ => simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A move: Xl copies `src` to `dst`; the stacked code is nothing (the
same location) or one row, after which the frame agrees again. -/
theorem move_sim {c : FnCtx} {dst src : Loc} {ins : List Instr} (hm : c.move dst src = .ok ins)
    {regs : Xl.Regs} {fr : Xl.Frame} {mem : Memory} {ctx : Word} {core : Core} (ha : Agree c regs fr mem ctx core)
    {v : Word} (hv : Xl.read regs fr src = some v) {regs' : Xl.Regs} {fr' : Xl.Frame}
    (hw : Xl.write regs fr dst v = some (regs', fr')) :
    (ins = [] ∧ After c [dst] regs fr mem core regs' fr' mem ctx core) ∨
    (∃ o xs core' fl, ins = [.op o xs] ∧ o.exec xs core {} = .ok (core', fl) ∧ (desc o).stack = .none ∧
      Foot c o xs mem core [src] [dst] ∧ After c [dst] regs fr mem core regs' fr' mem ctx core') := by
  rcases move_cases hm with ⟨rfl, rfl⟩ | ⟨d, s, rfl, rfl, hd, hs, rfl⟩ | ⟨d, m, rfl, hsc, hcm, hd, rfl⟩ |
      ⟨s, m, hdc, rfl, hcm, hs, rfl⟩
  · exact .inl ⟨rfl, after_same ha hv hw⟩
  · rw [Xl.read_reg hs] at hv
    have hcv := ha.regsRel s hs v hv
    obtain ⟨fl, hex⟩ := movRR_exec d s core
    rw [hcv] at hex
    refine .inr ⟨_, _, _, fl, rfl, hex, rfl, ⟨fun acc hacc => ?_, fun acc hacc => ?_, fun l hl hc => by simp at hl; subst hl; simp [Loc.isCell] at hc⟩, after_reg ha hw⟩
    · rw [(movRR_foot d s core).1] at hacc; cases hacc
    · rw [(movRR_foot d s core).2] at hacc; cases hacc
  · obtain ⟨m', hm', hv'⟩ := ha.cells src hsc v hv
    rw [hcm] at hm'
    cases hm'
    have hrd : core.memory.read? .w64 (m.eval core) = .ok v := by
      rw [(ha.frame.cell src m hcm).read? .w64, truncate_w64, hv']
    obtain ⟨fl, hex⟩ := load64_exec d m core hrd
    refine .inr ⟨_, _, _, fl, rfl, hex, rfl, ⟨fun acc hacc => ?_, fun acc hacc => ?_, fun l hl hc => by simp at hl; subst hl; simp [Loc.isCell] at hc⟩, after_reg ha hw⟩
    · rw [(load64_foot d m core).1] at hacc
      simp only [List.mem_singleton] at hacc
      subst hacc
      exact .inr ⟨Nat.le_refl _, src, List.mem_singleton_self _, hsc, m, hcm, rfl⟩
    · rw [(load64_foot d m core).2] at hacc; cases hacc
  · rw [Xl.read_reg hs] at hv
    have hcv := ha.regsRel s hs v hv
    have hwr : core.memory.write? .w64 (m.eval core) (core.readReg s) =
        .ok (core.memory.write .w64 (m.eval core) v) := by
      rw [hcv]; exact (ha.frame.cell dst m hcm).write? v
    obtain ⟨fl, hex⟩ := store64_exec m s core hwr
    refine .inr ⟨_, _, _, fl, rfl, hex, rfl, ⟨fun acc hacc => ?_, fun acc hacc => ?_, fun l hl _ m' hm' => by
      simp at hl; subst hl; rw [hcm] at hm'; cases hm'; rw [(store64_foot m s core).2]; simp⟩,
      after_cell ha hdc hcm hw⟩
    · rw [(store64_foot m s core).1] at hacc; cases hacc
    · rw [(store64_foot m s core).2] at hacc
      simp only [List.mem_singleton] at hacc
      subst hacc
      exact .inr ⟨rfl, dst, hdc, m, hcm, rfl⟩

/-- A zeroing: Xl and the stacked `xor r32, r32` both set the register to 0. -/
theorem zero_sim {regs : Xl.Regs} {fr : Xl.Frame} {mem : Memory} {ctx : Word} {r : GPR}
    {regs' : Xl.Regs} {fr' : Xl.Frame} {mem' : Memory}
    (h : Xl.execInst regs fr mem ctx (.zero (.reg r)) = some (regs', fr', mem')) :
    Xl.reserved r = false ∧ regs' = regs.set r (some 0) ∧ fr' = fr ∧ mem' = mem := by
  obtain ⟨fl, hex⟩ := zero_exec r ⟨fun q => (regs.get q).getD 0, mem⟩ {}
  cases hr : Xl.reserved r
  · simp [Xl.execInst, hr, execRows, execRow, hex, guard] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [Validate.readReg_setReg], rfl, rfl⟩
  · simp [Xl.execInst, hr, guard, failure] at h

end Compilatrix.Xv.Stacking.Proof
