import Compilatrix.Xv.Validate.Proof.Rows

/-!
# An instruction's rows at Xv and at Xl

`execBound_sim`: an instruction's rows, bound over operands paired with
their locations (`Bound (VReg × Loc)`), run at Xv with the registers and at
Xl with the locations. If the pairing satisfies the validator's checks
(`RowFacts`) and every use's location holds its register's value, then
whenever Xv runs the rows, Xl runs them too, with the same memory and
flags, each definition's location then holding its register's new value,
other registers and locations unchanged, and the frame's control fields
kept.
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (VReg Word Env)
open X86 (GPR)
open Compilatrix.Xv.Validate (Wide)
open Compilatrix.Xv.Xl (placeL xlLocs xlNamed xlCells xlFree xlTable WriteOk)

/-! ## Writing back -/

theorem Xl.WriteOk.of_sameCtl {fr fr' : Xl.Frame} (h : Xl.Frame.SameCtl fr fr') {l : Loc}
    (hw : WriteOk fr l) : WriteOk fr' l := by
  cases l <;> simp_all [WriteOk, h.inArgs]

theorem writeBacks_spec {core : X86.Core} :
    ∀ {L : List (Loc × GPR)} {regs : Xl.Regs} {fr : Xl.Frame},
      regs.size = 16 → (L.map Prod.fst).Nodup → (∀ p ∈ L, WriteOk fr p.1) →
      ∃ regs' fr', (L.map fun p => (p.1, some p.2)).foldlM (Xl.writeBack core) (regs, fr) =
          some (regs', fr') ∧ regs'.size = 16 ∧ Xl.Frame.SameCtl fr fr' ∧
        (∀ p ∈ L, Xl.read regs' fr' p.1 = some (core.readReg p.2)) ∧
        (∀ l, l ∉ L.map Prod.fst → Xl.read regs' fr' l = Xl.read regs fr l)
  | [], regs, fr, hs, _, _ => ⟨regs, fr, rfl, hs, Xl.Frame.SameCtl.refl _, by simp, fun _ _ => rfl⟩
  | p :: L, regs, fr, hs, hn, hw => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
      obtain ⟨regs₁, fr₁, hwr⟩ := Xl.write_ok (regs := regs) (hw p List.mem_cons_self) (core.readReg p.2)
      obtain ⟨hread, hother, hctl, hs₁⟩ := Xl.write_spec hs hwr
      obtain ⟨regs', fr', hfold, hs', hctl', hL, hL'⟩ := writeBacks_spec (L := L) hs₁ hn.2
        (fun q hq => Xl.WriteOk.of_sameCtl hctl (hw q (List.mem_cons_of_mem _ hq)))
      refine ⟨regs', fr', ?_, hs', hctl.trans hctl', ?_, ?_⟩
      · simp only [List.map_cons, List.foldlM_cons, Xl.writeBack, Option.bind_eq_bind]
        simp only [Option.bind_some, hwr]
        exact hfold
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · rw [hL' q.1 (fun hm => hn.1 (by
            obtain ⟨q', hq', e⟩ := List.mem_map.1 hm
            exact ⟨q', hq', e⟩)), hread]
        · exact hL q hq
      · intro l hl
        simp only [List.map_cons, List.mem_cons, not_or] at hl
        rw [hL' l hl.2, hother l hl.1]

/-- The readback list of paired bounds: each definition's location, from its
register. -/
theorem readback_eq {place : Loc → Option GPR} {h : Loc → GPR} :
    ∀ {bs : List (Bound (VReg × Loc))},
      (∀ b ∈ bs, Xl.Bound.placeable (b.map Prod.snd) = true) →
      (∀ b ∈ bs, ∀ d ∈ b.defs, place d.2 = some (h d.2)) → (∀ r, h (.reg r) = r) →
      (bs.map (Bound.map Prod.snd)).flatMap (Bound.readback place) =
        (bs.flatMap Bound.defs).map fun d => (d.2, some (h d.2))
  | [], _, _, _ => rfl
  | b :: bs, hp, hd, hr => by
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [readback_eq (fun b hb => hp b (List.mem_cons_of_mem _ hb))
        (fun b hb => hd b (List.mem_cons_of_mem _ hb)) hr]
      congr 1
      have hp₀ := hp b List.mem_cons_self
      have hd₀ := hd b List.mem_cons_self
      cases b with
      | output s x => simp [Bound.map, Bound.readback, Bound.defs, hd₀ x (by simp [Bound.defs])]
      | tied s a x =>
        simp only [Bound.map, Xl.Bound.placeable, Bool.and_eq_true, beq_iff_eq] at hp₀
        simp [Bound.map, Bound.readback, Bound.defs, hp₀.1, hd₀ x (by simp [Bound.defs])]
      | fixedDef i x =>
        simp only [Bound.map, Xl.Bound.placeable, beq_iff_eq] at hp₀
        simp [Bound.map, Bound.readback, Bound.defs, hp₀, hr]
      | fixedTied i a x =>
        simp only [Bound.map, Xl.Bound.placeable, Bool.and_eq_true, beq_iff_eq] at hp₀
        simp [Bound.map, Bound.readback, Bound.defs, hp₀.2, hr]
      | _ => rfl

/-! ## Xl's rows unfolded -/

/-- `guard` in `Option`. -/
def optGuard (p : Prop) [Decidable p] : Option Unit := guard p

theorem Xl.execBound_eq (parts : List (X86.Op × List (Bound Loc))) (regs : Xl.Regs) (fr : Xl.Frame)
    (mem : X86.Memory) (ctx : Word) (zf : Bool) :
    Xl.execBound parts regs fr mem ctx zf =
      Option.bind (optGuard ((parts.flatMap Prod.snd).all Xl.Bound.placeable)) fun _ =>
      Option.bind (optGuard ((xlNamed (parts.flatMap Prod.snd)).all (!Xl.reserved ·))) fun _ =>
      Option.bind (optGuard ((xlCells (parts.flatMap Prod.snd)).length ≤
        (xlFree (parts.flatMap Prod.snd)).length)) fun _ =>
      Option.bind (Xl.readAll regs fr ((parts.flatMap Prod.snd).flatMap Bound.uses)) fun _ =>
      Option.bind (optGuard ((Xl.zeroedRegs parts zf).all fun r =>
        !((parts.flatMap Prod.snd).flatMap Bound.uses).contains (.reg r))) fun _ =>
      Option.bind (parts.mapM (Xl.partArgs (Xl.placeIn (xlTable (parts.flatMap Prod.snd))))) fun margs =>
      Option.bind (execRows margs ⟨Xl.rowRegisters regs fr ctx (xlTable (parts.flatMap Prod.snd))
          (Xl.zeroedRegs parts zf), mem⟩) fun cf =>
      Option.bind (((parts.flatMap Prod.snd).flatMap
          (Bound.readback (Xl.placeIn (xlTable (parts.flatMap Prod.snd))))).foldlM
        (Xl.writeBack cf.1) (regs, fr)) fun rf =>
      some (rf.1, rf.2, cf.1.memory, cf.2) := rfl

end Compilatrix.Xv

