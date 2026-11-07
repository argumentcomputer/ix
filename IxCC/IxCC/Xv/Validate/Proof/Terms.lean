import IxCC.Xv.Validate.Proof.Calls

/-!
# Terminators

The validator's terminator checks decoded, the Xl image of each terminator
(`Term.substitute` with empty edge arguments), and an edge the validator
checked (`edge_sound`): Xl takes the same edge, with no parallel move left
to do, and the frames match at its target with the target's certificate.
-/

namespace IxCC.Xv.Validate

open IxCC.Lir (VReg Word Env Label FunId)
open IxCC.Xv.Alloc (Edit Output BlockOut)
open IxCC.Xv

/-! ## Checks -/

/-- An edge `checkEdges` accepted. -/
theorem checkEdges_mem {info : BlockInfo} {a : AState} :
    ∀ {edges : List (Edge VReg)}, checkEdges info a edges = none → ∀ {e : Edge VReg}, e ∈ edges →
      ∃ params cert, info.find? e.target = some (params, cert) ∧
        (cert.le (a.bindParams params e.args)) = true
  | [], _, _, he => by simp at he
  | e' :: es, h, e, he => by
      simp only [checkEdges] at h
      cases hf : info.find? e'.target with
      | none => simp [hf] at h
      | some pc =>
        obtain ⟨params, cert⟩ := pc
        simp only [hf] at h
        cases h₁ : (params.length != e'.args.length) <;> simp only [h₁, Bool.false_eq_true, ↓reduceIte] at h
        · cases h₂ : cert.le (a.bindParams params e'.args) <;>
            simp only [h₂, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨params, cert, hf, h₂⟩
          · exact checkEdges_mem h he
        · simp at h

set_option linter.unusedSimpArgs false in
/-- What the validator checks of a return. -/
theorem ret_check {c : Ctx} {a a' : AState} {vs : List VReg} {ls : List Loc}
    (h : stepTerm c a (.ret vs) ls = .ok a') :
    vs.length ≤ Xl.nResultRegs ∧ ls = resultLocs vs.length ∧
      (vs.zip ls).all (fun p => a.holds p.2 p.1) = true ∧ a' = a := by
  simp only [stepTerm, bind, Except.bind] at h
  cases h₁ : (decide (vs.length ≤ Xl.nResultRegs) && ls == resultLocs vs.length) <;>
    simp only [h₁, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  cases h₂ : (vs.zip ls).all (fun p => a.holds p.2 p.1) <;>
    simp only [h₂, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq, Except.ok.injEq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h₁
  exact ⟨h₁.1, h₁.2, rfl, h.symm⟩

set_option linter.unusedSimpArgs false in
/-- What the validator checks of a tail call. -/
theorem tail_check {c : Ctx} {a a' : AState} {g : FunId} {args : List VReg} {ls : List Loc}
    (h : stepTerm c a (.tail g args) ls = .ok a') :
    args.length ≤ Xl.nArgRegs ∧ ls = argLocs args.length ∧
      (args.zip ls).all (fun p => a.holds p.2 p.1) = true ∧ a' = a := by
  simp only [stepTerm, bind, Except.bind] at h
  cases h₁ : (decide (args.length ≤ Xl.nArgRegs) && ls == argLocs args.length) <;>
    simp only [h₁, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  cases h₂ : (args.zip ls).all (fun p => a.holds p.2 p.1) <;>
    simp only [h₂, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq, Except.ok.injEq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h₁
  exact ⟨h₁.1, h₁.2, rfl, h.symm⟩

/-- A jump leaves the abstract state as it is. -/
theorem jmp_check {c : Ctx} {a a' : AState} {e : Edge VReg} {ls : List Loc}
    (h : stepTerm c a (.jmp e) ls = .ok a') : a' = a := by
  simp only [stepTerm, bind, Except.bind] at h
  cases h₁ : ls.isEmpty <;>
    simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-! ## Images -/

theorem jmp_substitute {e : Edge VReg} {ls : List Loc} {t' : Term Loc}
    (h : (Term.jmp e).substitute ls ((Term.jmp e).edges.map fun _ => []) = some t') :
    t' = .jmp ⟨e.target, []⟩ := by
  simp only [Term.substitute, Term.edges, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    beq_self_eq_true, ↓reduceIte, pure, Option.bind_eq_bind, Option.bind_some, List.zip_cons_cons,
    List.zip_nil_right] at h
  simp only [guard, Option.bind] at h
  split at h <;> simp_all

theorem ret_substitute {vs : List VReg} {ls : List Loc} {t' : Term Loc}
    (h : (Term.ret vs).substitute ls ((Term.ret vs).edges.map fun _ => []) = some t') :
    t' = .ret ls := by
  simp only [Term.substitute, Term.edges, List.map_nil, List.length_nil, beq_self_eq_true, ↓reduceIte,
    pure, Option.bind_eq_bind, Option.bind_some, List.zip_nil_left] at h
  simp only [guard, Option.bind] at h
  split at h <;> simp_all

theorem tail_substitute {g : FunId} {args : List VReg} {ls : List Loc} {t' : Term Loc}
    (h : (Term.tail g args).substitute ls ((Term.tail g args).edges.map fun _ => []) = some t') :
    t' = .tail g ls := by
  simp only [Term.substitute, Term.edges, List.map_nil, List.length_nil, beq_self_eq_true, ↓reduceIte,
    pure, Option.bind_eq_bind, Option.bind_some, List.zip_nil_left] at h
  simp only [guard, Option.bind] at h
  split at h <;> simp_all

theorem fail_substitute {r : Sem.Resource} {ls : List Loc} {t' : Term Loc}
    (h : (Term.fail r : Term VReg).substitute ls ((Term.fail r : Term VReg).edges.map fun _ => []) =
      some t') :
    t' = .fail r := by
  simp only [Term.substitute, Term.edges, List.map_nil, List.length_nil, beq_self_eq_true, ↓reduceIte,
    pure, Option.bind_eq_bind, Option.bind_some, List.zip_nil_left] at h
  simp only [guard, Option.bind] at h
  split at h <;> simp_all

theorem trap_substitute {ls : List Loc} {t' : Term Loc}
    (h : (Term.trap : Term VReg).substitute ls ((Term.trap : Term VReg).edges.map fun _ => []) =
      some t') :
    t' = .trap := by
  simp only [Term.substitute, Term.edges, List.map_nil, List.length_nil, beq_self_eq_true, ↓reduceIte,
    pure, Option.bind_eq_bind, Option.bind_some, List.zip_nil_left] at h
  simp only [guard, Option.bind] at h
  split at h <;> simp_all

/-! ## Edges -/

theorem read_goto (regs : Xl.Regs) (fr : Xl.Frame) (L j : Nat) :
    Xl.read regs { fr with label := L, pos := j } = Xl.read regs fr := by
  funext l; cases l <;> rfl

/-- An Xv edge taken. -/
theorem takeEdge_next {f : Func VReg} {s s' : Lir.State} {fr : Lir.Frame} {rest : List Lir.Frame}
    {ρ : Env} {e : Edge VReg} {c : Bool} (h : Xv.takeEdge f s fr rest ρ e = .next s' c) :
    ∃ vals b' ρ', Xv.readAll ρ e.args = some vals ∧ f.blocks[e.target]? = some b' ∧
      Lir.bindParams ρ b'.params vals = some ρ' ∧
      s' = { s with stack := { fr with label := e.target, pos := 0, env := ρ' } :: rest } ∧
      c = decide (e.target ≤ fr.label) := by
  unfold Xv.takeEdge at h
  split at h
  · rename_i vals b' hr hb
    split at h
    · rename_i ρ' hρ
      simp only [Sem.Step.next.injEq] at h
      exact ⟨vals, b', ρ', hr, hb, hρ, h.1.symm, h.2.symm⟩
    · simp at h
  · simp at h

/-- An Xl edge with no arguments into a block with no parameters. -/
theorem xl_takeEdge {g : Func Loc} {t : Xl.State} {fl : Xl.Frame} {rest : List Xl.Frame} {regs : Xl.Regs}
    {L : Label} {bl : Block Loc} (hbl : g.blocks[L]? = some bl) (hp : bl.params = []) :
    Xl.takeEdge g t fl rest regs ⟨L, []⟩ =
      .next { t with regs, stack := { fl with label := L, pos := 0 } :: rest } (decide (L ≤ fl.label)) := by
  simp [Xl.takeEdge, Xl.readAll, hbl, hp, Xl.writeAll]

end IxCC.Xv.Validate
