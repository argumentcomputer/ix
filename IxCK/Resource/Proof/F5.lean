import IxCK.Resource.Proof.ReadProps

/-!
# Soundness of the Mode Checker to `ModeOk` (`F5`)

Proves:
* Section 1: `CM` algebra, `StepIndep` for all non-recursive helpers in `Check.lean`,
  witness-string independence (`OkEq`) for `applyValue`, and `applyValue_cls`.
* Section 2: `StatePres` (`AStateOk`, `AStateLe`, `regions` preservation) and `ValRegsOk`
  invariants for all non-recursive helpers.
* Section 3 (`F5a`): Mutual fuel soundness of `anTerm`, `anCall`, `anLam`, `anCase`,
  `anAlt`, and `anDef_sound`.
* Section 4 (`F5c`): `unchecked_default_body_ok` (`TermModesDefault` + no non-default
  references → `DefaultBodyOk`).
* Section 5 (`F5`): `checkBodies_accept` and `check_sound_modeOk`.
-/

namespace IxCK.Resource.Proof

open IxCK.Resource Ixon

/-! ## Section 1: `CM` Algebra, `StepIndep`, and `OkEq` -/

theorem CM_bind_elim {α β : Type} {m : CM α} {f : α → CM β} {s s' : CSt} {b : β}
    (h : (m >>= f).run s = .ok (b, s')) :
    ∃ a s₁, m.run s = .ok (a, s₁) ∧ (f a).run s₁ = .ok (b, s') := by
  rw [CM_bind_run] at h
  cases hm : m.run s with
  | error e => rw [hm] at h; cases h
  | ok p => rw [hm] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem CM_pure_elim {α : Type} {a b : α} {s s' : CSt}
    (h : (pure a : CM α).run s = .ok (b, s')) : a = b ∧ s = s' := by
  rw [CM_pure_run] at h
  injection h with hp
  exact Prod.mk.inj hp

private theorem CM_get_run (s : CSt) : (get : CM CSt).run s = .ok (s, s) := rfl

private theorem CM_set_run (s₁ s : CSt) : (set s₁ : CM Unit).run s = .ok ((), s₁) := rfl

private theorem CM_modify_run (f : CSt → CSt) (s : CSt) : (modify f : CM Unit).run s = .ok ((), f s) := rfl

private theorem CM_refuseM_run {α : Type} (w : String) (s : CSt) :
    (refuseM w : CM α).run s = .error (.refuse w) := rfl

theorem CM_declineM_run {α : Type} (w : String) (s : CSt) :
    (declineM w : CM α).run s = .error (.decline w) := rfl

theorem CM_map_run {α β : Type} (f : α → β) (m : CM α) (s : CSt) :
    (f <$> m).run s =
      (match m.run s with
       | Except.ok (a, s') => Except.ok (f a, s')
       | Except.error e => Except.error e) := by
  change (m.run s).map (fun p => (f p.1, p.2)) = _
  cases m.run s <;> rfl

theorem CM_map_elim {α β : Type} {f : α → β} {m : CM α} {s s' : CSt} {b : β}
    (h : (f <$> m).run s = .ok (b, s')) :
    ∃ a, m.run s = .ok (a, s') ∧ f a = b := by
  rw [CM_map_run] at h
  cases hm : m.run s with
  | error e => rw [hm] at h; cases h
  | ok p =>
    rw [hm] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨p.1, by rw [← h.2], h.1⟩

theorem CM_tick_elim {s s' : CSt} {u : Unit} (h : tick.run s = .ok (u, s')) :
    s.steps ≠ 0 ∧ s' = { s with steps := s.steps - 1 } := by
  unfold tick at h
  obtain ⟨s0, s1, hget, h⟩ := CM_bind_elim h
  rw [CM_get_run] at hget
  simp only [Except.ok.injEq, Prod.mk.injEq] at hget
  obtain ⟨rfl, rfl⟩ := hget
  dsimp only at h
  cases hz : (s.steps == 0) with
  | true =>
    simp only [hz, ↓reduceIte] at h
    obtain ⟨_, _, hth, _⟩ := CM_bind_elim h
    cases hth
  | false =>
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
    rw [CM_set_run] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨by intro h0; simp [h0] at hz, h.2.symm⟩

theorem ofCSt_set_steps (s : CSt) (k : Nat) :
    AState.ofCSt { s with steps := k } = AState.ofCSt s := rfl

theorem toCSt_steps (σ : AState) (k : Nat) : (σ.toCSt k).steps = k := rfl

theorem forIn_list_inv {α β : Type} (I : β → Prop) (l : List α)
    (f : α → β → CM (ForInStep β))
    (hstep : ∀ a ∈ l, ∀ b s step s', I b → (f a b).run s = .ok (step, s') →
      match step with | .done b' => I b' | .yield b' => I b') :
    ∀ b out s s', I b → (forIn (m := CM) l b f).run s = .ok (out, s') → I out := by
  induction l with
  | nil =>
    intro b out s s' hb hf
    rw [List.forIn_nil] at hf
    obtain ⟨rfl, _⟩ := CM_pure_elim hf; exact hb
  | cons a rest ih =>
    intro b out s s' hb hf
    rw [List.forIn_cons] at hf
    obtain ⟨step, s₁, hs, hf⟩ := CM_bind_elim hf
    have hI := hstep a (List.mem_cons_self ..) b s step s₁ hb hs
    cases step with
    | done b' =>
      obtain ⟨rfl, _⟩ := CM_pure_elim hf; exact hI
    | yield b' =>
      exact ih (fun a' ha' => hstep a' (List.mem_cons_of_mem _ ha')) b' out s₁ s' hI hf

theorem forIn_array_inv {α β : Type} (I : β → Prop) (arr : Array α)
    (f : α → β → CM (ForInStep β))
    (hstep : ∀ a ∈ arr.toList, ∀ b s step s', I b → (f a b).run s = .ok (step, s') →
      match step with | .done b' => I b' | .yield b' => I b')
    {b out : β} {s s' : CSt} (hb : I b)
    (hf : (forIn (m := CM) arr b f).run s = .ok (out, s')) : I out := by
  rw [← Array.forIn_toList] at hf
  exact forIn_list_inv I arr.toList f hstep b out s s' hb hf

theorem StepIndep.refuseM {α : Type} (w : String) : StepIndep (refuseM w : CM α) :=
  StepIndep.throw (.refuse w)

theorem StepIndep.refuseM_bind {α β : Type} (w : String) (f : α → CM β) :
    StepIndep (IxCK.Resource.refuseM w >>= f) := by
  intro σ k₁ k₂
  constructor
  · intro _ _ h; rw [CM_bind_run, CM_refuseM_run] at h; cases h
  · intro e h; rw [CM_bind_run, CM_refuseM_run] at h ⊢; exact h

theorem StepIndep.forIn_list {α β : Type} (l : List α) (f : α → β → CM (ForInStep β))
    (hf : ∀ a b, StepIndep (f a b)) : ∀ b, StepIndep (forIn (m := CM) l b f) := by
  induction l with
  | nil =>
    intro b
    simpa [List.forIn_nil] using StepIndep.pure b
  | cons a rest ih =>
    intro b
    have hEq : forIn (m := CM) (a :: rest) b f =
        (f a b >>= fun step => match step with
          | ForInStep.done b' => Pure.pure b'
          | ForInStep.yield b' => forIn (m := CM) rest b' f) := by
      funext s; rw [List.forIn_cons]; rfl
    rw [hEq]
    refine StepIndep.bind (hf a b) (fun step => ?_)
    cases step with
    | done b' => exact StepIndep.pure b'
    | yield b' => exact ih b'

theorem StepIndep.forIn_array {α β : Type} (arr : Array α) (f : α → β → CM (ForInStep β))
    (hf : ∀ a b, StepIndep (f a b)) (b : β) : StepIndep (forIn (m := CM) arr b f) := by
  have hEq : forIn (m := CM) arr b f = forIn (m := CM) arr.toList b f := by
    funext s; rw [← Array.forIn_toList]
  rw [hEq]
  exact StepIndep.forIn_list arr.toList f hf b

theorem StepIndep.readOnly {α : Type} {m : CM α} (f : AState → α)
    (hrun : ∀ s, m.run s = .ok (f (AState.ofCSt s), s)) : StepIndep m := by
  intro σ k₁ k₂
  constructor
  · intro a s₁ h
    rw [hrun] at h
    simp only [AState.ofCSt_toCSt, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by rw [hrun]; rfl⟩
  · intro e h
    rw [hrun] at h; cases h

theorem StepIndep.modifyAState {m : CM Unit} (g : AState → AState)
    (hrun : ∀ s, m.run s = .ok ((), (g (AState.ofCSt s)).toCSt s.steps)) : StepIndep m := by
  intro σ k₁ k₂
  constructor
  · intro a s₁ h
    cases a
    rw [hrun] at h
    simp only [AState.ofCSt_toCSt, toCSt_steps, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨rfl, by rw [hrun]; rfl⟩
  · intro e h
    rw [hrun] at h; cases h

theorem stOf_run (id : Nat) (s : CSt) :
    (stOf id).run s = .ok (s.st[id]?.getD .dead, s) := rfl

theorem setSt_run (id : Nat) (b : BSt) (s : CSt) :
    (setSt id b).run s = .ok ((), { s with st := s.st.set! id b }) := rfl

theorem isOnceBnd_run (id : Nat) (s : CSt) :
    (isOnceBnd id).run s = .ok (s.once[id]?.getD false, s) := rfl

theorem isSpent_run (id : Nat) (s : CSt) :
    (isSpent id).run s = .ok (s.spent[id]?.getD false, s) := rfl

theorem markSpent_run (id : Nat) (s : CSt) :
    (markSpent id).run s = .ok ((), { s with spent := s.spent.set! id true }) := rfl

theorem newBnd_run (v : AVal) (isOnce : Bool) (s : CSt) :
    (newBnd v isOnce).run s =
      .ok (s.st.size, ((AState.ofCSt s).pushBnd v isOnce).2.toCSt s.steps) := rfl

theorem openReg_run (s : CSt) :
    openReg.run s = .ok ((AState.ofCSt s).openReg.1, (AState.ofCSt s).openReg.2.toCSt s.steps) := rfl

theorem closeReg_run (r : Nat) (s : CSt) :
    (closeReg r).run s = .ok ((), ((AState.ofCSt s).closeReg r).toCSt s.steps) := rfl

theorem innermost_run (s : CSt) :
    innermost.run s = .ok (s.regions.headD 1, s) := rfl

theorem stepIndep_stOf (id : Nat) : StepIndep (stOf id) :=
  StepIndep.readOnly (fun σ => σ.st[id]?.getD .dead) (stOf_run id)

theorem stepIndep_setSt (id : Nat) (b : BSt) : StepIndep (setSt id b) :=
  StepIndep.modifyAState (fun σ => { σ with st := σ.st.set! id b }) (setSt_run id b)

theorem stepIndep_isOnceBnd (id : Nat) : StepIndep (isOnceBnd id) :=
  StepIndep.readOnly (fun σ => σ.once[id]?.getD false) (isOnceBnd_run id)

theorem stepIndep_isSpent (id : Nat) : StepIndep (isSpent id) :=
  StepIndep.readOnly (fun σ => σ.spent[id]?.getD false) (isSpent_run id)

theorem stepIndep_markSpent (id : Nat) : StepIndep (markSpent id) :=
  StepIndep.modifyAState (fun σ => { σ with spent := σ.spent.set! id true }) (markSpent_run id)

theorem stepIndep_newBnd (v : AVal) (isOnce : Bool) : StepIndep (newBnd v isOnce) := by
  intro σ k₁ k₂
  constructor
  · intro a s₁ h
    rw [newBnd_run] at h
    simp only [AState.ofCSt_toCSt, toCSt_steps, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by rw [newBnd_run]; rfl⟩
  · intro e h; rw [newBnd_run] at h; cases h

theorem stepIndep_openReg : StepIndep openReg := by
  intro σ k₁ k₂
  constructor
  · intro a s₁ h
    rw [openReg_run] at h
    simp only [AState.ofCSt_toCSt, toCSt_steps, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by rw [openReg_run]; rfl⟩
  · intro e h; rw [openReg_run] at h; cases h

theorem stepIndep_closeReg (r : Nat) : StepIndep (closeReg r) :=
  StepIndep.modifyAState (fun σ => σ.closeReg r) (closeReg_run r)

theorem stepIndep_innermost : StepIndep innermost :=
  StepIndep.readOnly (fun σ => σ.regions.headD 1) innermost_run

local macro "si_step" : tactic => `(tactic|
  (first
    | exact StepIndep.pure _
    | exact StepIndep.refuseM _
    | exact StepIndep.refuseM_bind _ _
    | exact stepIndep_stOf _
    | exact stepIndep_setSt _ _
    | exact stepIndep_isOnceBnd _
    | exact stepIndep_isSpent _
    | exact stepIndep_markSpent _
    | exact stepIndep_newBnd _ _
    | exact stepIndep_openReg
    | exact stepIndep_closeReg _
    | exact stepIndep_innermost
    | (apply StepIndep.bind; rotate_left; intro _; rotate_left)
    | (apply StepIndep.forIn_list; intro _ _)
    | (apply StepIndep.forIn_array; intro _ _)
    | split
    | dsimp only))

theorem stepIndep_valid (v : AVal) (w : String) : StepIndep (valid v w) := by
  unfold valid; repeat si_step

theorem stepIndep_readVar (env : List ABnd) (i : Nat) : StepIndep (readVar env i) := by
  unfold readVar
  repeat (first | exact stepIndep_valid _ _ | si_step)

theorem stepIndep_isUniq (v : AVal) : StepIndep (isUniq v) := by
  unfold isUniq; repeat si_step

theorem stepIndep_notOnceSrc (v : AVal) (w : String) : StepIndep (notOnceSrc v w) := by
  unfold notOnceSrc; repeat si_step

theorem stepIndep_killSrc (v : AVal) : StepIndep (killSrc v) := by
  unfold killSrc; repeat si_step

theorem stepIndep_flowTo (d : Dest) (exp : Skel) (v : AVal) (w : String) :
    StepIndep (flowTo d exp v w) := by
  unfold flowTo
  refine StepIndep.bind (stepIndep_valid v w) (fun _ => ?_)
  cases d with
  | once =>
    cases hsk : exp.admitsNA v.skel with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.refuseM_bind _ _
    | true => simp only [↓reduceIte]; repeat (first | exact stepIndep_killSrc _ | si_step)
  | lend =>
    cases ho : v.onceOnly with
    | true =>
      cases hsk : exp.admitsNA v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.refuseM_bind _ _
      | true => simp only [↓reduceIte]; exact StepIndep.refuseM_bind _ _
    | false =>
      cases hsk : exp.admits v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.refuseM_bind _ _
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        repeat (first | exact stepIndep_notOnceSrc _ _ | exact stepIndep_killSrc _ | si_step)
  | share =>
    cases ho : v.onceOnly with
    | true =>
      cases hsk : exp.admitsNA v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.refuseM_bind _ _
      | true => simp only [↓reduceIte]; exact StepIndep.refuseM_bind _ _
    | false =>
      cases hsk : exp.admits v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.refuseM_bind _ _
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        repeat (first | exact stepIndep_notOnceSrc _ _ | exact stepIndep_killSrc _ | si_step)
  | uniq b =>
    cases ho : v.onceOnly with
    | true =>
      cases hsk : exp.admitsNA v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.refuseM_bind _ _
      | true => simp only [↓reduceIte]; exact StepIndep.refuseM_bind _ _
    | false =>
      cases hsk : exp.admits v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.refuseM_bind _ _
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine StepIndep.bind (stepIndep_notOnceSrc v w) (fun _ => ?_)
        refine StepIndep.bind ?_ (fun _ => ?_)
        · apply StepIndep.forIn_list; intro x _; repeat si_step
        · cases hvc : (v.cls == .val) with
        | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact stepIndep_killSrc v
        | true =>
          simp only [↓reduceIte]
          refine StepIndep.bind (stepIndep_isUniq v) (fun u => ?_)
          cases u with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.refuseM_bind _ _
          | true =>
            simp only [↓reduceIte]
            cases hbr : (!b && !v.regs.isEmpty) with
            | true => simp only [↓reduceIte]; exact StepIndep.refuseM_bind _ _
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              repeat (first | exact stepIndep_killSrc _ | si_step)

theorem stepIndep_callResult (ifc : Iface) (avs : Array (Option AVal)) (w : String) :
    StepIndep (callResult ifc avs w) := by
  unfold callResult
  repeat (first
    | exact stepIndep_valid _ _
    | exact stepIndep_flowTo _ _ _ _
    | si_step)

theorem stepIndep_papVal (ifc : Iface) (avs : Array (Option AVal)) (w : String) :
    StepIndep (papVal ifc avs w) := by
  unfold papVal
  repeat (first | exact stepIndep_flowTo _ _ _ _ | si_step)

theorem stepIndep_applyValue (f a : AVal) (c : Cls) (w : String) :
    StepIndep (applyValue f a c w) := by
  unfold applyValue
  repeat (first
    | exact stepIndep_valid _ _
    | exact stepIndep_callResult _ _ _
    | si_step)

theorem stepIndep_unknownCall (avs : Array (Option AVal)) (c : Cls) :
    StepIndep (unknownCall avs c) := by
  unfold unknownCall
  repeat (first | exact stepIndep_flowTo _ _ _ _ | si_step)

theorem stepIndep_bindInnerRegs (m : BinderMode) (cls : Cls) (v : AVal) (s : Nat) (w : String) :
    StepIndep (bindInnerRegs m cls v s w) := by
  unfold bindInnerRegs
  repeat (first | exact stepIndep_valid _ _ | exact stepIndep_flowTo _ _ _ _ | si_step)

theorem stepIndep_bindInnerBase (m : BinderMode) (cls : Cls) (v : AVal) (s : Nat) (w : String) :
    StepIndep (bindInnerBase m cls v s w) := by
  unfold bindInnerBase
  exact StepIndep.bind (stepIndep_bindInnerRegs m cls v s w) (fun _ => StepIndep.pure _)

theorem stepIndep_bindInner (m : BinderMode) (cls : Cls) (v : AVal) (s : Nat) (w : String) :
    StepIndep (bindInner m cls v s w) := by
  unfold bindInner
  repeat (first
    | exact stepIndep_notOnceSrc _ _
    | exact stepIndep_bindInnerBase _ _ _ _ _
    | exact stepIndep_killSrc _
    | si_step)

theorem stepIndep_retCheck (exp : Skel) (res : ResultMode) (s : Nat) (r : AVal) (w : String) :
    StepIndep (retCheck exp res s r w) := by
  unfold retCheck
  refine StepIndep.bind (stepIndep_valid r w) (fun _ => ?_)
  cases had : exp.admits r.skel with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.refuseM_bind _ _
  | true =>
    simp only [↓reduceIte]
    cases ho : r.onceOnly with
    | true => simp only [↓reduceIte]; exact StepIndep.refuseM_bind _ _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine StepIndep.bind (stepIndep_notOnceSrc r w) (fun _ => ?_)
      cases hvc : (r.cls == .val) with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.pure ()
      | true =>
        simp only [↓reduceIte]
        cases res with
        | shared =>
          cases hc : r.regs.contains s with
          | true => simp only [↓reduceIte]; exact StepIndep.refuseM _
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.pure ()
        | borrowed => exact StepIndep.pure ()
        | unique =>
          cases hc : r.regs.contains s with
          | true => simp only [↓reduceIte]; exact StepIndep.refuseM_bind _ _
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine StepIndep.bind (stepIndep_isUniq r) (fun u => ?_)
            cases u with
            | false => exact StepIndep.refuseM_bind _ _
            | true =>
              cases he : r.regs.isEmpty with
              | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.refuseM_bind _ _
              | true => simp only [↓reduceIte]; repeat si_step
        | uniqueBorrowed =>
          refine StepIndep.bind (stepIndep_isUniq r) (fun u => ?_)
          cases u with
          | false => exact StepIndep.refuseM_bind _ _
          | true => repeat si_step

theorem stepIndep_anCtor (nP : Nat) (fields : Array Field) (avs : Array (Option AVal)) (c : Cls) :
    StepIndep (anCtor nP fields avs c) := by
  unfold anCtor
  by_cases hlt : avs.size < nP + fields.size
  · simp only [hlt, ↓reduceIte]
    refine StepIndep.bind (StepIndep.forIn_array avs _ (fun oa _ => ?_) _) (fun _ => StepIndep.pure _)
    cases oa with
    | none => exact StepIndep.pure _
    | some a => exact StepIndep.bind (stepIndep_flowTo .share .unknown a _) (fun _ => StepIndep.pure _)
  · simp only [hlt, ↓reduceIte]
    cases hk : ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).isEmpty with
    | true => simp only [↓reduceIte]; exact StepIndep.pure _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hw : ((c == .imm || c == .leaf) &&
          ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).size == 1) with
      | true =>
        simp only [↓reduceIte]
        repeat (first | exact stepIndep_valid _ _ | si_step)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine StepIndep.bind (StepIndep.forIn_array _ _ (fun i acc => ?_) _) (fun _ => StepIndep.pure _)
        cases avs[nP + i]? with
        | none => exact StepIndep.pure _
        | some oa =>
          cases oa with
          | none => exact StepIndep.pure _
          | some v =>
            cases fields[i]? with
            | none => exact StepIndep.pure _
            | some f =>
              refine StepIndep.bind (stepIndep_valid v _) (fun _ => ?_)
              cases ho : v.onceOnly with
              | true => simp only [↓reduceIte]; exact StepIndep.refuseM_bind _ _
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                cases ha : Skel.unknown.admits v.skel with
                | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.refuseM_bind _ _
                | true =>
                  simp only [↓reduceIte]
                  cases hsh : (f.fmode == .shared) with
                  | true =>
                    simp only [↓reduceIte]
                    cases hfl : (v.regs.filter (· != 1)).isEmpty with
                    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.refuseM_bind _ _
                    | true =>
                      simp only [↓reduceIte]
                      exact StepIndep.bind (stepIndep_flowTo .share v.skel v _) (fun _ => StepIndep.pure _)
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    cases hvc : (v.cls == .val) with
                    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StepIndep.pure _
                    | true =>
                      simp only [↓reduceIte]
                      refine StepIndep.bind (stepIndep_notOnceSrc v _) (fun _ => ?_)
                      refine StepIndep.bind (stepIndep_isUniq v) (fun u => ?_)
                      cases u with
                      | true => simp only [↓reduceIte]; split <;> exact StepIndep.pure _
                      | false => simp only [Bool.false_eq_true, ↓reduceIte]; split <;> exact StepIndep.pure _

theorem stepIndep_anProj (P : Prog) (s : Ref) (i : Nat) (v : AVal) (c : Cls) :
    StepIndep (anProj P s i v c) := by
  unfold anProj; repeat si_step

/-! ### Witness-string independence (`OkEq`) for `applyValue` -/

/-- Two `CM` computations agree on every successful outcome. -/
def OkEq {α : Type} (m₁ m₂ : CM α) : Prop :=
  ∀ s a s', m₁.run s = .ok (a, s') ↔ m₂.run s = .ok (a, s')

theorem OkEq.refl {α : Type} (m : CM α) : OkEq m m := fun _ _ _ => Iff.rfl

theorem OkEq.refuseM {α : Type} (w₁ w₂ : String) : OkEq (refuseM w₁ : CM α) (refuseM w₂ : CM α) := by
  intro s a s'; simp [CM_refuseM_run]

theorem OkEq.refuseM_bind {α β : Type} (w₁ w₂ : String) (f₁ f₂ : α → CM β) :
    OkEq (IxCK.Resource.refuseM w₁ >>= f₁) (IxCK.Resource.refuseM w₂ >>= f₂) := by
  intro s b s'
  simp only [CM_bind_run, CM_refuseM_run]
  constructor <;> (intro h; cases h)

theorem OkEq.bind {α β : Type} {m₁ m₂ : CM α} {f₁ f₂ : α → CM β}
    (hm : OkEq m₁ m₂) (hf : ∀ a, OkEq (f₁ a) (f₂ a)) : OkEq (m₁ >>= f₁) (m₂ >>= f₂) := by
  intro s b s'
  constructor
  · intro h
    obtain ⟨a, s₁, h1, h2⟩ := CM_bind_elim h
    rw [CM_bind_run, (hm s a s₁).mp h1]
    exact (hf a s₁ b s').mp h2
  · intro h
    obtain ⟨a, s₁, h1, h2⟩ := CM_bind_elim h
    rw [CM_bind_run, (hm s a s₁).mpr h1]
    exact (hf a s₁ b s').mpr h2

theorem OkEq.forIn_list {α β : Type} (l : List α)
    (f₁ f₂ : α → β → CM (ForInStep β)) (hf : ∀ a b, OkEq (f₁ a b) (f₂ a b)) :
    ∀ b, OkEq (forIn (m := CM) l b f₁) (forIn (m := CM) l b f₂) := by
  induction l with
  | nil => intro b; simpa [List.forIn_nil] using OkEq.refl (Pure.pure b : CM β)
  | cons a rest ih =>
    intro b
    have h1 : forIn (m := CM) (a :: rest) b f₁ =
        (f₁ a b >>= fun step => match step with
          | ForInStep.done b' => Pure.pure b'
          | ForInStep.yield b' => forIn (m := CM) rest b' f₁) := by
      funext s; rw [List.forIn_cons]; rfl
    have h2 : forIn (m := CM) (a :: rest) b f₂ =
        (f₂ a b >>= fun step => match step with
          | ForInStep.done b' => Pure.pure b'
          | ForInStep.yield b' => forIn (m := CM) rest b' f₂) := by
      funext s; rw [List.forIn_cons]; rfl
    rw [h1, h2]
    refine OkEq.bind (hf a b) (fun step => ?_)
    cases step with
    | done b' => exact OkEq.refl _
    | yield b' => exact ih b'

theorem OkEq.forIn_array {α β : Type} (arr : Array α)
    (f₁ f₂ : α → β → CM (ForInStep β)) (hf : ∀ a b, OkEq (f₁ a b) (f₂ a b)) (b : β) :
    OkEq (forIn (m := CM) arr b f₁) (forIn (m := CM) arr b f₂) := by
  have h1 : forIn (m := CM) arr b f₁ = forIn (m := CM) arr.toList b f₁ := by
    funext s; rw [← Array.forIn_toList]
  have h2 : forIn (m := CM) arr b f₂ = forIn (m := CM) arr.toList b f₂ := by
    funext s; rw [← Array.forIn_toList]
  rw [h1, h2]
  exact OkEq.forIn_list arr.toList f₁ f₂ hf b

theorem OkEq.ite_same {α : Type} (c : Prop) [Decidable c] {m₁ m₂ n₁ n₂ : CM α}
    (h₁ : c → OkEq m₁ m₂) (h₂ : ¬ c → OkEq n₁ n₂) :
    OkEq (if c then m₁ else n₁) (if c then m₂ else n₂) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h₁ hc
  · simp only [hc, ↓reduceIte]; exact h₂ hc

local macro "okeq_step" : tactic => `(tactic|
  (first
    | exact OkEq.refl _
    | exact OkEq.refuseM _ _
    | exact OkEq.refuseM_bind _ _ _ _
    | (apply OkEq.bind; rotate_left; intro _; rotate_left)
    | (apply OkEq.forIn_list; intro _ _)
    | (apply OkEq.forIn_array; intro _ _)
    | (apply OkEq.ite_same; intro _; rotate_left; intro _; rotate_left)
    | dsimp only))

theorem okEq_valid (v : AVal) (w₁ w₂ : String) : OkEq (valid v w₁) (valid v w₂) := by
  unfold valid; repeat okeq_step

theorem okEq_notOnceSrc (v : AVal) (w₁ w₂ : String) : OkEq (notOnceSrc v w₁) (notOnceSrc v w₂) := by
  unfold notOnceSrc
  cases v.src <;> repeat okeq_step

theorem okEq_flowTo (d : Dest) (exp : Skel) (v : AVal) (w₁ w₂ : String) :
    OkEq (flowTo d exp v w₁) (flowTo d exp v w₂) := by
  unfold flowTo
  refine OkEq.bind (okEq_valid v w₁ w₂) (fun _ => ?_)
  cases d with
  | once =>
    cases hsk : exp.admitsNA v.skel with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact OkEq.refuseM_bind _ _ _ _
    | true => simp only [↓reduceIte]; repeat okeq_step
  | lend =>
    cases ho : v.onceOnly with
    | true =>
      cases hsk : exp.admitsNA v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact OkEq.refuseM_bind _ _ _ _
      | true => simp only [↓reduceIte]; exact OkEq.refuseM_bind _ _ _ _
    | false =>
      cases hsk : exp.admits v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact OkEq.refuseM_bind _ _ _ _
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        repeat (first | exact okEq_notOnceSrc _ _ _ | okeq_step)
  | share =>
    cases ho : v.onceOnly with
    | true =>
      cases hsk : exp.admitsNA v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact OkEq.refuseM_bind _ _ _ _
      | true => simp only [↓reduceIte]; exact OkEq.refuseM_bind _ _ _ _
    | false =>
      cases hsk : exp.admits v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact OkEq.refuseM_bind _ _ _ _
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        repeat (first | exact okEq_notOnceSrc _ _ _ | okeq_step)
  | uniq b =>
    cases ho : v.onceOnly with
    | true =>
      cases hsk : exp.admitsNA v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact OkEq.refuseM_bind _ _ _ _
      | true => simp only [↓reduceIte]; exact OkEq.refuseM_bind _ _ _ _
    | false =>
      cases hsk : exp.admits v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact OkEq.refuseM_bind _ _ _ _
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine OkEq.bind (okEq_notOnceSrc v w₁ w₂) (fun _ => ?_)
        refine OkEq.bind (OkEq.refl _) (fun _ => ?_)
        cases hvc : (v.cls == .val) with
        | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact OkEq.refl _
        | true =>
          simp only [↓reduceIte]
          refine OkEq.bind (OkEq.refl _) (fun u => ?_)
          cases u with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact OkEq.refuseM_bind _ _ _ _
          | true =>
            simp only [↓reduceIte]
            cases hbr : (!b && !v.regs.isEmpty) with
            | true => simp only [↓reduceIte]; exact OkEq.refuseM_bind _ _ _ _
            | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact OkEq.refl _

theorem okEq_callResult (ifc : Iface) (avs : Array (Option AVal)) (w₁ w₂ : String) :
    OkEq (callResult ifc avs w₁) (callResult ifc avs w₂) := by
  unfold callResult
  refine OkEq.bind (OkEq.forIn_array ifc.params.zipIdx _ _ (fun ⟨p, i⟩ _ => ?_) _) (fun _ => ?_)
  · dsimp only
    cases avs[i]? with
    | none => exact OkEq.refl _
    | some oa =>
      cases oa with
      | none => exact OkEq.refl _
      | some a =>
        cases destOf p (ifc.resCls != .val) <;>
          repeat (first | exact okEq_flowTo _ _ _ _ _ | okeq_step)
  · refine OkEq.bind (OkEq.forIn_array ifc.params.zipIdx _ _ (fun ⟨p, i⟩ _ => ?_) ()) (fun _ => OkEq.refl _)
    dsimp only
    cases destOf p (ifc.resCls != .val) with
    | lend =>
      cases avs[i]? with
      | some oa =>
        cases oa with
        | some a => exact OkEq.bind (okEq_valid a w₁ w₂) (fun _ => OkEq.refl _)
        | none => exact OkEq.refl _
      | none => exact OkEq.refl _
    | share => exact OkEq.refl _
    | uniq _ => exact OkEq.refl _
    | once => exact OkEq.refl _

theorem okEq_applyValue (f a : AVal) (c : Cls) (w₁ w₂ : String) :
    OkEq (applyValue f a c w₁) (applyValue f a c w₂) := by
  unfold applyValue
  repeat (first
    | exact okEq_valid _ _ _
    | exact okEq_callResult _ _ _ _
    | okeq_step)

theorem applyValue_w_indep {f a : AVal} {c : Cls} {w₁ w₂ : String} {σ σ' : AState} {g : AVal}
    (h : Runs (applyValue f a c w₁) σ g σ') : Runs (applyValue f a c w₂) σ g σ' :=
  (okEq_applyValue f a c w₁ w₂ (σ.toCSt 0) g (σ'.toCSt 0)).mp h

theorem applyValue_cls {f a : AVal} {c : Cls} {w : String} {s s' : CSt} {g : AVal}
    (h : (applyValue f a c w).run s = .ok (g, s')) : g.cls = c := by
  unfold applyValue at h
  obtain ⟨_, _, _, h⟩ := CM_bind_elim h
  obtain ⟨_, _, _, h⟩ := CM_bind_elim h
  obtain ⟨_, _, _, h⟩ := CM_bind_elim h
  obtain ⟨_, _, _, h⟩ := CM_bind_elim h
  dsimp only at h
  cases ho : f.onceOnly with
  | false =>
    simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨rfl, _⟩ := CM_pure_elim h; rfl
  | true =>
    simp only [ho, ↓reduceIte] at h
    cases hsrc : f.src with
    | none => simp only [hsrc] at h; obtain ⟨rfl, _⟩ := CM_pure_elim h; rfl
    | some x =>
      simp only [hsrc] at h
      obtain ⟨_, _, _, h⟩ := CM_bind_elim h
      obtain ⟨rfl, _⟩ := CM_pure_elim h; rfl

/-! ## Section 2: `StatePres` and `ValRegsOk` Invariants -/

/-- Every region recorded on `v` is strictly below `n`. -/
def ValRegsOk (n : Nat) (v : AVal) : Prop :=
  ∀ r ∈ v.regs, r < n

/-- Every binding in `env` has its regions strictly below `n`. -/
def EnvRegsOk (n : Nat) (env : List ABnd) : Prop :=
  ∀ b ∈ env, ValRegsOk n b.val

theorem ValRegsOk.mono {n m : Nat} {v : AVal} (hle : n ≤ m) (h : ValRegsOk n v) :
    ValRegsOk m v := fun r hr => Nat.lt_of_lt_of_le (h r hr) hle

theorem EnvRegsOk.mono {n m : Nat} {env : List ABnd} (hle : n ≤ m) (h : EnvRegsOk n env) :
    EnvRegsOk m env := fun b hb => (h b hb).mono hle

theorem regs_natUnion_lt {n : Nat} {a b : List Nat}
    (ha : ∀ r ∈ a, r < n) (hb : ∀ r ∈ b, r < n) : ∀ r ∈ natUnion a b, r < n := by
  intro r hr
  rcases (natUnion_mem a b).mp hr with h1 | h2
  · exact ha r h1
  · exact hb r h2

theorem innermost_lt_of_AStateOk {σ : AState} (hok : AStateOk σ) :
    σ.regions.headD 1 < σ.nextRegion := by
  obtain ⟨_, _, _, h1in, _, hlt⟩ := hok
  cases hreg : σ.regions with
  | nil => rw [hreg] at h1in; cases h1in
  | cons r rest =>
    exact (hlt r (by rw [hreg]; exact List.mem_cons_self ..)).2

/-- A `CM` helper preserves `AStateOk`, advances monotonically in `AStateLe`, and keeps `regions`. -/
def StatePres {α : Type} (m : CM α) : Prop :=
  ∀ s a s', AStateOk (AState.ofCSt s) → m.run s = .ok (a, s') →
    AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
    s'.regions = s.regions

theorem StatePres.pure {α : Type} (a : α) : StatePres (Pure.pure a : CM α) := by
  intro s b s' hok h
  obtain ⟨_, rfl⟩ := CM_pure_elim h
  exact ⟨hok, AStateLe.refl _, rfl⟩

theorem StatePres.refuseM {α : Type} (w : String) : StatePres (refuseM w : CM α) := by
  intro _ _ _ _ h; rw [CM_refuseM_run] at h; cases h

theorem StatePres.refuseM_bind {α β : Type} (w : String) (f : α → CM β) :
    StatePres (IxCK.Resource.refuseM w >>= f) := by
  intro _ _ _ _ h; rw [CM_bind_run, CM_refuseM_run] at h; cases h

theorem StatePres.bind {α β : Type} {m : CM α} {f : α → CM β}
    (hm : StatePres m) (hf : ∀ a, StatePres (f a)) : StatePres (m >>= f) := by
  intro s b s' hok h
  obtain ⟨a, s₁, h1, h2⟩ := CM_bind_elim h
  obtain ⟨hok1, hle1, hreg1⟩ := hm s a s₁ hok h1
  obtain ⟨hok2, hle2, hreg2⟩ := hf a s₁ b s' hok1 h2
  exact ⟨hok2, hle1.trans hle2, hreg2.trans hreg1⟩

theorem StatePres.forIn_list {α β : Type} (l : List α) (f : α → β → CM (ForInStep β))
    (hf : ∀ a b, StatePres (f a b)) : ∀ b, StatePres (forIn (m := CM) l b f) := by
  induction l with
  | nil => intro b; simpa [List.forIn_nil] using StatePres.pure b
  | cons a rest ih =>
    intro b
    have hEq : forIn (m := CM) (a :: rest) b f =
        (f a b >>= fun step => match step with
          | ForInStep.done b' => Pure.pure b'
          | ForInStep.yield b' => forIn (m := CM) rest b' f) := by
      funext s; rw [List.forIn_cons]; rfl
    rw [hEq]
    refine StatePres.bind (hf a b) (fun step => ?_)
    cases step with
    | done b' => exact StatePres.pure b'
    | yield b' => exact ih b'

theorem StatePres.forIn_array {α β : Type} (arr : Array α) (f : α → β → CM (ForInStep β))
    (hf : ∀ a b, StatePres (f a b)) (b : β) : StatePres (forIn (m := CM) arr b f) := by
  have hEq : forIn (m := CM) arr b f = forIn (m := CM) arr.toList b f := by
    funext s; rw [← Array.forIn_toList]
  rw [hEq]
  exact StatePres.forIn_list arr.toList f hf b

theorem StatePres.of_state_eq {α : Type} {m : CM α}
    (heq : ∀ s a s', m.run s = .ok (a, s') → s' = s) : StatePres m := by
  intro s a s' hok h
  have := heq s a s' h; subst this
  exact ⟨hok, AStateLe.refl _, rfl⟩

theorem valid_state_eq {v : AVal} {w : String} {s s' : CSt} {u : Unit}
    (h : (valid v w).run s = .ok (u, s')) : s' = s := by
  unfold valid at h
  obtain ⟨_, s₁, hfl, hp⟩ := CM_bind_elim h
  have hs' := (CM_pure_elim hp).2; subst hs'
  have aux : ∀ (l : List Nat) (acc out : PUnit) (s0 s1 : CSt),
      (forIn (m := CM) l acc fun d _ => do
        if (← stOf d) == BSt.dead then refuseM s!"revokedUse: {w}, after a unique transfer"
        pure (ForInStep.yield PUnit.unit)).run s0 = .ok (out, s1) → s1 = s0 := by
    intro l
    induction l with
    | nil =>
      intro acc out s0 s1 hf
      rw [List.forIn_nil] at hf; exact (CM_pure_elim hf).2.symm
    | cons d rest ih =>
      intro acc out s0 s1 hf
      rw [List.forIn_cons] at hf
      obtain ⟨step, s2, hstep, hf⟩ := CM_bind_elim hf
      obtain ⟨b, s3, hst, hstep⟩ := CM_bind_elim hstep
      rw [stOf_run] at hst
      simp only [Except.ok.injEq, Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl⟩ := hst
      dsimp only at hstep
      cases hd : (s0.st[d]?.getD BSt.dead == BSt.dead) with
      | true =>
        simp only [hd, ↓reduceIte] at hstep
        obtain ⟨_, _, href, _⟩ := CM_bind_elim hstep
        rw [CM_refuseM_run] at href; cases href
      | false =>
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at hstep
        obtain ⟨rfl, rfl⟩ := CM_pure_elim hstep
        exact ih PUnit.unit out s0 s1 hf
  exact aux v.deps PUnit.unit _ s s₁ hfl

theorem isUniq_state_eq {v : AVal} {s s' : CSt} {b : Bool}
    (h : (isUniq v).run s = .ok (b, s')) : s' = s := by
  unfold isUniq at h
  cases h1 : (v.cls != .val) with
  | true => simp only [h1, ↓reduceIte] at h; exact (CM_pure_elim h).2.symm
  | false =>
    simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    cases h2 : (v.own != Own.uniq) with
    | true => simp only [h2, ↓reduceIte] at h; exact (CM_pure_elim h).2.symm
    | false =>
      simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      have hfl : ∀ (l : List Nat) (acc out : Option Bool × PUnit) (s0 s1 : CSt),
          (forIn (m := CM) l acc fun d _ => do
            if ((← stOf d) == BSt.live) = true then pure (ForInStep.yield (none, PUnit.unit))
            else pure (ForInStep.done (some false, PUnit.unit))).run s0 = .ok (out, s1) → s1 = s0 := by
        intro l
        induction l with
        | nil =>
          intro acc out s0 s1 hf
          rw [List.forIn_nil] at hf; exact (CM_pure_elim hf).2.symm
        | cons d rest ih =>
          intro acc out s0 s1 hf
          rw [List.forIn_cons] at hf
          obtain ⟨step, s2, hstep, hf⟩ := CM_bind_elim hf
          obtain ⟨bv, s3, hst, hstep⟩ := CM_bind_elim hstep
          rw [stOf_run] at hst
          simp only [Except.ok.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl⟩ := hst
          cases hl : (s0.st[d]?.getD BSt.dead == BSt.live) with
          | true =>
            simp only [hl, ↓reduceIte] at hstep
            obtain ⟨rfl, rfl⟩ := CM_pure_elim hstep
            exact ih (none, PUnit.unit) out s0 s1 hf
          | false =>
            simp only [hl, Bool.false_eq_true, ↓reduceIte] at hstep
            obtain ⟨rfl, rfl⟩ := CM_pure_elim hstep
            exact (CM_pure_elim hf).2.symm
      obtain ⟨r, s₁, hf, h⟩ := CM_bind_elim h
      have hs₁ := hfl v.deps (none, PUnit.unit) r s s₁ hf
      subst hs₁
      obtain ⟨r1, r2⟩ := r
      cases r1 with
      | some bv => exact (CM_pure_elim h).2.symm
      | none => exact (CM_pure_elim h).2.symm

theorem notOnceSrc_state_eq {v : AVal} {w : String} {s s' : CSt} {u : Unit}
    (h : (notOnceSrc v w).run s = .ok (u, s')) : s' = s := by
  unfold notOnceSrc at h
  cases hsrc : v.src with
  | none => simp only [hsrc] at h; exact (CM_pure_elim h).2.symm
  | some x =>
    simp only [hsrc] at h
    obtain ⟨b, s₁, hb, h⟩ := CM_bind_elim h
    rw [isOnceBnd_run] at hb
    simp only [Except.ok.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    cases h1 : s.once[x]?.getD false with
    | true => simp only [h1, ↓reduceIte] at h; rw [CM_refuseM_run] at h; cases h
    | false => simp only [h1, Bool.false_eq_true, ↓reduceIte] at h; exact (CM_pure_elim h).2.symm

theorem readVar_props {env : List ABnd} {i : Nat} {s s' : CSt} {v : AVal}
    (h : (readVar env i).run s = .ok (v, s')) :
    s' = s ∧ ∃ b, env[i]? = some b ∧ v.regs = b.val.regs := by
  unfold readVar at h
  cases he : env[i]? with
  | none => simp only [he] at h; rw [CM_refuseM_run] at h; cases h
  | some b =>
    simp only [he] at h
    cases her : (b.mode == .erased) with
    | true =>
      simp only [her, ↓reduceIte] at h
      obtain ⟨_, _, href, _⟩ := CM_bind_elim h
      rw [CM_refuseM_run] at href; cases href
    | false =>
      simp only [her, Bool.false_eq_true, ↓reduceIte] at h
      rw [CM_bind_run] at h
      cases hv : (valid { b.val with deps := b.id :: b.val.deps.filter (· != b.id), src := some b.id } "a binding is read").run s with
      | error e => rw [hv] at h; cases h
      | ok p =>
        rw [hv] at h
        have hp2 := valid_state_eq hv
        obtain ⟨rfl, rfl⟩ := CM_pure_elim h
        exact ⟨hp2, b, rfl, rfl⟩

theorem statePres_valid (v : AVal) (w : String) : StatePres (valid v w) :=
  StatePres.of_state_eq (fun _ _ _ h => valid_state_eq h)

theorem statePres_isUniq (v : AVal) : StatePres (isUniq v) :=
  StatePres.of_state_eq (fun _ _ _ h => isUniq_state_eq h)

theorem statePres_notOnceSrc (v : AVal) (w : String) : StatePres (notOnceSrc v w) :=
  StatePres.of_state_eq (fun _ _ _ h => notOnceSrc_state_eq h)

theorem statePres_readVar (env : List ABnd) (i : Nat) : StatePres (readVar env i) :=
  StatePres.of_state_eq (fun _ _ _ h => (readVar_props h).1)

theorem statePres_stOf (id : Nat) : StatePres (stOf id) :=
  StatePres.of_state_eq (fun s a s' h => by rw [stOf_run] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact h.2.symm)

theorem statePres_isOnceBnd (id : Nat) : StatePres (isOnceBnd id) :=
  StatePres.of_state_eq (fun s a s' h => by rw [isOnceBnd_run] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact h.2.symm)

theorem statePres_isSpent (id : Nat) : StatePres (isSpent id) :=
  StatePres.of_state_eq (fun s a s' h => by rw [isSpent_run] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact h.2.symm)

theorem statePres_innermost : StatePres innermost :=
  StatePres.of_state_eq (fun s a s' h => by rw [innermost_run] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact h.2.symm)

theorem statePres_setSt_dead (id : Nat) : StatePres (setSt id BSt.dead) := by
  intro s a s' hok h
  cases a
  rw [setSt_run] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  obtain ⟨h1, h2, hnr, h1in, hnd, hlt⟩ := hok
  have hsz : (s.st.set! id BSt.dead).size = s.st.size := Array.size_setIfInBounds
  refine ⟨⟨by rw [AState.ofCSt] at h1 ⊢; dsimp only at h1 ⊢; rw [hsz]; exact h1,
           by rw [AState.ofCSt] at h2 ⊢; dsimp only at h2 ⊢; rw [hsz]; exact h2,
           hnr, h1in, hnd, hlt⟩, ?_, rfl⟩
  refine ⟨by dsimp only [AState.ofCSt]; rw [hsz]; exact Nat.le_refl _, Nat.le_refl _, ?_, fun _ _ => rfl, fun _ _ hx => hx⟩
  intro i hi
  dsimp only [AState.ofCSt] at hi ⊢
  rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem (by omega)]
  by_cases heq : id = i
  · subst heq
    simp only [Array.set!, Array.getElem_setIfInBounds_self]
    cases s.st[id] <;> exact trivial
  · simp only [Array.set!]
    rw [Array.getElem_setIfInBounds_ne (h := heq)]
    exact BSt.le_refl _

theorem statePres_shareIfLive (x : Nat) :
    StatePres (do
      if (← stOf x) == BSt.live then
        setSt x BSt.shared
        pure (ForInStep.yield PUnit.unit)
      else pure (ForInStep.yield PUnit.unit)) := by
  intro s a s' hok h
  obtain ⟨b, s₁, hst, h⟩ := CM_bind_elim h
  rw [stOf_run] at hst
  simp only [Except.ok.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  cases hl : (s.st[x]?.getD BSt.dead == BSt.live) with
  | true =>
    simp only [hl, ↓reduceIte] at h
    obtain ⟨_, s₂, hset, hp⟩ := CM_bind_elim h
    rw [setSt_run] at hset
    simp only [Except.ok.injEq, Prod.mk.injEq] at hset
    obtain ⟨_, rfl⟩ := hset
    obtain ⟨_, rfl⟩ := CM_pure_elim hp
    obtain ⟨h1, h2, hnr, h1in, hnd, hlt⟩ := hok
    have hsz : (s.st.set! x BSt.shared).size = s.st.size := Array.size_setIfInBounds
    refine ⟨⟨by rw [AState.ofCSt] at h1 ⊢; dsimp only at h1 ⊢; rw [hsz]; exact h1,
             by rw [AState.ofCSt] at h2 ⊢; dsimp only at h2 ⊢; rw [hsz]; exact h2,
             hnr, h1in, hnd, hlt⟩, ?_, rfl⟩
    refine ⟨by dsimp only [AState.ofCSt]; rw [hsz]; exact Nat.le_refl _, Nat.le_refl _, ?_, fun _ _ => rfl, fun _ _ hx => hx⟩
    intro i hi
    dsimp only [AState.ofCSt] at hi ⊢
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem (by omega)]
    by_cases heq : x = i
    · subst heq
      simp only [Array.set!, Array.getElem_setIfInBounds_self]
      rw [Array.getElem?_eq_getElem hi] at hl
      cases hb : s.st[x] with
      | live => exact trivial
      | shared => rw [hb] at hl; cases hl
      | dead => rw [hb] at hl; cases hl
    · simp only [Array.set!]
      rw [Array.getElem_setIfInBounds_ne (h := heq)]
      exact BSt.le_refl _
  | false =>
    simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨_, rfl⟩ := CM_pure_elim h
    exact ⟨hok, AStateLe.refl _, rfl⟩

theorem statePres_markSpent (id : Nat) : StatePres (markSpent id) := by
  intro s a s' hok h
  cases a
  rw [markSpent_run] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  obtain ⟨h1, h2, hnr, h1in, hnd, hlt⟩ := hok
  have hsz : (s.spent.set! id true).size = s.spent.size := Array.size_setIfInBounds
  refine ⟨⟨h1, by rw [AState.ofCSt] at h2 ⊢; dsimp only at h2 ⊢; rw [hsz]; exact h2,
           hnr, h1in, hnd, hlt⟩, ?_, rfl⟩
  refine ⟨Nat.le_refl _, Nat.le_refl _, fun i hi => ?_, fun _ _ => rfl, ?_⟩
  · dsimp only [AState.ofCSt] at hi ⊢
    rw [Array.getElem?_eq_getElem hi]; exact BSt.le_refl _
  · intro i hi hsp
    dsimp only [AState.ofCSt] at hi hsp ⊢
    rw [Array.getElem?_eq_getElem (by omega)]
    by_cases heq : id = i
    · subst heq; simp [Array.set!]
    · simp only [Array.set!]
      rw [Array.getElem_setIfInBounds_ne (h := heq)]
      rwa [Array.getElem?_eq_getElem hi] at hsp

theorem statePres_newBnd (v : AVal) (isOnce : Bool) : StatePres (newBnd v isOnce) := by
  intro s a s' hok h
  rw [newBnd_run] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  have ⟨h1, h2⟩ := hok.pushBnd v isOnce
  exact ⟨h1, h2, rfl⟩

local macro "sp_step" : tactic => `(tactic|
  (first
    | exact StatePres.pure _
    | exact StatePres.refuseM _
    | exact StatePres.refuseM_bind _ _
    | exact statePres_stOf _
    | exact statePres_setSt_dead _
    | exact statePres_shareIfLive _
    | exact statePres_isOnceBnd _
    | exact statePres_isSpent _
    | exact statePres_markSpent _
    | exact statePres_newBnd _ _
    | exact statePres_innermost
    | exact statePres_valid _ _
    | exact statePres_isUniq _
    | exact statePres_notOnceSrc _ _
    | exact statePres_readVar _ _
    | (apply StatePres.bind; rotate_left; intro _; rotate_left)
    | (apply StatePres.forIn_list; intro _ _)
    | (apply StatePres.forIn_array; intro _ _)
    | split
    | dsimp only))

theorem statePres_killSrc (v : AVal) : StatePres (killSrc v) := by
  unfold killSrc; repeat sp_step

theorem statePres_flowTo (d : Dest) (exp : Skel) (v : AVal) (w : String) :
    StatePres (flowTo d exp v w) := by
  unfold flowTo
  refine StatePres.bind (statePres_valid v w) (fun _ => ?_)
  cases d with
  | once =>
    cases hsk : exp.admitsNA v.skel with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.refuseM_bind _ _
    | true =>
      simp only [↓reduceIte]
      refine StatePres.bind ?_ (fun _ => ?_)
      · apply StatePres.forIn_list; intro x _; repeat sp_step
      · refine StatePres.bind ?_ (fun _ => ?_)
        · apply StatePres.forIn_list; intro x _; repeat sp_step
        · cases hvc : (v.cls == .val) with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact statePres_killSrc v
          | true =>
            simp only [↓reduceIte]
            refine StatePres.bind ?_ (fun _ => statePres_killSrc v)
            apply StatePres.forIn_list; intro x _; exact statePres_shareIfLive x
  | lend =>
    cases ho : v.onceOnly with
    | true =>
      cases hsk : exp.admitsNA v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.refuseM_bind _ _
      | true => simp only [↓reduceIte]; exact StatePres.refuseM_bind _ _
    | false =>
      cases hsk : exp.admits v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.refuseM_bind _ _
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine StatePres.bind (statePres_notOnceSrc v w) (fun _ => ?_)
        refine StatePres.bind ?_ (fun _ => statePres_killSrc v)
        apply StatePres.forIn_list; intro x _; repeat sp_step
  | share =>
    cases ho : v.onceOnly with
    | true =>
      cases hsk : exp.admitsNA v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.refuseM_bind _ _
      | true => simp only [↓reduceIte]; exact StatePres.refuseM_bind _ _
    | false =>
      cases hsk : exp.admits v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.refuseM_bind _ _
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine StatePres.bind (statePres_notOnceSrc v w) (fun _ => ?_)
        refine StatePres.bind ?_ (fun _ => ?_)
        · apply StatePres.forIn_list; intro x _; repeat sp_step
        · cases hvc : (v.cls == .val) with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact statePres_killSrc v
          | true =>
            simp only [↓reduceIte]
            refine StatePres.bind ?_ (fun _ => statePres_killSrc v)
            apply StatePres.forIn_list; intro x _; exact statePres_shareIfLive x
  | uniq b =>
    cases ho : v.onceOnly with
    | true =>
      cases hsk : exp.admitsNA v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.refuseM_bind _ _
      | true => simp only [↓reduceIte]; exact StatePres.refuseM_bind _ _
    | false =>
      cases hsk : exp.admits v.skel with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.refuseM_bind _ _
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine StatePres.bind (statePres_notOnceSrc v w) (fun _ => ?_)
        refine StatePres.bind ?_ (fun _ => ?_)
        · apply StatePres.forIn_list; intro x _; repeat sp_step
        · cases hvc : (v.cls == .val) with
        | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact statePres_killSrc v
        | true =>
          simp only [↓reduceIte]
          refine StatePres.bind (statePres_isUniq v) (fun u => ?_)
          cases u with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.refuseM_bind _ _
          | true =>
            simp only [↓reduceIte]
            cases hbr : (!b && !v.regs.isEmpty) with
            | true => simp only [↓reduceIte]; exact StatePres.refuseM_bind _ _
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              refine StatePres.bind ?_ (fun _ => statePres_killSrc v)
              apply StatePres.forIn_list; intro x _
              exact StatePres.bind (statePres_setSt_dead x) (fun _ => StatePres.pure _)

theorem statePres_callResult (ifc : Iface) (avs : Array (Option AVal)) (w : String) :
    StatePres (callResult ifc avs w) := by
  unfold callResult
  repeat (first | exact statePres_flowTo _ _ _ _ | sp_step)

theorem statePres_papVal (ifc : Iface) (avs : Array (Option AVal)) (w : String) :
    StatePres (papVal ifc avs w) := by
  unfold papVal
  repeat (first | exact statePres_flowTo _ _ _ _ | sp_step)

theorem statePres_applyValue (f a : AVal) (c : Cls) (w : String) :
    StatePres (applyValue f a c w) := by
  unfold applyValue
  repeat (first | exact statePres_callResult _ _ _ | sp_step)

theorem statePres_bindInnerRegs (m : BinderMode) (cls : Cls) (v : AVal) (s : Nat) (w : String) :
    StatePres (bindInnerRegs m cls v s w) := by
  unfold bindInnerRegs
  repeat (first | exact statePres_flowTo _ _ _ _ | sp_step)

theorem statePres_bindInnerBase (m : BinderMode) (cls : Cls) (v : AVal) (s : Nat) (w : String) :
    StatePres (bindInnerBase m cls v s w) := by
  unfold bindInnerBase
  exact StatePres.bind (statePres_bindInnerRegs m cls v s w) (fun _ => StatePres.pure _)

theorem statePres_bindInner (m : BinderMode) (cls : Cls) (v : AVal) (s : Nat) (w : String) :
    StatePres (bindInner m cls v s w) := by
  unfold bindInner
  repeat (first | exact statePres_bindInnerBase _ _ _ _ _ | exact statePres_killSrc _ | sp_step)

theorem statePres_retCheck (exp : Skel) (res : ResultMode) (s : Nat) (r : AVal) (w : String) :
    StatePres (retCheck exp res s r w) := by
  unfold retCheck
  refine StatePres.bind (statePres_valid r w) (fun _ => ?_)
  cases had : exp.admits r.skel with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.refuseM_bind _ _
  | true =>
    simp only [↓reduceIte]
    cases ho : r.onceOnly with
    | true => simp only [↓reduceIte]; exact StatePres.refuseM_bind _ _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine StatePres.bind (statePres_notOnceSrc r w) (fun _ => ?_)
      cases hvc : (r.cls == .val) with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.pure ()
      | true =>
        simp only [↓reduceIte]
        cases res with
        | shared =>
          cases hc : r.regs.contains s with
          | true => simp only [↓reduceIte]; exact StatePres.refuseM _
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.pure ()
        | borrowed => exact StatePres.pure ()
        | unique =>
          cases hc : r.regs.contains s with
          | true => simp only [↓reduceIte]; exact StatePres.refuseM_bind _ _
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine StatePres.bind (statePres_isUniq r) (fun u => ?_)
            cases u with
            | false => exact StatePres.refuseM_bind _ _
            | true =>
              cases he : r.regs.isEmpty with
              | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.refuseM_bind _ _
              | true => simp only [↓reduceIte]; repeat sp_step
        | uniqueBorrowed =>
          refine StatePres.bind (statePres_isUniq r) (fun u => ?_)
          cases u with
          | false => exact StatePres.refuseM_bind _ _
          | true => repeat sp_step

theorem statePres_anCtor (nP : Nat) (fields : Array Field) (avs : Array (Option AVal)) (c : Cls) :
    StatePres (anCtor nP fields avs c) := by
  unfold anCtor
  by_cases hlt : avs.size < nP + fields.size
  · simp only [hlt, ↓reduceIte]
    refine StatePres.bind (StatePres.forIn_array avs _ (fun oa _ => ?_) _) (fun _ => StatePres.pure _)
    cases oa with
    | none => exact StatePres.pure _
    | some a => exact StatePres.bind (statePres_flowTo .share .unknown a _) (fun _ => StatePres.pure _)
  · simp only [hlt, ↓reduceIte]
    cases hk : ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).isEmpty with
    | true => simp only [↓reduceIte]; exact StatePres.pure _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hw : ((c == .imm || c == .leaf) &&
          ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).size == 1) with
      | true =>
        simp only [↓reduceIte]
        repeat sp_step
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine StatePres.bind (StatePres.forIn_array _ _ (fun i acc => ?_) _) (fun _ => StatePres.pure _)
        cases avs[nP + i]? with
        | none => exact StatePres.pure _
        | some oa =>
          cases oa with
          | none => exact StatePres.pure _
          | some v =>
            cases fields[i]? with
            | none => exact StatePres.pure _
            | some f =>
              refine StatePres.bind (statePres_valid v _) (fun _ => ?_)
              cases ho : v.onceOnly with
              | true => simp only [↓reduceIte]; exact StatePres.refuseM_bind _ _
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                cases ha : Skel.unknown.admits v.skel with
                | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.refuseM_bind _ _
                | true =>
                  simp only [↓reduceIte]
                  cases hsh : (f.fmode == .shared) with
                  | true =>
                    simp only [↓reduceIte]
                    cases hfl : (v.regs.filter (· != 1)).isEmpty with
                    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.refuseM_bind _ _
                    | true =>
                      simp only [↓reduceIte]
                      exact StatePres.bind (statePres_flowTo .share v.skel v _) (fun _ => StatePres.pure _)
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    cases hvc : (v.cls == .val) with
                    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact StatePres.pure _
                    | true =>
                      simp only [↓reduceIte]
                      refine StatePres.bind (statePres_notOnceSrc v _) (fun _ => ?_)
                      refine StatePres.bind (statePres_isUniq v) (fun u => ?_)
                      cases u with
                      | true => simp only [↓reduceIte]; split <;> exact StatePres.pure _
                      | false => simp only [Bool.false_eq_true, ↓reduceIte]; split <;> exact StatePres.pure _

theorem statePres_anProj (P : Prog) (s : Ref) (i : Nat) (v : AVal) (c : Cls) :
    StatePres (anProj P s i v c) := by
  unfold anProj; repeat sp_step

/-! ### `ValRegsOk` preservation for non-recursive value-returning helpers -/

theorem callResult_regsOk {ifc : Iface} {avs : Array (Option AVal)} {w : String}
    {s s' : CSt} {rv : AVal}
    (hok : AStateOk (AState.ofCSt s))
    (havs : ∀ a, some a ∈ avs.toList → ValRegsOk s.nextRegion a)
    (h : (callResult ifc avs w).run s = .ok (rv, s')) :
    ValRegsOk s'.nextRegion rv := by
  have ⟨_, hle', _⟩ := statePres_callResult ifc avs w s rv s' hok h
  have hnr : s.nextRegion ≤ s'.nextRegion := hle'.2.1
  unfold callResult at h
  obtain ⟨⟨deps, sdeps, regs⟩, s₁, hfl1, h⟩ := CM_bind_elim h
  have hregs1 : ∀ r ∈ regs, r < s.nextRegion := by
    refine forIn_array_inv (I := fun x => ∀ r ∈ x.2.2, r < s.nextRegion) _ _ (fun pi _ acc st0 step st1 hacc hstep => ?_)
      (fun _ hm => by cases hm) hfl1
    obtain ⟨p, i⟩ := pi
    dsimp only at hstep
    cases hai : avs[i]? with
    | none => simp only [hai] at hstep; obtain ⟨rfl, _⟩ := CM_pure_elim hstep; exact hacc
    | some oa =>
      cases oa with
      | none => simp only [hai] at hstep; obtain ⟨rfl, _⟩ := CM_pure_elim hstep; exact hacc
      | some a =>
        simp only [hai] at hstep
        obtain ⟨_, _, _, hstep⟩ := CM_bind_elim hstep
        have haMem : some a ∈ avs.toList := array_mem_toList_of_getElem?' hai
        cases hc : (ifc.res == ResultMode.unique && ifc.resCls == Cls.val && !a.regs.isEmpty &&
            a.cls != Cls.leaf && p.cls != Cls.leaf) with
        | false =>
          simp only [hc, Bool.false_eq_true, ↓reduceIte] at hstep
          split at hstep <;> (split at hstep <;> (obtain ⟨rfl, _⟩ := CM_pure_elim hstep; exact regs_natUnion_lt hacc (havs a haMem)))
        | true =>
          simp only [hc, ↓reduceIte] at hstep
          cases hd : destOf p (ifc.resCls != .val) with
          | share =>
            simp only [hd] at hstep
            obtain ⟨_, _, hr, _⟩ := CM_bind_elim hstep; rw [CM_refuseM_run] at hr; cases hr
          | once =>
            simp only [hd] at hstep
            obtain ⟨_, _, hr, _⟩ := CM_bind_elim hstep; rw [CM_refuseM_run] at hr; cases hr
          | lend =>
            simp only [hd] at hstep
            split at hstep <;> (obtain ⟨rfl, _⟩ := CM_pure_elim hstep; exact regs_natUnion_lt hacc (havs a haMem))
          | uniq _ =>
            simp only [hd] at hstep
            split at hstep <;> (obtain ⟨rfl, _⟩ := CM_pure_elim hstep; exact regs_natUnion_lt hacc (havs a haMem))
  obtain ⟨_, s₂, hfl2, h⟩ := CM_bind_elim h
  have hok1 : AStateOk (AState.ofCSt s₁) := by
    have happly : ∀ {α : Type} {m : CM α} {a : α}, StatePres m → m.run s = .ok (a, s₁) → AStateOk (AState.ofCSt s₁) :=
      fun hm hr => (hm s _ s₁ hok hr).1
    apply happly _ hfl1
    repeat (first | exact statePres_flowTo _ _ _ _ | sp_step)
  have hok2 : AStateOk (AState.ofCSt s₂) := by
    have happly : ∀ {α : Type} {m : CM α} {a : α}, StatePres m → m.run s₁ = .ok (a, s₂) → AStateOk (AState.ofCSt s₂) :=
      fun hm hr => (hm s₁ _ s₂ hok1 hr).1
    apply happly _ hfl2
    repeat sp_step
  cases h1 : (ifc.resCls == .irr || ifc.resCls == .imm) with
  | true =>
    simp only [h1, ↓reduceIte] at h
    obtain ⟨rfl, _⟩ := CM_pure_elim h; intro _ hm; cases hm
  | false =>
    simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    cases h2 : (ifc.resCls == .leaf) with
    | true =>
      simp only [h2, ↓reduceIte] at h
      obtain ⟨rfl, _⟩ := CM_pure_elim h
      intro r hm; split at hm <;> cases hm
    | false =>
      simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨inner, s₃, hin, h⟩ := CM_bind_elim h
      rw [innermost_run] at hin
      simp only [Except.ok.injEq, Prod.mk.injEq] at hin
      obtain ⟨rfl, rfl⟩ := hin
      have hinLt : s₂.regions.headD 1 < s₂.nextRegion := innermost_lt_of_AStateOk hok2
      cases hres : ifc.res with
      | unique =>
        simp only [hres] at h
        obtain ⟨rfl, _⟩ := CM_pure_elim h; intro _ hm; cases hm
      | uniqueBorrowed =>
        simp only [hres] at h
        obtain ⟨rfl, rfl⟩ := CM_pure_elim h
        exact regs_natUnion_lt (fun r hr => Nat.lt_of_lt_of_le (hregs1 r hr) hnr)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hinLt)
      | borrowed =>
        simp only [hres] at h
        obtain ⟨rfl, rfl⟩ := CM_pure_elim h
        exact regs_natUnion_lt (fun r hr => Nat.lt_of_lt_of_le (hregs1 r hr) hnr)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hinLt)
      | shared =>
        simp only [hres] at h
        obtain ⟨rfl, _⟩ := CM_pure_elim h
        exact fun r hr => Nat.lt_of_lt_of_le (hregs1 r hr) hnr

theorem papVal_regsOk {ifc : Iface} {avs : Array (Option AVal)} {w : String}
    {s s' : CSt} {rv : AVal}
    (hok : AStateOk (AState.ofCSt s))
    (havs : ∀ a, some a ∈ avs.toList → ValRegsOk s.nextRegion a)
    (h : (papVal ifc avs w).run s = .ok (rv, s')) :
    ValRegsOk s'.nextRegion rv := by
  have ⟨_, hle', _⟩ := statePres_papVal ifc avs w s rv s' hok h
  have hnr : s.nextRegion ≤ s'.nextRegion := hle'.2.1
  unfold papVal at h
  obtain ⟨⟨deps, regs, once⟩, s₁, hfl, h⟩ := CM_bind_elim h
  obtain ⟨rfl, _⟩ := CM_pure_elim h
  have hregs : ∀ r ∈ regs, r < s.nextRegion := by
    refine forIn_array_inv (I := fun x => ∀ r ∈ x.2.1, r < s.nextRegion) _ _ (fun pi _ acc st0 step st1 hacc hstep => ?_)
      (fun _ hm => by cases hm) hfl
    obtain ⟨p, i⟩ := pi
    dsimp only at hstep
    cases hai : avs[i]? with
    | none => simp only [hai] at hstep; obtain ⟨rfl, _⟩ := CM_pure_elim hstep; exact hacc
    | some oa =>
      cases oa with
      | none => simp only [hai] at hstep; obtain ⟨rfl, _⟩ := CM_pure_elim hstep; exact hacc
      | some a =>
        simp only [hai] at hstep
        have haMem : some a ∈ avs.toList := array_mem_toList_of_getElem?' hai
        cases hct : captureTransfers p.mode with
        | true =>
          simp only [hct, ↓reduceIte] at hstep
          obtain ⟨_, _, _, hstep⟩ := CM_bind_elim hstep
          obtain ⟨rfl, _⟩ := CM_pure_elim hstep
          exact regs_natUnion_lt hacc (havs a haMem)
        | false =>
          simp only [hct, Bool.false_eq_true, ↓reduceIte] at hstep
          obtain ⟨_, _, _, hstep⟩ := CM_bind_elim hstep
          obtain ⟨rfl, _⟩ := CM_pure_elim hstep
          exact regs_natUnion_lt hacc (havs a haMem)
  exact fun r hr => Nat.lt_of_lt_of_le (hregs r hr) hnr

theorem applyValue_regsOk {f a : AVal} {c : Cls} {w : String} {s s' : CSt} {rv : AVal}
    (hok : AStateOk (AState.ofCSt s))
    (hf : ValRegsOk s.nextRegion f) (ha : ValRegsOk s.nextRegion a)
    (h : (applyValue f a c w).run s = .ok (rv, s')) :
    ValRegsOk s'.nextRegion rv := by
  have ⟨_, hle', _⟩ := statePres_applyValue f a c w s rv s' hok h
  have hnr : s.nextRegion ≤ s'.nextRegion := hle'.2.1
  unfold applyValue at h
  obtain ⟨_, s₁, hv1, h⟩ := CM_bind_elim h
  have hs₁ := valid_state_eq hv1; subst s₁
  obtain ⟨fHasOnce, s₂, hfl, h⟩ := CM_bind_elim h
  have ⟨hok2, hle2, _⟩ : AStateOk (AState.ofCSt s₂) ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s₂) ∧ s₂.regions = s.regions := by
    have happly : ∀ {α : Type} {m : CM α} {a : α}, StatePres m → m.run s = .ok (a, s₂) →
        AStateOk (AState.ofCSt s₂) ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s₂) ∧ s₂.regions = s.regions :=
      fun hm hr => hm s _ s₂ hok hr
    apply happly _ hfl
    repeat sp_step
  obtain ⟨r, s₃, hcr, h⟩ := CM_bind_elim h
  have hrOk : ValRegsOk s₃.nextRegion r :=
    callResult_regsOk hok2 (fun a' hm => by
      simp only [List.mem_singleton, Option.some.injEq] at hm
      subst hm; exact ha.mono hle2.2.1) hcr
  obtain ⟨_, s₄, hv2, h⟩ := CM_bind_elim h
  have hs₄ := valid_state_eq hv2; subst s₄
  have hok3 := (statePres_callResult _ _ _ s₂ r s₃ hok2 hcr).1
  have hfin : ∀ (s₅ : CSt) (oo : Bool), s₃.nextRegion ≤ s₅.nextRegion →
      (pure ({ r with
        cls := c,
        regs := if c == .val then natUnion r.regs f.regs else r.regs,
        deps := if c == .val then natUnion (natUnion r.deps f.deps) a.deps else r.deps,
        onceOnly := oo } : AVal) : CM AVal).run s₅ =
        .ok (rv, s') → ValRegsOk s'.nextRegion rv := by
    intro s₅ oo hle5 hp
    obtain ⟨rfl, rfl⟩ := CM_pure_elim hp
    cases hc : (c == .val) with
    | true =>
      simp only [ValRegsOk, ↓reduceIte]
      exact regs_natUnion_lt (hrOk.mono hle5) (hf.mono hnr)
    | false =>
      simp only [ValRegsOk, Bool.false_eq_true, ↓reduceIte]
      exact hrOk.mono hle5
  cases honce : f.onceOnly with
  | true =>
    simp only [honce, ↓reduceIte] at h
    cases hsrc : f.src with
    | none => simp only [hsrc] at h; exact hfin s₃ _ (Nat.le_refl _) h
    | some x =>
      simp only [hsrc] at h
      obtain ⟨_, s₅, hset, h⟩ := CM_bind_elim h
      have hle5 := (statePres_setSt_dead x s₃ () s₅ hok3 hset).2.1
      exact hfin s₅ _ hle5.2.1 h
  | false =>
    simp only [honce, Bool.false_eq_true, ↓reduceIte] at h
    exact hfin s₃ _ (Nat.le_refl _) h

theorem bindInner_regsOk {m : BinderMode} {cls : Cls} {v : AVal} {reg : Nat} {w : String}
    {s s' : CSt} {bv : AVal}
    (hok : AStateOk (AState.ofCSt s))
    (hv : ValRegsOk s.nextRegion v) (hreg : reg < s.nextRegion)
    (h : (bindInner m cls v reg w).run s = .ok (bv, s')) :
    ValRegsOk s'.nextRegion bv := by
  have ⟨_, hle', _⟩ := statePres_bindInner m cls v reg w s bv s' hok h
  have hnr : s.nextRegion ≤ s'.nextRegion := hle'.2.1
  unfold bindInner at h
  have hcont : ∀ (s₁ : CSt), (do
      let r ← bindInnerBase m cls v reg w
      killSrc v
      pure r).run s₁ = .ok (bv, s') → ValRegsOk s'.nextRegion bv := by
    intro s₁ hc
    obtain ⟨r, _, hbase, hc⟩ := CM_bind_elim hc
    obtain ⟨_, _, _, hc⟩ := CM_bind_elim hc
    obtain ⟨rfl, _⟩ := CM_pure_elim hc
    unfold bindInnerBase at hbase
    obtain ⟨r0, _, hregs, hbase⟩ := CM_bind_elim hbase
    obtain ⟨rfl, _⟩ := CM_pure_elim hbase
    have hr0 : ValRegsOk s.nextRegion r0 := by
      unfold bindInnerRegs at hregs
      cases m with
      | erased =>
        obtain ⟨rfl, _⟩ := CM_pure_elim hregs; intro _ hm; cases hm
      | unique | uniqueBorrowed =>
        obtain ⟨_, _, _, hregs⟩ := CM_bind_elim hregs
        obtain ⟨rfl, _⟩ := CM_pure_elim hregs
        intro x hx; dsimp only at hx
        split at hx
        · exact regs_natUnion_lt hv (fun y hy => by simp only [List.mem_singleton] at hy; subst hy; exact hreg) x hx
        · cases hx
      | borrowed =>
        obtain ⟨_, _, _, hregs⟩ := CM_bind_elim hregs
        obtain ⟨rfl, _⟩ := CM_pure_elim hregs
        exact regs_natUnion_lt hv (fun y hy => by simp only [List.mem_singleton] at hy; subst hy; exact hreg)
      | once =>
        obtain ⟨_, _, _, hregs⟩ := CM_bind_elim hregs
        obtain ⟨rfl, _⟩ := CM_pure_elim hregs; exact hv
      | onceBorrowed =>
        obtain ⟨_, _, _, hregs⟩ := CM_bind_elim hregs
        obtain ⟨rfl, _⟩ := CM_pure_elim hregs
        exact regs_natUnion_lt hv (fun y hy => by simp only [List.mem_singleton] at hy; subst hy; exact hreg)
      | many =>
        obtain ⟨_, _, _, hregs⟩ := CM_bind_elim hregs
        obtain ⟨rfl, _⟩ := CM_pure_elim hregs; exact hv
    cases hlf : (cls == .leaf) with
    | true => simp only [↓reduceIte, ValRegsOk]; intro _ hm; cases hm
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hr0.mono hnr
  cases hm : (m.usage != .once) with
  | true =>
    simp only [hm, ↓reduceIte] at h
    obtain ⟨_, s₁, _, h⟩ := CM_bind_elim h
    exact hcont s₁ h
  | false =>
    simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
    exact hcont s h

theorem anCtor_regsOk {nP : Nat} {fields : Array Field} {avs : Array (Option AVal)} {c : Cls}
    {s s' : CSt} {rv : AVal}
    (hok : AStateOk (AState.ofCSt s))
    (havs : ∀ a, some a ∈ avs.toList → ValRegsOk s.nextRegion a)
    (h : (anCtor nP fields avs c).run s = .ok (rv, s')) :
    ValRegsOk s'.nextRegion rv := by
  have ⟨_, hle', _⟩ := statePres_anCtor nP fields avs c s rv s' hok h
  have hnr : s.nextRegion ≤ s'.nextRegion := hle'.2.1
  unfold anCtor at h
  by_cases hlt : avs.size < nP + fields.size
  · simp only [hlt, ↓reduceIte] at h
    obtain ⟨⟨deps, regs⟩, s₁, hfl, h⟩ := CM_bind_elim h
    obtain ⟨rfl, _⟩ := CM_pure_elim h
    have hregs : ∀ r ∈ regs, r < s.nextRegion := by
      refine forIn_array_inv (I := fun x => ∀ r ∈ x.2, r < s.nextRegion) _ _ (fun oa hoa acc st0 step st1 hacc hstep => ?_)
        (fun _ hm => by cases hm) hfl
      cases oa with
      | none => obtain ⟨rfl, _⟩ := CM_pure_elim hstep; exact hacc
      | some a =>
        obtain ⟨_, _, _, hstep⟩ := CM_bind_elim hstep
        obtain ⟨rfl, _⟩ := CM_pure_elim hstep
        exact regs_natUnion_lt hacc (havs a hoa)
    exact fun r hr => Nat.lt_of_lt_of_le (hregs r hr) hnr
  · simp only [hlt, ↓reduceIte] at h
    cases hk : ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).isEmpty with
    | true =>
      simp only [hk, ↓reduceIte] at h
      obtain ⟨rfl, _⟩ := CM_pure_elim h; intro _ hm; cases hm
    | false =>
      simp only [hk, Bool.false_eq_true, ↓reduceIte] at h
      cases hw : ((c == .imm || c == .leaf) &&
          ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).size == 1) with
      | true =>
        simp only [hw, ↓reduceIte] at h
        cases hav : avs[nP + ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2))[0]!]? with
        | none => simp only [hav] at h; obtain ⟨rfl, _⟩ := CM_pure_elim h; intro _ hm; cases hm
        | some oa =>
          cases oa with
          | none => simp only [hav] at h; obtain ⟨rfl, _⟩ := CM_pure_elim h; intro _ hm; cases hm
          | some v =>
            simp only [hav] at h
            obtain ⟨_, _, _, h⟩ := CM_bind_elim h
            obtain ⟨rfl, _⟩ := CM_pure_elim h
            exact (havs v (array_mem_toList_of_getElem?' hav)).mono hnr
      | false =>
        simp only [hw, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨⟨own, deps, regs⟩, s₁, hfl, h⟩ := CM_bind_elim h
        obtain ⟨rfl, _⟩ := CM_pure_elim h
        have hregs : ∀ r ∈ regs, r < s.nextRegion := by
          refine forIn_array_inv (I := fun x => ∀ r ∈ x.2.2, r < s.nextRegion) _ _
            (fun i _ acc st0 step st1 hacc hstep => ?_) (fun _ hm => by cases hm) hfl
          cases hai : avs[nP + i]? with
          | none => simp only [hai] at hstep; obtain ⟨rfl, _⟩ := CM_pure_elim hstep; exact hacc
          | some oa =>
            cases oa with
            | none => simp only [hai] at hstep; obtain ⟨rfl, _⟩ := CM_pure_elim hstep; exact hacc
            | some v =>
              cases hfi : fields[i]? with
              | none => simp only [hai, hfi] at hstep; obtain ⟨rfl, _⟩ := CM_pure_elim hstep; exact hacc
              | some f =>
                simp only [hai, hfi] at hstep
                obtain ⟨_, _, _, hstep⟩ := CM_bind_elim hstep
                cases ho : v.onceOnly with
                | true =>
                  simp only [ho, ↓reduceIte] at hstep
                  obtain ⟨_, _, hr, _⟩ := CM_bind_elim hstep; rw [CM_refuseM_run] at hr; cases hr
                | false =>
                  simp only [ho, Bool.false_eq_true, ↓reduceIte] at hstep
                  cases ha : Skel.unknown.admits v.skel with
                  | false =>
                    simp only [ha, Bool.false_eq_true, ↓reduceIte] at hstep
                    obtain ⟨_, _, hr, _⟩ := CM_bind_elim hstep; rw [CM_refuseM_run] at hr; cases hr
                  | true =>
                    simp only [ha, ↓reduceIte] at hstep
                    have hvOk := havs v (array_mem_toList_of_getElem?' hai)
                    cases hsh : (f.fmode == .shared) with
                    | true =>
                      simp only [hsh, ↓reduceIte] at hstep
                      cases hfilt : (v.regs.filter (· != 1)).isEmpty with
                      | false =>
                        simp only [hfilt, Bool.false_eq_true, ↓reduceIte] at hstep
                        obtain ⟨_, _, hr, _⟩ := CM_bind_elim hstep; rw [CM_refuseM_run] at hr; cases hr
                      | true =>
                        simp only [hfilt, ↓reduceIte] at hstep
                        obtain ⟨_, _, _, hstep⟩ := CM_bind_elim hstep
                        obtain ⟨rfl, _⟩ := CM_pure_elim hstep
                        exact regs_natUnion_lt hacc hvOk
                    | false =>
                      simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hstep
                      cases hvc : (v.cls == .val) with
                      | true =>
                        simp only [hvc, ↓reduceIte] at hstep
                        obtain ⟨_, _, _, hstep⟩ := CM_bind_elim hstep
                        obtain ⟨_, _, _, hstep⟩ := CM_bind_elim hstep
                        split at hstep <;> (split at hstep <;> (obtain ⟨rfl, _⟩ := CM_pure_elim hstep; exact regs_natUnion_lt hacc hvOk))
                      | false =>
                        simp only [hvc, Bool.false_eq_true, ↓reduceIte] at hstep
                        obtain ⟨rfl, _⟩ := CM_pure_elim hstep
                        exact regs_natUnion_lt hacc hvOk
        exact fun r hr => Nat.lt_of_lt_of_le (hregs r hr) hnr

theorem anProj_regsOk {P : Prog} {sRef : Ref} {i : Nat} {v : AVal} {c : Cls}
    {s s' : CSt} {rv : AVal}
    (hv : ValRegsOk s.nextRegion v)
    (h : (anProj P sRef i v c).run s = .ok (rv, s')) :
    ValRegsOk s'.nextRegion rv := by
  unfold anProj at h
  dsimp only at h
  generalize hfDef : (match (P.ctorsOf sRef)[0]? with
    | some ctor => match P.ctorOf? ctor with
      | some (_, _, _, fs) => fs
      | none => #[]
    | none => #[])[i]? = f? at h
  cases f? with
  | none =>
    obtain ⟨rfl, rfl⟩ := CM_pure_elim h; intro _ hm; cases hm
  | some f =>
    cases her : (f.mode == .erased) with
    | true =>
      simp only [her, ↓reduceIte] at h
      obtain ⟨_, _, hr, _⟩ := CM_bind_elim h; rw [CM_refuseM_run] at hr; cases hr
    | false =>
      simp only [her, Bool.false_eq_true, ↓reduceIte] at h
      cases h1 : (f.cls == .irr || c == .irr) with
      | true => simp only [h1, ↓reduceIte] at h; obtain ⟨rfl, rfl⟩ := CM_pure_elim h; intro _ hm; cases hm
      | false =>
        simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
        cases h2 : (c == .imm || c == .leaf) with
        | true => simp only [h2, ↓reduceIte] at h; obtain ⟨rfl, rfl⟩ := CM_pure_elim h; intro _ hm; cases hm
        | false =>
          simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
          cases h3 : (v.cls != .val) with
          | true => simp only [h3, ↓reduceIte] at h; obtain ⟨rfl, rfl⟩ := CM_pure_elim h; exact hv
          | false =>
            simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨rfl, rfl⟩ := CM_pure_elim h; exact hv

theorem paramVal_regsOk {p : Param} {s n : Nat} (hs : s < n) (h1 : 1 < n) :
    ValRegsOk n (paramVal p s) := by
  unfold paramVal
  cases p.mode with
  | erased | unique => intro _ hm; cases hm
  | uniqueBorrowed | borrowed | onceBorrowed =>
    intro r hr; dsimp only at hr
    cases hc : (p.cls == .val) with
    | false => simp [hc] at hr
    | true =>
      simp only [hc, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> assumption
  | many | once =>
    intro r hr; dsimp only at hr
    cases hc : (p.cls == .val) with
    | false => simp [hc] at hr
    | true =>
      simp only [hc, ↓reduceIte, List.mem_singleton] at hr
      subst hr; exact h1

theorem caseField_regsOk {P : Prog} {k : CaseInfo} {fields : Array Field} {mv : AVal}
    {consuming : Bool} {i n : Nat} (hmv : ValRegsOk n mv) :
    ValRegsOk n (caseField P k fields mv consuming i).1 := by
  unfold caseField
  split
  · intro _ hm; cases hm
  · split
    · intro _ hm; cases hm
    · split
      · intro _ hm; cases hm
      · split
        · intro _ hm; cases hm
        · split
          · exact hmv
          · split
            · intro _ hm; cases hm
            · split
              · exact hmv
              · split <;> exact hmv

theorem caseAltArgs_regsOk {P : Prog} {k : CaseInfo} {mv : AVal} {consuming : Bool}
    {j n : Nat} {ca : CaseAlt} (hmv : ValRegsOk n mv) :
    ∀ x ∈ caseAltArgs P k mv consuming j ca, ValRegsOk n x.1 := by
  intro x hx
  unfold caseAltArgs at hx
  rw [List.mem_map] at hx
  obtain ⟨fa, _, rfl⟩ := hx
  cases fa with
  | field i => exact caseField_regsOk hmv
  | irr => intro _ hm; cases hm
  | unit => intro _ hm; cases hm

/-! ## Section 3 (`F5a`): Mutual Fuel Soundness & `anDef_sound` -/

private theorem AStateLe_openReg (σ : AState) : AStateLe σ σ.openReg.2 := by
  refine ⟨Nat.le_refl _, Nat.le_succ _, ?_, fun _ _ => rfl, fun _ _ h => h⟩
  intro i hi
  dsimp only [AState.openReg]
  rw [Array.getElem?_eq_getElem hi]
  exact BSt.le_refl _

private theorem AStateLe_closeReg (σ : AState) (s : Nat) : AStateLe σ (σ.closeReg s) := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, ?_, fun _ _ => rfl, fun _ _ h => h⟩
  intro i hi
  dsimp only [AState.closeReg]
  rw [Array.getElem?_eq_getElem hi]
  exact BSt.le_refl _

theorem list_filter_bne_of_not_mem {s : Nat} :
    ∀ {l : List Nat}, s ∉ l → l.filter (· != s) = l
  | [], _ => rfl
  | x :: xs, hnot => by
    have hne : x ≠ s := fun h => hnot (h ▸ List.mem_cons_self ..)
    have hrest : s ∉ xs := fun h => hnot (List.mem_cons_of_mem _ h)
    have hbx : (x != s) = true := by simp [hne]
    simp only [List.filter_cons, hbx, ↓reduceIte, list_filter_bne_of_not_mem hrest]

theorem closeReg_cons_of_not_mem {s : Nat} {l : List Nat} (hnot : s ∉ l) :
    (s :: l).filter (· != s) = l := by
  have hbs : (s != s) = false := by simp
  simp only [List.filter_cons, hbs, Bool.false_eq_true, ↓reduceIte, list_filter_bne_of_not_mem hnot]

theorem AStateOk_restoreOwned (owned : List Nat) {σ : AState} (hok : AStateOk σ) :
    AStateOk (restoreOwned owned σ) := by
  obtain ⟨h1, h2, hnr, h1in, hnd, hlt⟩ := hok
  have hsz : ∀ (l : List Nat) (arr : Array BSt), (l.foldl (fun a x => a.set! x BSt.live) arr).size = arr.size := by
    intro l
    induction l with
    | nil => intro arr; rfl
    | cons x rest ih =>
      intro arr
      rw [List.foldl_cons, ih, Array.set!, Array.size_setIfInBounds]
  unfold restoreOwned
  refine ⟨by rw [hsz]; exact h1, by rw [hsz]; exact h2, hnr, h1in, hnd, hlt⟩

theorem AStateOk_set_nextRegion {σ : AState} {nr : Nat} (hok : AStateOk σ) (hle : σ.nextRegion ≤ nr) :
    AStateOk { σ with nextRegion := nr } := by
  obtain ⟨h1, h2, hnr, h1in, hnd, hlt⟩ := hok
  exact ⟨h1, h2, by dsimp only; omega, h1in, hnd, fun r hr => ⟨(hlt r hr).1, by have := (hlt r hr).2; dsimp only; omega⟩⟩

theorem AStateLe_set_nextRegion {σ₁ σ₂ : AState} {nr : Nat}
    (hle : AStateLe σ₁ σ₂) (hnr : σ₂.nextRegion ≤ nr) :
    AStateLe σ₁ { σ₂ with nextRegion := nr } := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hle
  exact ⟨h1, Nat.le_trans h2 hnr, h3, h4, h5⟩

theorem erasedAt_of_ifaceOf?_ge {d : RunDef} {ifc : Iface} {i : Nat}
    (hifc : ifaceOf? d = some ifc) (hge : ifc.params.size ≤ i) :
    erasedAt d i = false := by
  cases d with
  | body ps _ _ _ _ =>
    simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
    simp only [erasedAt]; rw [Array.getElem?_eq_none hge]; rfl
  | extern ps _ _ _ =>
    simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
    simp only [erasedAt]; rw [Array.getElem?_eq_none hge]; rfl
  | stuck ps _ _ _ =>
    simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
    simp only [erasedAt]; rw [Array.getElem?_eq_none hge]; rfl
  | ind _ | ctor _ _ _ _ | caseDef _ | prim _ => simp [ifaceOf?] at hifc

theorem ACallArgs_getElem?_isSome {P : Prog} {d? : Option RunDef} {env : List ABnd} :
    ∀ {off : Nat} {args : List Term} {σ σ' : AState} {avs : List (Option AVal)},
      ACallArgs P d? env off args σ avs σ' →
      ∀ (i : Nat) (oa : Option AVal), avs[i]? = some oa →
        (match d? with | some d => erasedAt d (off + i) | none => false) = false →
        oa.isSome = true
  | _, _, _, _, _, .nil, _, _, h, _ => by cases h
  | off, _, _, _, _, .consSkip hsk hrest, 0, oa, h, hne => by
    simp only [Nat.add_zero] at hne
    cases d? <;> simp_all
  | off, _, _, _, _, .consSkip _ hrest, i + 1, oa, h, hne => by
    simp only [List.getElem?_cons_succ] at h
    exact ACallArgs_getElem?_isSome hrest i oa h (by rwa [show off + 1 + i = off + (i + 1) by omega])
  | _, _, _, _, _, .consEval _ _ _, 0, oa, h, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; rfl
  | off, _, _, _, _, .consEval _ _ hrest, i + 1, oa, h, hne => by
    simp only [List.getElem?_cons_succ] at h
    exact ACallArgs_getElem?_isSome hrest i oa h (by rwa [show off + 1 + i = off + (i + 1) by omega])

theorem AEvals_length {P : Prog} {env : List ABnd} :
    ∀ {ts : List Term} {σ σ' : AState} {avs : List AVal},
      AEvals P env ts σ avs σ' → avs.length = ts.length
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons _ hrest => congrArg Nat.succ (AEvals_length hrest)

theorem termSpine_app_nonempty (f a : Term) (c : Cls) :
    (termSpine (.app f a c)).2.toList ≠ [] := by
  unfold termSpine
  simp only [Array.toList_push]
  intro h
  have := congrArg List.length h
  simp at this

/-! ### Loop Soundness Lemmas -/

theorem forIn_evals_sound {P : Prog} {n : Nat} {env : List ABnd}
    (ihTerm : ∀ {t s v s'}, AStateOk (AState.ofCSt s) → EnvRegsOk s.nextRegion env →
      (anTerm P n env t).run s = .ok (v, s') →
      ATerm P env t (AState.ofCSt s) v (AState.ofCSt s') ∧
      AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
      s'.regions = s.regions ∧ ValRegsOk s'.nextRegion v) :
    ∀ (ts : List Term) (acc out : Array AVal) (s s' : CSt),
      AStateOk (AState.ofCSt s) → EnvRegsOk s.nextRegion env →
      (forIn (m := CM) ts acc fun a avs => do
        pure (ForInStep.yield (avs.push (← anTerm P n env a)))).run s = .ok (out, s') →
      ∃ newAvs : List AVal,
        out.toList = acc.toList ++ newAvs ∧
        AEvals P env ts (AState.ofCSt s) newAvs (AState.ofCSt s') ∧
        AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
        s'.regions = s.regions ∧ (∀ v ∈ newAvs, ValRegsOk s'.nextRegion v) := by
  intro ts
  induction ts with
  | nil =>
    intro acc out s s' hok _ hf
    rw [List.forIn_nil] at hf
    obtain ⟨rfl, rfl⟩ := CM_pure_elim hf
    exact ⟨[], by simp, .nil, hok, AStateLe.refl _, rfl, fun _ h => by cases h⟩
  | cons t rest ih =>
    intro acc out s s' hok henv hf
    rw [List.forIn_cons] at hf
    obtain ⟨step, s₁, hstep, hf⟩ := CM_bind_elim hf
    obtain ⟨v, s₂, ht, hstep⟩ := CM_bind_elim hstep
    obtain ⟨rfl, hs2⟩ := CM_pure_elim hstep; subst s₂
    dsimp only at hf
    obtain ⟨hat, hok1, hle1, hreg1, hvOk⟩ := ihTerm hok henv ht
    obtain ⟨newRest, hout, hevals, hok2, hle2, hreg2, hrestOk⟩ :=
      ih (acc.push v) out s₁ s' hok1 (henv.mono hle1.2.1) hf
    refine ⟨v :: newRest, ?_, .cons hat hevals, hok2, hle1.trans hle2, hreg2.trans hreg1, ?_⟩
    · rw [hout, Array.toList_push, List.append_assoc]; rfl
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hvOk.mono hle2.2.1
      · exact hrestOk x hmem

theorem forIn_applyZipIdx_sound {c : Cls} :
    ∀ (l : List AVal) (off : Nat) (f out : AVal) (s s' : CSt),
      AStateOk (AState.ofCSt s) → ValRegsOk s.nextRegion f →
      (∀ a ∈ l, ValRegsOk s.nextRegion a) →
      (forIn (m := CM) (l.zipIdx off) f fun (av, i) f => do
        pure (ForInStep.yield (← applyValue f av (if i + 1 == off + l.length then c else .val) "an application"))).run s =
        .ok (out, s') →
      (l ≠ [] → AApps f l c (AState.ofCSt s) out (AState.ofCSt s')) ∧
      (l = [] → out = f ∧ s' = s) ∧
      AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
      s'.regions = s.regions ∧ ValRegsOk s'.nextRegion out := by
  intro l
  induction l with
  | nil =>
    intro off f out s s' hok hf _ hfl
    simp only [List.zipIdx_nil, List.forIn_nil] at hfl
    obtain ⟨rfl, rfl⟩ := CM_pure_elim hfl
    exact ⟨fun h => False.elim (h rfl), fun _ => ⟨rfl, rfl⟩, hok, AStateLe.refl _, rfl, hf⟩
  | cons a rest ih =>
    intro off f out s s' hok hf hl hfl
    simp only [List.zipIdx_cons, List.forIn_cons] at hfl
    obtain ⟨step, s₁, hstep, hfl⟩ := CM_bind_elim hfl
    obtain ⟨g, s₂, happ, hstep⟩ := CM_bind_elim hstep
    obtain ⟨rfl, hs2⟩ := CM_pure_elim hstep; subst s₂
    dsimp only at hfl
    have haOk : ValRegsOk s.nextRegion a := hl a (List.mem_cons_self ..)
    obtain ⟨hok1, hle1, hreg1⟩ := statePres_applyValue f a _ "an application" s g s₁ hok happ
    have hgOk : ValRegsOk s₁.nextRegion g := applyValue_regsOk hok hf haOk happ
    have hruns : Runs (applyValue f a (if off + 1 == off + (a :: rest).length then c else .val) "an application")
        (AState.ofCSt s) g (AState.ofCSt s₁) :=
      (stepIndep_applyValue f a _ "an application").toRuns happ
    have hshift : off + (a :: rest).length = (off + 1) + rest.length := by simp; omega
    have hfl' : (forIn (m := CM) (rest.zipIdx (off + 1)) g fun (av, i) f => do
        pure (ForInStep.yield (← applyValue f av (if i + 1 == (off + 1) + rest.length then c else .val) "an application"))).run s₁ =
        .ok (out, s') := by
      simpa only [hshift] using hfl
    obtain ⟨happsR, hnilR, hok2, hle2, hreg2, houtOk⟩ :=
      ih (off + 1) g out s₁ s' hok1 hgOk (fun x hx => (hl x (List.mem_cons_of_mem _ hx)).mono hle1.2.1) hfl'
    refine ⟨fun _ => ?_, (fun h => by cases h), hok2, hle1.trans hle2, hreg2.trans hreg1, houtOk⟩
    cases rest with
    | nil =>
      obtain ⟨rfl, rfl⟩ := hnilR rfl
      have hcond : (off + 1 == off + [a].length) = true := by simp
      simp only [hcond, ↓reduceIte] at happ hruns
      have hcls := applyValue_cls happ
      have hgeq : ({ out with cls := c } : AVal) = out := by cases out; simp at hcls; subst hcls; rfl
      rw [← hgeq]
      exact .consLast hruns
    | cons a2 rest2 =>
      have hcond : (off + 1 == off + (a :: a2 :: rest2).length) = false := by
        simp only [List.length_cons, beq_eq_false_iff_ne]; omega
      simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hruns
      exact .consMore hruns (happsR (by simp))

theorem forIn_applyOptZipIdx_sound {k : Nat} {c : Cls} :
    ∀ (l : List (Option AVal)) (off : Nat) (f out : AVal) (s s' : CSt),
      AStateOk (AState.ofCSt s) → ValRegsOk s.nextRegion f →
      (∀ oa ∈ l, oa.isSome = true) →
      (∀ a, some a ∈ l → ValRegsOk s.nextRegion a) →
      (forIn (m := CM) (l.zipIdx off) f fun (oa, i) f =>
        match oa with
        | some av => do
          pure (ForInStep.yield (← applyValue f av (if k + i + 1 == k + off + l.length then c else .val) "an application"))
        | none => pure (ForInStep.yield f)).run s = .ok (out, s') →
      AApps f (l.filterMap id) c (AState.ofCSt s) { out with cls := c } (AState.ofCSt s') ∧
      AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
      s'.regions = s.regions ∧ ValRegsOk s'.nextRegion { out with cls := c } := by
  intro l
  induction l with
  | nil =>
    intro off f out s s' hok hf _ _ hfl
    simp only [List.zipIdx_nil, List.forIn_nil] at hfl
    obtain ⟨rfl, rfl⟩ := CM_pure_elim hfl
    exact ⟨.nil, hok, AStateLe.refl _, rfl, hf⟩
  | cons oa rest ih =>
    intro off f out s s' hok hf hsome hl hfl
    have hoa : oa.isSome = true := hsome oa (List.mem_cons_self ..)
    cases oa with
    | none => simp at hoa
    | some av =>
      simp only [List.zipIdx_cons, List.forIn_cons] at hfl
      obtain ⟨step, s₁, hstep, hfl⟩ := CM_bind_elim hfl
      obtain ⟨g, s₂, happ, hstep⟩ := CM_bind_elim hstep
      obtain ⟨rfl, hs2⟩ := CM_pure_elim hstep; subst s₂
      dsimp only at hfl
      have havOk : ValRegsOk s.nextRegion av := hl av (List.mem_cons_self ..)
      obtain ⟨hok1, hle1, hreg1⟩ := statePres_applyValue f av _ "an application" s g s₁ hok happ
      have hgOk : ValRegsOk s₁.nextRegion g := applyValue_regsOk hok hf havOk happ
      have hruns : Runs (applyValue f av (if k + off + 1 == k + off + (some av :: rest).length then c else .val) "an application")
          (AState.ofCSt s) g (AState.ofCSt s₁) :=
        (stepIndep_applyValue f av _ "an application").toRuns happ
      have hshift : k + off + (some av :: rest).length = k + (off + 1) + rest.length := by simp; omega
      have hfl' : (forIn (m := CM) (rest.zipIdx (off + 1)) g fun (oa, i) f =>
          match oa with
          | some av => do
            pure (ForInStep.yield (← applyValue f av (if k + i + 1 == k + (off + 1) + rest.length then c else .val) "an application"))
          | none => pure (ForInStep.yield f)).run s₁ = .ok (out, s') := by
        simpa only [hshift] using hfl
      obtain ⟨happsR, hok2, hle2, hreg2, houtOk⟩ :=
        ih (off + 1) g out s₁ s' hok1 hgOk
          (fun x hx => hsome x (List.mem_cons_of_mem _ hx))
          (fun a ha => (hl a (List.mem_cons_of_mem _ ha)).mono hle1.2.1) hfl'
      refine ⟨?_, hok2, hle1.trans hle2, hreg2.trans hreg1, houtOk⟩
      cases rest with
      | nil =>
        simp only [List.zipIdx_nil, List.forIn_nil] at hfl'
        obtain ⟨rfl, rfl⟩ := CM_pure_elim hfl'
        have hcond : (k + off + 1 == k + off + [some av].length) = true := by simp
        simp only [hcond, ↓reduceIte] at hruns
        simpa using AApps.consLast hruns
      | cons oa2 rest2 =>
        have hoa2 : oa2.isSome = true := hsome oa2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        cases oa2 with
        | none => simp at hoa2
        | some av2 =>
          have hcond : (k + off + 1 == k + off + (some av :: some av2 :: rest2).length) = false := by
            simp only [List.length_cons, beq_eq_false_iff_ne]; omega
          simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hruns
          simpa using AApps.consMore hruns happsR

theorem forIn_applyAlt_sound :
    ∀ (l : List (AVal × Bool × Bool)) (f out : AVal) (s s' : CSt),
      l ≠ [] →
      AStateOk (AState.ofCSt s) → ValRegsOk s.nextRegion f →
      (∀ x ∈ l, ValRegsOk s.nextRegion x.1) →
      (forIn (m := CM) l f fun (av, _, _) f => do
        pure (ForInStep.yield (← applyValue f av .val "an alternative"))).run s = .ok (out, s') →
      AApps f (l.map (·.1)) .val (AState.ofCSt s) out (AState.ofCSt s') ∧
      AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
      s'.regions = s.regions ∧ ValRegsOk s'.nextRegion out := by
  intro l
  induction l with
  | nil => intro _ _ _ _ hne; exact False.elim (hne rfl)
  | cons x rest ih =>
    obtain ⟨av, er, fc⟩ := x
    intro f out s s' _ hok hf hl hfl
    rw [List.forIn_cons] at hfl
    obtain ⟨step, s₁, hstep, hfl⟩ := CM_bind_elim hfl
    obtain ⟨g, s₂, happ, hstep⟩ := CM_bind_elim hstep
    obtain ⟨rfl, hs2⟩ := CM_pure_elim hstep; subst s₂
    dsimp only at hfl
    have havOk : ValRegsOk s.nextRegion av := hl (av, er, fc) (List.mem_cons_self ..)
    obtain ⟨hok1, hle1, hreg1⟩ := statePres_applyValue f av .val "an alternative" s g s₁ hok happ
    have hgOk : ValRegsOk s₁.nextRegion g := applyValue_regsOk hok hf havOk happ
    have hruns : Runs (applyValue f av .val "an application") (AState.ofCSt s) g (AState.ofCSt s₁) :=
      applyValue_w_indep ((stepIndep_applyValue f av .val "an alternative").toRuns happ)
    cases rest with
    | nil =>
      rw [List.forIn_nil] at hfl
      obtain ⟨rfl, rfl⟩ := CM_pure_elim hfl
      have hcls := applyValue_cls happ
      have hgeq : ({ g with cls := .val } : AVal) = g := by cases g; simp at hcls; subst hcls; rfl
      refine ⟨?_, hok1, hle1, hreg1, hgOk⟩
      rw [← hgeq]; exact .consLast hruns
    | cons x2 rest2 =>
      obtain ⟨happsR, hok2, hle2, hreg2, houtOk⟩ :=
        ih g out s₁ s' (by simp) hok1 hgOk
          (fun y hy => (hl y (List.mem_cons_of_mem _ hy)).mono hle1.2.1) hfl
      exact ⟨.consMore hruns happsR, hok2, hle1.trans hle2, hreg2.trans hreg1, houtOk⟩

theorem forIn_callArgs_sound {P : Prog} {d : RunDef} {n : Nat} {env : List ABnd}
    (ihTerm : ∀ {t s v s'}, AStateOk (AState.ofCSt s) → EnvRegsOk s.nextRegion env →
      (anTerm P n env t).run s = .ok (v, s') →
      ATerm P env t (AState.ofCSt s) v (AState.ofCSt s') ∧
      AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
      s'.regions = s.regions ∧ ValRegsOk s'.nextRegion v) :
    ∀ (ts : List Term) (off : Nat) (acc out : Array (Option AVal)) (s s' : CSt),
      AStateOk (AState.ofCSt s) → EnvRegsOk s.nextRegion env →
      (forIn (m := CM) (ts.zipIdx off) acc fun (a, i) avs => do
        pure (ForInStep.yield (avs.push (← if erasedAt d i then pure none else some <$> anTerm P n env a)))).run s =
        .ok (out, s') →
      ∃ newAvs : List (Option AVal),
        out.toList = acc.toList ++ newAvs ∧
        ACallArgs P (some d) env off ts (AState.ofCSt s) newAvs (AState.ofCSt s') ∧
        AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
        s'.regions = s.regions ∧ (∀ a, some a ∈ newAvs → ValRegsOk s'.nextRegion a) := by
  intro ts
  induction ts with
  | nil =>
    intro off acc out s s' hok _ hfl
    simp only [List.zipIdx_nil, List.forIn_nil] at hfl
    obtain ⟨rfl, rfl⟩ := CM_pure_elim hfl
    exact ⟨[], by simp, .nil, hok, AStateLe.refl _, rfl, fun _ h => by cases h⟩
  | cons t rest ih =>
    intro off acc out s s' hok henv hfl
    simp only [List.zipIdx_cons, List.forIn_cons] at hfl
    obtain ⟨step, s₁, hstep, hfl⟩ := CM_bind_elim hfl
    cases hsk : erasedAt d off with
    | true =>
      simp only [hsk, ↓reduceIte] at hstep
      obtain ⟨oa, s₂, hp, hstep⟩ := CM_bind_elim hstep
      obtain ⟨rfl, hs2⟩ := CM_pure_elim hp; subst s₂
      obtain ⟨rfl, hs1⟩ := CM_pure_elim hstep; subst s₁
      dsimp only at hfl
      obtain ⟨newRest, hout, hca, hok2, hle2, hreg2, hrestOk⟩ :=
        ih (off + 1) (acc.push none) out s s' hok henv hfl
      refine ⟨none :: newRest, ?_, .consSkip hsk hca, hok2, hle2, hreg2, ?_⟩
      · rw [hout, Array.toList_push, List.append_assoc]; rfl
      · intro a ha
        rcases List.mem_cons.mp ha with hEq | hmem
        · cases hEq
        · exact hrestOk a hmem
    | false =>
      simp only [hsk, Bool.false_eq_true, ↓reduceIte] at hstep
      obtain ⟨oa, s₂, hmap, hstep⟩ := CM_bind_elim hstep
      obtain ⟨v, ht, rfl⟩ := CM_map_elim hmap
      obtain ⟨rfl, hs2⟩ := CM_pure_elim hstep; subst s₂
      dsimp only at hfl
      obtain ⟨hat, hok1, hle1, hreg1, hvOk⟩ := ihTerm hok henv ht
      obtain ⟨newRest, hout, hca, hok2, hle2, hreg2, hrestOk⟩ :=
        ih (off + 1) (acc.push (some v)) out s₁ s' hok1 (henv.mono hle1.2.1) hfl
      refine ⟨some v :: newRest, ?_, .consEval hsk hat hca, hok2, hle1.trans hle2, hreg2.trans hreg1, ?_⟩
      · rw [hout, Array.toList_push, List.append_assoc]; rfl
      · intro a ha
        rcases List.mem_cons.mp ha with hEq | hmem
        · injection hEq with hEq; subst hEq; exact hvOk.mono hle2.2.1
        · exact hrestOk a hmem

theorem forIn_primArgs_sound :
    ∀ (l : List (Option AVal)) (deps₀ regs₀ deps regs : List Nat) (s s' : CSt),
      AStateOk (AState.ofCSt s) →
      (∀ r ∈ regs₀, r < s.nextRegion) →
      (∀ a, some a ∈ l → ValRegsOk s.nextRegion a) →
      (forIn (m := CM) l (deps₀, regs₀) fun a __s =>
        match a with
        | some a =>
          if (a.cls == .val) = true then do
            flowTo .share .unknown a "a primitive's argument"
            pure (ForInStep.yield (natUnion __s.1 a.deps, natUnion __s.2 a.regs))
          else do
            valid a "a primitive's argument"
            pure (ForInStep.yield (__s.1, __s.2))
        | _ => pure (ForInStep.yield (__s.1, __s.2))).run s = .ok ((deps, regs), s') →
      APrimArgs l (AState.ofCSt s) deps₀ regs₀ deps regs (AState.ofCSt s') ∧
      AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
      s'.regions = s.regions ∧ (∀ r ∈ regs, r < s'.nextRegion) := by
  intro l
  induction l with
  | nil =>
    intro deps₀ regs₀ deps regs s s' hok hregs₀ _ hfl
    rw [List.forIn_nil] at hfl
    obtain ⟨hpair, rfl⟩ := CM_pure_elim hfl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    exact ⟨.nil, hok, AStateLe.refl _, rfl, hregs₀⟩
  | cons oa rest ih =>
    intro deps₀ regs₀ deps regs s s' hok hregs₀ hl hfl
    rw [List.forIn_cons] at hfl
    obtain ⟨step, s₁, hstep, hfl⟩ := CM_bind_elim hfl
    cases oa with
    | none =>
      obtain ⟨rfl, rfl⟩ := CM_pure_elim hstep
      obtain ⟨hpa, hok2, hle2, hreg2, hregs2⟩ :=
        ih deps₀ regs₀ deps regs s s' hok hregs₀ (fun a ha => hl a (List.mem_cons_of_mem _ ha)) hfl
      exact ⟨.consNone hpa, hok2, hle2, hreg2, hregs2⟩
    | some a =>
      have haOk := hl a (List.mem_cons_self ..)
      cases hvc : (a.cls == .val) with
      | true =>
        simp only [hvc, ↓reduceIte] at hstep
        obtain ⟨_, s₂, hft, hstep⟩ := CM_bind_elim hstep
        obtain ⟨rfl, hs2⟩ := CM_pure_elim hstep; subst s₂
        dsimp only at hfl
        obtain ⟨hok1, hle1, hreg1⟩ := statePres_flowTo .share .unknown a "a primitive's argument" s () s₁ hok hft
        have hruns := (stepIndep_flowTo .share .unknown a "a primitive's argument").toRuns hft
        obtain ⟨hpa, hok2, hle2, hreg2, hregs2⟩ :=
          ih (natUnion deps₀ a.deps) (natUnion regs₀ a.regs) deps regs s₁ s' hok1
            (regs_natUnion_lt (fun r hr => Nat.lt_of_lt_of_le (hregs₀ r hr) hle1.2.1) (haOk.mono hle1.2.1))
            (fun a' ha' => (hl a' (List.mem_cons_of_mem _ ha')).mono hle1.2.1) hfl
        have hcls : a.cls = .val := by
          cases hc : a.cls
          · exact absurd (hc ▸ hvc) (by decide)
          · exact absurd (hc ▸ hvc) (by decide)
          · exact absurd (hc ▸ hvc) (by decide)
          · rfl
        exact ⟨.consVal hcls hruns hpa, hok2, hle1.trans hle2, hreg2.trans hreg1, hregs2⟩
      | false =>
        simp only [hvc, Bool.false_eq_true, ↓reduceIte] at hstep
        obtain ⟨_, s₂, hv, hstep⟩ := CM_bind_elim hstep
        obtain ⟨rfl, hs2⟩ := CM_pure_elim hstep; subst s₂
        dsimp only at hfl
        have hs₁ := valid_state_eq hv; subst s₁
        have hruns := (stepIndep_valid a "a primitive's argument").toRuns hv
        obtain ⟨hpa, hok2, hle2, hreg2, hregs2⟩ :=
          ih deps₀ regs₀ deps regs s s' hok hregs₀ (fun a' ha' => hl a' (List.mem_cons_of_mem _ ha')) hfl
        have hne : a.cls ≠ .val := by intro hEq; rw [hEq] at hvc; cases hvc
        exact ⟨.consNonVal hne hruns hpa, hok2, hle2, hreg2, hregs2⟩

theorem forIn_caps_sound {env : List ABnd} :
    ∀ (l : List Nat) (deps₀ regs₀ owned₀ deps regs owned : List Nat) (s s' : CSt),
      AStateOk (AState.ofCSt s) → EnvRegsOk s.nextRegion env →
      (∀ r ∈ regs₀, r < s.nextRegion) →
      (forIn (m := CM) l (deps₀, regs₀, owned₀) fun i (deps, regs, owned) => do
        let some b := env[i]? | refuseM "a capture out of scope"
        let v ← readVar env i
        if captureTransfers b.mode then
          flowTo (.uniq b.mode.isBorrowed) v.skel v "a capture"
          pure (ForInStep.yield (deps, natUnion regs v.regs, b.id :: owned))
        else
          flowTo .share v.skel v "a capture"
          pure (ForInStep.yield (natUnion deps v.deps, natUnion regs v.regs, owned))).run s =
        .ok ((deps, regs, owned), s') →
      ACaps env l (AState.ofCSt s) deps₀ regs₀ owned₀ deps regs owned (AState.ofCSt s') ∧
      AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
      s'.regions = s.regions ∧ (∀ r ∈ regs, r < s'.nextRegion) := by
  intro l
  induction l with
  | nil =>
    intro deps₀ regs₀ owned₀ deps regs owned s s' hok _ hregs₀ hfl
    rw [List.forIn_nil] at hfl
    obtain ⟨hpair, rfl⟩ := CM_pure_elim hfl
    obtain ⟨rfl, hpair2⟩ := Prod.mk.inj hpair
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair2
    exact ⟨.nil, hok, AStateLe.refl _, rfl, hregs₀⟩
  | cons i rest ih =>
    intro deps₀ regs₀ owned₀ deps regs owned s s' hok henv hregs₀ hfl
    rw [List.forIn_cons] at hfl
    obtain ⟨step, s₁, hstep, hfl⟩ := CM_bind_elim hfl
    cases hei : env[i]? with
    | none => simp only [hei] at hstep; rw [CM_refuseM_run] at hstep; cases hstep
    | some b =>
      simp only [hei] at hstep
      obtain ⟨v, s₂, hrv, hstep⟩ := CM_bind_elim hstep
      obtain ⟨hs₂, b', hb', hvregs⟩ := readVar_props hrv
      subst s₂
      have hbeq : b' = b := by rw [hei] at hb'; exact Option.some.inj hb'.symm
      subst b'
      have hvOk : ValRegsOk s.nextRegion v := by
        intro r hr; rw [hvregs] at hr
        exact henv b (List.mem_of_getElem? hei) r hr
      have hrvRuns := (stepIndep_readVar env i).toRuns hrv
      cases hct : captureTransfers b.mode with
      | true =>
        simp only [hct, ↓reduceIte] at hstep
        obtain ⟨_, s₃, hft, hstep⟩ := CM_bind_elim hstep
        obtain ⟨rfl, hs3⟩ := CM_pure_elim hstep; subst s₃
        dsimp only at hfl
        obtain ⟨hok1, hle1, hreg1⟩ := statePres_flowTo (.uniq b.mode.isBorrowed) v.skel v "a capture" s () s₁ hok hft
        have hftRuns := (stepIndep_flowTo (.uniq b.mode.isBorrowed) v.skel v "a capture").toRuns hft
        obtain ⟨hcaps, hok2, hle2, hreg2, hregs2⟩ :=
          ih deps₀ (natUnion regs₀ v.regs) (b.id :: owned₀) deps regs owned s₁ s' hok1 (henv.mono hle1.2.1)
            (regs_natUnion_lt (fun r hr => Nat.lt_of_lt_of_le (hregs₀ r hr) hle1.2.1) (hvOk.mono hle1.2.1)) hfl
        exact ⟨.consUniq hei hrvRuns hct hftRuns hcaps, hok2, hle1.trans hle2, hreg2.trans hreg1, hregs2⟩
      | false =>
        simp only [hct, Bool.false_eq_true, ↓reduceIte] at hstep
        obtain ⟨_, s₃, hft, hstep⟩ := CM_bind_elim hstep
        obtain ⟨rfl, hs3⟩ := CM_pure_elim hstep; subst s₃
        dsimp only at hfl
        obtain ⟨hok1, hle1, hreg1⟩ := statePres_flowTo .share v.skel v "a capture" s () s₁ hok hft
        have hftRuns := (stepIndep_flowTo .share v.skel v "a capture").toRuns hft
        obtain ⟨hcaps, hok2, hle2, hreg2, hregs2⟩ :=
          ih (natUnion deps₀ v.deps) (natUnion regs₀ v.regs) owned₀ deps regs owned s₁ s' hok1 (henv.mono hle1.2.1)
            (regs_natUnion_lt (fun r hr => Nat.lt_of_lt_of_le (hregs₀ r hr) hle1.2.1) (hvOk.mono hle1.2.1)) hfl
        exact ⟨.consShare hei hrvRuns hct hftRuns hcaps, hok2, hle1.trans hle2, hreg2.trans hreg1, hregs2⟩

theorem forIn_restoreOwned_run :
    ∀ (owned : List Nat) (s : CSt),
      (forIn (m := CM) owned PUnit.unit fun x _ => do
        setSt x BSt.live
        pure (ForInStep.yield PUnit.unit)).run s =
      .ok (PUnit.unit, (restoreOwned owned (AState.ofCSt s)).toCSt s.steps)
  | [], _ => rfl
  | x :: rest, s => by
    rw [List.forIn_cons, CM_bind_run, CM_bind_run, setSt_run]
    dsimp only
    rw [CM_pure_run]
    dsimp only
    rw [forIn_restoreOwned_run rest { s with st := s.st.set! x BSt.live }]
    rfl

theorem forIn_consumed_props :
    ∀ (owned : List Nat) (acc out : Bool) (s s' : CSt),
      (forIn (m := CM) owned acc fun x c => do
        if (← stOf x) == BSt.dead then pure (ForInStep.yield true)
        else pure (ForInStep.yield c)).run s = .ok (out, s') →
      s' = s ∧ (acc = true → out = true) ∧
      (∀ x ∈ owned, s.st[x]?.getD .dead = .dead → out = true) := by
  intro owned
  induction owned with
  | nil =>
    intro acc out s s' hf
    rw [List.forIn_nil] at hf
    obtain ⟨rfl, rfl⟩ := CM_pure_elim hf
    exact ⟨rfl, id, fun _ hm => by cases hm⟩
  | cons x rest ih =>
    intro acc out s s' hf
    rw [List.forIn_cons] at hf
    obtain ⟨step, s₁, hstep, hf⟩ := CM_bind_elim hf
    obtain ⟨b, s₂, hst, hstep⟩ := CM_bind_elim hstep
    rw [stOf_run] at hst
    simp only [Except.ok.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    cases hd : (s.st[x]?.getD BSt.dead == BSt.dead) with
    | true =>
      simp only [hd, ↓reduceIte] at hstep
      obtain ⟨rfl, rfl⟩ := CM_pure_elim hstep
      obtain ⟨hs', htrue, hall⟩ := ih true out s s' hf
      refine ⟨hs', fun _ => htrue rfl, fun y hy hyd => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hrest
      · exact htrue rfl
      · exact hall y hrest hyd
    | false =>
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at hstep
      obtain ⟨rfl, rfl⟩ := CM_pure_elim hstep
      obtain ⟨hs', htrue, hall⟩ := ih acc out s s' hf
      refine ⟨hs', htrue, fun y hy hyd => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hrest
      · rw [hyd] at hd; cases hd
      · exact hall y hrest hyd

/-! ### `anCase` Join Lemmas -/

def joinBSt (a b : BSt) : BSt :=
  if a == BSt.dead || b == BSt.dead then BSt.dead
  else if a == BSt.shared || b == BSt.shared then BSt.shared
  else BSt.live

theorem BSt_le_joinBSt_left (a b : BSt) : BSt.le a (joinBSt a b) := by
  cases a <;> cases b <;> exact trivial

theorem BSt_le_joinBSt_right (a b : BSt) : BSt.le b (joinBSt a b) := by
  cases a <;> cases b <;> exact trivial

theorem forIn_stateJoin_range (post : CSt) (n : Nat) :
    ∀ (len start : Nat) (st st' : Array BSt × Array Bool) (s s' : CSt),
      st.1.size = n → st.2.size = n → start + len ≤ n →
      n ≤ post.st.size → n ≤ post.spent.size →
      (forIn (m := CM) (List.range' start len 1) st fun i __s =>
        if post.spent[i]! = true then
          pure (ForInStep.yield (__s.1.set! i (joinBSt __s.1[i]! post.st[i]!), __s.2.set! i true))
        else
          pure (ForInStep.yield (__s.1.set! i (joinBSt __s.1[i]! post.st[i]!), __s.2))).run s = .ok (st', s') →
      s' = s ∧ st'.1.size = n ∧ st'.2.size = n ∧
      (∀ j, j < n →
        match st.1[j]?, st'.1[j]? with
        | some b1, some b2 => BSt.le b1 b2
        | _, _ => False) ∧
      (∀ j, start ≤ j → j < start + len →
        match post.st[j]?, st'.1[j]? with
        | some bp, some b2 => BSt.le bp b2
        | _, _ => False) ∧
      (∀ j, j < n → st.2[j]? = some true → st'.2[j]? = some true) ∧
      (∀ j, start ≤ j → j < start + len → post.spent[j]? = some true → st'.2[j]? = some true) := by
  intro len
  induction len with
  | zero =>
    intro start st st' s s' hsz1 hsz2 _ _ _ hf
    rw [List.range'_zero, List.forIn_nil] at hf
    obtain ⟨rfl, rfl⟩ := CM_pure_elim hf
    refine ⟨rfl, hsz1, hsz2, ?_, fun _ h1 h2 => by omega, fun _ _ h => h, fun _ h1 h2 => by omega⟩
    intro j hj
    rw [Array.getElem?_eq_getElem (by omega)]
    exact BSt.le_refl _
  | succ len ih =>
    intro start st st' s s' hsz1 hsz2 hbound hpst hpsp hf
    rw [List.range'_succ, List.forIn_cons] at hf
    obtain ⟨step, s₁, hstep, hf⟩ := CM_bind_elim hf
    have hstepEq : step = ForInStep.yield
        (st.1.set! start (joinBSt st.1[start]! post.st[start]!),
         if post.spent[start]! then st.2.set! start true else st.2) ∧ s₁ = s := by
      cases hps : post.spent[start]! with
      | true =>
        simp only [hps, ↓reduceIte] at hstep ⊢
        obtain ⟨rfl, rfl⟩ := CM_pure_elim hstep; exact ⟨rfl, rfl⟩
      | false =>
        simp only [hps, Bool.false_eq_true, ↓reduceIte] at hstep ⊢
        obtain ⟨rfl, rfl⟩ := CM_pure_elim hstep; exact ⟨rfl, rfl⟩
    obtain ⟨rfl, hs1⟩ := hstepEq
    subst s₁
    have hlt : start < n := by omega
    have hsz1' : (st.1.set! start (joinBSt st.1[start]! post.st[start]!)).size = n := by
      simp [Array.set!, hsz1]
    have hsz2' : (if post.spent[start]! then st.2.set! start true else st.2).size = n := by
      cases post.spent[start]! <;> simp [Array.set!, hsz2]
    obtain ⟨hs', hszOut1, hszOut2, hmonoSt, hpostSt, hmonoSp, hpostSp⟩ :=
      ih (start + 1) _ st' s s' hsz1' hsz2' (by omega) hpst hpsp hf
    have hstepSt : ∀ j, j < n →
        match st.1[j]?, (st.1.set! start (joinBSt st.1[start]! post.st[start]!))[j]? with
        | some b1, some b2 => BSt.le b1 b2
        | _, _ => False := by
      intro j hj
      have hj1 : j < st.1.size := by omega
      have hj2 : j < (st.1.set! start (joinBSt st.1[start]! post.st[start]!)).size := by rw [hsz1']; exact hj
      rw [Array.getElem?_eq_getElem hj1, Array.getElem?_eq_getElem hj2]
      by_cases heq : start = j
      · subst heq
        simp only [Array.set!, Array.getElem_setIfInBounds_self]
        have hbang : st.1[start]! = st.1[start] := getElem!_pos st.1 start hj1
        rw [hbang]; exact BSt_le_joinBSt_left _ _
      · simp only [Array.set!]
        rw [Array.getElem_setIfInBounds_ne (h := heq)]
        exact BSt.le_refl _
    have hstepSp : ∀ j, j < n → st.2[j]? = some true →
        (if post.spent[start]! then st.2.set! start true else st.2)[j]? = some true := by
      intro j hj hsp
      cases hps : post.spent[start]! with
      | false => simpa [hps] using hsp
      | true =>
        simp only [↓reduceIte]
        have hj2 : j < (st.2.set! start true).size := by rw [Array.set!, Array.size_setIfInBounds]; omega
        rw [Array.getElem?_eq_getElem hj2]
        by_cases heq : start = j
        · subst heq; simp [Array.set!]
        · simp only [Array.set!]
          rw [Array.getElem_setIfInBounds_ne (h := heq)]
          rwa [Array.getElem?_eq_getElem (by omega)] at hsp
    refine ⟨hs', hszOut1, hszOut2, ?_, ?_, ?_, ?_⟩
    · intro j hj
      have h1 := hstepSt j hj
      have h2 := hmonoSt j hj
      have hj1 : j < st.1.size := by omega
      have hjm : j < (st.1.set! start (joinBSt st.1[start]! post.st[start]!)).size := by rw [hsz1']; exact hj
      have hjo : j < st'.1.size := by omega
      rw [Array.getElem?_eq_getElem hj1, Array.getElem?_eq_getElem hjm] at h1
      rw [Array.getElem?_eq_getElem hjm, Array.getElem?_eq_getElem hjo] at h2
      rw [Array.getElem?_eq_getElem hj1, Array.getElem?_eq_getElem hjo]
      exact BSt.le_trans h1 h2
    · intro j hj1 hj2
      by_cases heq : j = start
      · subst heq
        have h2 := hmonoSt j hlt
        have hjm : j < (st.1.set! j (joinBSt st.1[j]! post.st[j]!)).size := by rw [hsz1']; exact hlt
        have hjo : j < st'.1.size := by omega
        have hjp : j < post.st.size := by omega
        rw [Array.getElem?_eq_getElem hjm, Array.getElem?_eq_getElem hjo] at h2
        rw [Array.getElem?_eq_getElem hjp, Array.getElem?_eq_getElem hjo]
        simp only [Array.set!, Array.getElem_setIfInBounds_self] at h2
        have hbang : post.st[j]! = post.st[j] := getElem!_pos post.st j hjp
        rw [hbang] at h2
        exact BSt.le_trans (BSt_le_joinBSt_right _ _) h2
      · exact hpostSt j (by omega) (by omega)
    · intro j hj hsp
      exact hmonoSp j hj (hstepSp j hj hsp)
    · intro j hj1 hj2 hsp
      by_cases heq : j = start
      · subst heq
        have hjp : j < post.spent.size := by omega
        have hps : post.spent[j]! = true := by
          rw [getElem!_pos post.spent j hjp]
          rw [Array.getElem?_eq_getElem hjp] at hsp
          exact Option.some.inj hsp
        apply hmonoSp j hlt
        simp only [hps, ↓reduceIte]
        have hjm : j < (st.2.set! j true).size := by rw [Array.set!, Array.size_setIfInBounds]; omega
        rw [Array.getElem?_eq_getElem hjm]
        simp [Array.set!]
      · exact hpostSp j (by omega) (by omega) hsp

theorem forIn_stateJoin_sound (pre : AState) :
    ∀ (posts : List CSt) (st0 : Array BSt) (sp0 : Array Bool) (st1 : Array BSt) (sp1 : Array Bool) (s s' : CSt),
      st0.size = pre.st.size → sp0.size = pre.st.size →
      (∀ p ∈ posts, pre.st.size ≤ p.st.size ∧ pre.st.size ≤ p.spent.size) →
      (forIn (m := CM) posts (st0, sp0) fun post __s => do
        let __s ← forIn (m := CM) [:pre.st.size] (__s.1, __s.2) fun i __s =>
          if post.spent[i]! = true then
            pure (ForInStep.yield
              (__s.1.set! i (if (__s.1[i]! == BSt.dead || post.st[i]! == BSt.dead) = true then BSt.dead
                else if (__s.1[i]! == BSt.shared || post.st[i]! == BSt.shared) = true then BSt.shared else BSt.live),
               __s.2.set! i true))
          else
            pure (ForInStep.yield
              (__s.1.set! i (if (__s.1[i]! == BSt.dead || post.st[i]! == BSt.dead) = true then BSt.dead
                else if (__s.1[i]! == BSt.shared || post.st[i]! == BSt.shared) = true then BSt.shared else BSt.live),
               __s.2))
        pure (ForInStep.yield (__s.1, __s.2))).run s = .ok ((st1, sp1), s') →
      s' = s ∧ st1.size = pre.st.size ∧ sp1.size = pre.st.size ∧
      (∀ i, i < pre.st.size →
        match st0[i]?, st1[i]? with
        | some b1, some b2 => BSt.le b1 b2
        | _, _ => False) ∧
      (∀ i, i < pre.st.size → sp0[i]? = some true → sp1[i]? = some true) ∧
      (∀ p ∈ posts, ∀ i, i < pre.st.size →
        match p.st[i]?, st1[i]? with
        | some bp, some b2 => BSt.le bp b2
        | _, _ => False) ∧
      (∀ p ∈ posts, ∀ i, i < pre.st.size → p.spent[i]? = some true → sp1[i]? = some true) := by
  intro posts
  induction posts with
  | nil =>
    intro st0 sp0 st1 sp1 s s' hsz1 hsz2 _ hf
    rw [List.forIn_nil] at hf
    obtain ⟨hp, rfl⟩ := CM_pure_elim hf
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    refine ⟨rfl, hsz1, hsz2, ?_, fun _ _ h => h, fun _ hm => (by cases hm), fun _ hm => (by cases hm)⟩
    intro i hi; rw [Array.getElem?_eq_getElem (by omega)]; exact BSt.le_refl _
  | cons p rest ih =>
    intro st0 sp0 st1 sp1 s s' hsz1 hsz2 hposts hf
    rw [List.forIn_cons] at hf
    obtain ⟨step, s₁, hstep, hf⟩ := CM_bind_elim hf
    obtain ⟨⟨stm, spm⟩, s₂, hinner, hstep⟩ := CM_bind_elim hstep
    obtain ⟨rfl, hs2⟩ := CM_pure_elim hstep; subst s₂
    dsimp only at hf
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hinner
    have hrSz : ([0:pre.st.size] : Std.Legacy.Range).size = pre.st.size := by simp [Std.Legacy.Range.size]
    rw [hrSz] at hinner
    obtain ⟨hpst, hpsp⟩ := hposts p (List.mem_cons_self ..)
    obtain ⟨hs₁, hszm1, hszm2, hst0m, hpm, hsp0m, hpspm⟩ :=
      forIn_stateJoin_range p pre.st.size pre.st.size 0 (st0, sp0) (stm, spm) s s₁
        hsz1 hsz2 (by omega) hpst hpsp hinner
    dsimp only at hszm1 hszm2 hst0m hpm hsp0m hpspm
    subst s₁
    obtain ⟨hs', hsz1', hsz2', hstm1, hspm1, hrestSt, hrestSp⟩ :=
      ih stm spm st1 sp1 s s' hszm1 hszm2 (fun q hq => hposts q (List.mem_cons_of_mem _ hq)) hf
    refine ⟨hs', hsz1', hsz2', ?_, ?_, ?_, ?_⟩
    · intro i hi
      have h1 := hst0m i hi; have h2 := hstm1 i hi
      rw [Array.getElem?_eq_getElem (by omega)] at h1 ⊢
      rw [Array.getElem?_eq_getElem (by omega)] at h1 h2
      rw [Array.getElem?_eq_getElem (by omega)] at h2 ⊢
      exact BSt.le_trans h1 h2
    · intro i hi hsp; exact hspm1 i hi (hsp0m i hi hsp)
    · intro q hq i hi
      rcases List.mem_cons.mp hq with rfl | hr
      · have h1 := hpm i (Nat.zero_le _) (by omega); have h2 := hstm1 i hi
        rw [Array.getElem?_eq_getElem (by omega)] at h1 ⊢
        rw [Array.getElem?_eq_getElem (by omega)] at h1 h2
        rw [Array.getElem?_eq_getElem (by omega)] at h2 ⊢
        exact BSt.le_trans h1 h2
      · exact hrestSt q hr i hi
    · intro q hq i hi hsp
      rcases List.mem_cons.mp hq with rfl | hr
      · exact hspm1 i hi (hpspm i (Nat.zero_le _) (by omega) hsp)
      · exact hrestSp q hr i hi hsp

theorem forIn_valJoin_sound {preSize nr : Nat} :
    ∀ (l : List AVal) (r0 r1 : AVal) (s s' : CSt),
      (∀ d ∈ r0.deps, d < preSize) →
      ValRegsOk nr r0 →
      r0.onceOnly = false →
      (∀ x ∈ l, (∀ d ∈ x.deps, d < preSize) ∧ ValRegsOk nr x ∧ x.onceOnly = false) →
      (forIn (m := CM) l r0 fun x __s =>
        if x.skel.admits __s.skel = true then
          pure (ForInStep.yield
            { cls := __s.cls,
              own := if (__s.own == Own.uniq && x.own == Own.uniq) = true then Own.uniq else Own.shared,
              deps := natUnion __s.deps x.deps, regs := natUnion __s.regs x.regs, skel := __s.skel,
              onceOnly := __s.onceOnly || x.onceOnly, src := __s.src })
        else do
          refuseM "mode skeletons differ between a case's alternatives"
          pure (ForInStep.yield
            { cls := __s.cls,
              own := if (__s.own == Own.uniq && x.own == Own.uniq) = true then Own.uniq else Own.shared,
              deps := natUnion __s.deps x.deps, regs := natUnion __s.regs x.regs, skel := __s.skel,
              onceOnly := __s.onceOnly || x.onceOnly, src := __s.src })).run s = .ok (r1, s') →
      s' = s ∧ r1.skel = r0.skel ∧
      (r1.own = .uniq → r0.own = .uniq ∧ ∀ x ∈ l, x.own = .uniq) ∧
      (∀ d ∈ r0.deps, d ∈ r1.deps) ∧
      (∀ x ∈ l, ∀ d ∈ x.deps, d ∈ r1.deps) ∧
      (∀ d ∈ r1.deps, d < preSize) ∧
      (∀ reg ∈ r0.regs, reg ∈ r1.regs) ∧
      (∀ x ∈ l, ∀ reg ∈ x.regs, reg ∈ r1.regs) ∧
      ValRegsOk nr r1 ∧
      r1.onceOnly = false ∧
      (∀ x ∈ l, x.skel.admits r0.skel = true) := by
  intro l
  induction l with
  | nil =>
    intro r0 r1 s s' hdeps hregs honce _ hf
    rw [List.forIn_nil] at hf
    obtain ⟨rfl, rfl⟩ := CM_pure_elim hf
    exact ⟨rfl, rfl, fun h => ⟨h, fun _ hm => (by cases hm)⟩, fun _ h => h,
      fun _ hm => (by cases hm), hdeps, fun _ h => h, fun _ hm => (by cases hm), hregs, honce,
      fun _ hm => (by cases hm)⟩
  | cons x rest ih =>
    intro r0 r1 s s' hdeps hregs honce hl hf
    rw [List.forIn_cons] at hf
    obtain ⟨step, s₁, hstep, hf⟩ := CM_bind_elim hf
    cases had : x.skel.admits r0.skel with
    | false =>
      simp only [had, Bool.false_eq_true, ↓reduceIte] at hstep
      obtain ⟨_, _, href, _⟩ := CM_bind_elim hstep
      rw [CM_refuseM_run] at href; cases href
    | true =>
      simp only [had, ↓reduceIte] at hstep
      obtain ⟨rfl, hs1⟩ := CM_pure_elim hstep; subst s₁
      dsimp only at hf
      obtain ⟨hxDeps, hxRegs, hxOnce⟩ := hl x (List.mem_cons_self ..)
      have hr'Deps : ∀ d ∈ natUnion r0.deps x.deps, d < preSize := fun d hd => by
        rcases (natUnion_mem r0.deps x.deps).mp hd with h1 | h2
        · exact hdeps d h1
        · exact hxDeps d h2
      have hr'Regs : ValRegsOk nr { r0 with
          own := if r0.own == Own.uniq && x.own == Own.uniq then Own.uniq else Own.shared,
          deps := natUnion r0.deps x.deps, regs := natUnion r0.regs x.regs,
          onceOnly := r0.onceOnly || x.onceOnly } := regs_natUnion_lt hregs hxRegs
      have hr'Once : (r0.onceOnly || x.onceOnly) = false := by simp [honce, hxOnce]
      obtain ⟨hs', hsk, hown, hd0, hdR, hdLt, hr0, hrR, hrLt, ho1, hadR⟩ :=
        ih _ r1 s s' hr'Deps hr'Regs hr'Once (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hf
      refine ⟨hs', hsk, ?_, ?_, ?_, hdLt, ?_, ?_, hrLt, ho1, ?_⟩
      · intro hu
        obtain ⟨hu0, huR⟩ := hown hu
        have hboth : r0.own = .uniq ∧ x.own = .uniq := by
          cases ho0 : r0.own <;> cases hox : x.own <;> (rw [ho0, hox] at hu0; first | exact ⟨rfl, rfl⟩ | cases hu0)
        refine ⟨hboth.1, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hmem
        · exact hboth.2
        · exact huR y hmem
      · intro d hd; exact hd0 d ((natUnion_mem r0.deps x.deps).mpr (Or.inl hd))
      · intro y hy d hd
        rcases List.mem_cons.mp hy with hyx | hmem
        · rw [hyx] at hd; exact hd0 d ((natUnion_mem r0.deps x.deps).mpr (Or.inr hd))
        · exact hdR y hmem d hd
      · intro reg hreg; exact hr0 reg ((natUnion_mem r0.regs x.regs).mpr (Or.inl hreg))
      · intro y hy reg hreg
        rcases List.mem_cons.mp hy with hyx | hmem
        · rw [hyx] at hreg; exact hr0 reg ((natUnion_mem r0.regs x.regs).mpr (Or.inr hreg))
        · exact hrR y hmem reg hreg
      · intro y hy
        rcases List.mem_cons.mp hy with hyx | hmem
        · rw [hyx]; exact had
        · exact hadR y hmem

/-- Per-branch certificate accumulated during `anCase`'s alternative loop. -/
def BranchOk (P : Prog) (env : List ABnd) (k : CaseInfo) (mv : AVal) (consuming : Bool)
    (pre : AState) (j : Nat) (ca : CaseAlt) (altT : Term) (res : AVal) (post : CSt) : Prop :=
  ∃ nextReg_j r_j post_j σ_chk_j σ_val_j uniq_j,
    pre.nextRegion ≤ nextReg_j ∧
    AAlt P env altT (caseAltArgs P k mv consuming j ca)
      { pre with nextRegion := nextReg_j } r_j post_j ∧
    Runs (notOnceSrc r_j "a case alternative's result") post_j () σ_chk_j ∧
    r_j.onceOnly = false ∧
    Runs (valid r_j "a case alternative's result") σ_chk_j () σ_val_j ∧
    Runs (isUniq r_j) σ_val_j uniq_j (AState.ofCSt post) ∧
    AStateOk (AState.ofCSt post) ∧
    AStateLe pre (AState.ofCSt post) ∧
    post.regions = pre.regions ∧
    ValRegsOk post.nextRegion r_j ∧
    res = { r_j with
      own := if r_j.own == Own.uniq && uniq_j then Own.uniq else Own.shared,
      deps := r_j.deps.filter (· < pre.st.size) }

theorem branchOk_to_AAlts {P : Prog} {env : List ABnd} {k : CaseInfo} {mv : AVal} {consuming : Bool}
    {pre σ_join : AState} {r_join : AVal} {posts : Array CSt} {results : Array AVal} :
    ∀ (off : Nat) (cas : List CaseAlt) (altTs : List Term),
      cas.length = altTs.length →
      (∀ idx ca altT, cas[idx]? = some ca → altTs[idx]? = some altT →
        ∃ post res,
          posts[off + idx]? = some post ∧ results[off + idx]? = some res ∧
          BranchOk P env k mv consuming pre (off + idx) ca altT res post ∧
          StateJoinGe pre (AState.ofCSt post) σ_join ∧
          ValJoinGe pre.st.size res r_join) →
      AAlts P env k mv consuming pre off cas altTs r_join σ_join := by
  intro off cas
  induction cas generalizing off with
  | nil =>
    intro altTs hlen _
    cases altTs with
    | nil => exact .nil
    | cons _ _ => simp at hlen
  | cons ca casRest ih =>
    intro altTs hlen hall
    cases altTs with
    | nil => simp at hlen
    | cons altT altRest =>
      obtain ⟨post, res, _, _, hbr, hsj, hvj⟩ :=
        hall 0 ca altT (by simp) (by simp)
      simp only [Nat.add_zero] at hbr
      obtain ⟨nextReg_j, r_j, post_j, σ_chk_j, σ_val_j, uniq_j,
        hnr, halt, hno, ho, hval, huniq, _, _, _, _, hresEq⟩ := hbr
      have hvj' : ValJoinGe pre.st.size
          { r_j with own := if r_j.own == Own.uniq && uniq_j then Own.uniq else Own.shared } r_join := by
        obtain ⟨h1, h2, h3, h4, h5⟩ := hvj
        rw [hresEq] at h1 h2 h3 h4 h5
        refine ⟨h1, h2, ?_, h4, h5⟩
        intro d hd hlt
        exact h3 d (List.mem_filter.mpr ⟨hd, decide_eq_true hlt⟩) hlt
      refine .cons hnr halt hno ho hval huniq hsj hvj' ?_
      refine ih (off + 1) altRest (by simp at hlen; omega) (fun idx ca' altT' hca' haltT' => ?_)
      have hsub := hall (idx + 1) ca' altT' (by simpa using hca') (by simpa using haltT')
      rwa [show off + (idx + 1) = off + 1 + idx by omega] at hsub

/-! ### Mutual Fuel Induction (`anTerm`, `anCall`, `anLam`, `anCase`, `anAlt`) -/

abbrev TermSoundAt (P : Prog) (n : Nat) : Prop :=
  ∀ env t s v s', AStateOk (AState.ofCSt s) → EnvRegsOk s.nextRegion env →
    (anTerm P n env t).run s = .ok (v, s') →
    ATerm P env t (AState.ofCSt s) v (AState.ofCSt s') ∧
    AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
    s'.regions = s.regions ∧ ValRegsOk s'.nextRegion v

abbrev CallSoundAt (P : Prog) (n : Nat) : Prop :=
  ∀ env r args c s v s', AStateOk (AState.ofCSt s) → EnvRegsOk s.nextRegion env →
    (anCall P n env r args c).run s = .ok (v, s') →
    ACall P env r args.toList c (AState.ofCSt s) v (AState.ofCSt s') ∧
    AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
    s'.regions = s.regions ∧ ValRegsOk s'.nextRegion v

abbrev LamSoundAt (P : Prog) (n : Nat) : Prop :=
  ∀ env p res rc fvs body s v s', AStateOk (AState.ofCSt s) → EnvRegsOk s.nextRegion env →
    (anLam P n env p res rc fvs body).run s = .ok (v, s') →
    ATerm P env (.lam p res rc fvs body) (AState.ofCSt s) v (AState.ofCSt s') ∧
    AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
    s'.regions = s.regions ∧ ValRegsOk s'.nextRegion v

abbrev CaseSoundAt (P : Prog) (n : Nat) : Prop :=
  ∀ env k mj alts ex c s v s', AStateOk (AState.ofCSt s) → EnvRegsOk s.nextRegion env →
    (anCase P n env k mj alts ex c).run s = .ok (v, s') →
    ATerm P env (.case k mj alts ex c) (AState.ofCSt s) v (AState.ofCSt s') ∧
    AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
    s'.regions = s.regions ∧ ValRegsOk s'.nextRegion v

abbrev AltSoundAt (P : Prog) (n : Nat) : Prop :=
  ∀ env t args s v s', AStateOk (AState.ofCSt s) → EnvRegsOk s.nextRegion env →
    (∀ x ∈ args, ValRegsOk s.nextRegion x.1) →
    (anAlt P n env t args).run s = .ok (v, s') →
    AAlt P env t args (AState.ofCSt s) v (AState.ofCSt s') ∧
    AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
    s'.regions = s.regions ∧ ValRegsOk s'.nextRegion v

theorem anTerm_step {P : Prog} {n : Nat}
    (ihTerm : TermSoundAt P n) (ihCall : CallSoundAt P n)
    (ihLam : LamSoundAt P n) (ihCase : CaseSoundAt P n) : TermSoundAt P (n + 1) := by
      intro env t s v s' hok henv h
      unfold anTerm at h
      obtain ⟨_, s0, htick, h⟩ := CM_bind_elim h
      obtain ⟨_, hs0Eq⟩ := CM_tick_elim htick
      subst s0
      let s0 : CSt := { s with steps := s.steps - 1 }
      have hok0 : AStateOk (AState.ofCSt s0) := hok
      have henv0 : EnvRegsOk s0.nextRegion env := henv
      cases t with
      | irr =>
        obtain ⟨rfl, rfl⟩ := CM_pure_elim h
        exact ⟨.irr, hok, AStateLe.refl _, rfl, fun _ hm => by cases hm⟩
      | var i c =>
        obtain ⟨rv, s₁, hrv, h⟩ := CM_bind_elim h
        obtain ⟨rfl, rfl⟩ := CM_pure_elim h
        obtain ⟨hs₁, b, hbi, hvregs⟩ := readVar_props hrv
        subst s₁
        have hruns := (stepIndep_readVar env i).toRuns hrv
        have hvOk : ValRegsOk s.nextRegion { rv with cls := c } := by
          intro r hr; dsimp only at hr; rw [hvregs] at hr
          exact henv b (List.mem_of_getElem? hbi) r hr
        exact ⟨.var hruns, hok, AStateLe.refl _, rfl, hvOk⟩
      | natLit k =>
        obtain ⟨rfl, rfl⟩ := CM_pure_elim h
        exact ⟨.natLit, hok, AStateLe.refl _, rfl, fun _ hm => by cases hm⟩
      | strLit str =>
        obtain ⟨rfl, rfl⟩ := CM_pure_elim h
        exact ⟨.strLit, hok, AStateLe.refl _, rfl, fun _ hm => by cases hm⟩
      | const r c =>
        obtain ⟨hc, hok', hle', hreg', hvOk⟩ := ihCall env r #[] c s0 v s' hok0 henv0 h
        exact ⟨.constCall hc, hok', hle', hreg', hvOk⟩
      | app f a c =>
        dsimp only at h
        cases hsp : termSpine (.app f a c) with
        | mk hd args =>
          rw [hsp] at h
          cases hd with
          | const r rc =>
            obtain ⟨hc, hok', hle', hreg', hvOk⟩ := ihCall env r args c s0 v s' hok0 henv0 h
            exact ⟨.appConst hsp hc, hok', hle', hreg', hvOk⟩
          | _ =>
            obtain ⟨fv, s₁, hfv, h⟩ := CM_bind_elim h
            obtain ⟨hatF, hok1, hle1, hreg1, hfvOk⟩ := ihTerm env _ s0 fv s₁ hok0 henv0 hfv
            rw [← Array.forIn_toList] at h
            obtain ⟨avs, s₂, hevs, h⟩ := CM_bind_elim h
            obtain ⟨newAvs, havsEq, hevals, hok2, hle2, hreg2, havsOk⟩ :=
              forIn_evals_sound (fun hok' henv' ht' => ihTerm env _ _ _ _ hok' henv' ht')
                args.toList #[] avs s₁ s₂ hok1 (henv.mono hle1.2.1) hevs
            have havsList : avs.toList = newAvs := by simpa using havsEq
            rw [← Array.forIn_toList] at h
            have hzip : avs.zipIdx.toList = newAvs.zipIdx 0 := by
              rw [Array.toList_zipIdx, havsList]
            rw [hzip] at h
            have hszEq : avs.size = 0 + newAvs.length := by
              rw [Nat.zero_add, ← havsList]; rfl
            rw [hszEq] at h
            obtain ⟨res, s₃, happ, h⟩ := CM_bind_elim h
            obtain ⟨rfl, rfl⟩ := CM_pure_elim h
            have hne : newAvs ≠ [] := by
              intro hnil
              have hlen := AEvals_length hevals
              rw [hnil] at hlen
              have hnon := termSpine_app_nonempty f a c
              rw [hsp] at hnon
              cases hargs : args.toList with
              | nil => exact hnon hargs
              | cons _ _ => rw [hargs] at hlen; simp at hlen
            obtain ⟨happs, _, hok3, hle3, hreg3, hresOk⟩ :=
              forIn_applyZipIdx_sound newAvs 0 fv res s₂ s₃ hok2 (hfvOk.mono hle2.2.1) havsOk happ
            refine ⟨.appVal hsp (fun r rc hEq => by cases hEq) hatF hevals (happs hne),
              hok3, (hle1.trans hle2).trans hle3, hreg3.trans (hreg2.trans hreg1), hresOk⟩
      | lam p res rc fvs body =>
        exact ihLam env p res rc fvs body s0 v s' hok0 henv0 h
      | letE m d val b =>
        dsimp only at h
        have hletNonErased : m ≠ .value .erased →
            (do
              let x ← anTerm P n env val
              let s ← openReg
              let bm := m.binderMode
              let bv ← bindInner bm d x s "a let"
              let id ← newBnd bv (bm.usage == Usage.once)
              let r ← anTerm P n ({ id, mode := bm, val := bv } :: env) b
              valid r "a let's value"
              if r.regs.contains s then refuseM "borrowEscape: a value borrowed by a let outlives it"
              closeReg s
              pure r).run s0 = .ok (v, s') →
            ATerm P env (.letE m d val b) (AState.ofCSt s) v (AState.ofCSt s') ∧
            AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
            s'.regions = s.regions ∧ ValRegsOk s'.nextRegion v := by
          intro hne hl
          obtain ⟨x, s₁, hxv, hl⟩ := CM_bind_elim hl
          obtain ⟨hatV, hok1, hle1, hreg1, hxOk⟩ := ihTerm env val s0 x s₁ hok0 henv0 hxv
          obtain ⟨sreg, s₂, hop, hl⟩ := CM_bind_elim hl
          rw [openReg_run] at hop
          simp only [Except.ok.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop
          obtain ⟨hok2, hsregEq, hsregNotMem⟩ := hok1.openReg
          have hle12 : AStateLe (AState.ofCSt s₁) (AState.ofCSt s₁).openReg.2 := AStateLe_openReg _
          obtain ⟨bv, s₃, hbi, hl⟩ := CM_bind_elim hl
          have hbiRuns := (stepIndep_bindInner m.binderMode d x (AState.ofCSt s₁).openReg.1 "a let").toRuns hbi
          let s1Open : CSt := (AState.ofCSt s₁).openReg.2.toCSt s₁.steps
          obtain ⟨hok3, hle23, hreg23⟩ :=
            statePres_bindInner m.binderMode d x (AState.ofCSt s₁).openReg.1 "a let" s1Open bv s₃ hok2 hbi
          have hbvOk : ValRegsOk s₃.nextRegion bv :=
            bindInner_regsOk (s := s1Open) hok2
              (hxOk.mono (by dsimp [s1Open, AState.openReg, AState.ofCSt, AState.toCSt]; omega))
              (by rw [hsregEq]; dsimp [s1Open, AState.openReg, AState.ofCSt, AState.toCSt]; omega) hbi
          obtain ⟨id, s₄, hnb, hl⟩ := CM_bind_elim hl
          rw [newBnd_run] at hnb
          simp only [Except.ok.injEq, Prod.mk.injEq] at hnb
          obtain ⟨rfl, rfl⟩ := hnb
          obtain ⟨hok4, hle34⟩ := hok3.pushBnd bv (m.binderMode.usage == .once)
          have henv4 : EnvRegsOk ((AState.ofCSt s₃).pushBnd bv (m.binderMode.usage == .once)).2.nextRegion
              ({ id := s₃.st.size, mode := m.binderMode, val := bv } :: env) := by
            intro b0 hb0
            rcases List.mem_cons.mp hb0 with rfl | hrest
            · exact hbvOk
            · exact henv b0 hrest |>.mono ((hle1.trans hle12).trans hle23).2.1
          obtain ⟨r, s₅, hrb, hl⟩ := CM_bind_elim hl
          let s3Push : CSt := ((AState.ofCSt s₃).pushBnd bv (m.binderMode.usage == .once)).2.toCSt s₃.steps
          obtain ⟨hatB, hok5, hle45, hreg45, hrOk⟩ := ihTerm _ b s3Push r s₅ hok4 henv4 hrb
          obtain ⟨_, s₆, hvalR, hl⟩ := CM_bind_elim hl
          have hs₆ := valid_state_eq hvalR; subst s₆
          have hvalRuns := (stepIndep_valid r "a let's value").toRuns hvalR
          cases hcont : r.regs.contains (AState.ofCSt s₁).openReg.1 with
          | true =>
            simp only [hcont, ↓reduceIte] at hl
            obtain ⟨_, _, href, _⟩ := CM_bind_elim hl; rw [CM_refuseM_run] at href; cases href
          | false =>
            simp only [hcont, Bool.false_eq_true, ↓reduceIte] at hl
            have hnotIn : ¬ ((AState.ofCSt s₁).openReg.1 ∈ r.regs) := by
              intro hmem; have := List.contains_iff_mem.mpr hmem; rw [hcont] at this; cases this
            obtain ⟨_, s₇, hcl, hl⟩ := CM_bind_elim hl
            rw [closeReg_run] at hcl
            simp only [Except.ok.injEq, Prod.mk.injEq] at hcl
            obtain ⟨_, rfl⟩ := hcl
            obtain ⟨rfl, rfl⟩ := CM_pure_elim hl
            have hsregNe1 : (AState.ofCSt s₁).openReg.1 ≠ 1 := by
              have := hok1.2.2.1; rw [hsregEq]; omega
            have hok7 : AStateOk ((AState.ofCSt s₅).closeReg (AState.ofCSt s₁).openReg.1) :=
              hok5.closeReg hsregNe1
            have hreg7 : ((AState.ofCSt s₅).closeReg (AState.ofCSt s₁).openReg.1).regions = s.regions := by
              dsimp only [AState.closeReg]
              change s₅.regions.filter (· != (AState.ofCSt s₁).openReg.1) = s.regions
              rw [hreg45]; dsimp only [s3Push, AState.pushBnd, AState.toCSt, AState.ofCSt]
              rw [hreg23]; dsimp only [s1Open, AState.openReg, AState.toCSt, AState.ofCSt]
              rw [closeReg_cons_of_not_mem (by simpa [AState.openReg, AState.ofCSt] using hsregNotMem)]
              exact hreg1
            have hleTot : AStateLe (AState.ofCSt s) ((AState.ofCSt s₅).closeReg (AState.ofCSt s₁).openReg.1) :=
              ((((hle1.trans hle12).trans hle23).trans hle34).trans hle45).trans (AStateLe_closeReg _ _)
            exact ⟨.letVal hne hatV hbiRuns hatB hvalRuns hnotIn, hok7, hleTot, hreg7, hrOk⟩
        cases hm : m with
        | borrow =>
          have := hletNonErased (by intro hEq; rw [hm] at hEq; cases hEq) (by simpa [hm] using h)
          simpa [hm] using this
        | value bm =>
          cases hbm : bm with
          | erased =>
            simp only [hm, hbm] at h
            obtain ⟨id, s₁, hnb, h⟩ := CM_bind_elim h
            rw [newBnd_run] at hnb
            simp only [Except.ok.injEq, Prod.mk.injEq] at hnb
            obtain ⟨rfl, rfl⟩ := hnb
            obtain ⟨hok1, hle1⟩ := hok0.pushBnd { cls := .irr } false
            have henv1 : EnvRegsOk ((AState.ofCSt s0).pushBnd { cls := .irr } false).2.nextRegion
                ({ id := s0.st.size, mode := .erased, val := { cls := .irr } } :: env) := by
              intro b0 hb0
              rcases List.mem_cons.mp hb0 with rfl | hrest
              · intro _ hm; cases hm
              · exact henv b0 hrest
            obtain ⟨hatB, hok2, hle2, hreg2, hvOk⟩ :=
              ihTerm _ b (((AState.ofCSt s0).pushBnd { cls := .irr } false).2.toCSt s0.steps) v s' hok1 henv1 h
            exact ⟨.letErased hatB, hok2, hle1.trans hle2, hreg2, hvOk⟩
          | many | once | borrowed | onceBorrowed | unique | uniqueBorrowed =>
            have := hletNonErased (by intro hEq; rw [hm, hbm] at hEq; cases hEq) (by simpa [hm, hbm] using h)
            simpa [hm, hbm] using this
      | proj sRef i e c =>
        obtain ⟨ve, s₁, he, h⟩ := CM_bind_elim h
        obtain ⟨hatE, hok1, hle1, hreg1, hveOk⟩ := ihTerm env e s0 ve s₁ hok0 henv0 he
        obtain ⟨_, s₂, hvalE, h⟩ := CM_bind_elim h
        have hs₂ := valid_state_eq hvalE; subst s₂
        have hvalRuns := (stepIndep_valid ve "a projection").toRuns hvalE
        have hprojRuns := (stepIndep_anProj P sRef i ve c).toRuns h
        obtain ⟨hok3, hle23, hreg23⟩ := statePres_anProj P sRef i ve c s₁ v s' hok1 h
        have hvOk := anProj_regsOk hveOk h
        exact ⟨.proj hatE hvalRuns hprojRuns, hok3, hle1.trans hle23, hreg23.trans hreg1, hvOk⟩
      | case k mj alts ex c =>
        exact ihCase env k mj alts ex c s0 v s' hok0 henv0 h

theorem anCall_step {P : Prog} {n : Nat} (ihTerm : TermSoundAt P n) : CallSoundAt P (n + 1) := by
      intro env r args c s v s' hok henv h
      unfold anCall at h
      dsimp only at h
      cases hd : P.find? r with
      | none =>
        simp only [hd] at h
        rw [← Array.forIn_toList] at h
        obtain ⟨avs, s₁, _, h⟩ := CM_bind_elim h
        rw [CM_refuseM_run] at h; cases h
      | some d =>
        simp only [hd] at h
        have hiface : ∀ (ifc : Iface) (avs : Array (Option AVal)) (newAvs : List (Option AVal)) (s₁ : CSt),
            ifaceOf? d = some ifc →
            avs.toList = newAvs →
            ACallArgs P (some d) env 0 args.toList (AState.ofCSt s) newAvs (AState.ofCSt s₁) →
            AStateOk (AState.ofCSt s₁) → AStateLe (AState.ofCSt s) (AState.ofCSt s₁) →
            s₁.regions = s.regions → (∀ a, some a ∈ newAvs → ValRegsOk s₁.nextRegion a) →
            (let k := ifc.params.size
             if avs.size < k then papVal ifc avs "a partial application"
             else do
               let r0 ← if k == 0 then pure ({ cls := ifc.resCls, skel := ifc.resSkel } : AVal)
                 else callResult ifc (avs.extract 0 k) "a call"
               let mut f := r0
               for (a, i) in (avs.extract k avs.size).zipIdx do
                 match a with
                 | some av => f ← applyValue f av (if k + i + 1 == avs.size then c else .val) "an application"
                 | none => pure ()
               pure { f with cls := c }).run s₁ = .ok (v, s') →
            ACall P env r args.toList c (AState.ofCSt s) v (AState.ofCSt s') ∧
            AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
            s'.regions = s.regions ∧ ValRegsOk s'.nextRegion v := by
          intro ifc avs newAvs s₁ hifc havsList hca hok1 hle1 hreg1 havsOk htail
          have havsArr : avs = newAvs.toArray := by rw [← havsList]
          have hsz : avs.size = newAvs.length := by rw [← havsList]; rfl
          dsimp only at htail
          by_cases hlt : newAvs.length < ifc.params.size
          · have hltA : avs.size < ifc.params.size := by omega
            simp only [hltA, ↓reduceIte] at htail
            have hpapRuns : Runs (papVal ifc newAvs.toArray "a partial application")
                (AState.ofCSt s₁) v (AState.ofCSt s') := by
              rw [← havsArr]; exact (stepIndep_papVal ifc avs "a partial application").toRuns htail
            obtain ⟨hok2, hle2, hreg2⟩ := statePres_papVal ifc avs "a partial application" s₁ v s' hok1 htail
            have hvOk := papVal_regsOk hok1 (by simpa [havsList] using havsOk) htail
            exact ⟨.ifacePap hd hifc hca hlt hpapRuns, hok2, hle1.trans hle2, hreg2.trans hreg1, hvOk⟩
          · have hltA : ¬ avs.size < ifc.params.size := by omega
            simp only [hltA, ↓reduceIte] at htail
            have hdropSome : ∀ oa ∈ newAvs.drop ifc.params.size, oa.isSome = true := by
              intro oa hoa
              obtain ⟨idx, hgetI⟩ := List.mem_iff_getElem?.mp hoa
              rw [List.getElem?_drop] at hgetI
              exact ACallArgs_getElem?_isSome hca (ifc.params.size + idx) oa hgetI
                (erasedAt_of_ifaceOf?_ge hifc (by omega))
            have hextractList : (avs.extract ifc.params.size avs.size).toList = newAvs.drop ifc.params.size := by
              rw [Array.toList_extract, havsList]
              exact List.take_of_length_le (by simp; omega)
            have hextractZip : (avs.extract ifc.params.size avs.size).zipIdx.toList =
                (newAvs.drop ifc.params.size).zipIdx 0 := by
              rw [Array.toList_zipIdx, hextractList]
            have hszDrop : avs.size = ifc.params.size + 0 + (newAvs.drop ifc.params.size).length := by
              simp only [Nat.add_zero, List.length_drop]; omega
            by_cases hk0 : ifc.params.size = 0
            · have hk0b : (ifc.params.size == 0) = true := by simp [hk0]
              simp only [hk0b, ↓reduceIte] at htail
              obtain ⟨r0, s₂, hr0, htail⟩ := CM_bind_elim htail
              obtain ⟨rfl, hs2⟩ := CM_pure_elim hr0; subst s₂
              rw [← Array.forIn_toList, hextractZip, hszDrop] at htail
              obtain ⟨fOut, s₃, hfLoop, htail⟩ := CM_bind_elim htail
              obtain ⟨rfl, rfl⟩ := CM_pure_elim htail
              obtain ⟨happs, hok3, hle3, hreg3, hvOk⟩ :=
                forIn_applyOptZipIdx_sound (k := ifc.params.size) (c := c) (newAvs.drop ifc.params.size) 0
                  { cls := ifc.resCls, skel := ifc.resSkel } fOut s₁ s₃ hok1 (fun _ hm => by cases hm) hdropSome
                  (fun a ha => havsOk a (List.mem_of_mem_drop ha)) hfLoop
              have hdrop0 : newAvs.drop ifc.params.size = newAvs := by simp [hk0]
              rw [hdrop0] at happs
              exact ⟨.ifaceFullZero hd hifc hca hk0 happs, hok3, hle1.trans hle3, hreg3.trans hreg1, hvOk⟩
            · have hk0b : (ifc.params.size == 0) = false := by simp [hk0]
              simp only [hk0b, Bool.false_eq_true, ↓reduceIte] at htail
              obtain ⟨r0, s₂, hcr, htail⟩ := CM_bind_elim htail
              have hcrRuns : Runs (callResult ifc (newAvs.toArray.extract 0 ifc.params.size) "a call")
                  (AState.ofCSt s₁) r0 (AState.ofCSt s₂) := by
                rw [← havsArr]; exact (stepIndep_callResult ifc _ "a call").toRuns hcr
              obtain ⟨hok2, hle2, hreg2⟩ := statePres_callResult ifc _ "a call" s₁ r0 s₂ hok1 hcr
              have hr0Ok : ValRegsOk s₂.nextRegion r0 :=
                callResult_regsOk hok1 (fun a ha => havsOk a (by
                  rw [← havsList]; exact array_extract_mem ha)) hcr
              rw [← Array.forIn_toList, hextractZip, hszDrop] at htail
              obtain ⟨fOut, s₃, hfLoop, htail⟩ := CM_bind_elim htail
              obtain ⟨rfl, rfl⟩ := CM_pure_elim htail
              obtain ⟨happs, hok3, hle3, hreg3, hvOk⟩ :=
                forIn_applyOptZipIdx_sound (k := ifc.params.size) (c := c) (newAvs.drop ifc.params.size) 0
                  r0 fOut s₂ s₃ hok2 hr0Ok hdropSome
                  (fun a ha => (havsOk a (List.mem_of_mem_drop ha)).mono hle2.2.1) hfLoop
              exact ⟨.ifaceFullPos hd hifc hca (by omega) (by omega) hcrRuns happs,
                hok3, (hle1.trans hle2).trans hle3, hreg3.trans (hreg2.trans hreg1), hvOk⟩
        cases d with
        | caseDef k =>
          obtain ⟨_, _, href, _⟩ := CM_bind_elim h
          rw [CM_refuseM_run] at href; cases href
        | ind cs =>
          rw [← Array.forIn_toList, Array.toList_zipIdx] at h
          obtain ⟨avs, s₁, hcaLoop, h⟩ := CM_bind_elim h
          obtain ⟨newAvs, _, hca, hok1, hle1, hreg1, _⟩ :=
            forIn_callArgs_sound (fun hok' henv' ht' => ihTerm env _ _ _ _ hok' henv' ht')
              args.toList 0 #[] avs s s₁ hok henv hcaLoop
          obtain ⟨rfl, rfl⟩ := CM_pure_elim h
          exact ⟨.ind hd hca, hok1, hle1, hreg1, fun _ hm => by cases hm⟩
        | ctor ind ci nP fields =>
          rw [← Array.forIn_toList, Array.toList_zipIdx] at h
          obtain ⟨avs, s₁, hcaLoop, h⟩ := CM_bind_elim h
          obtain ⟨newAvs, havsEq, hca, hok1, hle1, hreg1, havsOk⟩ :=
            forIn_callArgs_sound (fun hok' henv' ht' => ihTerm env _ _ _ _ hok' henv' ht')
              args.toList 0 #[] avs s s₁ hok henv hcaLoop
          have havsList : avs.toList = newAvs := by simpa using havsEq
          have hctorRuns : Runs (anCtor nP fields newAvs.toArray c) (AState.ofCSt s₁) v (AState.ofCSt s') := by
            have hArr : avs = newAvs.toArray := by rw [← havsList]
            rw [← hArr]; exact (stepIndep_anCtor nP fields avs c).toRuns h
          obtain ⟨hok2, hle2, hreg2⟩ := statePres_anCtor nP fields avs c s₁ v s' hok1 h
          have hvOk := anCtor_regsOk hok1 (by simpa [havsList] using havsOk) h
          exact ⟨.ctor hd hca hctorRuns, hok2, hle1.trans hle2, hreg2.trans hreg1, hvOk⟩
        | prim p =>
          rw [← Array.forIn_toList, Array.toList_zipIdx] at h
          obtain ⟨avs, s₁, hcaLoop, h⟩ := CM_bind_elim h
          obtain ⟨newAvs, havsEq, hca, hok1, hle1, hreg1, havsOk⟩ :=
            forIn_callArgs_sound (fun hok' henv' ht' => ihTerm env _ _ _ _ hok' henv' ht')
              args.toList 0 #[] avs s s₁ hok henv hcaLoop
          have havsList : avs.toList = newAvs := by simpa using havsEq
          rw [← Array.forIn_toList, havsList] at h
          obtain ⟨⟨deps, regs⟩, s₂, hpLoop, h⟩ := CM_bind_elim h
          obtain ⟨hpa, hok2, hle2, hreg2, hregs2⟩ :=
            forIn_primArgs_sound newAvs [] [] deps regs s₁ s₂ hok1 (fun _ hm => by cases hm) havsOk hpLoop
          have hsz : avs.size = newAvs.length := by rw [← havsList]; rfl
          rw [hsz] at h
          by_cases hlt : newAvs.length < p.arity
          · simp only [hlt, ↓reduceIte] at h
            obtain ⟨rfl, rfl⟩ := CM_pure_elim h
            exact ⟨by simpa [hlt] using ACall.prim hd hca hpa, hok2, hle1.trans hle2, hreg2.trans hreg1, hregs2⟩
          · simp only [hlt, ↓reduceIte] at h
            obtain ⟨rfl, rfl⟩ := CM_pure_elim h
            exact ⟨by simpa [hlt] using ACall.prim hd hca hpa, hok2, hle1.trans hle2, hreg2.trans hreg1,
              fun _ hm => by cases hm⟩
        | body ps res rc rs bodyT =>
          rw [← Array.forIn_toList, Array.toList_zipIdx] at h
          obtain ⟨avs, s₁, hcaLoop, h⟩ := CM_bind_elim h
          obtain ⟨newAvs, havsEq, hca, hok1, hle1, hreg1, havsOk⟩ :=
            forIn_callArgs_sound (fun hok' henv' ht' => ihTerm env _ _ _ _ hok' henv' ht')
              args.toList 0 #[] avs s s₁ hok henv hcaLoop
          exact hiface ⟨ps, res, rc, rs⟩ avs newAvs s₁ rfl (by simpa using havsEq) hca hok1 hle1 hreg1 havsOk h
        | extern ps res rc rs =>
          rw [← Array.forIn_toList, Array.toList_zipIdx] at h
          obtain ⟨avs, s₁, hcaLoop, h⟩ := CM_bind_elim h
          obtain ⟨newAvs, havsEq, hca, hok1, hle1, hreg1, havsOk⟩ :=
            forIn_callArgs_sound (fun hok' henv' ht' => ihTerm env _ _ _ _ hok' henv' ht')
              args.toList 0 #[] avs s s₁ hok henv hcaLoop
          exact hiface ⟨ps, res, rc, rs⟩ avs newAvs s₁ rfl (by simpa using havsEq) hca hok1 hle1 hreg1 havsOk h
        | stuck ps res rc rs =>
          rw [← Array.forIn_toList, Array.toList_zipIdx] at h
          obtain ⟨avs, s₁, hcaLoop, h⟩ := CM_bind_elim h
          obtain ⟨newAvs, havsEq, hca, hok1, hle1, hreg1, havsOk⟩ :=
            forIn_callArgs_sound (fun hok' henv' ht' => ihTerm env _ _ _ _ hok' henv' ht')
              args.toList 0 #[] avs s s₁ hok henv hcaLoop
          exact hiface ⟨ps, res, rc, rs⟩ avs newAvs s₁ rfl (by simpa using havsEq) hca hok1 hle1 hreg1 havsOk h

theorem anLam_step {P : Prog} {n : Nat} (ihTerm : TermSoundAt P n) : LamSoundAt P (n + 1) := by
      intro env p res rc fvs body s v s' hok henv h
      unfold anLam at h
      obtain ⟨⟨deps, regs, owned⟩, s₁, hcapsLoop, h⟩ := CM_bind_elim h
      obtain ⟨hcaps, hok1, hle1, hreg1, hregsOk1⟩ :=
        forIn_caps_sound fvs.toList [] [] [] deps regs owned s s₁ hok henv (fun _ hm => by cases hm) hcapsLoop
      obtain ⟨saved, s₂, hget, h⟩ := CM_bind_elim h
      rw [CM_get_run] at hget
      simp only [Except.ok.injEq, Prod.mk.injEq] at hget
      obtain ⟨rfl, rfl⟩ := hget
      obtain ⟨_, s₃, hrest, h⟩ := CM_bind_elim h
      rw [forIn_restoreOwned_run] at hrest
      simp only [Except.ok.injEq, Prod.mk.injEq] at hrest
      obtain ⟨_, rfl⟩ := hrest
      have hokRest : AStateOk (restoreOwned owned (AState.ofCSt s₁)) := AStateOk_restoreOwned owned hok1
      obtain ⟨sreg, s₄, hop, h⟩ := CM_bind_elim h
      rw [openReg_run] at hop
      simp only [AState.ofCSt_toCSt, toCSt_steps, Except.ok.injEq, Prod.mk.injEq] at hop
      obtain ⟨rfl, rfl⟩ := hop
      obtain ⟨hokOpen, hsregEq, _⟩ := hokRest.openReg
      obtain ⟨pid, s₅, hnb, h⟩ := CM_bind_elim h
      rw [newBnd_run] at hnb
      simp only [AState.ofCSt_toCSt, toCSt_steps, Except.ok.injEq, Prod.mk.injEq] at hnb
      obtain ⟨rfl, rfl⟩ := hnb
      obtain ⟨hokPush, _⟩ := hokOpen.pushBnd (paramVal p (restoreOwned owned (AState.ofCSt s₁)).openReg.1)
        (p.mode.usage == .once)
      have henvBody : EnvRegsOk ((restoreOwned owned (AState.ofCSt s₁)).openReg.2.pushBnd
            (paramVal p (restoreOwned owned (AState.ofCSt s₁)).openReg.1) (p.mode.usage == .once)).2.nextRegion
          ({ id := (restoreOwned owned (AState.ofCSt s₁)).openReg.2.st.size,
             mode := p.mode,
             val := paramVal p (restoreOwned owned (AState.ofCSt s₁)).openReg.1 } :: env) := by
        intro b0 hb0
        rcases List.mem_cons.mp hb0 with rfl | hrestEnv
        · apply paramVal_regsOk
          · rw [hsregEq]; dsimp [AState.pushBnd, AState.openReg, restoreOwned]; omega
          · have := hok1.2.2.1; dsimp [AState.pushBnd, AState.openReg, restoreOwned]; omega
        · have := henv b0 hrestEnv
          have hnr : s.nextRegion ≤ ((restoreOwned owned (AState.ofCSt s₁)).openReg.2.pushBnd
              (paramVal p (restoreOwned owned (AState.ofCSt s₁)).openReg.1) (p.mode.usage == .once)).2.nextRegion := by
            have := hle1.2.1; dsimp [AState.pushBnd, AState.openReg, restoreOwned, AState.ofCSt] at this ⊢; omega
          exact this.mono hnr
      obtain ⟨rBody, s₆, hbody, h⟩ := CM_bind_elim h
      let sLamBody : CSt := ((restoreOwned owned (AState.ofCSt s₁)).openReg.2.pushBnd
        (paramVal p (restoreOwned owned (AState.ofCSt s₁)).openReg.1) (p.mode.usage == .once)).2.toCSt s₁.steps
      obtain ⟨hatBody, hok6, hle6, _, _⟩ := ihTerm _ body sLamBody rBody s₆ hokPush henvBody hbody
      obtain ⟨_, s₇, hret, h⟩ := CM_bind_elim h
      have hretRuns := (stepIndep_retCheck rBody.skel res (restoreOwned owned (AState.ofCSt s₁)).openReg.1
        { rBody with cls := rc } "a closure's result").toRuns hret
      obtain ⟨_, hle7, _⟩ := statePres_retCheck _ _ _ _ _ s₆ () s₇ hok6 hret
      obtain ⟨consumed, s₈, hcons, h⟩ := CM_bind_elim h
      obtain ⟨hs₈, _, hconsProp⟩ := forIn_consumed_props owned false consumed s₇ s₈ hcons
      subst s₈
      obtain ⟨after, s₉, hget2, h⟩ := CM_bind_elim h
      rw [CM_get_run] at hget2
      simp only [Except.ok.injEq, Prod.mk.injEq] at hget2
      obtain ⟨rfl, rfl⟩ := hget2
      obtain ⟨_, s₁₀, hset, h⟩ := CM_bind_elim h
      rw [CM_set_run] at hset
      simp only [Except.ok.injEq, Prod.mk.injEq] at hset
      obtain ⟨_, rfl⟩ := hset
      obtain ⟨rfl, rfl⟩ := CM_pure_elim h
      have hnrLe : s₁.nextRegion ≤ s₇.nextRegion := by
        have h1 : s₁.nextRegion ≤ ((restoreOwned owned (AState.ofCSt s₁)).openReg.2.pushBnd
            (paramVal p (restoreOwned owned (AState.ofCSt s₁)).openReg.1) (p.mode.usage == .once)).2.nextRegion := by
          dsimp [AState.pushBnd, AState.openReg, restoreOwned, AState.ofCSt]; omega
        exact Nat.le_trans h1 (hle6.trans hle7).2.1
      have hokEnd : AStateOk (AState.ofCSt { s₁ with steps := s₇.steps, nextRegion := s₇.nextRegion }) :=
        AStateOk_set_nextRegion hok1 hnrLe
      have hleEnd : AStateLe (AState.ofCSt s) (AState.ofCSt { s₁ with steps := s₇.steps, nextRegion := s₇.nextRegion }) :=
        AStateLe_set_nextRegion hle1 hnrLe
      have hvOkEnd : ValRegsOk s₇.nextRegion
          { cls := .val, deps, regs, onceOnly := consumed, skel := .arrow p.mode p.skel res rBody.skel } :=
        fun r hr => Nat.lt_of_lt_of_le (hregsOk1 r hr) hnrLe
      exact ⟨.lam hcaps hatBody hretRuns hconsProp rfl, hokEnd, hleEnd, hreg1, hvOkEnd⟩
theorem CM_forIn_zipIdx_inv {α β : Type} (I : Nat → β → CSt → Prop)
    (P : Nat → α → Prop)
    (step : α × Nat → β → CM (ForInStep β))
    (hstep : ∀ a j acc st acc' st', I j acc st → P j a →
      (step (a, j) acc).run st = .ok (.yield acc', st') → I (j + 1) acc' st')
    (hnoDone : ∀ a j acc st acc' st', I j acc st → P j a →
      (step (a, j) acc).run st = .ok (.done acc', st') → False) :
    ∀ (l : List α) (off : Nat) (acc out : β) (st st' : CSt),
      I off acc st →
      (∀ i a, l[i]? = some a → P (off + i) a) →
      (forIn (m := CM) (l.zipIdx off) acc step).run st = .ok (out, st') →
      I (off + l.length) out st' := by
  intro l
  induction l with
  | nil =>
    intro off acc out st st' hi _ hf
    simp only [List.zipIdx_nil, List.forIn_nil] at hf
    obtain ⟨rfl, rfl⟩ := CM_pure_elim hf
    simpa using hi
  | cons a rest ih =>
    intro off acc out st st' hi hp hf
    simp only [List.zipIdx_cons, List.forIn_cons] at hf
    obtain ⟨sRes, st₁, hs, hf⟩ := CM_bind_elim hf
    have hp0 : P off a := by simpa using hp 0 a (by simp)
    cases sRes with
    | done b => exact False.elim (hnoDone a off acc st b st₁ hi hp0 hs)
    | yield b =>
      dsimp only at hf
      have hres := ih (off + 1) b out st₁ st' (hstep a off acc st b st₁ hi hp0 hs)
        (fun i x hx => by
          have := hp (i + 1) x (by simpa using hx)
          rwa [show off + (i + 1) = off + 1 + i by omega] at this)
        hf
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hres

theorem anCase_major_elim {P : Prog} {n : Nat} {env : List ABnd} {mj : Term} {s s' : CSt} {v : AVal}
    (ihTerm : TermSoundAt P n)
    (hok : AStateOk (AState.ofCSt s)) (henv : EnvRegsOk s.nextRegion env)
    (cont : AVal × Bool → CM AVal)
    (h : (match mj with
      | Term.var j mc =>
        match env[j]? with
        | some b => do
          let v ← readVar env j
          if (b.mode.isUnique && mc == Cls.val) = true then do
            flowTo (Dest.uniq b.mode.isBorrowed) v.skel v "a consuming match"
            let __x ← pure (({ cls := mc, own := Own.uniq, regs := v.regs, skel := v.skel, onceOnly := v.onceOnly } : AVal), true)
            cont __x
          else do
            let __x ← pure (({ cls := mc, own := v.own, deps := v.deps, regs := v.regs, skel := v.skel, onceOnly := v.onceOnly, src := v.src } : AVal), false)
            cont __x
        | _ => do
          let __x ← refuseM "a variable out of scope"
          cont __x
      | t => do
        let __do_lift ← anTerm P n env t
        let __x ← pure (__do_lift, false)
        cont __x).run s = .ok (v, s')) :
    ∃ mv consuming sPre,
      AMajor P env mj (AState.ofCSt s) mv consuming (AState.ofCSt sPre) ∧
      AStateOk (AState.ofCSt sPre) ∧ AStateLe (AState.ofCSt s) (AState.ofCSt sPre) ∧
      sPre.regions = s.regions ∧ ValRegsOk sPre.nextRegion mv ∧
      (cont (mv, consuming)).run sPre = .ok (v, s') := by
  have hnonVar : (∀ j mc, mj ≠ .var j mc) →
      (do let __do_lift ← anTerm P n env mj; let __x ← pure (__do_lift, false); cont __x).run s = .ok (v, s') →
      ∃ mv consuming sPre,
        AMajor P env mj (AState.ofCSt s) mv consuming (AState.ofCSt sPre) ∧
        AStateOk (AState.ofCSt sPre) ∧ AStateLe (AState.ofCSt s) (AState.ofCSt sPre) ∧
        sPre.regions = s.regions ∧ ValRegsOk sPre.nextRegion mv ∧
        (cont (mv, consuming)).run sPre = .ok (v, s') := by
    intro hne hnv
    obtain ⟨rv, s₁, htm, hnv⟩ := CM_bind_elim hnv
    obtain ⟨⟨mv, consuming⟩, sPre, hp, hnv⟩ := CM_bind_elim hnv
    obtain ⟨hpair, hs1⟩ := CM_pure_elim hp; subst sPre
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    obtain ⟨hat, hokP, hleP, hregP, hvOk⟩ := ihTerm env mj s rv s₁ hok henv htm
    exact ⟨rv, false, s₁, .nonVar hne hat, hokP, hleP, hregP, hvOk, hnv⟩
  cases mj with
  | var j mc =>
    cases hej : env[j]? with
    | none =>
      simp only [hej] at h
      obtain ⟨_, _, href, _⟩ := CM_bind_elim h; rw [CM_refuseM_run] at href; cases href
    | some b =>
      simp only [hej] at h
      obtain ⟨rv, s₁, hrv, h⟩ := CM_bind_elim h
      obtain ⟨hs₁, b', hb', hvregs⟩ := readVar_props hrv
      subst s₁
      have hbeq : b' = b := by rw [hej] at hb'; exact Option.some.inj hb'.symm
      subst b'
      have hrvRuns := (stepIndep_readVar env j).toRuns hrv
      have hrvOk : ValRegsOk s.nextRegion rv := by
        intro r hr; rw [hvregs] at hr; exact henv b (List.mem_of_getElem? hej) r hr
      cases hcu : (b.mode.isUnique && mc == .val) with
      | true =>
        simp only [hcu, ↓reduceIte] at h
        obtain ⟨_, s₂, hft, h⟩ := CM_bind_elim h
        obtain ⟨⟨mv, consuming⟩, sPre, hp, h⟩ := CM_bind_elim h
        obtain ⟨hpair, hs2⟩ := CM_pure_elim hp; subst sPre
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
        obtain ⟨hokP, hleP, hregP⟩ :=
          statePres_flowTo (.uniq b.mode.isBorrowed) rv.skel rv "a consuming match" s () s₂ hok hft
        have hftRuns := (stepIndep_flowTo (.uniq b.mode.isBorrowed) rv.skel rv "a consuming match").toRuns hft
        have hbu : b.mode.isUnique = true := (Bool.and_eq_true _ _ |>.mp hcu).1
        have hmc : mc = .val := by
          have h2 := (Bool.and_eq_true _ _ |>.mp hcu).2
          cases mc
          · exact absurd h2 (by decide)
          · exact absurd h2 (by decide)
          · exact absurd h2 (by decide)
          · rfl
        exact ⟨_, true, s₂, .varConsuming hej hrvRuns hbu hmc hftRuns, hokP, hleP, hregP, hrvOk.mono hleP.2.1, h⟩
      | false =>
        simp only [hcu, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨⟨mv, consuming⟩, sPre, hp, h⟩ := CM_bind_elim h
        obtain ⟨hpair, hs⟩ := CM_pure_elim hp; subst sPre
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
        have hor : b.mode.isUnique = false ∨ mc ≠ .val := by
          cases hbu : b.mode.isUnique
          · exact Or.inl rfl
          · right; intro hEq; rw [hbu, hEq] at hcu; exact absurd hcu (by decide)
        exact ⟨_, false, s, .varPlain hej hrvRuns hor, hok, AStateLe.refl _, rfl, hrvOk, h⟩
  | irr | natLit _ | strLit _ | const _ _ | app _ _ _ | lam _ _ _ _ _ | letE _ _ _ _ | proj _ _ _ _ | case _ _ _ _ _ =>
    exact hnonVar (fun _ _ hEq => by cases hEq) h

theorem anCase_step {P : Prog} {n : Nat}
    (ihTerm : TermSoundAt P n) (ihAlt : AltSoundAt P n) : CaseSoundAt P (n + 1) := by
  intro env k mj alts ex c s v s' hok henv h
  rw [anCase.eq_2] at h
  split at h
  · rename_i hszAlts
    have haltsEq : alts.size = k.alts.size := beq_iff_eq.mp hszAlts
    obtain ⟨mv, consuming, pre, hamaj, hokPre, hlePre, hregPre, hmvOk, h⟩ :=
      anCase_major_elim ihTerm hok henv _ h
    dsimp only at h
    obtain ⟨pre2, sPre2, hgetPre, h⟩ := CM_bind_elim h
    rw [CM_get_run] at hgetPre
    simp only [Except.ok.injEq, Prod.mk.injEq] at hgetPre
    obtain ⟨rfl, rfl⟩ := hgetPre
    rw [← Array.forIn_toList, Array.toList_zipIdx] at h
    obtain ⟨⟨posts, results, stepsOut, nextRegOut⟩, sAfterAlts, haltsLoop, h⟩ := CM_bind_elim h
    let IAlts : Nat → (Array CSt × Array AVal × Nat × Nat) → CSt → Prop :=
      fun off tup _ =>
        let (posts0, results0, _, nextReg0) := tup
        posts0.size = off ∧ results0.size = off ∧ pre.nextRegion ≤ nextReg0 ∧
        (∀ i, i < off → ∀ ca altT post res,
          k.alts[i]? = some ca → alts[i]? = some altT →
          posts0[i]? = some post → results0[i]? = some res →
          BranchOk P env k mv consuming (AState.ofCSt pre) i ca altT res post ∧
          post.nextRegion ≤ nextReg0)
    have hAltsInv :
        IAlts (0 + k.alts.toList.length) (posts, results, stepsOut, nextRegOut) sAfterAlts := by
      refine CM_forIn_zipIdx_inv IAlts (fun j ca => k.alts[j]? = some ca) _
        (fun ca off acc st acc' st' ⟨hp0, hr0, hnr0, hinv⟩ hcaOff hstep => ?_)
        (fun ca off acc st acc' st' _ _ hstep => ?_)
        k.alts.toList 0 (#[], #[], pre.steps, pre.nextRegion) (posts, results, stepsOut, nextRegOut) pre sAfterAlts
        ⟨rfl, rfl, Nat.le_refl _, fun _ hi => by omega⟩
        (fun i ca hca => by simpa using hca)
        haltsLoop
      · obtain ⟨posts0, results0, steps0, nextReg0⟩ := acc
        dsimp only at hstep hp0 hr0 hnr0 hinv
        obtain ⟨_, st3, hset0, hstep⟩ := CM_bind_elim hstep
        rw [CM_set_run] at hset0
        simp only [Except.ok.injEq, Prod.mk.injEq] at hset0
        obtain ⟨_, rfl⟩ := hset0
        cases haltGet : alts[off]? with
        | none =>
          simp only [haltGet] at hstep
          obtain ⟨_, _, href, _⟩ := CM_bind_elim hstep; rw [CM_refuseM_run] at href; cases href
        | some altT =>
          simp only [haltGet] at hstep
          obtain ⟨r_j, st4, haltRun, hstep⟩ := CM_bind_elim hstep
          have hokStart : AStateOk (AState.ofCSt { pre with steps := steps0, nextRegion := nextReg0 }) :=
            AStateOk_set_nextRegion hokPre hnr0
          have henvStart : EnvRegsOk nextReg0 env := (henv.mono hlePre.2.1).mono hnr0
          have hargsStart : ∀ x ∈ caseAltArgs P k mv consuming off ca, ValRegsOk nextReg0 x.1 :=
            caseAltArgs_regsOk (hmvOk.mono hnr0)
          obtain ⟨haltDeriv, hok4, hle4, hreg4, hrjOk⟩ :=
            ihAlt env altT (caseAltArgs P k mv consuming off ca)
              { pre with steps := steps0, nextRegion := nextReg0 } r_j st4 hokStart henvStart hargsStart haltRun
          obtain ⟨_, st5, hnoRun, hstep⟩ := CM_bind_elim hstep
          have hst5 := notOnceSrc_state_eq hnoRun; subst st5
          have hnoRuns := (stepIndep_notOnceSrc r_j "a case alternative's result").toRuns hnoRun
          cases hoj : r_j.onceOnly with
          | true =>
            simp only [hoj, ↓reduceIte] at hstep
            obtain ⟨_, _, href, _⟩ := CM_bind_elim hstep; rw [CM_refuseM_run] at href; cases href
          | false =>
            simp only [hoj, Bool.false_eq_true, ↓reduceIte] at hstep
            obtain ⟨_, st6, hvalRun, hstep⟩ := CM_bind_elim hstep
            have hst6 := valid_state_eq hvalRun; subst st6
            have hvalRuns := (stepIndep_valid r_j "a case alternative's result").toRuns hvalRun
            obtain ⟨uniq_j, st7, huniqRun, hstep⟩ := CM_bind_elim hstep
            have hst7 := isUniq_state_eq huniqRun; subst st7
            have huniqRuns := (stepIndep_isUniq r_j).toRuns huniqRun
            obtain ⟨postJ, st8, hgetP, hstep⟩ := CM_bind_elim hstep
            rw [CM_get_run] at hgetP
            simp only [Except.ok.injEq, Prod.mk.injEq] at hgetP
            obtain ⟨rfl, rfl⟩ := hgetP
            obtain ⟨hy, hs8⟩ := CM_pure_elim hstep
            injection hy with haccEq; subst haccEq; subst st'
            have hnrStep : nextReg0 ≤ st4.nextRegion := hle4.2.1
            have hlePrePost : AStateLe (AState.ofCSt pre) (AState.ofCSt st4) :=
              (AStateLe_set_nextRegion (AStateLe.refl _) hnr0).trans hle4
            have hbrOff : BranchOk P env k mv consuming (AState.ofCSt pre) off ca altT
                { cls := r_j.cls,
                  own := if r_j.own == Own.uniq && uniq_j then Own.uniq else Own.shared,
                  deps := r_j.deps.filter (· < pre.st.size),
                  regs := r_j.regs, skel := r_j.skel, onceOnly := false, src := r_j.src } st4 :=
              ⟨nextReg0, r_j, AState.ofCSt st4, AState.ofCSt st4, AState.ofCSt st4, uniq_j,
                hnr0, haltDeriv, hnoRuns, hoj, hvalRuns, huniqRuns, hok4, hlePrePost, hreg4, hrjOk,
                by cases r_j; simp at hoj; subst hoj; rfl⟩
            refine ⟨by simp [hp0], by simp [hr0], Nat.le_trans hnr0 hnrStep, ?_⟩
            intro i hi ca' altT' p' r' hka' halt' hp' hr'
            by_cases heq : i = off
            · subst heq
              rw [hcaOff] at hka'; injection hka' with hcaEq; subst hcaEq
              rw [haltGet] at halt'; injection halt' with haltEq; subst haltEq
              rw [← hp0] at hp'; simp only [Array.getElem?_push_size, Option.some.injEq] at hp'; subst hp'
              rw [← hr0] at hr'; simp only [Array.getElem?_push_size, Option.some.injEq] at hr'; subst hr'
              exact ⟨hbrOff, Nat.le_refl _⟩
            · have hltI : i < off := by omega
              rw [Array.getElem?_push_lt (by omega)] at hp'
              rw [Array.getElem?_push_lt (by omega)] at hr'
              have ⟨hbo, hnrO⟩ := hinv i hltI ca' altT' p' r' hka' halt'
                (by rwa [Array.getElem?_eq_getElem (by omega)])
                (by rwa [Array.getElem?_eq_getElem (by omega)])
              exact ⟨hbo, Nat.le_trans hnrO hnrStep⟩
      · obtain ⟨posts0, results0, steps0, nextReg0⟩ := acc
        dsimp only at hstep
        obtain ⟨_, st3, hset0, hstep⟩ := CM_bind_elim hstep
        rw [CM_set_run] at hset0; simp only [Except.ok.injEq, Prod.mk.injEq] at hset0; obtain ⟨_, rfl⟩ := hset0
        cases haltGet : alts[off]? with
        | none =>
          simp only [haltGet] at hstep
          obtain ⟨_, _, href, _⟩ := CM_bind_elim hstep; rw [CM_refuseM_run] at href; cases href
        | some altT =>
          simp only [haltGet] at hstep
          obtain ⟨r_j, st4, _, hstep⟩ := CM_bind_elim hstep
          obtain ⟨_, st5, _, hstep⟩ := CM_bind_elim hstep
          cases hoj : r_j.onceOnly with
          | true =>
            simp only [hoj, ↓reduceIte] at hstep
            obtain ⟨_, _, href, _⟩ := CM_bind_elim hstep; rw [CM_refuseM_run] at href; cases href
          | false =>
            simp only [hoj, Bool.false_eq_true, ↓reduceIte] at hstep
            obtain ⟨_, st6, _, hstep⟩ := CM_bind_elim hstep
            obtain ⟨_, st7, _, hstep⟩ := CM_bind_elim hstep
            obtain ⟨_, st8, _, hstep⟩ := CM_bind_elim hstep
            obtain ⟨hy, _⟩ := CM_pure_elim hstep; cases hy
    obtain ⟨hpostsSz, hresultsSz, hnrOut, hbranches⟩ := hAltsInv
    simp only [Nat.zero_add, Array.length_toList] at hpostsSz hresultsSz hbranches
    -- State join loop
    dsimp only at h
    rw [← Array.forIn_toList] at h
    obtain ⟨⟨stJoin, spentJoin⟩, sAfterSJ, hsjLoop, h⟩ := CM_bind_elim h
    have hpostsPre : ∀ p ∈ posts.toList, pre.st.size ≤ p.st.size ∧ pre.st.size ≤ p.spent.size := by
      intro p hp
      obtain ⟨idx, hgetI⟩ := List.mem_iff_getElem?.mp hp
      have hltI : idx < posts.size := by
        have := (List.getElem?_eq_some_iff.mp hgetI).1; simpa using this
      have hltK : idx < k.alts.size := by omega
      have hca : k.alts[idx]? = some k.alts[idx] := Array.getElem?_eq_getElem hltK
      have haltT : alts[idx]? = some alts[idx] := Array.getElem?_eq_getElem (by omega)
      have hres : results[idx]? = some results[idx] := Array.getElem?_eq_getElem (by omega)
      have hpost : posts[idx]? = some p := by simpa using hgetI
      obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, hokP, hleP, _, _, _⟩, _⟩ :=
        hbranches idx hltK _ _ p _ hca haltT hpost hres
      exact ⟨hleP.1, by have := hokP.2.1; have := hleP.1; dsimp [AState.ofCSt] at *; omega⟩
    obtain ⟨_, hstJSz, hspJSz, hpreStLe, hpreSpLe, hpostsStLe, hpostsSpLe⟩ :=
      forIn_stateJoin_sound (AState.ofCSt pre) posts.toList pre.st pre.spent stJoin spentJoin
        sAfterAlts sAfterSJ rfl hokPre.2.1.symm hpostsPre hsjLoop
    obtain ⟨_, sJoinCSt, hsetJoin, h⟩ := CM_bind_elim h
    rw [CM_set_run] at hsetJoin
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsetJoin
    obtain ⟨_, rfl⟩ := hsetJoin
    let sJoin : CSt := { pre with st := stJoin, spent := spentJoin, steps := stepsOut, nextRegion := nextRegOut }
    let σ_join : AState := AState.ofCSt sJoin
    have hokJoin : AStateOk σ_join := by
      obtain ⟨h1, h2, hnr, h1in, hnd, hlt⟩ := hokPre
      refine ⟨by dsimp [σ_join, sJoin, AState.ofCSt] at h1 hstJSz ⊢; omega,
        by dsimp [σ_join, sJoin, AState.ofCSt] at h2 hstJSz hspJSz ⊢; omega,
        by dsimp [σ_join, sJoin, AState.ofCSt] at hnr ⊢; omega,
        h1in, hnd, fun r hr => ⟨(hlt r hr).1, by have := (hlt r hr).2; dsimp [σ_join, sJoin, AState.ofCSt] at *; omega⟩⟩
    have hlePreJoin : AStateLe (AState.ofCSt pre) σ_join :=
      ⟨by dsimp [σ_join, sJoin, AState.ofCSt] at hstJSz ⊢; omega, hnrOut, hpreStLe, fun _ _ => rfl,
        fun i hi hsp => hpreSpLe i (by have := hokPre.2.1; dsimp [AState.ofCSt] at *; omega) hsp⟩
    have hZero : k.alts.size = 0 →
        σ_join.st = (AState.ofCSt pre).st ∧ σ_join.once = (AState.ofCSt pre).once ∧
        σ_join.spent = (AState.ofCSt pre).spent ∧ σ_join.regions = (AState.ofCSt pre).regions ∧
        (AState.ofCSt pre).nextRegion ≤ σ_join.nextRegion := by
      intro hz
      have hpostsNil : posts.toList = [] := List.eq_nil_of_length_eq_zero (by simpa [hz] using hpostsSz)
      rw [hpostsNil, List.forIn_nil] at hsjLoop
      obtain ⟨hp, _⟩ := CM_pure_elim hsjLoop
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      exact ⟨rfl, rfl, rfl, rfl, hnrOut⟩
    -- Common tail for `ex` + `applyValue`
    have hexTail : ∀ (r_join : AVal),
        r_join.cls = c → r_join.src = none → r_join.onceOnly = false →
        (∀ d ∈ r_join.deps, d < pre.st.size) →
        ValRegsOk nextRegOut r_join →
        (∀ x ∈ results.toList, ValJoinGe pre.st.size x r_join) →
        ((forIn (m := CM) ex (#[] : Array AVal) fun e __s => do
            let __do_lift ← anTerm P n env e
            pure (ForInStep.yield (__s.push __do_lift))) >>= fun __s_2 =>
          (forIn (m := CM) __s_2.zipIdx r_join fun (x : AVal × Nat) __s => do
            let r ← applyValue __s x.1 (if (x.2 + 1 == __s_2.size) = true then c else Cls.val) "an application"
            pure (ForInStep.yield r)) >>= fun __s => pure __s).run sJoin = .ok (v, s') →
        ATerm P env (.case k mj alts ex c) (AState.ofCSt s) v (AState.ofCSt s') ∧
        AStateOk (AState.ofCSt s') ∧ AStateLe (AState.ofCSt s) (AState.ofCSt s') ∧
        s'.regions = s.regions ∧ ValRegsOk s'.nextRegion v := by
      intro r_join hrjCls hrjSrc hrjOnce hrjDeps hrjRegs hvalJoins htail
      rw [← Array.forIn_toList] at htail
      obtain ⟨avs, sEx, hexLoop, htail⟩ := CM_bind_elim htail
      obtain ⟨newAvs, havsEq, hevals, hokEx, hleEx, hregEx, havsOk⟩ :=
        forIn_evals_sound (fun hok' henv' ht' => ihTerm env _ _ _ _ hok' henv' ht')
          ex.toList #[] avs sJoin sEx hokJoin (henv.mono (hlePre.trans hlePreJoin).2.1) hexLoop
      have havsList : avs.toList = newAvs := by simpa using havsEq
      rw [← Array.forIn_toList] at htail
      have hzip : avs.zipIdx.toList = newAvs.zipIdx 0 := by rw [Array.toList_zipIdx, havsList]
      rw [hzip] at htail
      have hszEx : avs.size = 0 + newAvs.length := by rw [Nat.zero_add, ← havsList]; rfl
      rw [hszEx] at htail
      obtain ⟨resEnd, sEnd, happLoop, htail⟩ := CM_bind_elim htail
      obtain ⟨rfl, rfl⟩ := CM_pure_elim htail
      obtain ⟨happsNonEmpty, happsEmpty, hokEnd, hleEnd, hregEnd, hresEndOk⟩ :=
        forIn_applyZipIdx_sound newAvs 0 r_join resEnd sEx sEnd hokEx (hrjRegs.mono hleEx.2.1) havsOk happLoop
      have happsAll : AApps r_join newAvs c (AState.ofCSt sEx) resEnd (AState.ofCSt sEnd) := by
        cases newAvs with
        | nil =>
          obtain ⟨rfl, rfl⟩ := happsEmpty rfl
          have heq : ({ resEnd with cls := c } : AVal) = resEnd := by
            cases resEnd; simp at hrjCls; subst hrjCls; rfl
          rw [← heq]
          exact .nil
        | cons _ _ => exact happsNonEmpty (by simp)
      have hAAlts : AAlts P env k mv consuming (AState.ofCSt pre) 0 k.alts.toList alts.toList r_join σ_join := by
        refine branchOk_to_AAlts (posts := posts) (results := results) 0 k.alts.toList alts.toList (by simp [haltsEq]) (fun idx ca altT hca haltT => ?_)
        simp only [Nat.zero_add]
        have hltK : idx < k.alts.size := by
          have := (List.getElem?_eq_some_iff.mp hca).1; simpa using this
        have hcaA : k.alts[idx]? = some ca := by simpa using hca
        have haltA : alts[idx]? = some altT := by simpa using haltT
        have hpostA : posts[idx]? = some posts[idx] := Array.getElem?_eq_getElem (by omega)
        have hresA : results[idx]? = some results[idx] := Array.getElem?_eq_getElem (by omega)
        obtain ⟨hbr, hnrPost⟩ := hbranches idx hltK ca altT posts[idx] results[idx] hcaA haltA hpostA hresA
        have hpostMem : posts[idx] ∈ posts.toList := array_mem_toList_of_getElem?' hpostA
        have hresMem : results[idx] ∈ results.toList := array_mem_toList_of_getElem?' hresA
        have hsj : StateJoinGe (AState.ofCSt pre) (AState.ofCSt posts[idx]) σ_join :=
          ⟨hstJSz, rfl, by dsimp [σ_join, sJoin, AState.ofCSt]; rw [hspJSz]; exact hokPre.2.1, rfl, hnrPost,
            fun i hi => hpostsStLe posts[idx] hpostMem i hi,
            fun i hi hsp => hpostsSpLe posts[idx] hpostMem i (by have := hokPre.2.1; dsimp [AState.ofCSt] at *; omega) hsp⟩
        exact ⟨posts[idx], results[idx], hpostA, hresA, hbr, hsj, hvalJoins results[idx] hresMem⟩
      exact ⟨.caseTerm haltsEq hamaj hAAlts hZero hrjCls hrjSrc hrjOnce hrjDeps hrjRegs hevals happsAll,
        hokEnd, ((hlePre.trans hlePreJoin).trans hleEx).trans hleEnd,
        hregEnd.trans (hregEx.trans hregPre), hresEndOk⟩
    -- Dispatch on `results[0]?`
    cases hr0 : results[0]? with
    | none =>
      simp only [hr0] at h
      apply hexTail { cls := c } rfl rfl rfl (fun _ hm => by cases hm) (fun _ hm => by cases hm)
      · intro x hx
        have hsz0 : results.size = 0 := by
          by_cases hpos : 0 < results.size
          · rw [Array.getElem?_eq_getElem hpos] at hr0; cases hr0
          · omega
        have hnil : results.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using hsz0)
        rw [hnil] at hx; cases hx
      · exact h
    | some r0 =>
      simp only [hr0] at h
      rw [← Array.forIn_toList] at h
      obtain ⟨r0Join, sAfterVJ, hvjLoop, h⟩ := CM_bind_elim h
      have hallRes : ∀ x ∈ results.toList,
          (∀ d ∈ x.deps, d < pre.st.size) ∧ ValRegsOk nextRegOut x ∧ x.onceOnly = false := by
        intro x hx
        obtain ⟨idx, hgetI⟩ := List.mem_iff_getElem?.mp hx
        have hltI : idx < results.size := by
          have := (List.getElem?_eq_some_iff.mp hgetI).1; simpa using this
        have hltK : idx < k.alts.size := by omega
        have hca : k.alts[idx]? = some k.alts[idx] := Array.getElem?_eq_getElem hltK
        have haltT : alts[idx]? = some alts[idx] := Array.getElem?_eq_getElem (by omega)
        have hpost : posts[idx]? = some posts[idx] := Array.getElem?_eq_getElem (by omega)
        have hres : results[idx]? = some x := by simpa using hgetI
        obtain ⟨⟨_, r_j, _, _, _, _, _, _, _, hoj, _, _, _, _, _, hrjOk, hxEq⟩, hnrPost⟩ :=
          hbranches idx hltK _ _ _ x hca haltT hpost hres
        subst hxEq
        exact ⟨fun d hd => of_decide_eq_true (List.mem_filter.mp hd).2, hrjOk.mono hnrPost, hoj⟩
      obtain ⟨hr0Deps, hr0Regs, hr0Once⟩ := hallRes r0 (array_mem_toList_of_getElem?' hr0)
      obtain ⟨hsVJ, hsk, hown, _, hdR, hdLt, _, hrR, hrLt, ho1, hadR⟩ :=
        forIn_valJoin_sound results.toList r0 r0Join sJoin sAfterVJ hr0Deps hr0Regs hr0Once hallRes hvjLoop
      subst sAfterVJ
      let rJoin : AVal := { r0Join with cls := c, src := none }
      apply hexTail rJoin rfl rfl ho1 hdLt hrLt
      · intro x hx
        have hxOnce := (hallRes x hx).2.2
        exact ⟨by rw [hsk]; exact hadR x hx, fun hu => (hown hu).2 x hx,
          fun d hd _ => hdR x hx d hd, fun reg hreg => hrR x hx reg hreg,
          fun h0 => by rw [hxOnce] at h0; cases h0⟩
      · exact h
  · obtain ⟨_, _, href, _⟩ := CM_bind_elim h; rw [CM_refuseM_run] at href; cases href

theorem anAlt_step {P : Prog} {n : Nat}
    (ihTerm : TermSoundAt P n) (ihAlt : AltSoundAt P n) : AltSoundAt P (n + 1) := by
      intro env t args s v s' hok henv hargs h
      cases args with
      | nil =>
        unfold anAlt at h
        obtain ⟨hat, hok', hle', hreg', hvOk⟩ := ihTerm env t s v s' hok henv h
        exact ⟨.nil hat, hok', hle', hreg', hvOk⟩
      | cons arg0 rest =>
        obtain ⟨a0, er, fromCell⟩ := arg0
        unfold anAlt at h
        cases t with
        | lam p res rc fvs body =>
          obtain ⟨sreg, s₁, hop, h⟩ := CM_bind_elim h
          rw [openReg_run] at hop
          simp only [Except.ok.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop
          obtain ⟨hok1, hsregEq, hsregNotMem⟩ := hok.openReg
          have hle01 : AStateLe (AState.ofCSt s) (AState.ofCSt s).openReg.2 := AStateLe_openReg _
          have ha0Ok : ValRegsOk s.nextRegion a0 := hargs (a0, er, fromCell) (List.mem_cons_self ..)
          cases er with
          | true =>
            simp only [↓reduceIte] at h
            obtain ⟨⟨mode, bv⟩, s₂, hp, h⟩ := CM_bind_elim h
            obtain ⟨hpair, rfl⟩ := CM_pure_elim hp
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
            obtain ⟨id, s₃, hnb, h⟩ := CM_bind_elim h
            rw [newBnd_run] at hnb
            simp only [AState.ofCSt_toCSt, toCSt_steps, Except.ok.injEq, Prod.mk.injEq] at hnb
            obtain ⟨rfl, rfl⟩ := hnb
            obtain ⟨hok3, hle13⟩ := hok1.pushBnd { cls := .irr } false
            have henv3 : EnvRegsOk ((AState.ofCSt s).openReg.2.pushBnd { cls := .irr } false).2.nextRegion
                ({ id := (AState.ofCSt s).openReg.2.st.size, mode := .erased, val := { cls := .irr } } :: env) := by
              intro b0 hb0
              rcases List.mem_cons.mp hb0 with rfl | hrest
              · intro _ hm; cases hm
              · exact (henv b0 hrest).mono (by dsimp [AState.pushBnd, AState.openReg, AState.ofCSt]; omega)
            have hargs3 : ∀ x ∈ rest, ValRegsOk ((AState.ofCSt s).openReg.2.pushBnd { cls := .irr } false).2.nextRegion x.1 :=
              fun x hx => (hargs x (List.mem_cons_of_mem _ hx)).mono (by dsimp [AState.pushBnd, AState.openReg, AState.ofCSt]; omega)
            obtain ⟨r, s₄, haltR, h⟩ := CM_bind_elim h
            let sAltEr : CSt := ((AState.ofCSt s).openReg.2.pushBnd { cls := .irr } false).2.toCSt s.steps
            obtain ⟨haltDeriv, hok4, hle34, hreg34, hrOk⟩ := ihAlt _ body rest sAltEr r s₄ hok3 henv3 hargs3 haltR
            obtain ⟨_, s₅, hret, h⟩ := CM_bind_elim h
            have hretRuns := (stepIndep_retCheck r.skel res (AState.ofCSt s).openReg.1 { r with cls := rc } "a case alternative").toRuns hret
            obtain ⟨hok5, hle45, hreg45⟩ := statePres_retCheck _ _ _ _ _ s₄ () s₅ hok4 hret
            obtain ⟨_, s₆, hcl, h⟩ := CM_bind_elim h
            rw [closeReg_run] at hcl
            simp only [Except.ok.injEq, Prod.mk.injEq] at hcl
            obtain ⟨_, rfl⟩ := hcl
            obtain ⟨inner, s₇, hin, h⟩ := CM_bind_elim h
            rw [innermost_run] at hin
            simp only [AState.toCSt, Except.ok.injEq, Prod.mk.injEq] at hin
            obtain ⟨rfl, rfl⟩ := hin
            obtain ⟨rfl, rfl⟩ := CM_pure_elim h
            have hsregNe1 : (AState.ofCSt s).openReg.1 ≠ 1 := by
              have := hok.2.2.1; rw [hsregEq]; omega
            have hok6 : AStateOk ((AState.ofCSt s₅).closeReg (AState.ofCSt s).openReg.1) :=
              hok5.closeReg hsregNe1
            have hreg6 : ((AState.ofCSt s₅).closeReg (AState.ofCSt s).openReg.1).regions = s.regions := by
              dsimp only [AState.closeReg]
              change s₅.regions.filter (· != (AState.ofCSt s).openReg.1) = s.regions
              rw [hreg45, hreg34]
              dsimp only [AState.pushBnd, AState.openReg, AState.toCSt]
              exact closeReg_cons_of_not_mem hsregNotMem
            have hleTot : AStateLe (AState.ofCSt s) ((AState.ofCSt s₅).closeReg (AState.ofCSt s).openReg.1) :=
              (((hle01.trans hle13).trans hle34).trans hle45).trans (AStateLe_closeReg _ _)
            have hinLt : ((AState.ofCSt s₅).closeReg (AState.ofCSt s).openReg.1).regions.headD 1 < s₅.nextRegion :=
              innermost_lt_of_AStateOk hok6
            have hrvOk : ValRegsOk s₅.nextRegion
                (altRetVal res rc (AState.ofCSt s).openReg.1
                  (((AState.ofCSt s₅).closeReg (AState.ofCSt s).openReg.1).regions.headD 1) r) := by
              unfold altRetVal
              intro reg hreg; dsimp only at hreg
              split at hreg
              · cases hreg
              · split at hreg
                · exact regs_natUnion_lt (fun x hx => (hrOk.mono hle45.2.1) x (List.mem_filter.mp hx).1)
                    (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hinLt) reg hreg
                · exact (hrOk.mono hle45.2.1) reg (List.mem_filter.mp hreg).1
            exact ⟨.lamErased haltDeriv hretRuns, hok6, hleTot, hreg6, hrvOk⟩
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h
            let aVal : AVal := if fromCell && p.cls != .val then { a0 with deps := [], regs := [] } else a0
            have haValOk : ValRegsOk s.nextRegion aVal := by
              dsimp only [aVal]
              split
              · intro _ hm; cases hm
              · exact ha0Ok
            cases had : p.skel.admits aVal.skel with
            | false =>
              simp only [aVal] at had
              simp only [had, Bool.false_eq_true, ↓reduceIte] at h
              obtain ⟨_, _, href, _⟩ := CM_bind_elim h; rw [CM_refuseM_run] at href; cases href
            | true =>
              simp only [aVal] at had
              simp only [had, ↓reduceIte] at h
              obtain ⟨bv0, s₂, hbi, h⟩ := CM_bind_elim h
              obtain ⟨⟨mode, bv⟩, s₂', hp, h⟩ := CM_bind_elim h
              obtain ⟨hpair, hs2'⟩ := CM_pure_elim hp; subst s₂'
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
              dsimp only at h
              have hbiRuns := (stepIndep_bindInner p.mode p.cls aVal (AState.ofCSt s).openReg.1 "a case field's binder").toRuns hbi
              let s1Alt : CSt := (AState.ofCSt s).openReg.2.toCSt s.steps
              obtain ⟨hok2, hle12, hreg12⟩ :=
                statePres_bindInner p.mode p.cls aVal (AState.ofCSt s).openReg.1 "a case field's binder" s1Alt bv0 s₂ hok1 hbi
              have hbvOk : ValRegsOk s₂.nextRegion bv0 :=
                bindInner_regsOk (s := s1Alt) hok1
                  (haValOk.mono (by dsimp [s1Alt, AState.openReg, AState.ofCSt, AState.toCSt]; omega))
                  (by rw [hsregEq]; dsimp [s1Alt, AState.openReg, AState.ofCSt, AState.toCSt]; omega) hbi
              obtain ⟨id, s₃, hnb, h⟩ := CM_bind_elim h
              rw [newBnd_run] at hnb
              simp only [Except.ok.injEq, Prod.mk.injEq] at hnb
              obtain ⟨rfl, rfl⟩ := hnb
              obtain ⟨hok3, hle23⟩ := hok2.pushBnd bv0 (p.mode.usage == .once)
              have henv3 : EnvRegsOk s₂.nextRegion ({ id := s₂.st.size, mode := p.mode, val := bv0 } :: env) := by
                intro b0 hb0
                rcases List.mem_cons.mp hb0 with rfl | hrest
                · exact hbvOk
                · exact (henv b0 hrest).mono (hle01.trans hle12).2.1
              have hargs3 : ∀ x ∈ rest, ValRegsOk s₂.nextRegion x.1 :=
                fun x hx => (hargs x (List.mem_cons_of_mem _ hx)).mono (hle01.trans hle12).2.1
              obtain ⟨r, s₄, haltR, h⟩ := CM_bind_elim h
              let sAltKept : CSt := ((AState.ofCSt s₂).pushBnd bv0 (p.mode.usage == .once)).2.toCSt s₂.steps
              obtain ⟨haltDeriv, hok4, hle34, hreg34, hrOk⟩ := ihAlt _ body rest sAltKept r s₄ hok3 henv3 hargs3 haltR
              obtain ⟨_, s₅, hret, h⟩ := CM_bind_elim h
              have hretRuns := (stepIndep_retCheck r.skel res (AState.ofCSt s).openReg.1 { r with cls := rc } "a case alternative").toRuns hret
              obtain ⟨hok5, hle45, hreg45⟩ := statePres_retCheck _ _ _ _ _ s₄ () s₅ hok4 hret
              obtain ⟨_, s₆, hcl, h⟩ := CM_bind_elim h
              rw [closeReg_run] at hcl
              simp only [Except.ok.injEq, Prod.mk.injEq] at hcl
              obtain ⟨_, rfl⟩ := hcl
              obtain ⟨inner, s₇, hin, h⟩ := CM_bind_elim h
              rw [innermost_run] at hin
              simp only [AState.toCSt, Except.ok.injEq, Prod.mk.injEq] at hin
              obtain ⟨rfl, rfl⟩ := hin
              obtain ⟨rfl, rfl⟩ := CM_pure_elim h
              have hsregNe1 : (AState.ofCSt s).openReg.1 ≠ 1 := by
                have := hok.2.2.1; rw [hsregEq]; omega
              have hok6 : AStateOk ((AState.ofCSt s₅).closeReg (AState.ofCSt s).openReg.1) :=
                hok5.closeReg hsregNe1
              have hreg6 : ((AState.ofCSt s₅).closeReg (AState.ofCSt s).openReg.1).regions = s.regions := by
                dsimp only [AState.closeReg]
                change s₅.regions.filter (· != (AState.ofCSt s).openReg.1) = s.regions
                rw [hreg45, hreg34]; dsimp only [sAltKept, AState.pushBnd, AState.toCSt, AState.ofCSt]
                rw [hreg12]; dsimp only [s1Alt, AState.openReg, AState.toCSt, AState.ofCSt]
                exact closeReg_cons_of_not_mem hsregNotMem
              have hleTot : AStateLe (AState.ofCSt s) ((AState.ofCSt s₅).closeReg (AState.ofCSt s).openReg.1) :=
                ((((hle01.trans hle12).trans hle23).trans hle34).trans hle45).trans (AStateLe_closeReg _ _)
              have hinLt : ((AState.ofCSt s₅).closeReg (AState.ofCSt s).openReg.1).regions.headD 1 < s₅.nextRegion :=
                innermost_lt_of_AStateOk hok6
              have hrvOk : ValRegsOk s₅.nextRegion
                  (altRetVal res rc (AState.ofCSt s).openReg.1
                    (((AState.ofCSt s₅).closeReg (AState.ofCSt s).openReg.1).regions.headD 1) r) := by
                unfold altRetVal
                intro reg hreg; dsimp only at hreg
                split at hreg
                · cases hreg
                · split at hreg
                  · exact regs_natUnion_lt (fun x hx => (hrOk.mono hle45.2.1) x (List.mem_filter.mp hx).1)
                      (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hinLt) reg hreg
                  · exact (hrOk.mono hle45.2.1) reg (List.mem_filter.mp hreg).1
              exact ⟨.lamKept had hbiRuns haltDeriv hretRuns, hok6, hleTot, hreg6, hrvOk⟩
        | _ =>
          cases hany : ((a0, er, fromCell) :: rest).any (·.2.1) with
          | true =>
            simp only [hany, ↓reduceIte] at h
            obtain ⟨_, _, href, _⟩ := CM_bind_elim h; rw [CM_refuseM_run] at href; cases href
          | false =>
            simp only [hany, Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨fv, s₁, hfv, h⟩ := CM_bind_elim h
            obtain ⟨hatF, hok1, hle1, hreg1, hfvOk⟩ := ihTerm env _ s fv s₁ hok henv hfv
            obtain ⟨resEnd, s₂, happLoop, h⟩ := CM_bind_elim h
            obtain ⟨rfl, rfl⟩ := CM_pure_elim h
            obtain ⟨happs, hok2, hle2, hreg2, hresOk⟩ :=
              forIn_applyAlt_sound ((a0, er, fromCell) :: rest) fv resEnd s₁ s₂ (by simp)
                hok1 hfvOk (fun x hx => (hargs x hx).mono hle1.2.1) happLoop
            exact ⟨.nonLam (fun _ _ _ _ _ hEq => by cases hEq) hany hatF happs,
              hok2, hle1.trans hle2, hreg2.trans hreg1, hresOk⟩

theorem an_sound (P : Prog) (fuel : Nat) :
    TermSoundAt P fuel ∧ CallSoundAt P fuel ∧ LamSoundAt P fuel ∧
    CaseSoundAt P fuel ∧ AltSoundAt P fuel := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ _ _ _ _ h; simp [anTerm, CM_declineM_run] at h
    · intro _ _ _ _ _ _ _ _ _ h; simp [anCall, CM_declineM_run] at h
    · intro _ _ _ _ _ _ _ _ _ _ _ h; simp [anLam, CM_declineM_run] at h
    · intro _ _ _ _ _ _ _ _ _ _ _ h; simp [anCase, CM_declineM_run] at h
    · intro _ _ _ _ _ _ _ _ _ h; simp [anAlt, CM_declineM_run] at h
  | succ n ih =>
    obtain ⟨ihTerm, ihCall, ihLam, ihCase, ihAlt⟩ := ih
    exact ⟨anTerm_step ihTerm ihCall ihLam ihCase, anCall_step ihTerm, anLam_step ihTerm,
      anCase_step ihTerm ihAlt, anAlt_step ihTerm ihAlt⟩

/-- Soundness of `anDef`: an accepting run produces a step-free `BodyOk` derivation. -/
theorem anDef_sound {P : Prog} {fuel steps : Nat} {params : Array Param} {res : ResultMode}
    {rc : Cls} {rs : Skel} {body : Term}
    (h : (anDef P fuel params res rc rs body).run' { steps } = .ok ()) :
    BodyOk P params res rc rs body := by
  unfold StateT.run' at h
  change (·.1) <$> (anDef P fuel params res rc rs body).run { steps } = .ok () at h
  cases hrun : (anDef P fuel params res rc rs body).run { steps } with
  | error e => rw [hrun] at h; cases h
  | ok pair =>
    obtain ⟨u, sFinal⟩ := pair
    unfold anDef at hrun
    cases hst : (decide (params.size > 0) || res == .shared) with
    | false =>
      simp only [hst, Bool.false_eq_true, ↓reduceIte] at hrun
      obtain ⟨_, _, href, _⟩ := CM_bind_elim hrun; rw [CM_refuseM_run] at href; cases href
    | true =>
      simp only [hst, ↓reduceIte] at hrun
      have hstatic : 0 < params.size ∨ res = .shared := by
        rcases Bool.or_eq_true _ _ |>.mp hst with h1 | h2
        · exact Or.inl (of_decide_eq_true h1)
        · right; cases res <;> simp at h2 ⊢
      obtain ⟨sreg, s₁, hop, hrun⟩ := CM_bind_elim hrun
      rw [openReg_run] at hop
      simp only [Except.ok.injEq, Prod.mk.injEq] at hop
      obtain ⟨rfl, rfl⟩ := hop
      -- Connect `for p in params do newBnd ...` with `initBody params`
      rw [← Array.forIn_toList] at hrun
      obtain ⟨env, s₂, hparamLoop, hrun⟩ := CM_bind_elim hrun
      have hinitLoop : ∀ (ps : List Param) (accEnv : List ABnd) (σ0 : AState),
          (forIn (m := CM) ps accEnv fun p env => do
            let v := paramVal p 2
            let id ← newBnd v (p.mode.usage == .once)
            pure (ForInStep.yield ({ id, mode := p.mode, val := v } :: env))).run (σ0.toCSt steps) =
          .ok ((ps.foldl (fun (e, σ) p =>
            let v := paramVal p 2
            let (id, σ') := σ.pushBnd v (p.mode.usage == .once)
            ({ id, mode := p.mode, val := v } :: e, σ')) (accEnv, σ0)).1,
            (ps.foldl (fun (e, σ) p =>
            let v := paramVal p 2
            let (id, σ') := σ.pushBnd v (p.mode.usage == .once)
            ({ id, mode := p.mode, val := v } :: e, σ')) (accEnv, σ0)).2.toCSt steps) := by
        intro ps
        induction ps with
        | nil => intro accEnv σ0; rfl
        | cons p rest ihP =>
          intro accEnv σ0
          rw [List.forIn_cons, CM_bind_run, CM_bind_run, newBnd_run]
          dsimp only [AState.ofCSt_toCSt, toCSt_steps]
          rw [CM_pure_run]
          dsimp only
          exact ihP _ _
      have hs1Eq : (AState.ofCSt ({ steps } : CSt)).openReg.2.toCSt steps =
          ({ regions := [2, 1], nextRegion := 3 } : AState).toCSt steps := rfl
      have hreg2Eq : (AState.ofCSt ({ steps } : CSt)).openReg.1 = 2 := rfl
      rw [hreg2Eq, hs1Eq, hinitLoop] at hparamLoop
      simp only [Except.ok.injEq, Prod.mk.injEq] at hparamLoop
      obtain ⟨rfl, rfl⟩ := hparamLoop
      have hinitEq : (params.toList.foldl (fun (e, σ) p =>
          let v := paramVal p 2
          let (id, σ') := σ.pushBnd v (p.mode.usage == .once)
          ({ id, mode := p.mode, val := v } :: e, σ')) ([], ({ regions := [2, 1], nextRegion := 3 } : AState))) =
          initBody params := by
        unfold initBody; rw [← Array.foldl_toList]
      rw [hinitEq] at hrun
      obtain ⟨r, s₃, hbody, hret⟩ := CM_bind_elim hrun
      have hokInit : AStateOk (initBody params).2 := AStateOk_initBody params
      have henvInit : EnvRegsOk (initBody params).2.nextRegion (initBody params).1 := by
        unfold initBody; rw [← Array.foldl_toList]
        suffices ∀ (ps : List Param) (acc : List ABnd × AState),
            acc.2.nextRegion = 3 → EnvRegsOk 3 acc.1 →
            let res := ps.foldl (fun (e, σ) p =>
              let v := paramVal p 2
              let (id, σ') := σ.pushBnd v (p.mode.usage == .once)
              ({ id, mode := p.mode, val := v } :: e, σ')) acc
            res.2.nextRegion = 3 ∧ EnvRegsOk 3 res.1 by
          have := this params.toList ([], { regions := [2, 1], nextRegion := 3 }) rfl (fun _ hm => by cases hm)
          rw [this.1]; exact this.2
        intro ps
        induction ps with
        | nil => intro acc hnr he; exact ⟨hnr, he⟩
        | cons p rest ihP =>
          intro acc hnr he
          simp only [List.foldl_cons]
          apply ihP _ (by dsimp [AState.pushBnd]; exact hnr)
          intro b0 hb0
          rcases List.mem_cons.mp hb0 with rfl | hrest
          · exact paramVal_regsOk (by omega) (by omega)
          · exact he b0 hrest
      obtain ⟨hat, _, _, _, _⟩ := (an_sound P fuel).1 (initBody params).1 body ((initBody params).2.toCSt steps) r s₃
        hokInit henvInit hbody
      have hretRuns := (stepIndep_retCheck rs res 2 { r with cls := rc } "the result").toRuns hret
      exact ⟨hstatic, r, AState.ofCSt s₃, AState.ofCSt sFinal, hat, hretRuns⟩

/-! ## Section 4 (`F5c`): Unchecked Default Bodies -/

theorem Reading.complete_walked {rd : Reading} (h : rd.complete = .ok ()) : rd.walked = true := by
  unfold Reading.complete at h
  cases hw : rd.walked with
  | true => rfl
  | false =>
    simp only [hw, Bool.false_eq_true, ↓reduceIte, Ex_throw, Ex_bind_err] at h
    cases h

theorem array_attach_any_false {α : Type} {arr : Array α} {p : α → Bool}
    (h : arr.attach.any (fun ⟨x, _⟩ => p x) = false) :
    ∀ x ∈ arr.toList, p x = false := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hi' : i < arr.size := by simpa using hi
  have hiA : i < arr.attach.size := by rw [Array.size_attach]; exact hi'
  cases hpx : p arr.toList[i] with
  | false => rfl
  | true =>
    have htrue : arr.attach.any (fun ⟨y, _⟩ => p y) = true := by
      rw [Array.any_eq_true]
      exact ⟨i, hiA, by simpa [Array.getElem_attach] using hpx⟩
    rw [htrue] at h; cases h

theorem termTouchesNonDefault_empty {t : Term} (hmd : TermModesDefault t) :
    termTouchesNonDefault #[] t = false := by
  induction hmd with
  | irr | var | natLit | strLit => simp [termTouchesNonDefault]
  | const => simp [termTouchesNonDefault, Array.contains]
  | app _ _ ihf iha => simp [termTouchesNonDefault, ihf, iha]
  | lam _ _ _ ihb => simpa [termTouchesNonDefault] using ihb
  | letE _ _ ihv ihb => simp [termTouchesNonDefault, ihv, ihb]
  | proj _ ihe => simp [termTouchesNonDefault, Array.contains, ihe]
  | case _ _ _ ihm iha ihe =>
    simp [termTouchesNonDefault, Array.contains, ihm]
    exact ⟨fun i hi => iha _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi)),
      fun i hi => ihe _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi))⟩

/-- A term whose own binders are default (`TermModesDefault`) and that touches no record in `bad`
(where every closure record outside `bad` satisfies `recordDefault c = .ok true`) satisfies
`DefaultTerm P`. -/
theorem termModesDefault_to_defaultTerm {s : Subject} {cl : Classifier} {P : Prog}
    {bad : Array Address}
    (hp : readProg s cl = .ok P)
    (hdefAll : ∀ a c, a ∈ (Reading.make s).closure.toList → s.store a = some c →
      bad.contains a = false → recordDefault c = .ok true) :
    ∀ {t : Term}, TermModesDefault t → termTouchesNonDefault bad t = false → DefaultTerm P t := by
  obtain ⟨_, rt, hrt, _, _, hfindElim, _, _, _⟩ := readProg_elim hp
  have hctorsDef : ∀ ind : Ref, bad.contains ind.block = false →
      ∀ ctor ∈ (P.ctorsOf ind).toList, ∀ ind' ci nP fs,
        P.ctorOf? ctor = some (ind', ci, nP, fs) →
        ∀ f ∈ fs.toList, f.mode = .many ∧ f.fmode = .inherited := by
    intro ind hnotBad ctor hctor ind' ci nP fs hco
    have hblk : ctor.block = ind.block := readProg_ind_ctor_block hp hctor
    have hfindC : P.find? ctor = some (.ctor ind' ci nP fs) := by
      unfold Prog.ctorOf? at hco
      cases hf : P.find? ctor with
      | none => simp [hf] at hco
      | some d =>
        rw [hf] at hco
        cases d <;> simp at hco
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hco
        rfl
    obtain ⟨recC, hmem, hst, _, hrd⟩ := hfindElim ctor _ hfindC
    have hdef := hdefAll ctor.block recC hmem hst (hblk ▸ hnotBad)
    exact readDef_defaultIface hrt hst hdef hrd
  intro t hmd
  induction hmd with
  | irr => intro _; exact .irr
  | var => intro _; exact .var
  | natLit => intro _; exact .natLit
  | strLit => intro _; exact .strLit
  | @const r c =>
    intro htouch
    unfold termTouchesNonDefault at htouch
    refine .const fun d hfind => ?_
    obtain ⟨recC, hmem, hst, _, hrd⟩ := hfindElim r d hfind
    exact readDef_defaultIface hrt hst (hdefAll r.block recC hmem hst htouch) hrd
  | app _ _ ihf iha =>
    intro htouch
    unfold termTouchesNonDefault at htouch
    obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp htouch
    exact .app (ihf h1) (iha h2)
  | lam hpM hres _ ihb =>
    intro htouch
    unfold termTouchesNonDefault at htouch
    exact .lam hpM hres (ihb htouch)
  | letE _ _ ihv ihb =>
    intro htouch
    unfold termTouchesNonDefault at htouch
    obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp htouch
    exact .letE (ihv h1) (ihb h2)
  | @proj sRef i e c _ ihe =>
    intro htouch
    unfold termTouchesNonDefault at htouch
    obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp htouch
    exact .proj (hctorsDef sRef h1) (ihe h2)
  | @case k mj alts ex c _ _ _ ihm iha ihe =>
    intro htouch
    unfold termTouchesNonDefault at htouch
    obtain ⟨h123, h4⟩ := Bool.or_eq_false_iff.mp htouch
    obtain ⟨h12, h3⟩ := Bool.or_eq_false_iff.mp h123
    obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp h12
    exact .case (hctorsDef k.ind h1) (ihm h2)
      (fun a ha => iha a ha (array_attach_any_false h3 a ha))
      (fun e he => ihe e he (array_attach_any_false h4 e he))

/-- An unchecked default-mode body (not bound by `rt`, in a default record, and touching no record
in `bad`) satisfies `DefaultBodyOk`. -/
theorem unchecked_default_body_ok {s : Subject} {cl : Classifier} {P : Prog}
    {rt : Array (Ref × RunDef)} {bad : Array Address}
    {r : Ref} {c : Ixon.Constant} {params : Array Param} {res : ResultMode}
    {rc : Cls} {rs : Skel} {body : Term}
    (hp : readProg s cl = .ok P)
    (hrt : (Reading.make s).runTable cl = .ok rt)
    (hrtNone : rt.find? (·.1 == r) = none)
    (hst : s.store r.block = some c)
    (hdef : recordDefault c = .ok true)
    (hrd : (Reading.make s).readDef cl rt true r = .ok (.body params res rc rs body))
    (hdefAll : ∀ a c, a ∈ (Reading.make s).closure.toList → s.store a = some c →
      bad.contains a = false → recordDefault c = .ok true)
    (htouch : termTouchesNonDefault bad body = false) :
    DefaultBodyOk P params res rs body := by
  obtain ⟨hiface, hmd⟩ := readDef_body_modesDefault hrt hrtNone hst hdef hrd
  obtain ⟨hpDef, hresDef, hrsDef⟩ := hiface
  exact ⟨hpDef, hresDef, hrsDef, termModesDefault_to_defaultTerm hp hdefAll hmd htouch⟩

/-! ## Section 5 (`F5`): `checkBodies_accept` and `check_sound_modeOk` -/

/-- Named predicate over a `ForInStep`, avoiding auxiliary matcher mismatch when splitting `if` inside loops. -/
def stepHolds {β : Type} (IY ID : β → Prop) : ForInStep β → Prop
  | .yield b' => IY b'
  | .done b' => ID b'

theorem Id_forIn_list_inv {α β : Type}
    (IYield : List α → β → Prop) (IDone : β → Prop)
    (step : α → β → Id (ForInStep β))
    (hstep : ∀ seen a acc, IYield seen acc →
      stepHolds (IYield (seen ++ [a])) IDone (step a acc).run) :
    ∀ (l seen : List α) (acc : β),
      IYield seen acc →
      IYield (seen ++ l) (forIn (m := Id) l acc step).run ∨ IDone (forIn (m := Id) l acc step).run := by
  intro l
  induction l with
  | nil => intro seen acc hi; exact Or.inl (by simpa using hi)
  | cons a rest ih =>
    intro seen acc hi
    rw [List.forIn_cons]
    have hs := hstep seen a acc hi
    change IYield (seen ++ a :: rest) (match (step a acc).run with
        | .done b => b
        | .yield b => (forIn (m := Id) rest b step).run) ∨
      IDone (match (step a acc).run with
        | .done b => b
        | .yield b => (forIn (m := Id) rest b step).run)
    cases hst : (step a acc).run with
    | done b => rw [hst] at hs; exact Or.inr hs
    | yield b =>
      rw [hst] at hs
      rcases ih (seen ++ [a]) b hs with hy | hd
      · exact Or.inl (by simpa [List.append_assoc] using hy)
      · exact Or.inr hd

theorem Id_bind_forIn_inv {α β γ : Type}
    (IYield : List α → β → Prop) (IDone : β → Prop)
    {l : List α} {acc : β} {step : α → β → Id (ForInStep β)}
    {k : β → Id γ} {out : γ}
    (h : (forIn (m := Id) l acc step >>= k).run = out)
    (hinit : IYield [] acc)
    (hstep : ∀ seen a b, IYield seen b →
      stepHolds (IYield (seen ++ [a])) IDone (step a b).run) :
    ∃ res, (k res).run = out ∧ (IYield l res ∨ IDone res) :=
  ⟨(forIn (m := Id) l acc step).run, h, by simpa using Id_forIn_list_inv IYield IDone step hstep l [] acc hinit⟩

theorem Id_forIn_list_goal {α β : Type} {l : List α} {acc : β}
    {step : α → β → Id (ForInStep β)} {P : β → Prop}
    (IYield : List α → β → Prop)
    (hinit : IYield [] acc)
    (hstep : ∀ seen a b, IYield seen b →
      stepHolds (IYield (seen ++ [a])) (fun _ => False) (step a b).run)
    (hpost : ∀ b, IYield l b → P b) :
    P (forIn (m := Id) l acc step).run := by
  rcases Id_forIn_list_inv IYield (fun _ => False) step hstep l [] acc hinit with hy | hf
  · exact hpost _ (by simpa using hy)
  · exact False.elim hf

theorem Id_ite_run {α : Type} {c : Prop} {d : Decidable c} {a b : Id α} {P : α → Prop}
    (ht : c → P a.run) (hf : ¬ c → P b.run) :
    P (@ite (Id α) c d a b).run := by
  cases d with
  | isTrue hc => exact ht hc
  | isFalse hc => exact hf hc

theorem not_mem_toList_of_contains_false {α : Type} [BEq α] [LawfulBEq α]
    {arr : Array α} {a : α} (hc : arr.contains a = false) : a ∉ arr.toList := by
  intro hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  have hi' : i < arr.size := by simpa using hi
  have htrue : arr.contains arr.toList[i] = true := by
    unfold Array.contains
    rw [Array.any_eq_true]
    exact ⟨i, hi', by simp⟩
  rw [htrue] at hc; cases hc

theorem readFailure_ne_accept (w e : String) (n : Nat) (fp : Bool) :
    readFailure w e ≠ .accept n fp := by
  unfold readFailure
  split <;> intro h <;> cases h

/-- If `checkBodies` accepts, every `.body` in `rs` was accepted by `anDef`. -/
theorem checkBodies_accept {lim : Limits} {P : Prog} {rs : List Ref} {n : Nat} {fp : Bool}
    (h : checkBodies lim P rs = .accept n fp) :
    ∀ r ∈ rs, ∀ params res rc rsk body,
      P.find? r = some (.body params res rc rsk body) →
      (anDef P lim.depth params res rc rsk body).run' { steps := lim.steps } = .ok () := by
  unfold checkBodies at h
  dsimp only at h
  let IY : List Ref → (Option Verdict × Nat) → Prop := fun seen st =>
    st.1 = none ∧
    ∀ r ∈ seen, ∀ params res rc rsk body,
      P.find? r = some (.body params res rc rsk body) →
      (anDef P lim.depth params res rc rsk body).run' { steps := lim.steps } = .ok ()
  let ID : (Option Verdict × Nat) → Prop := fun st =>
    ∃ v, st.1 = some v ∧ ∀ m b, v ≠ .accept m b
  obtain ⟨⟨ret?, cnt⟩, hk, hinv⟩ := Id_bind_forIn_inv IY ID h ⟨rfl, fun _ hm => by cases hm⟩
    (fun seen r acc ⟨_, hok⟩ => by
      cases hf : P.find? r with
      | none =>
        refine ⟨rfl, fun x hx => ?_⟩
        rcases List.mem_append.mp hx with hs | hr
        · exact hok x hs
        · simp only [List.mem_singleton] at hr; subst hr
          intro _ _ _ _ _ hfd; rw [hf] at hfd; cases hfd
      | some d =>
        cases d with
        | body params res rc rsk body =>
          dsimp only
          cases han : (anDef P lim.depth params res rc rsk body).run' { steps := lim.steps } with
          | ok u =>
            cases u
            dsimp only
            refine ⟨rfl, fun x hx => ?_⟩
            rcases List.mem_append.mp hx with hs | hr
            · exact hok x hs
            · simp only [List.mem_singleton] at hr; subst hr
              intro ps' res' rc' rs' bd' hfd
              rw [hf] at hfd; injection hfd with hEq; injection hEq with h1 h2 h3 h4 h5
              subst h1; subst h2; subst h3; subst h4; subst h5
              exact han
          | error halt =>
            cases halt with
            | refuse w => dsimp only; exact ⟨_, rfl, fun _ _ hEq => by cases hEq⟩
            | decline w => dsimp only; exact ⟨_, rfl, fun _ _ hEq => by cases hEq⟩
        | ind _ | ctor _ _ _ _ | caseDef _ | prim _ | extern _ _ _ _ | stuck _ _ _ _ =>
          dsimp only
          refine ⟨rfl, fun x hx => ?_⟩
          rcases List.mem_append.mp hx with hs | hr
          · exact hok x hs
          · simp only [List.mem_singleton] at hr; subst hr
            intro _ _ _ _ _ hfd; rw [hf] at hfd; cases hfd)
  rcases hinv with ⟨hnone, hall⟩ | ⟨v, hsome, hne⟩
  · exact hall
  · dsimp only at hsome; subst hsome; exact False.elim (hne n fp hk)

theorem rolesDisjointFromInductives_of_ok {s : Subject} (h : rolesDisjointOk s = true) :
    RolesDisjointFromInductives s := by
  intro r role hro hprim
  unfold roleOf? at hro
  cases hf : s.table.bound.find? (fun p : Ix.Kernel.Role × Address => Ix.Kernel.Reader.resolve s.store p.2 == some r) with
  | none => simp [hf] at hro
  | some p =>
    simp only [hf, Option.map_some, Option.some.injEq] at hro
    have hmem : p ∈ s.table.bound := Array.mem_of_find?_eq_some hf
    have hpred : (Ix.Kernel.Reader.resolve s.store p.2 == some r) = true :=
      Array.find?_some (p := fun p : Ix.Kernel.Role × Address => Ix.Kernel.Reader.resolve s.store p.2 == some r) hf
    have hres : Ix.Kernel.Reader.resolve s.store p.2 = some r := beq_iff_eq.mp hpred
    unfold rolesDisjointOk at h
    rw [Array.all_eq_true] at h
    obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hmem
    have hiok := h i hi
    rw [hget] at hiok
    simp only [hro, hprim, Bool.not_true, Bool.false_or, hres] at hiok
    exact Option.isNone_iff_eq_none.mp hiok

/-- Top-level soundness of `IxCK.Resource.check` into `ModeOk`: whenever `check` accepts a subject,
the runtime `rolesDisjointOk` check establishes `RolesDisjointFromInductives` and the subject
reads at `lim.oracle` into a run program `P` satisfying `ModeOk P`. -/
theorem check_sound_modeOk {lim : Limits} {env : Ix.Kernel.Env .anon} {s : Subject}
    {n : Nat} {fp : Bool}
    (hchk : check lim env s = .accept n fp) :
    ∃ P, Reads lim.oracle env s P ∧ ModeOk P := by
  unfold check at hchk
  dsimp only at hchk
  have hrdj : rolesDisjointOk s = true := by
    cases h : rolesDisjointOk s
    · simp only [h] at hchk; cases hchk
    · rfl
  have hroles : RolesDisjointFromInductives s := rolesDisjointFromInductives_of_ok hrdj
  simp only [hrdj, ↓reduceIte] at hchk
  let rd : Reading := Reading.make s lim.walk
  cases hcomp1 : rd.complete with
  | error e =>
    dsimp only [rd] at hcomp1
    rw [hcomp1] at hchk
    dsimp only at hchk
    split at hchk <;> cases hchk
  | ok u =>
    cases u
    have hcomp1' : (Reading.make s lim.walk).complete = .ok () := hcomp1
    rw [hcomp1'] at hchk
    dsimp only at hchk
    rw [← Array.forIn_toList] at hchk
    -- 1. Analyze the `nonDefault` loop
    let IYnd : List Address → (Option Verdict × Array Address) → Prop := fun seen st =>
      st.1 = none ∧
      ∀ a ∈ seen, ∀ c, s.store a = some c → a ∉ st.2.toList → recordDefault c = .ok true
    let IDnd : (Option Verdict × Array Address) → Prop := fun st =>
      ∃ v, st.1 = some v ∧ ∀ m b, v ≠ .accept m b
    obtain ⟨⟨ndRet?, nonDefault⟩, hchk, hndInv⟩ := Id_bind_forIn_inv IYnd IDnd hchk
      ⟨rfl, fun _ hm => by cases hm⟩
      (fun seen a acc ⟨_, hok⟩ => by
        cases hst : s.store a with
        | none =>
          refine ⟨rfl, fun x hx c hxc hnot => ?_⟩
          rcases List.mem_append.mp hx with hs | ha
          · exact hok x hs c hxc hnot
          · simp only [List.mem_singleton] at ha; subst ha; rw [hst] at hxc; cases hxc
        | some c =>
          dsimp only
          cases hdef : recordDefault c with
          | ok b =>
            cases b with
            | true =>
              dsimp only
              refine ⟨rfl, fun x hx c' hxc hnot => ?_⟩
              rcases List.mem_append.mp hx with hs | ha
              · exact hok x hs c' hxc hnot
              · simp only [List.mem_singleton] at ha; subst ha
                rw [hst] at hxc; injection hxc with hcEq; subst hcEq; exact hdef
            | false =>
              dsimp only
              refine ⟨rfl, fun x hx c' hxc hnot => ?_⟩
              rcases List.mem_append.mp hx with hs | ha
              · exact hok x hs c' hxc (fun hm => hnot (by
                  rw [Array.toList_push]; exact List.mem_append.mpr (Or.inl hm)))
              · simp only [List.mem_singleton] at ha; subst ha
                exact False.elim (hnot (by rw [Array.toList_push]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))))
          | error e =>
            dsimp only
            exact ⟨_, rfl, fun _ _ hEq => by cases hEq⟩)
    rcases hndInv with ⟨hndNone, hndOk⟩ | ⟨v, hndSome, hndNe⟩
    · dsimp only at hndNone; subst hndNone
      dsimp only at hchk
      -- 2. Analyze `readProg s cl`
      let cl : Classifier := oracleClassifier env (ctorShapes rd) lim.oracle
      cases hp : readProg s cl with
      | error e =>
        dsimp only [cl, rd] at hp
        rw [hp] at hchk
        exact False.elim (readFailure_ne_accept "the reading" e n fp hchk)
      | ok P =>
        have hp' : readProg s (oracleClassifier env (ctorShapes (Reading.make s lim.walk)) lim.oracle) = .ok P := hp
        rw [hp'] at hchk
        dsimp only at hchk
        -- Bridge `rd = Reading.make s`
        obtain ⟨hcomp2, rt, hrt, _, _, hfindElim, _, _, _⟩ := readProg_elim hp
        have hrdEq : Reading.make s lim.walk = Reading.make s :=
          Reading.make_eq_of_walked s (Reading.complete_walked hcomp1) (Reading.complete_walked hcomp2)
        have hreads : Reads lim.oracle env s P := by
          unfold Reads
          have hclEq : oracleClassifier env (ctorShapes (Reading.make s)) lim.oracle = cl := by
            dsimp only [cl, rd]; rw [hrdEq]
          rw [hclEq]; exact hp
        have hctors : CtorsIndexed P := readProg_ctorsIndexed hp hroles
        have hdefAll : ∀ a c, a ∈ (Reading.make s).closure.toList → s.store a = some c →
            nonDefault.contains a = false → recordDefault c = .ok true := by
          intro a c hmem hst hnc
          exact hndOk a (hrdEq.symm ▸ hmem) c hst (not_mem_toList_of_contains_false hnc)
        -- 3. Fast path vs slow path
        cases hfast : (nonDefault.isEmpty && s.runTable.isEmpty) with
        | true =>
          obtain ⟨hndEmpty, hrtEmpty⟩ := Bool.and_eq_true _ _ |>.mp hfast
          have hndNil : nonDefault.toList = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [Array.length_toList]
            exact Array.isEmpty_iff_size_eq_zero.mp hndEmpty
          have hndEmptyArr : nonDefault = #[] := by
            cases nonDefault with
            | mk l => simp at hndNil; subst hndNil; rfl
          have hrtNil : rt = #[] := by
            have h0 : (Reading.make s).runTable cl = .ok #[] := by
              unfold Reading.runTable; dsimp only [Reading.make]; simp [hrtEmpty]
            rw [h0] at hrt; injection hrt with hEq; exact hEq.symm
          refine ⟨P, hreads, hctors, fun r params res rc rs body hfind => ?_⟩
          obtain ⟨c, hmem, hst, _, hrd⟩ := hfindElim r _ hfind
          refine ⟨(readDef_body_struct hrt hrd).1, (readDef_body_struct hrt hrd).2, Or.inr ?_⟩
          have hdefC : recordDefault c = .ok true := hndOk r.block (hrdEq.symm ▸ hmem) c hst (by simp [hndNil])
          have hrtNone : rt.find? (·.1 == r) = none := by rw [hrtNil]; rfl
          have hmd := (readDef_body_modesDefault hrt hrtNone hst hdefC hrd).2
          exact unchecked_default_body_ok hp hrt hrtNone hst hdefC hrd
            (by rw [← hndEmptyArr]; exact hdefAll) (termTouchesNonDefault_empty hmd)
        | false =>
          simp only [hfast, Bool.false_eq_true, ↓reduceIte] at hchk
          cases hrtRun : rd.runTable cl with
          | error e =>
            dsimp only [rd, cl] at hrtRun
            rw [hrtRun] at hchk
            exact False.elim (readFailure_ne_accept "the run table" e n fp hchk)
          | ok rt' =>
            have hrtRun' : (Reading.make s lim.walk).runTable
                (oracleClassifier env (ctorShapes (Reading.make s lim.walk)) lim.oracle) = .ok rt' := hrtRun
            rw [hrtRun'] at hchk
            have hrtEq : rt' = rt := by
              dsimp only [rd] at hrtRun; rw [hrdEq] at hrtRun; rw [hrtRun] at hrt; injection hrt
            subst rt'
            dsimp only at hchk
            simp only [pure_bind] at hchk
            rw [← Array.forIn_toList] at hchk
            -- 4. Analyze the `toCheck` loop
            let IYtc : List Address → Array Ref → Prop := fun seen tc =>
              ∀ a ∈ seen, ∀ c, s.store a = some c → ∀ r ∈ (refsOf a c).toList,
                ∀ params res rc rs body, P.find? r = some (.body params res rc rs body) →
                r ∉ tc.toList →
                nonDefault.contains a = false ∧
                rt.any (fun x => x.1.block == a) = false ∧
                termTouchesNonDefault nonDefault body = false
            obtain ⟨toCheck, hchk, htcInv⟩ := Id_bind_forIn_inv IYtc (fun _ => False) hchk
              (fun _ hm => by cases hm)
              (fun seen a tc hok => by
                have hstCases : s.store a = none ∨ ∃ c, s.store a = some c := by
                  cases s.store a with
                  | none => exact Or.inl rfl
                  | some c => exact Or.inr ⟨c, rfl⟩
                rcases hstCases with hst | ⟨c, hst⟩
                · simp only [hst]
                  intro x hx c hxc
                  rcases List.mem_append.mp hx with hs | ha
                  · exact hok x hs c hxc
                  · simp only [List.mem_singleton] at ha; subst ha; rw [hst] at hxc; cases hxc
                · simp only [hst]
                  refine Id_ite_run (P := stepHolds (IYtc (seen ++ [a])) (fun _ => False))
                    (fun _ => ?_) (fun hnotCond => ?_)
                  · dsimp only [stepHolds]
                    rw [← Array.forIn_toList]
                    refine Id_forIn_list_goal (P := IYtc (seen ++ [a]))
                      (fun seenR (tc' : Array Ref) =>
                        (∀ y ∈ tc.toList, y ∈ tc'.toList) ∧ (∀ r ∈ seenR, r ∈ tc'.toList))
                      ⟨fun _ h => h, fun _ hm => by cases hm⟩
                      (fun seenR r tc' ⟨hsub, hsr⟩ => by
                        refine ⟨fun y hy => by rw [Array.toList_push]; exact List.mem_append.mpr (Or.inl (hsub y hy)),
                          fun x hx => ?_⟩
                        rcases List.mem_append.mp hx with hs | hr
                        · rw [Array.toList_push]; exact List.mem_append.mpr (Or.inl (hsr x hs))
                        · simp only [List.mem_singleton] at hr; subst hr
                          rw [Array.toList_push]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
                      (fun tc' ⟨hsub, hallR⟩ => by
                        intro x hx c' hxc r hr ps' res' rc' rs' bd' hfd hnot
                        rcases List.mem_append.mp hx with hs | ha
                        · exact hok x hs c' hxc r hr ps' res' rc' rs' bd' hfd (fun hm => hnot (hsub r hm))
                        · simp only [List.mem_singleton] at ha; subst ha
                          rw [hst] at hxc; injection hxc with hcEq; subst hcEq
                          exact False.elim (hnot (hallR r hr)))
                  · have hcond := Bool.eq_false_iff.mpr hnotCond
                    obtain ⟨h12, hrtF⟩ := Bool.or_eq_false_iff.mp hcond
                    obtain ⟨h1, _⟩ := Bool.or_eq_false_iff.mp h12
                    obtain ⟨hndF, _⟩ := Bool.or_eq_false_iff.mp h1
                    dsimp only [stepHolds]
                    rw [← Array.forIn_toList]
                    refine Id_forIn_list_goal (P := IYtc (seen ++ [a]))
                      (fun seenR (tc' : Array Ref) =>
                        (∀ y ∈ tc.toList, y ∈ tc'.toList) ∧
                        (∀ r ∈ seenR, ∀ ps' res' rc' rs' bd', P.find? r = some (.body ps' res' rc' rs' bd') →
                          termTouchesNonDefault nonDefault bd' = true → r ∈ tc'.toList))
                      ⟨fun _ h => h, fun _ hm => by cases hm⟩
                      (fun seenR r tc' ⟨hsub, hsr⟩ => by
                        cases hfr : P.find? r with
                        | none =>
                          dsimp only
                          refine ⟨hsub, fun x hx => ?_⟩
                          rcases List.mem_append.mp hx with hs | hr
                          · exact hsr x hs
                          · simp only [List.mem_singleton] at hr; subst hr
                            intro _ _ _ _ _ hfd; rw [hfr] at hfd; cases hfd
                        | some d =>
                          cases d with
                          | body ps0 res0 rc0 rs0 bd0 =>
                            dsimp only
                            cases htb : termTouchesNonDefault nonDefault bd0 with
                            | true =>
                              simp only [↓reduceIte]
                              refine ⟨fun y hy => by rw [Array.toList_push]; exact List.mem_append.mpr (Or.inl (hsub y hy)),
                                fun x hx => ?_⟩
                              rcases List.mem_append.mp hx with hs | hr
                              · intro ps' res' rc' rs' bd' hfd ht'
                                rw [Array.toList_push]; exact List.mem_append.mpr (Or.inl (hsr x hs ps' res' rc' rs' bd' hfd ht'))
                              · simp only [List.mem_singleton] at hr; subst hr
                                intro _ _ _ _ _ _ _
                                rw [Array.toList_push]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              refine ⟨hsub, fun x hx => ?_⟩
                              rcases List.mem_append.mp hx with hs | hr
                              · exact hsr x hs
                              · simp only [List.mem_singleton] at hr; subst hr
                                intro ps' res' rc' rs' bd' hfd ht'
                                rw [hfr] at hfd; injection hfd with hEq; injection hEq with _ _ _ _ hbdEq
                                subst hbdEq; rw [htb] at ht'; cases ht'
                          | ind _ | ctor _ _ _ _ | caseDef _ | prim _ | extern _ _ _ _ | stuck _ _ _ _ =>
                            dsimp only
                            refine ⟨hsub, fun x hx => ?_⟩
                            rcases List.mem_append.mp hx with hs | hr
                            · exact hsr x hs
                            · simp only [List.mem_singleton] at hr; subst hr
                              intro _ _ _ _ _ hfd; rw [hfr] at hfd; cases hfd)
                      (fun tc' ⟨hsub, hsomeR⟩ => by
                        intro x hx c' hxc r hr ps' res' rc' rs' bd' hfd hnot
                        rcases List.mem_append.mp hx with hs | ha
                        · exact hok x hs c' hxc r hr ps' res' rc' rs' bd' hfd (fun hm => hnot (hsub r hm))
                        · simp only [List.mem_singleton] at ha; subst ha
                          rw [hst] at hxc; injection hxc with hcEq; subst hcEq
                          refine ⟨hndF, hrtF, ?_⟩
                          cases htb : termTouchesNonDefault nonDefault bd' with
                          | false => rfl
                          | true => exact False.elim (hnot (hsomeR r hr ps' res' rc' rs' bd' hfd htb))))
            rcases htcInv with htcOk | hf
            · -- 5. Combine `checkBodies_accept` + `anDef_sound` (checked) and `unchecked_default_body_ok` (unchecked)
              refine ⟨P, hreads, hctors, fun r params res rc rs body hfind => ?_⟩
              obtain ⟨c, hmem, hst, hrRefs, hrd⟩ := hfindElim r _ hfind
              refine ⟨(readDef_body_struct hrt hrd).1, (readDef_body_struct hrt hrd).2, ?_⟩
              by_cases hmemTC : r ∈ toCheck.toList
              · exact Or.inl (anDef_sound (checkBodies_accept hchk r hmemTC params res rc rs body hfind))
              · right
                obtain ⟨hndF, hrtAnyF, hbodyF⟩ :=
                  htcOk r.block (hrdEq.symm ▸ hmem) c hst r hrRefs params res rc rs body hfind hmemTC
                have hdefC : recordDefault c = .ok true := hdefAll r.block c hmem hst hndF
                have hrtNone : rt.find? (·.1 == r) = none := by
                  cases hf : rt.find? (·.1 == r) with
                  | none => rfl
                  | some q =>
                    have hqmem : q ∈ rt := Array.mem_of_find?_eq_some hf
                    have hqeq : q.1 = r :=
                      beq_iff_eq.mp (Array.find?_some (p := fun x : Ref × RunDef => x.1 == r) hf)
                    have htrue : rt.any (fun x => x.1.block == r.block) = true := by
                      rw [Array.any_eq_true]
                      obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hqmem
                      refine ⟨i, hi, ?_⟩
                      rw [hget, hqeq]; exact beq_self_eq_true r.block
                    rw [htrue] at hrtAnyF; cases hrtAnyF
                exact unchecked_default_body_ok hp hrt hrtNone hst hdefC hrd hdefAll hbodyF
            · exact False.elim hf
    · dsimp only at hndSome; subst hndSome; exact False.elim (hndNe n fp hchk)

end IxCK.Resource.Proof
