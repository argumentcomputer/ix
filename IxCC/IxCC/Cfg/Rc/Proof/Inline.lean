import IxCC.Cfg.Rc.Proof.InlineSites
import IxCC.Lir.Proof.Relabel
import IxCC.Lir.Proof.Split

/-! # Semantic preservation of inline RC fast paths (`Cfg.Rc.Inline`)

Proves `inlineProgram_sim`: for any raw Lir program whose runtime wrappers and
procedures match `RuntimeFuncs l raw`, `inlineProgram l raw` simulates `raw`
with exact result equality (`Eq`) and clock map
`fun k => k + 2 * Lir.fuelFor (inlineProgram l raw) k`.

No heap invariant is needed: `step_match` aligns every source, runtime, and
inlined RC site step via `MatchedStep`, from which both `forward_run` and
`backward_run` follow in ~25 lines each. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Inline

open IxCC.Cfg.Rc.Native

/-! ## Stack and state relation between `raw` and `inlineProgram l raw` -/

/-- Frame-level correspondence for normal frames. -/
inductive FrameRel (l : Layout) (raw : Lir.Program) : Lir.Frame → Lir.Frame → Prop
  | runtime {fr : Lir.Frame} (hge : l.sourceCount ≤ fr.fn) :
      FrameRel l raw fr fr
  | emptySource {F : Lir.Func} {fr : Lir.Frame}
      (hlt : fr.fn < l.sourceCount)
      (hF : raw.funcs[fr.fn]? = some F)
      (hnone : F.blocks[fr.label]? = none) :
      FrameRel l raw fr fr
  | source {F : Lir.Func} {B : Lir.Block} {fr₁ fr₂ : Lir.Frame}
      (hlt : fr₁.fn < l.sourceCount)
      (hfn : fr₂.fn = fr₁.fn)
      (hF : raw.funcs[fr₁.fn]? = some F)
      (hcp : ChunkPos l F fr₁.label B fr₁.pos fr₂.label fr₂.pos)
      (hagree : AgreeBelow (freshBase F) fr₁.env fr₂.env)
      (hdsts : fr₂.dsts = fr₁.dsts) :
      FrameRel l raw fr₁ fr₂

/-- Stack-level correspondence: either matching frames, or a suspended `dec`
slow-path call where `raw` has `decWrapper` at `pos = 1` over `caller₁` while
`inlineProgram` has `caller₂` at `(inLbl + 2, pos = 1)` waiting to jump to
`inLbl + 5` and assign `dst := 1`. -/
inductive StackRel (l : Layout) (raw : Lir.Program) : List Lir.Frame → List Lir.Frame → Prop
  | nil : StackRel l raw [] []
  | cons {fr₁ fr₂ : Lir.Frame} {rest₁ rest₂ : List Lir.Frame}
      (hfr : FrameRel l raw fr₁ fr₂)
      (hrest : StackRel l raw rest₁ rest₂) :
      StackRel l raw (fr₁ :: rest₁) (fr₂ :: rest₂)
  | consDecSlow {F : Lir.Func} {B : Lir.Block} {wrapFr caller₁ caller₂ : Lir.Frame}
      {rest₁ rest₂ : List Lir.Frame} {dst x : Lir.VReg} {inLbl : Lir.Label}
      (hwrap : wrapFr.fn = l.decWrapper ∧ wrapFr.label = 0 ∧ wrapFr.pos = 1 ∧ wrapFr.dsts = [])
      (hlt : caller₁.fn < l.sourceCount)
      (hfn : caller₂.fn = caller₁.fn)
      (hF : raw.funcs[caller₁.fn]? = some F)
      (hdsts₁ : caller₁.dsts = [dst])
      (hdsts₂ : caller₂.dsts = [])
      (hfree : caller₂.label = inLbl + 2 ∧ caller₂.pos = 1)
      (hfreeBlk : (inlineFunc l F).blocks[inLbl + 2]? =
        some { body := #[.call [] l.decProc [.v x]], term := .jump ⟨inLbl + 5, []⟩, cold := B.cold })
      (hjoinBlk : ∃ jb, (inlineFunc l F).blocks[inLbl + 5]? = some jb ∧
        jb.params = [] ∧ 0 < jb.body.size ∧ jb.body[0]? = some (.assign dst (.arg (.imm 1))))
      (hcpNext : ChunkPos l F caller₁.label B caller₁.pos (inLbl + 5) 1)
      (hagree : AgreeBelow (freshBase F) caller₁.env caller₂.env)
      (hrest : StackRel l raw rest₁ rest₂) :
      StackRel l raw (wrapFr :: caller₁ :: rest₁) (caller₂ :: rest₂)

/-- Whole-state correspondence: identical memory and context, related stacks,
and the running top frame always has empty `dsts`. -/
structure StateRel (l : Layout) (raw : Lir.Program) (s₁ s₂ : Lir.State) : Prop where
  mem : s₂.mem = s₁.mem
  ctx : s₂.ctx = s₁.ctx
  stack : StackRel l raw s₁.stack s₂.stack
  topDsts : ∀ fr rest, s₁.stack = fr :: rest → fr.dsts = []

/-! ## Generic `Sem.runClocked` / `Sem.Star` / `Sem.Reaches` helpers -/

theorem runClocked_step_free {σ α : Type} {st : σ → Sem.Step σ α} {fuel k : Nat} {s s' : σ}
    (hs : st s = .next s' false) :
    Sem.runClocked st (fuel + 1) k s = Sem.runClocked st fuel k s' := by
  simp [Sem.runClocked, hs]

theorem runClocked_step_charge {σ α : Type} {st : σ → Sem.Step σ α} {fuel k : Nat} {s s' : σ}
    (hs : st s = .next s' true) :
    Sem.runClocked st (fuel + 1) (k + 1) s = Sem.runClocked st fuel k s' := by
  simp [Sem.runClocked, hs]

theorem runClocked_step_charge_zero {σ α : Type} {st : σ → Sem.Step σ α} {fuel : Nat} {s s' : σ}
    (hs : st s = .next s' true) :
    Sem.runClocked st (fuel + 1) 0 s = .timeout := by
  simp [Sem.runClocked, hs]

theorem runClocked_star_inv {σ α : Type} {st : σ → Sem.Step σ α} :
    ∀ {s s' : σ} {c : Nat}, Sem.Star st s c s' →
    ∀ {fuel k : Nat} {r : Sem.Result α},
      Sem.runClocked st fuel k s = r → r ≠ .timeout →
      ∃ fuel' k', fuel' ≤ fuel ∧ k = c + k' ∧ Sem.runClocked st fuel' k' s' = r
  | _, _, 0, .refl _, fuel, k, _, hrun, _ => ⟨fuel, k, Nat.le_refl _, (Nat.zero_add k).symm, hrun⟩
  | _, _, _, .free hs hstar, fuel, k, _, hrun, hne => by
    cases fuel with
    | zero => simp [Sem.runClocked] at hrun; exact absurd hrun.symm hne
    | succ fuel =>
      rw [runClocked_step_free hs] at hrun
      obtain ⟨f', k', hf', hk', hrun'⟩ := runClocked_star_inv hstar hrun hne
      exact ⟨f', k', by omega, hk', hrun'⟩
  | _, _, _ + 1, .charge hs hstar, fuel, k, _, hrun, hne => by
    cases fuel with
    | zero => simp [Sem.runClocked] at hrun; exact absurd hrun.symm hne
    | succ fuel =>
      cases k with
      | zero => rw [runClocked_step_charge_zero hs] at hrun; exact absurd hrun.symm hne
      | succ k =>
        rw [runClocked_step_charge hs] at hrun
        obtain ⟨f', k', hf', hk', hrun'⟩ := runClocked_star_inv hstar hrun hne
        exact ⟨f', k', by omega, by omega, hrun'⟩

theorem runClocked_star_inv_lt {σ α : Type} {st : σ → Sem.Step σ α} {s s₁ s₂ : σ}
    {b : Bool} {c : Nat} (h1 : st s = .next s₁ b) (hstar : Sem.Star st s₁ c s₂)
    {fuel k : Nat} {r : Sem.Result α}
    (hrun : Sem.runClocked st fuel k s = r) (hne : r ≠ .timeout) :
    ∃ fuel' k', fuel' < fuel ∧ k = b.toNat + c + k' ∧ Sem.runClocked st fuel' k' s₂ = r := by
  cases fuel with
  | zero => simp [Sem.runClocked] at hrun; exact absurd hrun.symm hne
  | succ fuel =>
    cases b with
    | false =>
      rw [runClocked_step_free h1] at hrun
      obtain ⟨f', k', hf', hk', hrun'⟩ := runClocked_star_inv hstar hrun hne
      exact ⟨f', k', by omega, by simpa using hk', hrun'⟩
    | true =>
      cases k with
      | zero => rw [runClocked_step_charge_zero h1] at hrun; exact absurd hrun.symm hne
      | succ k =>
        rw [runClocked_step_charge h1] at hrun
        obtain ⟨f', k', hf', hk', hrun'⟩ := runClocked_star_inv hstar hrun hne
        exact ⟨f', k', by omega, by simp; omega, hrun'⟩

theorem reaches_of_star_reaches {σ α : Type} {st : σ → Sem.Step σ α} {s s' : σ} {c k : Nat}
    {r : Sem.Result α} (hstar : Sem.Star st s c s') (hr : Sem.Reaches st s' k r) :
    Sem.Reaches st s (c + k) r := by
  induction hstar with
  | refl => simpa using hr
  | free hs _ ih => exact .free hs (ih hr)
  | charge hs _ ih =>
    have := Sem.Reaches.charge hs (ih hr)
    rwa [Nat.add_right_comm] at this

/-! ## Function entry, return, and edge correspondence -/

theorem enter_rel (l : Layout) (raw : Lir.Program) {g : Lir.FunId} {vs : List Lir.Word} :
    (∀ callee₁, Lir.enter raw g vs = some callee₁ →
      ∃ callee₂, Lir.enter (inlineProgram l raw) g vs = some callee₂ ∧
        FrameRel l raw callee₁ callee₂ ∧ callee₁.dsts = []) ∧
    (∀ callee₂, Lir.enter (inlineProgram l raw) g vs = some callee₂ →
      ∃ callee₁, Lir.enter raw g vs = some callee₁ ∧
        FrameRel l raw callee₁ callee₂ ∧ callee₁.dsts = []) ∧
    (Lir.enter raw g vs = none ↔ Lir.enter (inlineProgram l raw) g vs = none) := by
  by_cases hlt : g < l.sourceCount
  · have hget := inlineProgram_get_lt l raw hlt
    cases hF : raw.funcs[g]? with
    | none => simp [Lir.enter, hF, hget]
    | some F =>
      have hF' : (inlineProgram l raw).funcs[g]? = some (inlineFunc l F) := by rw [hget, hF]; rfl
      have hparams : (inlineFunc l F).params = F.params := rfl
      simp only [Lir.enter, hF, hF', hparams, Option.bind_eq_bind, Option.bind_some]
      cases hbp : Lir.bindParams {} F.params vs with
      | none => simp
      | some ρ =>
        cases hB0 : F.blocks[0]? with
        | none =>
          exact ⟨fun _ h1 => by cases h1; exact ⟨_, rfl, .emptySource hlt hF hB0, rfl⟩,
            fun _ h2 => by cases h2; exact ⟨_, rfl, .emptySource hlt hF hB0, rfl⟩, by simp⟩
        | some B0 =>
          have hcp : ChunkPos l F 0 B0 0 0 0 := ChunkPos.entry l F hB0
          exact ⟨fun _ h1 => by cases h1; exact ⟨_, rfl, .source hlt rfl hF hcp AgreeBelow.refl rfl, rfl⟩,
            fun _ h2 => by cases h2; exact ⟨_, rfl, .source hlt rfl hF hcp AgreeBelow.refl rfl, rfl⟩, by simp⟩
  · have hge : l.sourceCount ≤ g := Nat.le_of_not_lt hlt
    have hget := inlineProgram_get_ge l raw hge
    simp only [Lir.enter, hget]
    cases raw.funcs[g]? with
    | none => simp
    | some F =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases Lir.bindParams {} F.params vs with
      | none => simp
      | some ρ =>
        exact ⟨fun _ h1 => by cases h1; exact ⟨_, rfl, .runtime hge, rfl⟩,
          fun _ h2 => by cases h2; exact ⟨_, rfl, .runtime hge, rfl⟩, by simp⟩

/-- Unified single-step or single-site matching relation between `raw` and `inlineProgram l raw`. -/
inductive MatchedStep (l : Layout) (raw : Lir.Program) (s₁ s₂ : Lir.State) : Prop
  | rawStuck : Lir.step raw s₁ = .stuck → MatchedStep l raw s₁ s₂
  | rawStuckWithin {c₁ : Nat} : c₁ ≤ 2 →
      Sem.Reaches (Lir.semStep raw) s₁ c₁ .stuck →
      MatchedStep l raw s₁ s₂
  | sameFinal {r : Sem.Result (List Lir.Word × X86.Memory)} :
      Sem.Final (Lir.semStep raw s₁) r → Sem.Final (Lir.semStep (inlineProgram l raw) s₂) r →
      MatchedStep l raw s₁ s₂
  | sameOom {c₁ : Nat} : c₁ ≤ 2 →
      Sem.Reaches (Lir.semStep raw) s₁ c₁ (.resource .heap) →
      Sem.Reaches (Lir.semStep (inlineProgram l raw)) s₂ 0 (.resource .heap) →
      MatchedStep l raw s₁ s₂
  | sync {s₁' s₂' s₁'' s₂'' : Lir.State} {b₁ b₂ : Bool} {c₁ c₂ : Nat} :
      Lir.semStep raw s₁ = .next s₁' b₁ → Sem.Star (Lir.semStep raw) s₁' c₁ s₁'' →
      Lir.semStep (inlineProgram l raw) s₂ = .next s₂' b₂ → Sem.Star (Lir.semStep (inlineProgram l raw)) s₂' c₂ s₂'' →
      b₁.toNat + c₁ ≤ b₂.toNat + c₂ + 2 →
      StateRel l raw s₁'' s₂'' →
      MatchedStep l raw s₁ s₂

private theorem matched_of_ret {l : Layout} {raw : Lir.Program} {mem : X86.Memory} {ctx : Lir.Word}
    {fr₁ fr₂ : Lir.Frame} {rest₁ rest₂ : List Lir.Frame} {vals : List Lir.Word}
    (hstep₁ : Lir.step raw { mem, ctx, stack := fr₁ :: rest₁ } =
      match rest₁ with
      | [] => .done vals mem
      | caller :: rest =>
        match Lir.bindParams caller.env caller.dsts vals with
        | some ρ => .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest } false
        | none => .stuck)
    (hstep₂ : Lir.step (inlineProgram l raw) { mem, ctx, stack := fr₂ :: rest₂ } =
      match rest₂ with
      | [] => .done vals mem
      | caller :: rest =>
        match Lir.bindParams caller.env caller.dsts vals with
        | some ρ => .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest } false
        | none => .stuck)
    (hrest : StackRel l raw rest₁ rest₂) :
    MatchedStep l raw { mem, ctx, stack := fr₁ :: rest₁ } { mem, ctx, stack := fr₂ :: rest₂ } := by
  cases hrest with
  | nil =>
    apply MatchedStep.sameFinal (r := .ok (vals, mem))
    · rw [Lir.semStep, hstep₁]; exact .done
    · rw [Lir.semStep, hstep₂]; exact .done
  | @cons caller₁ caller₂ rest₁' rest₂' hfr hrest' =>
    cases hfr with
    | runtime hge =>
      cases hbp : Lir.bindParams caller₁.env caller₁.dsts vals with
      | none =>
        apply MatchedStep.rawStuck
        simpa [hbp] using hstep₁
      | some ρ =>
        refine .sync (Lir.semStep_next.mpr (by simpa [hbp] using hstep₁)) (.refl _)
          (Lir.semStep_next.mpr (by simpa [hbp] using hstep₂)) (.refl _) (by omega) ?_
        exact ⟨rfl, rfl, .cons (.runtime hge) hrest', fun _ _ h => by cases h; rfl⟩
    | emptySource hlt hF hnone =>
      cases hbp : Lir.bindParams caller₁.env caller₁.dsts vals with
      | none =>
        apply MatchedStep.rawStuck
        simpa [hbp] using hstep₁
      | some ρ =>
        refine .sync (Lir.semStep_next.mpr (by simpa [hbp] using hstep₁)) (.refl _)
          (Lir.semStep_next.mpr (by simpa [hbp] using hstep₂)) (.refl _) (by omega) ?_
        exact ⟨rfl, rfl, .cons (.emptySource hlt hF hnone) hrest', fun _ _ h => by cases h; rfl⟩
    | source hlt hfn hF hcp hagree hdsts =>
      obtain ⟨hfwd, _, _⟩ := hagree.bindParams_agree caller₁.dsts vals
      cases hbp : Lir.bindParams caller₁.env caller₁.dsts vals with
      | none =>
        apply MatchedStep.rawStuck
        simpa [hbp] using hstep₁
      | some ρ₁ =>
        obtain ⟨ρ₂, hbp₂, hagree'⟩ := hfwd ρ₁ hbp
        refine .sync (Lir.semStep_next.mpr (by simpa [hbp] using hstep₁)) (.refl _)
          (Lir.semStep_next.mpr (by simpa [hdsts, hbp₂] using hstep₂)) (.refl _) (by omega) ?_
        exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcp hagree' rfl) hrest', fun _ _ h => by cases h; rfl⟩
  | consDecSlow hwrap hlt hfn hF hdsts₁ hdsts₂ hfree hfreeBlk hjoinBlk hcpNext hagree hrest' =>
    cases vals with
    | nil =>
      refine .sync (Lir.semStep_next.mpr (by simpa [hwrap.2.2.2, Lir.bindParams] using hstep₁)) (.refl _)
        (Lir.semStep_next.mpr (by simpa [hdsts₂, Lir.bindParams] using hstep₂)) (.refl _) (by omega) ?_
      exact ⟨rfl, rfl, .consDecSlow ⟨hwrap.1, hwrap.2.1, hwrap.2.2.1, rfl⟩ hlt hfn hF hdsts₁ rfl
        hfree hfreeBlk hjoinBlk hcpNext hagree hrest', fun _ _ h => by cases h; rfl⟩
    | cons _ _ =>
      apply MatchedStep.rawStuck
      simpa [hwrap.2.2.2, Lir.bindParams] using hstep₁

private theorem matched_of_runtime_edge {l : Layout} {raw : Lir.Program} {F : Lir.Func}
    {mem : X86.Memory} {ctx : Lir.Word} {fr₁ : Lir.Frame} {rest₁ rest₂ : List Lir.Frame}
    {ρ0 : Lir.Env} {e : Lir.Edge}
    (hge : l.sourceCount ≤ fr₁.fn) (htop : fr₁.dsts = [])
    (hrest : StackRel l raw rest₁ rest₂)
    (hstep₁ : Lir.step raw { mem, ctx, stack := fr₁ :: rest₁ } =
      Lir.takeEdge F { mem, ctx, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ0 e)
    (hstep₂ : Lir.step (inlineProgram l raw) { mem, ctx, stack := fr₁ :: rest₂ } =
      Lir.takeEdge F { mem, ctx, stack := fr₁ :: rest₂ } fr₁ rest₂ ρ0 e) :
    MatchedStep l raw { mem, ctx, stack := fr₁ :: rest₁ } { mem, ctx, stack := fr₁ :: rest₂ } := by
  cases ha : Lir.evalArgs ρ0 e.args with
  | none => exact .rawStuck (by simp [hstep₁, Lir.takeEdge, ha])
  | some vals =>
    cases htb : F.blocks[e.target]? with
    | none => exact .rawStuck (by simp [hstep₁, Lir.takeEdge, ha, htb])
    | some TB =>
      cases hbp : Lir.bindParams ρ0 TB.params vals with
      | none => exact .rawStuck (by simp [hstep₁, Lir.takeEdge, ha, htb, hbp])
      | some ρ' =>
        have hs₁ := Lir.semStep_next.mpr (hstep₁.trans (Lir.takeEdge_ok ha htb hbp))
        have hs₂ := Lir.semStep_next.mpr (hstep₂.trans (Lir.takeEdge_ok ha htb hbp))
        refine .sync hs₁ (.refl _) hs₂ (.refl _) (by omega) ?_
        exact ⟨rfl, rfl, .cons (.runtime hge) hrest, fun _ _ h => by cases h; exact htop⟩

private theorem matched_of_edge {l : Layout} {raw : Lir.Program} {F : Lir.Func} {B : Lir.Block}
    {mem : X86.Memory} {ctx : Lir.Word} {fr₁ fr₂ : Lir.Frame} {rest₁ rest₂ : List Lir.Frame}
    {ρ₁ ρ₂ : Lir.Env} {e : Lir.Edge}
    (hlt : fr₁.fn < l.sourceCount) (hfn : fr₂.fn = fr₁.fn)
    (hF : raw.funcs[fr₁.fn]? = some F) (hB : F.blocks[fr₁.label]? = some B)
    (hdsts₁ : fr₁.dsts = []) (hdsts₂ : fr₂.dsts = [])
    (hlbl₂ : fr₂.label = newLabel l F fr₁.label + blockExtra l B)
    (hagree : AgreeBelow (freshBase F) ρ₁ ρ₂)
    (heLt : argsMax e.args 0 < freshBase F)
    (hrest : StackRel l raw rest₁ rest₂)
    (hstep₁ : Lir.step raw { mem, ctx, stack := fr₁ :: rest₁ } =
      Lir.takeEdge F { mem, ctx, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ₁ e)
    (hstep₂ : Lir.step (inlineProgram l raw) { mem, ctx, stack := fr₂ :: rest₂ } =
      Lir.takeEdge (inlineFunc l F) { mem, ctx, stack := fr₂ :: rest₂ } fr₂ rest₂ ρ₂ (relabelEdge (newLabel l F) e)) :
    MatchedStep l raw { mem, ctx, stack := fr₁ :: rest₁ } { mem, ctx, stack := fr₂ :: rest₂ } := by
  have hargsEq : Lir.evalArgs ρ₁ e.args = Lir.evalArgs ρ₂ e.args := hagree.evalArgs_eq heLt
  cases hargs : Lir.evalArgs ρ₁ e.args with
  | none =>
    apply MatchedStep.rawStuck
    simp [hstep₁, Lir.takeEdge, hargs]
  | some vals =>
    have hargs₂ : Lir.evalArgs ρ₂ (relabelEdge (newLabel l F) e).args = some vals := by
      simpa [relabelEdge, hargsEq] using hargs
    cases hTB : F.blocks[e.target]? with
    | none =>
      apply MatchedStep.rawStuck
      simp [hstep₁, Lir.takeEdge, hargs, hTB]
    | some TB =>
      obtain ⟨TB', hTB', hparams⟩ := ChunkPos.entry_params l F hTB
      have hcp' := ChunkPos.entry l F hTB
      obtain ⟨hfwd, _, _⟩ := hagree.bindParams_agree TB.params vals
      cases hbp : Lir.bindParams ρ₁ TB.params vals with
      | none =>
        apply MatchedStep.rawStuck
        simp [hstep₁, Lir.takeEdge, hargs, hTB, hbp]
      | some ρ₁' =>
        obtain ⟨ρ₂', hbp₂, hagree'⟩ := hfwd ρ₁' hbp
        have hcharge : decide (newLabel l F e.target ≤ fr₂.label) = decide (e.target ≤ fr₁.label) := by
          rw [hlbl₂]
          by_cases hle : e.target ≤ fr₁.label
          · have h1 : newLabel l F e.target ≤ newLabel l F fr₁.label + blockExtra l B :=
              (newLabel_end_le_iff l F hB).mpr hle
            simp only [decide_eq_true hle, decide_eq_true h1]
          · have h1 : ¬ newLabel l F e.target ≤ newLabel l F fr₁.label + blockExtra l B := by
              intro hle'; exact hle ((newLabel_end_le_iff l F hB).mp hle')
            simp only [decide_eq_false hle, decide_eq_false h1]
        have hs₁ : Lir.semStep raw { mem, ctx, stack := fr₁ :: rest₁ } =
            .next { mem, ctx, stack := { fr₁ with label := e.target, pos := 0, env := ρ₁' } :: rest₁ }
              (decide (e.target ≤ fr₁.label)) := by
          apply Lir.semStep_next.mpr
          rw [hstep₁]
          exact Lir.takeEdge_ok hargs hTB hbp
        have hs₂ : Lir.semStep (inlineProgram l raw) { mem, ctx, stack := fr₂ :: rest₂ } =
            .next { mem, ctx, stack := { fr₂ with label := newLabel l F e.target, pos := 0, env := ρ₂' } :: rest₂ }
              (decide (e.target ≤ fr₁.label)) := by
          apply Lir.semStep_next.mpr
          rw [hstep₂, ← hcharge]
          exact Lir.takeEdge_ok hargs₂ (by simpa [relabelEdge] using hTB') (by simpa [hparams] using hbp₂)
        refine .sync hs₁ (.refl _) hs₂ (.refl _) (by omega) ?_
        exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcp' hagree' (by simp [hdsts₁, hdsts₂])) hrest,
          fun _ _ h => by cases h; exact hdsts₁⟩

/-! ## Master single-step / single-site simulation theorem -/

theorem step_match {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {s₁ s₂ : Lir.State} (hrel : StateRel l raw s₁ s₂) :
    MatchedStep l raw s₁ s₂ := by
  rcases s₁ with ⟨mem₁, ctx₁, stack₁⟩
  rcases s₂ with ⟨mem₂, ctx₂, stack₂⟩
  rcases hrel with ⟨hmem, hctx, hstack, htopDsts⟩
  dsimp only at hmem hctx hstack htopDsts
  subst mem₂; subst ctx₂
  cases hstack with
  | nil =>
    exact .rawStuck rfl
  | @consDecSlow F B wrapFr caller₁ caller₂ rest₁ rest₂ dst x inLbl
      hwrap hlt hfn hF hdsts₁ hdsts₂ hfree hfreeBlk hjoinBlk hcpNext hagree hrest =>
    obtain ⟨jb, hb5, hjp, hjbPos, hjbStmt⟩ := hjoinBlk
    have hF' : (inlineProgram l raw).funcs[caller₂.fn]? = some (inlineFunc l F) := by
      rw [hfn, inlineProgram_get_lt l raw hlt, hF]; rfl
    have hs₁ : Lir.semStep raw { mem := mem₁, ctx := ctx₁, stack := wrapFr :: caller₁ :: rest₁ } =
        .next { mem := mem₁, ctx := ctx₁, stack := { caller₁ with env := caller₁.env.insert dst 1, dsts := [] } :: rest₁ } false := by
      apply Lir.semStep_next.mpr
      have hterm := Lir.step_term (p := raw) (F := decrementWrapper l.decProc)
        (B := (decrementWrapper l.decProc).blocks[0]!) (fr := wrapFr) (rest := caller₁ :: rest₁)
        (mem := mem₁) (ctx := ctx₁) (by rw [hwrap.1]; exact hr.decWrap)
        (by rw [hwrap.2.1]; rfl) (by rw [hwrap.2.2.1]; rfl)
      rw [hterm]
      simp [decrementWrapper, Lir.evalArgs, Lir.Arg.eval, hdsts₁, Lir.bindParams]
    have hs₂_1 : Lir.semStep (inlineProgram l raw) { mem := mem₁, ctx := ctx₁, stack := caller₂ :: rest₂ } =
        .next { mem := mem₁, ctx := ctx₁, stack := { caller₂ with label := inLbl + 5, pos := 0 } :: rest₂ } false := by
      apply Lir.semStep_next.mpr
      have hterm := Lir.step_term (p := inlineProgram l raw) (F := inlineFunc l F)
        (B := { body := #[.call [] l.decProc [.v x]], term := .jump ⟨inLbl + 5, []⟩, cold := B.cold })
        (fr := caller₂) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
        hF' (by rw [hfree.1]; exact hfreeBlk) (by rw [hfree.2]; rfl)
      rw [hterm]
      have hfwd : ¬ (inLbl + 5 ≤ caller₂.label) := by
        rw [hfree.1]; dsimp only [Lir.Label]; omega
      simp [Lir.takeEdge, Lir.evalArgs, hb5, hjp, Lir.bindParams, hfwd]
    have hjbGet : jb.body[0] = .assign dst (.arg (.imm 1)) := by
      rw [Array.getElem?_eq_getElem hjbPos, Option.some.injEq] at hjbStmt; exact hjbStmt
    have hs₂_2 : Lir.semStep (inlineProgram l raw)
        { mem := mem₁, ctx := ctx₁, stack := { caller₂ with label := inLbl + 5, pos := 0 } :: rest₂ } =
        .next { mem := mem₁, ctx := ctx₁, stack := { caller₂ with label := inLbl + 5, pos := 1, env := caller₂.env.insert dst 1, dsts := [] } :: rest₂ } false := by
      apply Lir.semStep_next.mpr
      have h1 := Lir.step_stmt (p := inlineProgram l raw) (F := inlineFunc l F) (B := jb)
        (fr := { caller₂ with label := inLbl + 5, pos := 0 }) (rest := rest₂)
        (mem := mem₁) (ctx := ctx₁) (ρ' := caller₂.env.insert dst 1) (mem' := mem₁)
        hF' hb5 hjbPos hjbGet rfl (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval])
      simpa [hdsts₂] using h1
    refine .sync hs₁ (.refl _) hs₂_1 (.free hs₂_2 (.refl _)) (by omega) ?_
    exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext (hagree.insert_same dst 1) rfl) hrest,
      fun _ _ h => by cases h; rfl⟩
  | @cons fr₁ fr₂ rest₁ rest₂ hfr hrest =>
    have htop : fr₁.dsts = [] := htopDsts fr₁ rest₁ rfl
    cases hfr with
    | emptySource _ hF hnone =>
      exact .rawStuck (by unfold Lir.step; simp [hF, hnone])
    | runtime hge =>
      have hfunEq : (inlineProgram l raw).funcs[fr₁.fn]? = raw.funcs[fr₁.fn]? :=
        inlineProgram_get_ge l raw hge
      cases hF : raw.funcs[fr₁.fn]? with
      | none => exact .rawStuck (by unfold Lir.step; simp [hF])
      | some F =>
        have hF' : (inlineProgram l raw).funcs[fr₁.fn]? = some F := by rw [hfunEq, hF]
        cases hB : F.blocks[fr₁.label]? with
        | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB])
        | some B =>
          by_cases hpos : fr₁.pos < B.body.size
          · cases hs : B.body[fr₁.pos] with
            | call rs g as =>
              cases hargs : Lir.evalArgs fr₁.env as with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hargs])
              | some vs =>
                obtain ⟨heFwd, _, _⟩ := enter_rel l raw (g := g) (vs := vs)
                cases hent : Lir.enter raw g vs with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hargs, hent])
                | some callee₁ =>
                  obtain ⟨callee₂, hent₂, hfrCallee, hdstCallee⟩ := heFwd callee₁ hent
                  have hs₁ := Lir.semStep_next.mpr (Lir.step_call (p := raw) (mem := mem₁) (ctx := ctx₁) (rest := rest₁) hF hB hpos hs hargs hent)
                  have hs₂ := Lir.semStep_next.mpr (Lir.step_call (p := inlineProgram l raw) (mem := mem₁) (ctx := ctx₁) (rest := rest₂) hF' hB hpos hs hargs hent₂)
                  refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                  exact ⟨rfl, rfl, .cons hfrCallee (.cons (.runtime hge) hrest),
                    fun _ _ h => by cases h; exact hdstCallee⟩
            | assign x r =>
              cases hx : (Lir.Stmt.assign x r).exec fr₁.env mem₁ ctx₁ with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hx])
              | some p =>
                rcases p with ⟨ρ', mem'⟩
                have hs₁ := Lir.semStep_next.mpr (Lir.step_stmt (p := raw) (rest := rest₁) hF hB hpos hs rfl hx)
                have hs₂ := Lir.semStep_next.mpr (Lir.step_stmt (p := inlineProgram l raw) (rest := rest₂) hF' hB hpos hs rfl hx)
                refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                exact ⟨rfl, rfl, .cons (.runtime hge) hrest, fun _ _ h => by cases h; exact htop⟩
            | limb r1 r2 op =>
              cases hx : (Lir.Stmt.limb r1 r2 op).exec fr₁.env mem₁ ctx₁ with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hx])
              | some p =>
                rcases p with ⟨ρ', mem'⟩
                have hs₁ := Lir.semStep_next.mpr (Lir.step_stmt (p := raw) (rest := rest₁) hF hB hpos hs rfl hx)
                have hs₂ := Lir.semStep_next.mpr (Lir.step_stmt (p := inlineProgram l raw) (rest := rest₂) hF' hB hpos hs rfl hx)
                refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                exact ⟨rfl, rfl, .cons (.runtime hge) hrest, fun _ _ h => by cases h; exact htop⟩
            | store w m a =>
              cases hx : (Lir.Stmt.store w m a).exec fr₁.env mem₁ ctx₁ with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hx])
              | some p =>
                rcases p with ⟨ρ', mem'⟩
                have hs₁ := Lir.semStep_next.mpr (Lir.step_stmt (p := raw) (rest := rest₁) hF hB hpos hs rfl hx)
                have hs₂ := Lir.semStep_next.mpr (Lir.step_stmt (p := inlineProgram l raw) (rest := rest₂) hF' hB hpos hs rfl hx)
                refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                exact ⟨rfl, rfl, .cons (.runtime hge) hrest, fun _ _ h => by cases h; exact htop⟩
          · have hposGe : ¬ fr₁.pos < B.body.size := hpos
            cases ht : B.term with
            | jump e =>
              exact matched_of_runtime_edge (F := F) (ρ0 := fr₁.env) (e := e) hge htop hrest
                (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht])
                (by unfold Lir.step; simp only [hF', hB, hposGe, ↓reduceDIte, ht])
            | br c w a b' t f =>
              cases ha : a.eval fr₁.env with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha])
              | some va =>
                cases hb : b'.eval fr₁.env with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha, hb])
                | some vb =>
                  exact matched_of_runtime_edge (F := F) (ρ0 := fr₁.env) (e := if c.holds w va vb then t else f)
                    hge htop hrest
                    (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, ha, hb])
                    (by unfold Lir.step; simp only [hF', hB, hposGe, ↓reduceDIte, ht, ha, hb])
            | brOvf o x a b' ok ovf =>
              cases ha : a.eval fr₁.env with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha])
              | some va =>
                cases hb : b'.eval fr₁.env with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha, hb])
                | some vb =>
                  exact matched_of_runtime_edge (F := F) (ρ0 := fr₁.env.insert x (o.eval va vb).1)
                    (e := if (o.eval va vb).2 then ovf else ok) hge htop hrest
                    (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, ha, hb])
                    (by unfold Lir.step; simp only [hF', hB, hposGe, ↓reduceDIte, ht, ha, hb])
            | ret as =>
              cases hargs : Lir.evalArgs fr₁.env as with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, hargs])
              | some vals =>
                exact matched_of_ret (vals := vals)
                  (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, hargs]; rfl)
                  (by unfold Lir.step; simp only [hF', hB, hposGe, ↓reduceDIte, ht, hargs]; rfl) hrest
            | tail g as =>
              cases hargs : Lir.evalArgs fr₁.env as with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, hargs])
              | some vs =>
                obtain ⟨heFwd, _, _⟩ := enter_rel l raw (g := g) (vs := vs)
                cases hent : Lir.enter raw g vs with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, hargs, hent])
                | some callee₁ =>
                  obtain ⟨callee₂, hent₂, hfrCallee, hdstCallee⟩ := heFwd callee₁ hent
                  have hs₁ : Lir.semStep raw { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } =
                      .next { mem := mem₁, ctx := ctx₁, stack := callee₁ :: rest₁ } true := by
                    apply Lir.semStep_next.mpr; unfold Lir.step; simp [hF, hB, hposGe, ht, hargs, hent]
                  have hs₂ : Lir.semStep (inlineProgram l raw) { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } =
                      .next { mem := mem₁, ctx := ctx₁, stack := callee₂ :: rest₂ } true := by
                    apply Lir.semStep_next.mpr; unfold Lir.step; simp [hF', hB, hposGe, ht, hargs, hent₂]
                  refine .sync hs₁ (.refl _) hs₂ (.refl _) (by omega) ?_
                  exact ⟨rfl, rfl, .cons hfrCallee hrest, fun _ _ h => by cases h; exact hdstCallee⟩
            | fail r =>
              refine .sameFinal (r := .resource r) ?_ ?_
              · rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hposGe, ht]; exact .fail
              · rw [Lir.semStep]; unfold Lir.step; simp [hF', hB, hposGe, ht]; exact .fail
            | trap =>
              refine .sameFinal (r := .trap) ?_ ?_
              · rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hposGe, ht]; exact .trap
              · rw [Lir.semStep]; unfold Lir.step; simp [hF', hB, hposGe, ht]; exact .trap
    | @source F B _ _ hlt hfn hF hcp0 hagree hdsts =>
      have hdsts₂ : fr₂.dsts = [] := hdsts.trans htop
      have hF' : (inlineProgram l raw).funcs[fr₂.fn]? = some (inlineFunc l F) := by
        rw [hfn, inlineProgram_get_lt l raw hlt, hF]; rfl
      obtain ⟨tmp, params, acc, rest0, hcp⟩ := hcp0
      have hB : F.blocks[fr₁.label]? = some B := hcp.bLookup
      by_cases hpos : fr₁.pos < B.body.size
      · obtain ⟨restStmts, hrest0⟩ := ChunkPos.rest_cons hcp hpos
        let s := B.body[fr₁.pos]
        have hsMem : s ∈ B.body.toList := by
          have : B.body.toList[fr₁.pos]? = some s := by
            rw [Array.getElem?_toList, Array.getElem?_eq_getElem hpos]
          exact List.mem_of_getElem? this
        have hsMax : stmtMax s 0 < freshBase F := by
          have := stmt_le_maxVReg hB hsMem; unfold freshBase; omega
        cases hcls : classify l s with
        | none =>
          obtain ⟨⟨blk, hblk, hinPosLt, hblkStmt⟩, hcpNext⟩ :=
            ChunkPos.step_normal hcp hrest0 hcls hpos rfl
          have hblkGet : blk.body[fr₂.pos] = s := by
            rw [Array.getElem?_eq_getElem hinPosLt, Option.some.injEq] at hblkStmt; exact hblkStmt
          cases hsEq : B.body[fr₁.pos] with
          | call rs g as =>
            have hargsLt : argsMax as 0 < freshBase F := call_args_lt_freshBase hB (by rw [← hsEq]; exact hsMem)
            have hargsEq := hagree.evalArgs_eq hargsLt
            cases hargs : Lir.evalArgs fr₁.env as with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, hargs])
            | some vs =>
              obtain ⟨heFwd, _, _⟩ := enter_rel l raw (g := g) (vs := vs)
              cases hent : Lir.enter raw g vs with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, hargs, hent])
              | some callee₁ =>
                obtain ⟨callee₂, hent₂, hfrCallee, hdstCallee⟩ := heFwd callee₁ hent
                have hs₁ := Lir.semStep_next.mpr (Lir.step_call (p := raw) (mem := mem₁) (ctx := ctx₁) (rest := rest₁) hF hB hpos hsEq hargs hent)
                have hs₂ := Lir.semStep_next.mpr (Lir.step_call (p := inlineProgram l raw) (mem := mem₁) (ctx := ctx₁) (rest := rest₂) hF' hblk hinPosLt
                  (hblkGet.trans hsEq) (by rw [← hargsEq, hargs]) hent₂)
                refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
                exact ⟨rfl, rfl, .cons hfrCallee (.cons (.source hlt hfn hF hcpNext hagree rfl) hrest),
                  fun _ _ h => by cases h; exact hdstCallee⟩
          | assign x r =>
            obtain ⟨hfwd, _, _⟩ := hagree.stmt_exec (s := .assign x r) (by simpa [s, hsEq] using hsMax) mem₁ ctx₁
            cases hx : (Lir.Stmt.assign x r).exec fr₁.env mem₁ ctx₁ with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, hx])
            | some p =>
              rcases p with ⟨ρ₁', mem'⟩
              obtain ⟨ρ₂', hx₂, hagree'⟩ := hfwd ρ₁' mem' hx
              have hs₁ := Lir.semStep_next.mpr (Lir.step_stmt (p := raw) (rest := rest₁) hF hB hpos hsEq rfl hx)
              have hs₂ := Lir.semStep_next.mpr (Lir.step_stmt (p := inlineProgram l raw) (rest := rest₂) hF' hblk hinPosLt
                (hblkGet.trans hsEq) rfl hx₂)
              refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
              exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' hdsts) hrest,
                fun _ _ h => by cases h; exact htop⟩
          | limb r1 r2 op =>
            obtain ⟨hfwd, _, _⟩ := hagree.stmt_exec (s := .limb r1 r2 op) (by simpa [s, hsEq] using hsMax) mem₁ ctx₁
            cases hx : (Lir.Stmt.limb r1 r2 op).exec fr₁.env mem₁ ctx₁ with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, hx])
            | some p =>
              rcases p with ⟨ρ₁', mem'⟩
              obtain ⟨ρ₂', hx₂, hagree'⟩ := hfwd ρ₁' mem' hx
              have hs₁ := Lir.semStep_next.mpr (Lir.step_stmt (p := raw) (rest := rest₁) hF hB hpos hsEq rfl hx)
              have hs₂ := Lir.semStep_next.mpr (Lir.step_stmt (p := inlineProgram l raw) (rest := rest₂) hF' hblk hinPosLt
                (hblkGet.trans hsEq) rfl hx₂)
              refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
              exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' hdsts) hrest,
                fun _ _ h => by cases h; exact htop⟩
          | store w m a =>
            obtain ⟨hfwd, _, _⟩ := hagree.stmt_exec (s := .store w m a) (by simpa [s, hsEq] using hsMax) mem₁ ctx₁
            cases hx : (Lir.Stmt.store w m a).exec fr₁.env mem₁ ctx₁ with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, hx])
            | some p =>
              rcases p with ⟨ρ₁', mem'⟩
              obtain ⟨ρ₂', hx₂, hagree'⟩ := hfwd ρ₁' mem' hx
              have hs₁ := Lir.semStep_next.mpr (Lir.step_stmt (p := raw) (rest := rest₁) hF hB hpos hsEq rfl hx)
              have hs₂ := Lir.semStep_next.mpr (Lir.step_stmt (p := inlineProgram l raw) (rest := rest₂) hF' hblk hinPosLt
                (hblkGet.trans hsEq) rfl hx₂)
              refine .sync hs₁ (.refl _) hs₂ (.refl _) (by simp) ?_
              exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' hdsts) hrest,
                fun _ _ h => by cases h; exact htop⟩
        | some site =>
          cases site with
          | inc dst x =>
            obtain ⟨wLit, hsEq0⟩ := classify_eq_inc hcls
            have hsEq : B.body[fr₁.pos] = .call [dst] l.incWrapper [.v x, .imm wLit] := hsEq0
            have hxLt : x < freshBase F := by
              have h1 := call_args_lt_freshBase hB (by rw [← hsEq]; exact hsMem)
              have h2 : x ≤ argsMax [.v x, .imm wLit] 0 := mem_le_argsMax (by simp)
              dsimp only [Lir.VReg] at h2 ⊢; omega
            have hxEq : fr₁.env[x]? = fr₂.env[x]? := hagree x hxLt
            cases hx : fr₁.env[x]? with
            | none =>
              exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, Lir.evalArgs, Lir.Arg.eval, hx])
            | some xVal =>
              have hraw := raw_inc_exec hr hF hB hpos hsEq hx (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
              obtain ⟨hcpNext, hinl⟩ := inl_inc_exec (raw := raw) (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp
                (by rwa [← hsEq]) hpos hsEq (by rw [← hxEq, hx]) hxLt (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
              cases hout : evalIncSite xVal mem₁ with
              | stuck =>
                rw [hout] at hraw
                exact .rawStuckWithin (by omega) hraw
              | oom =>
                rw [hout] at hraw hinl
                exact .sameOom (by omega) hraw hinl
              | ok mem' =>
                rw [hout] at hraw hinl
                obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
                obtain ⟨env', s₂', hs₂, hstar₂, hag'⟩ := hinl
                have hagree' : AgreeBelow (freshBase F) (fr₁.env.insert dst 1) env' := fun r hr' => by
                  rw [← hag' r hr', Lir.env_insert_get, Lir.env_insert_get]
                  split
                  · rfl
                  · exact hagree r hr'
                refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
                  fun _ _ h => by cases h; rfl⟩
          | dec dst x =>
            have hsEq : B.body[fr₁.pos] = .call [dst] l.decWrapper [.v x] := classify_eq_dec hcls
            have hxLt : x < freshBase F := by
              have h1 := call_args_lt_freshBase hB (by rw [← hsEq]; exact hsMem)
              have h2 : x ≤ argsMax [.v x] 0 := mem_le_argsMax (by simp)
              dsimp only [Lir.VReg] at h2 ⊢; omega
            have hxEq : fr₁.env[x]? = fr₂.env[x]? := hagree x hxLt
            cases hx : fr₁.env[x]? with
            | none =>
              exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, Lir.evalArgs, Lir.Arg.eval, hx])
            | some xVal =>
              have hraw := raw_dec_exec hr hF hB hpos hsEq hx (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
              obtain ⟨hcpNext, hfreeBlk, hjoinBlk, hinl⟩ := inl_dec_exec hr (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp
                (by rwa [← hsEq]) hpos hsEq (by rw [← hxEq, hx]) hxLt (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
              cases hout : evalDecSite xVal mem₁ with
              | stuck =>
                rw [hout] at hraw
                exact .rawStuckWithin (by omega) hraw
              | ok mem' =>
                rw [hout] at hraw hinl
                obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
                obtain ⟨env', s₂', hs₂, hstar₂, hag'⟩ := hinl
                have hagree' : AgreeBelow (freshBase F) (fr₁.env.insert dst 1) env' := fun r hr' => by
                  rw [← hag' r hr', Lir.env_insert_get, Lir.env_insert_get]
                  split
                  · rfl
                  · exact hagree r hr'
                refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
                  fun _ _ h => by cases h; rfl⟩
              | free =>
                rw [hout] at hraw hinl
                obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
                obtain ⟨env', s₂', hs₂, hstar₂, hag'⟩ := hinl
                have hagree' : AgreeBelow (freshBase F) fr₁.env env' := fun r hr' =>
                  (hagree r hr').trans (hag' r hr')
                have hdecGe : l.sourceCount ≤ l.decProc := by
                  simp [Layout.decProc, Layout.incProc]; omega
                refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                exact ⟨rfl, rfl, .cons (.runtime hdecGe)
                  (.consDecSlow ⟨rfl, rfl, rfl, rfl⟩ hlt hfn hF rfl rfl ⟨rfl, rfl⟩ hfreeBlk hjoinBlk hcpNext hagree' hrest),
                  fun _ _ h => by cases h; rfl⟩
          | alloc dst idx lay cls args =>
            obtain ⟨c, hc, hsEq0, hlay, hclsOk, hlen, hok, _⟩ := classify_eq_alloc hcls
            have hsEq : B.body[fr₁.pos] = .call [dst] (l.allocWrapper idx) args := hsEq0
            have hargsLt : argsMax args 0 < freshBase F := call_args_lt_freshBase hB (by rw [← hsEq]; exact hsMem)
            have hargsEq : Lir.evalArgs fr₁.env args = Lir.evalArgs fr₂.env args := hagree.evalArgs_eq hargsLt
            cases hargs : Lir.evalArgs fr₁.env args with
            | none =>
              exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hsEq, hargs])
            | some vals =>
              have hraw := raw_alloc_exec hr hF hB hpos hc hlay hclsOk hok hlen hsEq hargs
                (rest := rest₁) (mem := mem₁) (ctx := ctx₁)
              obtain ⟨hcpNext, hinl⟩ := inl_alloc_exec (raw := raw) (hfn ▸ hlt) (by rwa [hfn]) hdsts₂ hcp
                (by rwa [← hsEq]) (by rwa [← hsEq]) hpos hsEq (by rw [← hargsEq, hargs]) hargsLt
                (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
              cases hres : evalAllocReserve lay cls mem₁ ctx₁ with
              | stuck =>
                rw [hres] at hraw
                exact .rawStuckWithin (by omega) hraw
              | oom =>
                rw [hres] at hraw hinl
                exact .sameOom (by omega) hraw hinl
              | ok addr mem₂ =>
                rw [hres] at hraw hinl
                dsimp only at hraw hinl
                cases hwf : writeFieldsMem mem₂ addr 0 vals with
                | none =>
                  rw [hwf] at hraw
                  exact .rawStuckWithin (by omega) hraw
                | some mem' =>
                  rw [hwf] at hraw hinl
                  obtain ⟨s₁', hs₁, hstar₁⟩ := hraw
                  obtain ⟨env', s₂', hs₂, hstar₂, hag'⟩ := hinl
                  have hagree' : AgreeBelow (freshBase F) (fr₁.env.insert dst addr) env' := fun r hr' => by
                    rw [← hag' r hr', Lir.env_insert_get, Lir.env_insert_get]
                    split
                    · rfl
                    · exact hagree r hr'
                  refine .sync hs₁ hstar₁ hs₂ hstar₂ (by simp) ?_
                  exact ⟨rfl, rfl, .cons (.source hlt hfn hF hcpNext hagree' rfl) hrest,
                    fun _ _ h => by cases h; rfl⟩
      · have hposEq : fr₁.pos = B.body.size := by have := hcp.posLe; omega
        obtain ⟨blk, hblk, hinPosEq, htermEq, hlbl₂⟩ := ChunkPos.at_term ⟨tmp, params, acc, rest0, hcp⟩ hposEq
        have hposGe : ¬ fr₁.pos < B.body.size := hpos
        have hinPosGe : ¬ fr₂.pos < blk.body.size := by omega
        have htMax : termMax B.term 0 < freshBase F := by
          have := term_le_maxVReg hB; unfold freshBase; omega
        cases ht : B.term with
        | jump e =>
          have heLt : argsMax e.args 0 < freshBase F := by simpa [ht, termMax, edgeMax] using htMax
          exact matched_of_edge hlt hfn hF hB htop hdsts₂ hlbl₂ hagree heLt hrest
            (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht])
            (by unfold Lir.step; simp only [hF', hblk, hinPosGe, ↓reduceDIte, htermEq, ht, relabelTerm])
        | br c w a b' t f =>
          simp only [ht, termMax] at htMax
          obtain ⟨hfLt, h1⟩ := AgreeBelow.edge_lt_of_chain htMax
          obtain ⟨htLt, h2⟩ := AgreeBelow.edge_lt_of_chain h1
          obtain ⟨hbLt, haLt⟩ := AgreeBelow.arg_lt_of_chain h2
          have haEq := hagree.arg_eval haLt
          have hbEq := hagree.arg_eval hbLt
          cases ha : a.eval fr₁.env with
          | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha])
          | some va =>
            cases hb : b'.eval fr₁.env with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha, hb])
            | some vb =>
              by_cases hcond : c.holds w va vb = true
              · exact matched_of_edge hlt hfn hF hB htop hdsts₂ hlbl₂ hagree htLt hrest
                  (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, ha, hb, hcond, ↓reduceIte])
                  (by unfold Lir.step; simp only [hF', hblk, hinPosGe, ↓reduceDIte, htermEq, ht, relabelTerm, ← haEq, ha, ← hbEq, hb, hcond, ↓reduceIte])
              · have hcondF : c.holds w va vb = false := by simpa using hcond
                exact matched_of_edge hlt hfn hF hB htop hdsts₂ hlbl₂ hagree hfLt hrest
                  (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, ha, hb, hcondF, Bool.false_eq_true, ↓reduceIte])
                  (by unfold Lir.step; simp only [hF', hblk, hinPosGe, ↓reduceDIte, htermEq, ht, relabelTerm, ← haEq, ha, ← hbEq, hb, hcondF, Bool.false_eq_true, ↓reduceIte])
        | brOvf o x a b' ok ovf =>
          simp only [ht, termMax] at htMax
          obtain ⟨hovfLt, h1⟩ := AgreeBelow.edge_lt_of_chain htMax
          obtain ⟨hokLt, h2⟩ := AgreeBelow.edge_lt_of_chain h1
          obtain ⟨hbLt, h3⟩ := AgreeBelow.arg_lt_of_chain h2
          obtain ⟨haLt, _⟩ := AgreeBelow.arg_lt_of_chain h3
          have haEq := hagree.arg_eval haLt
          have hbEq := hagree.arg_eval hbLt
          cases ha : a.eval fr₁.env with
          | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha])
          | some va =>
            cases hb : b'.eval fr₁.env with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, ha, hb])
            | some vb =>
              let res := o.eval va vb
              have hagree' := hagree.insert_same x res.1
              cases hov : res.2 with
              | true =>
                exact matched_of_edge hlt hfn hF hB htop hdsts₂ hlbl₂ hagree' hovfLt hrest
                  (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, ha, hb, res, hov, ↓reduceIte])
                  (by unfold Lir.step; simp only [hF', hblk, hinPosGe, ↓reduceDIte, htermEq, ht, relabelTerm, ← haEq, ha, ← hbEq, hb, res, hov, ↓reduceIte])
              | false =>
                exact matched_of_edge hlt hfn hF hB htop hdsts₂ hlbl₂ hagree' hokLt hrest
                  (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, ha, hb, res, hov, Bool.false_eq_true, ↓reduceIte])
                  (by unfold Lir.step; simp only [hF', hblk, hinPosGe, ↓reduceDIte, htermEq, ht, relabelTerm, ← haEq, ha, ← hbEq, hb, res, hov, Bool.false_eq_true, ↓reduceIte])
        | ret as =>
          have hargsLt : argsMax as 0 < freshBase F := by simpa [ht, termMax] using htMax
          have hargsEq := hagree.evalArgs_eq hargsLt
          cases hargs : Lir.evalArgs fr₁.env as with
          | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, hargs])
          | some vals =>
            exact matched_of_ret (vals := vals)
              (by unfold Lir.step; simp only [hF, hB, hposGe, ↓reduceDIte, ht, hargs]; rfl)
              (by unfold Lir.step; simp only [hF', hblk, hinPosGe, ↓reduceDIte, htermEq, ht, relabelTerm, ← hargsEq, hargs]; rfl) hrest
        | tail g as =>
          have hargsLt : argsMax as 0 < freshBase F := by simpa [ht, termMax] using htMax
          have hargsEq := hagree.evalArgs_eq hargsLt
          cases hargs : Lir.evalArgs fr₁.env as with
          | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, hargs])
          | some vs =>
            obtain ⟨heFwd, _, _⟩ := enter_rel l raw (g := g) (vs := vs)
            cases hent : Lir.enter raw g vs with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hposGe, ht, hargs, hent])
            | some callee₁ =>
              obtain ⟨callee₂, hent₂, hfrCallee, hdstCallee⟩ := heFwd callee₁ hent
              have hs₁ : Lir.semStep raw { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } =
                  .next { mem := mem₁, ctx := ctx₁, stack := callee₁ :: rest₁ } true := by
                apply Lir.semStep_next.mpr; unfold Lir.step; simp [hF, hB, hposGe, ht, hargs, hent]
              have hs₂ : Lir.semStep (inlineProgram l raw) { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } =
                  .next { mem := mem₁, ctx := ctx₁, stack := callee₂ :: rest₂ } true := by
                apply Lir.semStep_next.mpr; unfold Lir.step
                simp [hF', hblk, hinPosGe, htermEq, ht, relabelTerm, ← hargsEq, hargs, hent₂]
              refine .sync hs₁ (.refl _) hs₂ (.refl _) (by omega) ?_
              exact ⟨rfl, rfl, .cons hfrCallee hrest, fun _ _ h => by cases h; exact hdstCallee⟩
        | fail r =>
          refine .sameFinal (r := .resource r) ?_ ?_
          · rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hposGe, ht]; exact .fail
          · rw [Lir.semStep]; unfold Lir.step; simp [hF', hblk, hinPosGe, htermEq, ht, relabelTerm]; exact .fail
        | trap =>
          refine .sameFinal (r := .trap) ?_ ?_
          · rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hposGe, ht]; exact .trap
          · rw [Lir.semStep]; unfold Lir.step; simp [hF', hblk, hinPosGe, htermEq, ht, relabelTerm]; exact .trap

/-! ## Forward and backward clocked runs -/

theorem forward_run {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw) :
    ∀ fuel k s₁ s₂ r, StateRel l raw s₁ s₂ →
      Sem.runClocked (Lir.semStep raw) fuel k s₁ = r →
      r ≠ .timeout → r ≠ .stuck →
      ∃ k' r₂, Sem.Reaches (Lir.semStep (inlineProgram l raw)) s₂ k' r₂ ∧ Sem.Result.Refines Eq r r₂ := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro k s₁ s₂ r hrel hrun hnt hns
    have hr1 : Sem.Reaches (Lir.semStep raw) s₁ k r := Sem.runClocked_sound hrun hnt
    cases step_match hr hrel with
    | rawStuck hst =>
      have h2 : Sem.Reaches (Lir.semStep raw) s₁ k .stuck := .final (by rw [Lir.semStep, hst]; exact .stuck)
      exact absurd (hr1.det h2) hns
    | @rawStuckWithin c₁ hc hst =>
      have h2 : Sem.Reaches (Lir.semStep raw) s₁ (max k c₁) .stuck := hst.mono (by simp) (Nat.le_max_right k c₁)
      have h1 : Sem.Reaches (Lir.semStep raw) s₁ (max k c₁) r := hr1.mono hnt (Nat.le_max_left k c₁)
      exact absurd (h1.det h2) hns
    | sameFinal hf₁ hf₂ =>
      have heq : r = _ := hr1.det (.final hf₁)
      subst heq
      exact ⟨0, _, .final hf₂, Sem.Result.Refines.refl (fun _ => rfl)⟩
    | @sameOom c₁ hc hoom₁ hoom₂ =>
      have h2 : Sem.Reaches (Lir.semStep raw) s₁ (max k c₁) (.resource .heap) := hoom₁.mono (by simp) (Nat.le_max_right k c₁)
      have h1 : Sem.Reaches (Lir.semStep raw) s₁ (max k c₁) r := hr1.mono hnt (Nat.le_max_left k c₁)
      have heq := h1.det h2
      subst heq
      exact ⟨0, .resource .heap, hoom₂, .resource .heap⟩
    | sync hs₁ hstar₁ hs₂ hstar₂ _ hrel' =>
      obtain ⟨fuel', k', hflt, _, hrun'⟩ := runClocked_star_inv_lt hs₁ hstar₁ hrun hnt
      obtain ⟨k₂, r₂, hreach₂, href⟩ := ih fuel' hflt k' _ _ r hrel' hrun' hnt hns
      exact ⟨_, r₂, reaches_of_star_reaches (Sem.Star.head hs₂ hstar₂) hreach₂, href⟩

theorem backward_run {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw) :
    ∀ fuel k s₁ s₂ r, StateRel l raw s₁ s₂ →
      Sem.runClocked (Lir.semStep (inlineProgram l raw)) fuel k s₂ = r →
      r ≠ .timeout → (∀ fail, r ≠ .resource fail) →
      ∃ r₁, r₁ ≠ .timeout ∧ Sem.Reaches (Lir.semStep raw) s₁ (k + 2 * fuel) r₁ := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro k s₁ s₂ r hrel hrun hnt hnr
    have hfuelPos : 1 ≤ fuel := by
      cases fuel with
      | zero => simp [Sem.runClocked] at hrun; exact absurd hrun.symm hnt
      | succ _ => omega
    have hr2 : Sem.Reaches (Lir.semStep (inlineProgram l raw)) s₂ k r := Sem.runClocked_sound hrun hnt
    cases step_match hr hrel with
    | rawStuck hst =>
      exact ⟨.stuck, by simp, .final (by rw [Lir.semStep, hst]; exact .stuck)⟩
    | rawStuckWithin hc hst =>
      exact ⟨.stuck, by simp, hst.mono (by simp) (by omega)⟩
    | sameFinal hf₁ hf₂ =>
      have heq : r = _ := hr2.det (.final hf₂)
      subst heq
      exact ⟨r, hnt, .final hf₁⟩
    | sameOom hc hoom₁ hoom₂ =>
      have h2 := hoom₂.mono (by simp) (Nat.zero_le k)
      exact absurd (hr2.det h2) (hnr .heap)
    | @sync s₁' s₂' s₁'' s₂'' b₁ b₂ c₁ c₂ hs₁ hstar₁ hs₂ hstar₂ hchg hrel' =>
      obtain ⟨fuel', k', hflt, hkEq, hrun'⟩ := runClocked_star_inv_lt hs₂ hstar₂ hrun hnt
      obtain ⟨r₁, hr₁nt, hreach₁⟩ := ih fuel' hflt k' s₁'' s₂'' r hrel' hrun' hnt hnr
      have htotal := reaches_of_star_reaches (Sem.Star.head hs₁ hstar₁) hreach₁
      exact ⟨r₁, hr₁nt, htotal.mono hr₁nt (by omega)⟩

/-! ## Top-level simulation theorem (`inlineProgram_sim`) -/

/-- **`inlineProgram l raw` simulates `raw` with exact value equality.** -/
theorem inlineProgram_sim {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    (args : List Lir.Word) (mem : X86.Memory) (ctx : Lir.Word) :
    Sem.Sim Eq (fun k => k + 2 * Lir.fuelFor (inlineProgram l raw) k)
      (fun k => Lir.eval raw k args mem ctx)
      (fun k => Lir.eval (inlineProgram l raw) k args mem ctx) := by
  let inl := inlineProgram l raw
  have hmain : inl.main = raw.main := rfl
  obtain ⟨heFwd, _, heNone⟩ := enter_rel l raw (g := raw.main) (vs := args)
  cases hent : Lir.enter raw raw.main args with
  | none =>
    have hent₂ : Lir.enter inl inl.main args = none := by rw [hmain]; exact heNone.mp hent
    have he1 : ∀ k, Lir.eval raw k args mem ctx = .stuck := fun k => by
      simp [Lir.eval, Lir.State.initial, hent]
    have he2 : ∀ k, Lir.eval inl k args mem ctx = .stuck := fun k => by
      simp [Lir.eval, Lir.State.initial, hent₂]
    exact {
      forward := fun k _ => ⟨k, by rw [he1, he2]; exact .stuck⟩
      timeout := fun k hk => by rw [he1] at hk; cases hk }
  | some fr₁ =>
    obtain ⟨fr₂, hent₂, hfr, hdst₁⟩ := heFwd fr₁ hent
    let s₁ : Lir.State := { mem, ctx, stack := [fr₁] }
    let s₂ : Lir.State := { mem, ctx, stack := [fr₂] }
    have hinit₁ : Lir.State.initial raw args mem ctx = some s₁ := by
      simp [Lir.State.initial, hent, s₁]
    have hinit₂ : Lir.State.initial inl args mem ctx = some s₂ := by
      simp [Lir.State.initial, hmain, inl, hent₂, s₂]
    have hruns₁ := Lir.runs_eval hinit₁
    have hruns₂ := Lir.runs_eval hinit₂
    have hrel : StateRel l raw s₁ s₂ :=
      ⟨rfl, rfl, .cons hfr .nil, fun _ _ h => by cases h; exact hdst₁⟩
    exact {
      forward := fun k hk => by
        by_cases hst : Lir.eval raw k args mem ctx = .stuck
        · exact ⟨0, hst ▸ .stuck⟩
        · have hrun : Sem.runClocked (Lir.semStep raw) (Lir.fuelFor raw k) k s₁ =
              Lir.eval raw k args mem ctx := by
            rw [Lir.eval_eq, hinit₁]
          obtain ⟨k', r₂, hreach₂, href⟩ := forward_run hr (Lir.fuelFor raw k) k s₁ s₂ _ hrel hrun hk hst
          exact ⟨k', hruns₂.eq hreach₂ ▸ href⟩
      timeout := fun k hk => by
        by_cases hto : Lir.eval inl k args mem ctx = .timeout
        · exact .inl hto
        · by_cases hres : ∃ fail, Lir.eval inl k args mem ctx = .resource fail
          · exact .inr hres
          · have hres' : ∀ fail, Lir.eval inl k args mem ctx ≠ .resource fail :=
              fun fail h => hres ⟨fail, h⟩
            have hrun₂ : Sem.runClocked (Lir.semStep inl) (Lir.fuelFor inl k) k s₂ =
                Lir.eval inl k args mem ctx := by
              rw [Lir.eval_eq, hinit₂]
            obtain ⟨r₁, hr₁nt, hreach₁⟩ := backward_run hr (Lir.fuelFor inl k) k s₁ s₂ _ hrel hrun₂ hto hres'
            have hto₁ : Sem.Reaches (Lir.semStep raw) s₁ (k + 2 * Lir.fuelFor inl k) .timeout :=
              hk ▸ hruns₁ (k + 2 * Lir.fuelFor inl k)
            exact absurd (hreach₁.det hto₁) hr₁nt }

/-! ## Lifting `inlineProgram_sim` across `splitCriticalEdges` and clock maps -/

private theorem foldl_add_eq_sum {α : Type} (f : α → Nat) :
    ∀ (xs : List α) (acc : Nat), xs.foldl (fun n x => n + f x) acc = acc + (xs.map f).sum
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldl_add_eq_sum f xs]
    omega

theorem func_size_eq_sum (F : Lir.Func) :
    F.size = (F.blocks.toList.map Lir.Block.size).sum := by
  unfold Lir.Func.size
  rw [← Array.foldl_toList, foldl_add_eq_sum, Nat.zero_add]

theorem program_size_eq_sum (p : Lir.Program) :
    p.size = (p.funcs.toList.map Lir.Func.size).sum := by
  unfold Lir.Program.size
  rw [← Array.foldl_toList, foldl_add_eq_sum, Nat.zero_add]

private theorem emit_size_ge (blocks : List Lir.Block) (critical : Lir.Block → Lir.Edge → Bool)
    (relabel : Lir.Label → Lir.Label) :
    ∀ (bs : List Lir.Block) (ls : List Lir.Label), bs.length = ls.length →
      (bs.map Lir.Block.size).sum ≤
        ((Lir.Func.splitCriticalEdges.emit blocks critical relabel bs ls).map Lir.Block.size).sum
  | [], [], _ => Nat.le_refl _
  | b :: bs, l :: ls, hlen => by
    simp only [Lir.Func.splitCriticalEdges.emit, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, Lir.Block.size]
    have ih := emit_size_ge blocks critical relabel bs ls (by simpa using hlen)
    omega
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem func_size_le_split (F : Lir.Func) : F.size ≤ F.splitCriticalEdges.size := by
  rw [func_size_eq_sum, func_size_eq_sum]
  unfold Lir.Func.splitCriticalEdges
  dsimp only
  split
  · exact Nat.le_refl _
  · rw [List.toList_toArray]
    apply emit_size_ge
    rw [Lir.newLabels_length]
    simp

private theorem list_sum_map_le {α : Type} (f g : α → Nat) (h : ∀ x, f x ≤ g x) :
    ∀ (xs : List α), (xs.map f).sum ≤ (xs.map g).sum
  | [] => Nat.le_refl _
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons]
    have hx := h x
    have ih := list_sum_map_le f g h xs
    omega

theorem program_size_le_split (p : Lir.Program) : p.size ≤ p.splitCriticalEdges.size := by
  rw [program_size_eq_sum, program_size_eq_sum]
  simp only [Lir.Program.splitCriticalEdges, Array.toList_map, List.map_map]
  exact list_sum_map_le Lir.Func.size (Lir.Func.size ∘ Lir.Func.splitCriticalEdges)
    func_size_le_split p.funcs.toList

theorem fuelFor_le_split (p : Lir.Program) (k : Nat) :
    Lir.fuelFor p k ≤ Lir.fuelFor p.splitCriticalEdges k := by
  unfold Lir.fuelFor
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (program_size_le_split p) 1)

theorem fuelFor_main (p : Lir.Program) (m k : Nat) :
    Lir.fuelFor { p with main := m } k = Lir.fuelFor p k := rfl

/-- Target-indexed clock map for `inlineProgram` followed by `splitCriticalEdges`. -/
def inlineClock (p : Lir.Program) (k : Nat) : Nat := k + 2 * Lir.fuelFor p k

/-- Entry-level clock map composing `Nat.succ` with `inlineClock`. -/
def inlineEntryClock (p : Lir.Program) (k : Nat) : Nat := Nat.succ (inlineClock p k)

theorem inlineProgram_sim_clock {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    (args : List Lir.Word) (mem : X86.Memory) (ctx : Lir.Word)
    {f : Nat → Nat} (hf : ∀ k, k + 2 * Lir.fuelFor (inlineProgram l raw) k ≤ f k) :
    Sem.Sim Eq f
      (fun k => Lir.eval raw k args mem ctx)
      (fun k => Lir.eval (inlineProgram l raw) k args mem ctx) :=
  let hsim := inlineProgram_sim hr args mem ctx
  { forward := hsim.forward
    timeout := fun k hk => by
      apply hsim.timeout k
      by_cases h0 : Lir.eval raw (k + 2 * Lir.fuelFor (inlineProgram l raw) k) args mem ctx = .timeout
      · exact h0
      · have heq := Lir.eval_mono raw args mem ctx (hf k) h0
        dsimp only at heq
        rw [hk] at heq
        exact absurd heq.symm h0 }

end IxCC.Cfg.Rc.Inline
