import Compilatrix.Rt.Proof.Program

/-!
# `Rt.lower_correct`

The runtime lowering (Cfg's immortal fragment to Lir) is a clocked
simulation from Cfg's total clock to Lir's: whatever Cfg's run of function
`g` on `args` over heap `H` produces, other than a timeout or a stuck state,
the Lir program run from `g` on related words over a memory holding `H`
produces with related results, or fails for a resource (`natOverflow`,
`heap`); and where Cfg times out at clock `k + 1`, Lir times out or fails
for a resource at `k` (06 S32's timeout clause; Cfg charges the entry Lir's
`eval` does not, and from the entry on the clocks agree).

The proof composes the forward diagram from Cfg to the unpruned program
(`diagram`, entered by `entry_rel`) with the lock-step relabellings of
pruning and edge splitting.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word Label)
open Compilatrix.Rt.Lower
open Compilatrix.Src (NatMap NatSet)

/-- **Cfg's clock is defined on a successfully lowered program.** -/
theorem lower_ordered {P : Cfg.Program} {roots : List (Nat × String)} (hl : Lowers P roots) : Cfg.Ordered P where
  forward := by
    intro f fd b blk e hfd hb he hback
    obtain ⟨fd', params, raw, hfd', hraw, -⟩ := hl.fn (hl.dense hfd)
    rw [hfd] at hfd'
    cases hfd'
    obtain ⟨starts, hL⟩ := functionRaw_lowered hraw "" .internal
    have := hL.edges (by simpa [Cfg.Fun.block?] using hb) he
    rw [hback] at this
    exact Nat.lt_of_not_le (of_decide_eq_false this.symm)
  dense := hl.dense

/-- The frame a function is entered with. -/
def entryFrame (g : Nat) (b0 : Cfg.Block) (args : List Own.RVal) : Cfg.Frame :=
  { fn := g, blk := 0, rest := b0.body, env := Own.bindAll .leaf (b0.params.map (·.1)) args }

/-- Cfg's first step from a call: the entry, or stuck. -/
theorem call_step_cases {P : Cfg.Program} {g : Nat} {args : List Own.RVal} {H : Own.Heap} :
    Cfg.step .immortal P (.call g args [] H) = .stuck ∨
      ∃ fd b0, P.fun? g = some fd ∧ fd.blocks[0]? = some b0 ∧ args.length = b0.params.length ∧
        Cfg.step .immortal P (.call g args [] H) =
          .next (.run (entryFrame g b0 args) [] H) true := by
  simp only [Cfg.step]
  cases hfd : P.fun? g with
  | none => exact .inl rfl
  | some fd =>
    simp only [Cfg.Fun.block?]
    cases hb0 : fd.blocks[0]? with
    | none => exact .inl rfl
    | some b0 =>
      simp only
      split
      · rename_i hlen
        exact .inr ⟨fd, b0, rfl, hb0, hlen, rfl⟩
      · exact .inl rfl

/-- **`Rt.lower_correct`**, assuming `SwitchSel` of every state Cfg's run
reaches (`lower_correct` assumes `SwitchOk`; the pipeline's switch check
gives `SwitchSel` everywhere, `switchSel_of_ok`). -/
theorem lower_correct_sel {cfg : Config} {P : Cfg.Program} {L : Compilatrix.Rt.Lowered}
    (h : Compilatrix.Rt.lower cfg P = .ok L) {g : Nat} {args : List Own.RVal} {H : Own.Heap} {ws : List Word}
    {mem : X86.Memory} {ctx : Word} {Pw : List Word} (hargs : ListRel (ValRel (tables P) Pw) args ws)
    (hheap : HeapInv (tables P) Pw H ctx mem)
    (hsafe : ∀ s, Reach P (.call g args [] H) s → SwitchSel P s) :
    Sem.Sim (Res P ctx) (· + 1) (fun k => Cfg.run .immortal P k g args H)
      (fun k => Lir.eval { L.program with main := g } k ws mem ctx) := by
  have hl := (lower_lowers h).1
  have hruns₁ := Cfg.runs_run .immortal (lower_ordered hl) g args H
  rcases call_step_cases (P := P) (g := g) (args := args) (H := H) with hst | ⟨fd, b0, hfd, hb0, hlen, hst⟩
  · -- Cfg is stuck at the entry
    have hstuck : ∀ k, Cfg.run .immortal P k g args H = .stuck := by
      intro k
      exact (hruns₁ k).inv_final (hst ▸ .stuck)
    exact { forward := fun k _ => ⟨0, by rw [hstuck k]; exact .stuck⟩
            timeout := fun k hk => by rw [hstuck] at hk; cases hk }
  · -- the entry, and the run from it
    have ht := target_raw hl g
    obtain ⟨callee₀, he₀, s₂', hst₀, hrel⟩ := entry_rel (ctx := ctx) ht hfd hb0 hlen hargs hheap .nil
    have hlock := (raw_pruned hl g).lockStep.comp (pruned_split h g).lockStep
    obtain ⟨callee₁, he₁, hcr₁⟩ := (raw_pruned hl g).enter he₀
    obtain ⟨callee₂, he₂, hcr₂⟩ := (pruned_split h g).enter he₁
    have hinit₂ : Lir.State.initial { L.program with main := g } ws mem ctx = some { mem, ctx, stack := [callee₂] } := by
      simp [Lir.State.initial, he₂]
    have hruns₂ := Lir.runs_eval hinit₂
    have hm : (∃ u, Lir.StateRel (pruneRel P) { mem, ctx, stack := [callee₀] } u ∧
        Lir.StateRel (splitRelOf P L.roots) u { mem, ctx, stack := [callee₂] }) :=
      ⟨{ mem, ctx, stack := [callee₁] }, ⟨rfl, rfl, .cons hcr₁ .nil⟩, ⟨rfl, rfl, .cons hcr₂ .nil⟩⟩
    have hd := diagram_sel (ctx := ctx) ht (.call g args [] H) hsafe
    have hreach₁ : Reach P (.call g args [] H) (.run (entryFrame g b0 args) [] H) :=
      ⟨1, by simpa using Sem.Star.single hst⟩
    -- carry a run of the unpruned program from the entry to the final program
    have hcarry : ∀ {k : Nat} {r : Sem.Result (List Word × X86.Memory)}, r ≠ .stuck →
        Sem.Reaches (Lir.semStep (stageProg P (rawOf P L.roots) g)) s₂' k r →
        Lir.eval { L.program with main := g } k ws mem ctx = r := by
      intro k r hr h₀
      have h₁ : Sem.Reaches (Lir.semStep _) { mem, ctx, stack := [callee₀] } (k + 0) r := h₀.star hst₀
      exact hruns₂.eq (hlock.reaches h₁ hr hm)
    refine { forward := fun k hk => ?_, timeout := fun k hk => ?_ }
    · by_cases hstuck : Cfg.run .immortal P k g args H = .stuck
      · exact ⟨0, by rw [hstuck]; exact .stuck⟩
      · have hreach := hruns₁ k
        cases k with
        | zero => exact absurd (hreach.inv_charge_zero hst) hk
        | succ k =>
          have h₁ := hreach.inv_charge hst
          obtain ⟨k', r₂, hr₂, href⟩ := hd.forward h₁ hk hstuck ⟨hrel, hreach₁⟩
          have hr₂s : r₂ ≠ .stuck := fun e => hstuck (by subst e; exact Sem.Result.Refines.of_stuck href)
          exact ⟨k', by rw [hcarry hr₂s hr₂]; exact href⟩
    · have hreach : Sem.Reaches (Cfg.step .immortal P) (.call g args [] H) (k + 1) .timeout := by
        have := hruns₁ (k + 1)
        simp only at this hk
        rw [hk] at this
        exact this
      have h₁ := hreach.inv_charge hst
      rcases hd.timeout h₁ ⟨hrel, hreach₁⟩ with h₂ | ⟨failure, h₂⟩
      · exact .inl (hcarry (by simp) h₂)
      · exact .inr ⟨failure, hcarry (by simp) h₂⟩

/-- **`Rt.lower_correct`**: the runtime lowering simulates Cfg's immortal
semantics, with the clock map `k ↦ k + 1` at the level of `Cfg.run` and
`Lir.eval` (Cfg charges the entry), related arguments and results (`Res`:
one word related by `ValRel`, the heap invariant), resource failures
(`natOverflow`, `heap`) allowed, and a stuck Cfg run imposing nothing. It
assumes `SwitchOk` of every state Cfg's run reaches: each executed switch
scrutinises a value its lowering dispatches on (as a well-typed program's
do). -/
theorem lower_correct {cfg : Config} {P : Cfg.Program} {L : Compilatrix.Rt.Lowered}
    (h : Compilatrix.Rt.lower cfg P = .ok L) {g : Nat} {args : List Own.RVal} {H : Own.Heap} {ws : List Word}
    {mem : X86.Memory} {ctx : Word} {Pw : List Word} (hargs : ListRel (ValRel (tables P) Pw) args ws)
    (hheap : HeapInv (tables P) Pw H ctx mem)
    (hsafe : ∀ s, Reach P (.call g args [] H) s → SwitchOk P s) :
    Sem.Sim (Res P ctx) (· + 1) (fun k => Cfg.run .immortal P k g args H)
      (fun k => Lir.eval { L.program with main := g } k ws mem ctx) :=
  lower_correct_sel h hargs hheap fun s hs => (hsafe s hs).sel

end Compilatrix.Rt.Proof
