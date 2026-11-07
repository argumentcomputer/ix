import IxCC.Rt.Proof.StepTerm
import IxCC.Sem.Forward

/-!
# The forward diagram from Cfg to the lowered Lir

`diagram`: `Rel` (on Cfg states reachable from `s₀`) is a forward diagram
from Cfg's immortal step to the lowered program's Lir step, with final
values related by `Res`: every Cfg step is matched by Lir steps spending at
least its charge, or Lir fails for a resource (`natOverflow`, `heap`); a
Cfg return from the outermost frame is Lir's, and a Cfg trap is Lir's. It
assumes `SwitchOk` of the reachable states: each switch Cfg executes (not a
fused one) scrutinises a value its lowering dispatches on (`Dispatches`).
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

/-- Cfg states reachable from `s₀`. -/
def Reach (P : Cfg.Program) (s₀ s : Cfg.State) : Prop := ∃ c, Sem.Star (Cfg.step .immortal P) s₀ c s

/-- **What the switch lowering needs of a Cfg state**: at a switch that is
not a fused comparison's, the scrutinee is one the lowering dispatches on. -/
def SwitchOk (P : Cfg.Program) : Cfg.State → Prop
  | .run fr _ H => ∀ fd b x alts d v, P.fun? fr.fn = some fd → fd.blocks[fr.blk]? = some b → fr.rest = [] →
      fusable (tables P) (useCounts fd) b = none → b.term = .switch x alts d → fr.env.get? x = some v →
      Dispatches (tables P) H v alts
  | _ => True

/-- **What the switch lowering needs where Cfg steps**: `SwitchOk` only at
a scrutinee related to a word under the heap invariant whose key selects an
edge (a switch Cfg is stuck on needs nothing). `Rt.Proof.switchSel_of_ok`
gives it at every state of a program the pipeline's check accepts. -/
def SwitchSel (P : Cfg.Program) : Cfg.State → Prop
  | .run fr _ H => ∀ fd b x alts d v key fs e Pw w ctx m, P.fun? fr.fn = some fd → fd.blocks[fr.blk]? = some b →
      fr.rest = [] → fusable (tables P) (useCounts fd) b = none → b.term = .switch x alts d →
      fr.env.get? x = some v → ValRel (tables P) Pw v w → HeapInv (tables P) Pw H ctx m →
      v.asCtor P.known H = some (key, fs) → Cfg.selectEdge key alts d = some e → Dispatches (tables P) H v alts
  | _ => True

theorem SwitchOk.sel {P : Cfg.Program} : ∀ {s : Cfg.State}, SwitchOk P s → SwitchSel P s
  | .run _ _ _, h => fun fd b x alts d v _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 _ _ _ _ => h fd b x alts d v h1 h2 h3 h4 h5 h6
  | .call .., _ => trivial
  | .ret .., _ => trivial

/-- Cfg's step over an instruction other than a call. -/
theorem step_bind {P : Cfg.Program} {fr : Cfg.Frame} {stk : List (Cfg.Frame × Nat)} {H : Own.Heap} {x : Nat}
    {r : Own.Rhs} {is : List Cfg.Instr} (hfr : fr.rest = .bind x r :: is) (hnc : ∀ g as, r ≠ .fir (.call g as)) :
    Cfg.step .immortal P (.run fr stk H) =
      match Own.evalRhs .immortal P.tables fr.env H r with
      | .ok (v, H') => .next (.run { fr with rest := is, env := fr.env.insert x v } stk H') false
      | .resource r => .fail r
      | .trap => .trap
      | .timeout | .stuck => .stuck := by
  cases r with
  | fir e =>
    cases e with
    | call g as => exact absurd rfl (hnc g as)
    | _ => simp only [Cfg.step, hfr]; rfl
  | _ => simp only [Cfg.step, hfr]; rfl

/-- **The forward diagram**, given `SwitchSel` of the reachable states
(`diagram` with `SwitchOk`, `switchSel_of_ok` with the pipeline's check). -/
theorem diagram_sel {P : Cfg.Program} {lp : Lir.Program} {ctx : Word} (ht : Target P lp) (s₀ : Cfg.State)
    (hsafe : ∀ s, Reach P s₀ s → SwitchSel P s) :
    Sem.Forward (Cfg.step .immortal P) (Lir.semStep lp) (Res P ctx)
      (fun s₁ s₂ => Rel P lp ctx s₁ s₂ ∧ Reach P s₀ s₁) where
  next := by
    intro s₁ s₁' s₂ b ⟨hrel, c₀, hreach⟩ hs
    have hreach' : Reach P s₀ s₁' := ⟨c₀ + b.toNat, hreach.trans (.single hs)⟩
    match s₁, hrel, hs with
    | .call g vs stk H, hrel, hs =>
      have hb : b = true := by
        simp only [Cfg.step] at hs
        split at hs
        · split at hs
          · split at hs
            · simp only [Sem.Step.next.injEq] at hs; exact hs.2.symm
            · cases hs
          · cases hs
        · cases hs
      subst hb
      obtain ⟨c, s₂', hst, hc, hrel'⟩ := step_enter ht hrel hs
      exact .inl ⟨c, s₂', hst, hc, hrel', hreach'⟩
    | .ret v [] H, _, hs => simp [Cfg.step] at hs
    | .ret v ((fr, x) :: stk) H, hrel, hs =>
      simp only [Cfg.step, Sem.Step.next.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨s₂', h₁, hrel'⟩ := step_return hrel
      exact .inl ⟨0, s₂', by simpa using Lir.star_of_step h₁, Nat.le_refl _, hrel', hreach'⟩
    | .run fr stk H, hrel, hs =>
      cases hfr : fr.rest with
      | nil =>
        have hdisp := hsafe _ ⟨c₀, hreach⟩
        exact (step_term_sel ht hrel hfr
          (fun fd b x alts d v key fs e Pw w ctx' m h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
            hdisp fd b x alts d v key fs e Pw w ctx' m h1 h2 hfr h3 h4 h5 h6 h7 h8 h9)
          hs).imp (fun ⟨c, s₂', hst, hc, hrel'⟩ => ⟨c, s₂', hst, hc, hrel', hreach'⟩) id
      | cons i is =>
        obtain ⟨x, r⟩ := i
        by_cases hcall : ∃ g as, r = .fir (.call g as)
        · obtain ⟨g, as, rfl⟩ := hcall
          simp only [Cfg.step, hfr] at hs
          cases hvs : Own.evalArgs fr.env as with
          | none => simp [hvs] at hs
          | some vs =>
            simp only [hvs, Sem.Step.next.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            rcases step_call_instr hrel hfr hvs with hrel' | hfail
            · exact .inl ⟨0, s₂, .refl _, Nat.le_refl _, hrel', hreach'⟩
            · exact .inr hfail
        · have hnc : ∀ g as, r ≠ .fir (.call g as) := fun g as h => hcall ⟨g, as, h⟩
          rw [step_bind hfr hnc] at hs
          cases hev : Own.evalRhs .immortal P.tables fr.env H r with
          | ok p =>
            obtain ⟨v, H'⟩ := p
            simp only [hev, Sem.Step.next.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            rcases step_instr ht hrel hfr hnc hev with ⟨c, s₂', hst, hrel'⟩ | hfail
            · exact .inl ⟨c, s₂', hst, Nat.zero_le _, hrel', hreach'⟩
            · exact .inr hfail
          | _ => simp [hev] at hs
  final := by
    intro s₁ s₂ r ⟨hrel, _⟩ hf hr
    match s₁, hrel, hf with
    | .call g vs stk H, _, hf =>
      exfalso
      simp only [Cfg.step] at hf
      split at hf
      · split at hf
        · split at hf
          · cases hf
          · cases hf; exact hr rfl
        · cases hf; exact hr rfl
      · cases hf; exact hr rfl
    | .ret v [] H, hrel, hf =>
      simp only [Cfg.step] at hf
      cases hf
      obtain ⟨w, h₁, hres⟩ := final_return hrel
      exact .inl ⟨0, s₂, .ok ([w], s₂.mem), .refl _, by rw [Lir.semStep, h₁]; exact .done, .ok hres⟩
    | .ret v ((fr, x) :: stk) H, _, hf => simp only [Cfg.step] at hf; cases hf
    | .run fr stk H, hrel, hf =>
      cases hfr : fr.rest with
      | nil =>
        -- a `trap`, or a stuck step
        cases hst : Cfg.step .immortal P (.run fr stk H) with
        | trap =>
          rw [hst] at hf
          cases hf
          exact .inl ⟨0, s₂, .trap, .refl _, by rw [Lir.semStep, final_trap hrel hfr hst]; exact .trap, .trap⟩
        | stuck => rw [hst] at hf; cases hf; exact absurd rfl hr
        | next s b => rw [hst] at hf; cases hf
        | done p =>
          exfalso
          simp only [Cfg.step, hfr] at hst
          split at hst
          · split at hst
            · split at hst
              · simp [Cfg.takeEdge] at hst; split at hst <;> (try split at hst) <;> cases hst
              · split at hst
                · split at hst
                  · split at hst
                    · simp [Cfg.takeEdge] at hst; split at hst <;> (try split at hst) <;> cases hst
                    · cases hst
                  · cases hst
                · cases hst
              · split at hst <;> cases hst
              · split at hst <;> cases hst
              · cases hst
            · cases hst
          · cases hst
        | fail f =>
          exfalso
          simp only [Cfg.step, hfr] at hst
          split at hst
          · split at hst
            · split at hst
              · simp [Cfg.takeEdge] at hst; split at hst <;> (try split at hst) <;> cases hst
              · split at hst
                · split at hst
                  · split at hst
                    · simp [Cfg.takeEdge] at hst; split at hst <;> (try split at hst) <;> cases hst
                    · cases hst
                  · cases hst
                · cases hst
              · split at hst <;> cases hst
              · split at hst <;> cases hst
              · cases hst
            · cases hst
          · cases hst
      | cons i is =>
        exfalso
        obtain ⟨x, r'⟩ := i
        by_cases hcall : ∃ g as, r' = .fir (.call g as)
        · obtain ⟨g, as, rfl⟩ := hcall
          simp only [Cfg.step, hfr] at hf
          split at hf
          · cases hf
          · cases hf; exact hr rfl
        · rw [step_bind hfr (fun g as h => hcall ⟨g, as, h⟩)] at hf
          rcases evalRhs_ok_or_stuck (T := P.tables) (ρ := fr.env) (H := H) r' with ⟨p, hp⟩ | hp
          · rw [hp] at hf; cases hf
          · rw [hp] at hf; cases hf; exact hr rfl

/-- **The forward diagram.** -/
theorem diagram {P : Cfg.Program} {lp : Lir.Program} {ctx : Word} (ht : Target P lp) (s₀ : Cfg.State)
    (hsafe : ∀ s, Reach P s₀ s → SwitchOk P s) :
    Sem.Forward (Cfg.step .immortal P) (Lir.semStep lp) (Res P ctx)
      (fun s₁ s₂ => Rel P lp ctx s₁ s₂ ∧ Reach P s₀ s₁) :=
  diagram_sel ht s₀ fun s h => (hsafe s h).sel

end IxCC.Rt.Proof
