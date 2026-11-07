import IxCC.Lir.Proof.Steps
import IxCC.Sem.Forward

/-!
# Relabelled functions run in lock step

A function `G` simulates `F` under a label relation `L` (`FuncSim`) when
the entries correspond, related labels hold the same block up to its
terminator, and each edge of a terminator is taken in `G` either directly to
a related label with the same arguments and charge, or through an empty
block (at a later label) that jumps there with them (`EdgeSim`). Programs
whose functions are pairwise so related (`ProgSim`) run in lock step
(`ProgSim.lockStep`): the same statements, calls, returns and charges.
Pruning unreachable blocks and splitting critical edges are both such
relabellings.
-/

set_option autoImplicit false

namespace IxCC.Lir

/-! ## Inverting a step -/

theorem takeEdge_next_full {F : Func} {s : State} {fr : Frame} {rest : List Frame} {ρ : Env} {e : Edge} {s₁ : State}
    {b : Bool} (h : takeEdge F s fr rest ρ e = .next s₁ b) :
    ∃ vals TB ρ', evalArgs ρ e.args = some vals ∧ F.blocks[e.target]? = some TB ∧
      bindParams ρ TB.params vals = some ρ' ∧
      s₁ = { s with stack := { fr with label := e.target, pos := 0, env := ρ' } :: rest } ∧
      b = decide (e.target ≤ fr.label) := by
  unfold takeEdge at h
  split at h
  · rename_i vals TB hv htb
    split at h
    · rename_i ρ' hp
      simp only [Step.next.injEq] at h
      exact ⟨vals, TB, ρ', hv, htb, hp, h.1.symm, h.2.symm⟩
    · cases h
  · cases h

/-- What a step that goes on did. -/
theorem step_next_cases {p : Program} {mem : X86.Memory} {ctx : Word} {fr : Frame} {rest : List Frame}
    {s₁ : State} {b : Bool} (h : step p { mem, ctx, stack := fr :: rest } = .next s₁ b) :
    ∃ F B, p.funcs[fr.fn]? = some F ∧ F.blocks[fr.label]? = some B ∧
      ((∃ hp : fr.pos < B.body.size,
        (∃ rs g as vs callee, B.body[fr.pos] = .call rs g as ∧ evalArgs fr.env as = some vs ∧
          enter p g vs = some callee ∧
          s₁ = { mem, ctx, stack := callee :: { fr with pos := fr.pos + 1, dsts := rs } :: rest } ∧ b = true) ∨
        (∃ ρ' mem', B.body[fr.pos].isCall = false ∧ B.body[fr.pos].exec fr.env mem ctx = some (ρ', mem') ∧
          s₁ = { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := ρ' } :: rest } ∧ b = false)) ∨
      (¬ fr.pos < B.body.size ∧
        ((∃ e, B.term = .jump e ∧ takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env e = .next s₁ b) ∨
         (∃ c w a b' t f va vb, B.term = .br c w a b' t f ∧ a.eval fr.env = some va ∧ b'.eval fr.env = some vb ∧
           takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env (if c.holds w va vb then t else f) =
             .next s₁ b) ∨
         (∃ o x a b' ok ovf va vb, B.term = .brOvf o x a b' ok ovf ∧ a.eval fr.env = some va ∧
           b'.eval fr.env = some vb ∧
           takeEdge F { mem, ctx, stack := fr :: rest } fr rest (fr.env.insert x (o.eval va vb).1)
             (if (o.eval va vb).2 then ovf else ok) = .next s₁ b) ∨
         (∃ as vals caller rest₂ ρ, B.term = .ret as ∧ evalArgs fr.env as = some vals ∧ rest = caller :: rest₂ ∧
           bindParams caller.env caller.dsts vals = some ρ ∧
           s₁ = { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest₂ } ∧ b = false) ∨
         (∃ g as vs callee, B.term = .tail g as ∧ evalArgs fr.env as = some vs ∧ enter p g vs = some callee ∧
           s₁ = { mem, ctx, stack := callee :: rest } ∧ b = true)))) := by
  unfold step at h
  simp only at h
  split at h
  · cases h
  · rename_i F hF
    split at h
    · cases h
    · rename_i B hB
      refine ⟨F, B, hF, hB, ?_⟩
      split at h
      · rename_i hp
        refine .inl ⟨hp, ?_⟩
        split at h
        · rename_i rs g as hcall
          split at h
          · rename_i callee he
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at he
            obtain ⟨vs, hvs, he⟩ := he
            simp only [Step.next.injEq] at h
            exact .inl ⟨rs, g, as, vs, callee, hcall, hvs, he, h.1.symm, h.2.symm⟩
          · cases h
        · rename_i stmt hnot
          split at h
          · rename_i ρ' mem' hx
            simp only [Step.next.injEq] at h
            refine .inr ⟨ρ', mem', ?_, hx, h.1.symm, h.2.symm⟩
            cases hs : B.body[fr.pos] with
            | call rs g as => exact absurd hs (hnot rs g as)
            | _ => rfl
          · cases h
      · rename_i hp
        refine .inr ⟨hp, ?_⟩
        split at h
        · rename_i e he; exact .inl ⟨e, he, h⟩
        · rename_i c w a b' t f ht
          split at h
          · rename_i va vb ha hb
            exact .inr (.inl ⟨c, w, a, b', t, f, va, vb, ht, ha, hb, h⟩)
          · cases h
        · rename_i o x a b' ok ovf ht
          split at h
          · rename_i va vb ha hb
            exact .inr (.inr (.inl ⟨o, x, a, b', ok, ovf, va, vb, ht, ha, hb, h⟩))
          · cases h
        · rename_i as ht
          split at h
          · cases h
          · rename_i vals hv
            split at h
            · cases h
            · rename_i caller rest₂
              split at h
              · rename_i ρ hρ
                simp only [Step.next.injEq] at h
                exact .inr (.inr (.inr (.inl ⟨as, vals, caller, rest₂, ρ, ht, hv, rfl, hρ, h.1.symm, h.2.symm⟩)))
              · cases h
        · rename_i g as ht
          split at h
          · rename_i callee he
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at he
            obtain ⟨vs, hvs, he⟩ := he
            simp only [Step.next.injEq] at h
            exact .inr (.inr (.inr (.inr ⟨g, as, vs, callee, ht, hvs, he, h.1.symm, h.2.symm⟩)))
          · cases h
        · cases h
        · cases h


theorem takeEdge_not_final {F : Func} {s : State} {fr : Frame} {rest : List Frame} {ρ : Env} {e : Edge}
    {r : Sem.Result (List Word × X86.Memory)} (h : Sem.Final (takeEdge F s fr rest ρ e).toSem r) : r = .stuck := by
  unfold takeEdge at h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · cases h; rfl

/-- What a final step other than a stuck one did. -/
theorem step_final_cases {p : Program} {mem : X86.Memory} {ctx : Word} {fr : Frame} {rest : List Frame}
    {r : Sem.Result (List Word × X86.Memory)} (h : Sem.Final (semStep p { mem, ctx, stack := fr :: rest }) r)
    (hr : r ≠ .stuck) :
    ∃ F B, p.funcs[fr.fn]? = some F ∧ F.blocks[fr.label]? = some B ∧ ¬ fr.pos < B.body.size ∧
      ((∃ as vals, B.term = .ret as ∧ evalArgs fr.env as = some vals ∧ rest = [] ∧ r = .ok (vals, mem)) ∨
       (∃ f, B.term = .fail f ∧ r = .resource f) ∨ (B.term = .trap ∧ r = .trap)) := by
  unfold semStep step at h
  simp only at h
  split at h
  · cases h; exact absurd rfl hr
  · rename_i F hF
    split at h
    · cases h; exact absurd rfl hr
    · rename_i B hB
      refine ⟨F, B, hF, hB, ?_⟩
      split at h
      · exfalso
        split at h
        · split at h
          · cases h
          · cases h; exact hr rfl
        · split at h
          · cases h
          · cases h; exact hr rfl
      · rename_i hp
        refine ⟨hp, ?_⟩
        split at h
        · exact absurd (takeEdge_not_final h) hr
        · split at h
          · exact absurd (takeEdge_not_final h) hr
          · cases h; exact absurd rfl hr
        · split at h
          · exact absurd (takeEdge_not_final h) hr
          · cases h; exact absurd rfl hr
        · rename_i as ht
          split at h
          · cases h; exact absurd rfl hr
          · rename_i vals hv
            split at h
            · cases h
              exact .inl ⟨as, vals, ht, hv, rfl, rfl⟩
            · split at h
              · cases h
              · cases h; exact absurd rfl hr
        · split at h
          · cases h
          · cases h; exact absurd rfl hr
        · rename_i f ht
          cases h
          exact .inr (.inl ⟨f, ht, rfl⟩)
        · rename_i ht
          cases h
          exact .inr (.inr ⟨ht, rfl⟩)

/-! ## Relabelled functions -/

/-- How an edge `e` of `F`, taken from label `l`, is taken in `G` from
`l'`: directly to a related label with the same arguments and charge, or
through an empty block at a later label that jumps there with them. -/
def EdgeSim (F G : Func) (L : Label → Label → Prop) (l l' : Label) (e e' : Edge) : Prop :=
  ∀ {TB : Block}, F.blocks[e.target]? = some TB →
    (e'.args = e.args ∧ L e.target e'.target ∧ decide (e'.target ≤ l') = decide (e.target ≤ l)) ∨
    (e'.args = [] ∧ l' < e'.target ∧ ∃ e'' c, G.blocks[e'.target]? = some { term := .jump e'', cold := c } ∧
      e''.args = e.args ∧ L e.target e''.target ∧ decide (e''.target ≤ e'.target) = decide (e.target ≤ l))

/-- Terminators that differ only in their edges, edge by edge as
`EdgeSim`. -/
def TermSim (F G : Func) (L : Label → Label → Prop) (l l' : Label) : Term → Term → Prop
  | .jump e, t' => ∃ e', t' = .jump e' ∧ EdgeSim F G L l l' e e'
  | .br c w a b t f, t' => ∃ t₁ f₁, t' = .br c w a b t₁ f₁ ∧ EdgeSim F G L l l' t t₁ ∧ EdgeSim F G L l l' f f₁
  | .brOvf o x a b ok ovf, t' => ∃ ok₁ ovf₁, t' = .brOvf o x a b ok₁ ovf₁ ∧ EdgeSim F G L l l' ok ok₁ ∧
      EdgeSim F G L l l' ovf ovf₁
  | t, t' => t' = t

/-- **`G` simulates `F` under the label relation `L`.** -/
structure FuncSim (F G : Func) (L : Label → Label → Prop) : Prop where
  params : G.params = F.params
  entry : L 0 0
  block : ∀ {l l' : Label} {B : Block}, L l l' → F.blocks[l]? = some B →
    ∃ t' c, G.blocks[l']? = some { B with term := t', cold := c } ∧ TermSim F G L l l' B.term t'

/-- Programs whose functions are pairwise relabelled. -/
structure ProgSim (p q : Program) (L : Nat → Label → Label → Prop) : Prop where
  main : q.main = p.main
  funcs : ∀ {g : Nat} {F : Func}, p.funcs[g]? = some F → ∃ G, q.funcs[g]? = some G ∧ FuncSim F G (L g)

/-- Related frames: the same position up to labels. -/
def FrameRel (L : Nat → Label → Label → Prop) (fr fr' : Frame) : Prop :=
  fr'.fn = fr.fn ∧ L fr.fn fr.label fr'.label ∧ fr'.pos = fr.pos ∧ fr'.env = fr.env ∧ fr'.dsts = fr.dsts

inductive StackRel (L : Nat → Label → Label → Prop) : List Frame → List Frame → Prop
  | nil : StackRel L [] []
  | cons {fr fr' : Frame} {rest rest' : List Frame} : FrameRel L fr fr' → StackRel L rest rest' →
    StackRel L (fr :: rest) (fr' :: rest')

/-- Related states. -/
def StateRel (L : Nat → Label → Label → Prop) (s t : State) : Prop :=
  t.mem = s.mem ∧ t.ctx = s.ctx ∧ StackRel L s.stack t.stack

theorem ProgSim.enter {p q : Program} {L : Nat → Label → Label → Prop} (h : ProgSim p q L) {g : Nat}
    {vs : List Word} {callee : Frame} (he : Lir.enter p g vs = some callee) :
    ∃ callee', Lir.enter q g vs = some callee' ∧ FrameRel L callee callee' := by
  simp only [Lir.enter, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
  obtain ⟨F, hF, ρ, hρ, hcal⟩ := he
  simp only [Option.some.injEq] at hcal
  subst hcal
  obtain ⟨G, hG, hsim⟩ := h.funcs hF
  refine ⟨{ fn := g, label := 0, pos := 0, env := ρ }, ?_, rfl, hsim.entry, rfl, rfl, rfl⟩
  simp [Lir.enter, hG, hsim.params, hρ]

/-- A terminator step, at any position past the body. -/
theorem step_term_ge {p : Program} {mem : X86.Memory} {ctx : Word} {fr : Frame} {rest : List Frame} {F : Func}
    {B : Block} (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hpos : ¬ fr.pos < B.body.size) :
    step p { mem, ctx, stack := fr :: rest } =
      match B.term with
      | .jump e => takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env e
      | .br c w a b' t e =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
            takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env (if c.holds w va vb then t else e)
          | _, _ => .stuck
      | .brOvf o x a b' ok ovf =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
              let (r, carry) := o.eval va vb
              takeEdge F { mem, ctx, stack := fr :: rest } fr rest (fr.env.insert x r) (if carry then ovf else ok)
          | _, _ => .stuck
      | .ret as =>
          match evalArgs fr.env as with
          | none => .stuck
          | some vals =>
              match rest with
              | [] => .done vals mem
              | caller :: rest' =>
                  match bindParams caller.env caller.dsts vals with
                  | some ρ => .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest' } false
                  | none => .stuck
      | .tail g as =>
          match evalArgs fr.env as >>= enter p g with
          | some callee => .next { mem, ctx, stack := callee :: rest } true
          | none => .stuck
      | .fail r => .fail r
      | .trap => .trap := by
  unfold step
  simp only [hf, hb, hpos, ↓reduceDIte]
  rfl

/-- **Related edges are taken in lock step.** -/
theorem edgeSim_step {q : Program} {L : Nat → Label → Label → Prop} {F G : Func}
    {fr fr' : Frame} (hsim : FuncSim F G (L fr.fn)) (hG : q.funcs[fr'.fn]? = some G)
    (hfr : FrameRel L fr fr') {mem : X86.Memory} {ctx : Word} {rest rest' : List Frame}
    (hrest : StackRel L rest rest') {ρ : Env} {e e' : Edge} (hes : EdgeSim F G (L fr.fn) fr.label fr'.label e e')
    {s₁ : State} {b : Bool} (hs : takeEdge F { mem, ctx, stack := fr :: rest } fr rest ρ e = .next s₁ b)
    (hq : step q { mem, ctx, stack := fr' :: rest' } = takeEdge G { mem, ctx, stack := fr' :: rest' } fr' rest' ρ e') :
    ∃ t₁, Sem.Star (semStep q) { mem, ctx, stack := fr' :: rest' } b.toNat t₁ ∧ StateRel L s₁ t₁ := by
  obtain ⟨vals, TB, ρ', hv, htb, hp, rfl, rfl⟩ := takeEdge_next_full hs
  obtain ⟨hfn, hL, hpos, henv, hdsts⟩ := hfr
  rcases hes htb with ⟨hargs, hLt, hc⟩ | ⟨hargs, hlt, e'', c, hhop, hargs', hLt, hc⟩
  · obtain ⟨t', c', htb', -⟩ := hsim.block hLt htb
    have h1 := takeEdge_ok (F := G) (s := { mem, ctx, stack := fr' :: rest' }) (fr := fr') (rest := rest')
      (ρ' := ρ') (by rw [hargs]; exact hv) htb' hp
    rw [h1, hc] at hq
    refine ⟨_, Sem.Star.single (semStep_next.2 hq), rfl, rfl, .cons ⟨hfn, hLt, rfl, rfl, hdsts⟩ hrest⟩
  · -- the hop through the split block
    have h1 := takeEdge_ok (F := G) (s := { mem, ctx, stack := fr' :: rest' }) (fr := fr') (rest := rest')
      (ρ' := ρ) (vals := []) (by rw [hargs]; rfl) hhop rfl
    rw [h1, decide_eq_false (Nat.not_le.2 hlt)] at hq
    obtain ⟨t', c', htb', -⟩ := hsim.block hLt htb
    have h2 := step_jump (p := q) (mem := mem) (ctx := ctx) (rest := rest')
      (fr := { fr' with label := e'.target, pos := 0, env := ρ }) hG hhop rfl rfl
    have h3 := takeEdge_ok (F := G) (s := { mem, ctx, stack := { fr' with label := e'.target, pos := 0, env := ρ } :: rest' })
      (fr := { fr' with label := e'.target, pos := 0, env := ρ }) (rest := rest') (ρ' := ρ')
      (by rw [hargs']; exact hv) htb' hp
    rw [h3] at h2
    simp only at h2
    rw [hc] at h2
    refine ⟨_, Sem.Star.free (semStep_next.2 hq) (Sem.Star.single (semStep_next.2 h2)), rfl, rfl,
      .cons ⟨hfn, hLt, rfl, rfl, hdsts⟩ hrest⟩


/-- A related frame, spelled out. -/
theorem frameRel_eq {L : Nat → Label → Label → Prop} {fr fr' : Frame} (h : FrameRel L fr fr') :
    ∃ l', L fr.fn fr.label l' ∧ fr' = { fr with label := l' } := by
  obtain ⟨hfn, hL, hpos, henv, hdsts⟩ := h
  refine ⟨fr'.label, hL, ?_⟩
  obtain ⟨fn, label, pos, env, dsts⟩ := fr'
  simp only at hfn hpos henv hdsts
  subst hfn hpos henv hdsts
  rfl

/-- **Relabelled programs run in lock step.** -/
theorem ProgSim.lockStep {p q : Program} {L : Nat → Label → Label → Prop} (h : ProgSim p q L) :
    Sem.LockStep (semStep p) (semStep q) (StateRel L) where
  next := by
    intro s s₁ t b ⟨hmem, hctx, hstk⟩ hs
    obtain ⟨mem, ctx, stack⟩ := s
    obtain ⟨mem', ctx', stack'⟩ := t
    simp only at hmem hctx hstk
    subst mem' ctx'
    cases hstk with
    | nil => simp [semStep, step, Step.toSem] at hs
    | @cons fr fr' rest rest' hfr hrest =>
      obtain ⟨F, B, hF, hB, hcase⟩ := step_next_cases (semStep_next.1 hs)
      obtain ⟨G, hG, hsim⟩ := h.funcs hF
      obtain ⟨l', hL, rfl⟩ := frameRel_eq hfr
      obtain ⟨t', c, hB', hts⟩ := hsim.block hL hB
      have hG' : q.funcs[({ fr with label := l' } : Frame).fn]? = some G := hG
      have hB'' : G.blocks[({ fr with label := l' } : Frame).label]? = some { B with term := t', cold := c } := hB'
      rcases hcase with ⟨hp, ⟨rs, g, as, vs, callee, hcall, hvs, he, rfl, rfl⟩ | ⟨ρ', mem'', hnc, hx, rfl, rfl⟩⟩ |
        ⟨hp, hterm⟩
      · obtain ⟨callee', he', hcr⟩ := h.enter he
        have := step_call (p := q) (mem := mem) (ctx := ctx) (rest := rest') hG' hB'' hp hcall hvs he'
        exact ⟨_, Sem.Star.single (semStep_next.2 this), rfl, rfl,
          .cons hcr (.cons ⟨rfl, hL, rfl, rfl, rfl⟩ hrest)⟩
      · have := step_stmt (p := q) (mem := mem) (ctx := ctx) (rest := rest') hG' hB'' hp rfl hnc hx
        exact ⟨_, Sem.Star.single (semStep_next.2 this), rfl, rfl, .cons ⟨rfl, hL, rfl, rfl, rfl⟩ hrest⟩
      · have hq := step_term_ge (p := q) (mem := mem) (ctx := ctx) (rest := rest') hG' hB'' hp
        rcases hterm with ⟨e, ht, htk⟩ | ⟨c₀, w, a, b', t₀, f₀, va, vb, ht, ha, hb, htk⟩ |
          ⟨o, x, a, b', ok, ovf, va, vb, ht, ha, hb, htk⟩ | ⟨as, vals, caller, rest₂, ρ, ht, hv, rfl, hρ, rfl, rfl⟩ |
          ⟨g, as, vs, callee, ht, hvs, he, rfl, rfl⟩
        · rw [ht] at hts
          obtain ⟨e', rfl, hes⟩ := hts
          exact edgeSim_step hsim hG' ⟨rfl, hL, rfl, rfl, rfl⟩ hrest hes htk hq
        · rw [ht] at hts
          obtain ⟨t₁, f₁, rfl, hest, hesf⟩ := hts
          simp only [ha, hb] at hq
          have hes : EdgeSim F G (L fr.fn) fr.label l' (if c₀.holds w va vb then t₀ else f₀)
              (if c₀.holds w va vb then t₁ else f₁) := by
            split
            · exact hest
            · exact hesf
          exact edgeSim_step hsim hG' ⟨rfl, hL, rfl, rfl, rfl⟩ hrest hes htk hq
        · rw [ht] at hts
          obtain ⟨ok₁, ovf₁, rfl, hesok, hesovf⟩ := hts
          simp only [ha, hb] at hq
          have hes : EdgeSim F G (L fr.fn) fr.label l' (if (o.eval va vb).2 then ovf else ok)
              (if (o.eval va vb).2 then ovf₁ else ok₁) := by
            split
            · exact hesovf
            · exact hesok
          exact edgeSim_step hsim hG' ⟨rfl, hL, rfl, rfl, rfl⟩ hrest hes htk hq
        · rw [ht] at hts
          simp only [TermSim] at hts
          subst hts
          cases hrest with
          | @cons caller caller' rest₂ rest₂' hcf hrest₂ =>
            obtain ⟨hfn', hL', hpos', henv', hdsts'⟩ := hcf
            simp only [hv] at hq
            rw [henv', hdsts', hρ] at hq
            exact ⟨_, Sem.Star.single (semStep_next.2 hq), rfl, rfl, .cons ⟨hfn', hL', hpos', rfl, rfl⟩ hrest₂⟩
        · rw [ht] at hts
          simp only [TermSim] at hts
          subst hts
          obtain ⟨callee', he', hcr⟩ := h.enter he
          simp only [hvs, Option.bind_eq_bind, Option.bind_some, he'] at hq
          exact ⟨_, Sem.Star.single (semStep_next.2 hq), rfl, rfl, .cons hcr hrest⟩
  final := by
    intro s t r ⟨hmem, hctx, hstk⟩ hf hr
    obtain ⟨mem, ctx, stack⟩ := s
    obtain ⟨mem', ctx', stack'⟩ := t
    simp only at hmem hctx hstk
    subst mem' ctx'
    cases hstk with
    | nil =>
      simp only [semStep, step, Step.toSem] at hf
      cases hf
      exact absurd rfl hr
    | @cons fr fr' rest rest' hfr hrest =>
      obtain ⟨F, B, hF, hB, hp, hcase⟩ := step_final_cases hf hr
      obtain ⟨G, hG, hsim⟩ := h.funcs hF
      obtain ⟨l', hL, rfl⟩ := frameRel_eq hfr
      obtain ⟨t', c, hB', hts⟩ := hsim.block hL hB
      have hq := step_term_ge (p := q) (mem := mem) (ctx := ctx) (rest := rest') (fr := { fr with label := l' })
        hG hB' hp
      refine ⟨_, .refl _, ?_⟩
      rcases hcase with ⟨as, vals, ht, hv, rfl, rfl⟩ | ⟨f, ht, rfl⟩ | ⟨ht, rfl⟩
      · rw [ht] at hts
        simp only [TermSim] at hts
        subst hts
        cases hrest
        simp only [hv] at hq
        rw [semStep, hq]
        exact .done
      · rw [ht] at hts
        simp only [TermSim] at hts
        subst hts
        rw [semStep, hq]
        exact .fail
      · rw [ht] at hts
        simp only [TermSim] at hts
        subst hts
        rw [semStep, hq]
        exact .trap

end IxCC.Lir
