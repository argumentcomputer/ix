import IxCC.Lam.Erase.Proof.BuildBody
import IxCC.Lam.Erase.Proof.Main

/-! # What a successful erasure produced

`Lam.erase p ch = .ok (L, st)` gives a key relation `G` (the final key
table) under which every global of `L` has the key it is named by and a
`BodyR` body (`ProgR`), every root's global is its δ body's or its special
head's wrapper (`RootR`), `L`'s pinned constructors are the input's, and
`Nat.succ`'s field is kept: the setting of the erasure simulation. The
queue loop keeps every allocated key either erased or queued, so at its
end every key is erased. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels NatMap)

section

variable (I : Input)

/-- A key whose global has been erased. -/
def Done (s : St) (key : Key.GKey) (g : GlobalId) : Prop :=
  ∃ gl, s.globals.get? g = some gl ∧ gl.key = key ∧ ∀ G, Covers G s → BodyR I G key gl.body

/-- The queue loop's invariant. -/
structure LoopInv (s : St) : Prop where
  ids : IdsOk s
  keys : ∀ key g, keyOf s key = some g → Done I s key g ∨ (key, g) ∈ s.front ∨ (key, g) ∈ s.back
  queued : ∀ p, p ∈ s.front ∨ p ∈ s.back → keyOf s p.1 = some p.2

theorem loop_sound : ∀ (fuel : Nat) (s s' : St), (loop I fuel).run s = .ok ((), s') →
    LoopInv I s →
    LoopInv I s' ∧ s'.front = [] ∧ s'.back = [] ∧
      ∀ key g, keyOf s key = some g → keyOf s' key = some g
  | 0, s, s', e, _ => by
    unfold loop at e
    exact ((Sound.decline (Q := fun _ _ => False) s () s' e).2 (fun _ _ => True)
      fun _ _ _ => trivial).elim
  | fuel + 1, s, s', e, hinv => by
    unfold loop at e
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at e
    cases hf : s.front with
    | cons p rest =>
      obtain ⟨key, g⟩ := p
      rw [hf] at e
      dsimp only at e
      obtain ⟨_, s₁, e₁, e₂⟩ := Sound.bind_run e
      simp only [StateT.run_set] at e₁
      cases e₁
      obtain ⟨⟨body, res⟩, s₂, e₃, e₄⟩ := Sound.bind_run e₂
      obtain ⟨hg₂, hbody⟩ := sound_keyBody I key _ _ _ e₃
      obtain ⟨_, s₃, e₅, e₆⟩ := Sound.bind_run e₄
      simp only [StateT.run_modify] at e₅
      injection e₅ with e₅
      injection e₅ with _ e₅
      have hs₃ids : s₃.ids = s₂.ids := by rw [← e₅]
      have hs₃next : s₃.next = s₂.next := by rw [← e₅]
      have hs₃front : s₃.front = s₂.front := by rw [← e₅]
      have hs₃back : s₃.back = s₂.back := by rw [← e₅]
      have hs₃glob : s₃.globals = s₂.globals.insert g ⟨key, body, res⟩ := by rw [← e₅]
      -- The state before the rest of the loop.
      have hk₃ : ∀ key', keyOf s₃ key' = keyOf s₂ key' := fun _ => by
        unfold keyOf; rw [hs₃ids]
      have hq : keyOf s key = some g :=
        hinv.queued (key, g) (.inl (by rw [hf]; exact List.mem_cons_self))
      have hids₂ : IdsOk s₂ := hg₂.ids hinv.ids
      have hids₃ : IdsOk s₃ := by
        obtain ⟨h₁, h₂⟩ := hids₂
        exact ⟨fun k g' hk => by rw [hk₃] at hk; rw [hs₃next]; exact h₁ k g' hk,
          fun k k' g' hk hk' => by rw [hk₃] at hk hk'; exact h₂ k k' g' hk hk'⟩
      have hdone : Done I s₃ key g :=
        ⟨_, by rw [hs₃glob]; exact NatMap.get?_insert_self _ _ _, rfl,
          fun G hG => hbody G fun k g' hk => hG k g' (by rw [hk₃]; exact hk)⟩
      have hinv₃ : LoopInv I s₃ := by
        refine ⟨hids₃, fun key' g' hk => ?_, fun p hp => ?_⟩
        · rw [hk₃] at hk
          rcases hg₂.fresh key' g' hk with hk₁ | hb
          · rcases hinv.keys key' g' hk₁ with ⟨gl, hgl, hkey, hB⟩ | hfr | hbk
            · by_cases hgg : g' = g
              · subst hgg
                have := hinv.ids.2 key key' _ hq hk₁
                subst this
                exact .inl hdone
              · refine .inl ⟨gl, ?_, hkey, fun G hG => hB G fun k g'' hk' => ?_⟩
                · rw [hs₃glob]
                  rw [NatMap.get?_insert_ne _ _ hgg, hg₂.globals]
                  exact hgl
                · exact hG k g'' (by rw [hk₃]; exact hg₂.keys k g'' hk')
            · rw [hf] at hfr
              rcases List.mem_cons.1 hfr with e' | hr
              · cases e'
                exact .inl hdone
              · exact .inr (.inl (by rw [hs₃front, hg₂.front]; exact hr))
            · exact .inr (.inr (by rw [hs₃back]; exact hg₂.back _ hbk))
          · exact .inr (.inr (by rw [hs₃back]; exact hb))
        · rw [hk₃]
          rw [hs₃front, hs₃back] at hp
          rcases hp with hp | hp
          · have hp' : p ∈ s.front := by
              rw [hf]
              exact List.mem_cons_of_mem _ (by have h' := hp; rw [hg₂.front] at h'; exact h')
            exact hg₂.keys _ _ (hinv.queued p (.inl hp'))
          · rcases hg₂.backKeys p hp with hb | hk
            · exact hg₂.keys _ _ (hinv.queued p (.inr hb))
            · exact hk
      obtain ⟨h₁, h₂, h₃, h₄⟩ := loop_sound fuel _ s' e₆ hinv₃
      exact ⟨h₁, h₂, h₃, fun k g' hk => h₄ k g' (by rw [hk₃]; exact hg₂.keys k g' hk)⟩
    | nil =>
      rw [hf] at e
      dsimp only at e
      cases hb : s.back with
      | nil =>
        rw [hb] at e
        simp only [StateT.run_pure] at e
        cases e
        exact ⟨hinv, hf, hb, fun _ _ h => h⟩
      | cons p ps =>
        rw [hb] at e
        dsimp only at e
        obtain ⟨_, s₁, e₁, e₂⟩ := Sound.bind_run e
        simp only [StateT.run_set] at e₁
        cases e₁
        have hinv₁ : LoopInv I { s with front := (p :: ps).reverse, back := [] } := by
          refine ⟨hinv.ids, fun key g hk => ?_, fun q hq => ?_⟩
          · rcases hinv.keys key g hk with hd | hfr | hbk
            · exact .inl hd
            · rw [hf] at hfr; cases hfr
            · rw [hb] at hbk
              exact .inr (.inl (List.mem_reverse.2 hbk))
          · rcases hq with hq | hq
            · exact hinv.queued q (.inr (by rw [hb]; exact List.mem_reverse.1 hq))
            · cases hq
        obtain ⟨h₁, h₂, h₃, h₄⟩ := loop_sound fuel _ s' e₂ hinv₁
        exact ⟨h₁, h₂, h₃, fun k g hk => h₄ k g hk⟩

theorem sound_rootId (c : CId) :
    Sound (rootId I c) fun g G => RootR I G c g := by
  unfold rootId
  dsimp only
  split
  · next _ g₀ vs _ hr =>
    exact (sound_globalId _).imp fun g G h => .const (b := .const g₀ vs)
      (by simp [Input.deltaBody, hr]) h
  · next _ _ body hr =>
    exact (sound_globalId _).imp fun g G h => .const (b := body)
      (by simp [Input.deltaBody, hr]) h
  · next lv ty v hr hd =>
    exact (sound_globalId _).imp fun g G h => .const (b := v)
      (by simp [Input.deltaBody, hr, hd]) h
  · next lv ty v hr hd =>
    refine Sound.ite (fun hop => ?_) fun _ => Sound.decline
    exact (sound_globalId _).imp fun g G h => .const (b := v)
      (by simp [Input.deltaBody, hr, hd, hop]) h
  · next op _ hr =>
    exact (sound_globalId _).imp fun g G h => .wrapper (by simp [Input.headOf, hr]) h
  · exact Sound.decline
  · next r' _ hr =>
    exact (sound_globalId _).imp fun g G h => .wrapper (by simp [Input.headOf, hr]) h
  · next hr hd =>
    exact (sound_globalId _).imp fun g G h => .wrapper (by simp [Input.headOf, hr, hd]) h
  · next hr hd =>
    exact (sound_globalId _).imp fun g G h => .wrapper (by simp [Input.headOf, hr, hd]) h
  · next hr hd =>
    exact (sound_globalId _).imp fun g G h => .wrapper (by simp [Input.headOf, hr, hd]) h
  · next hr hd =>
    exact (sound_globalId _).imp fun g G h => .wrapper (by simp [Input.headOf, hr, hd]) h
  · exact Sound.decline

end

theorem keyOf_empty (key : Key.GKey) : keyOf {} key = none := rfl

theorem idsOk_empty : IdsOk {} := by
  unfold IdsOk
  constructor
  · intro key g h; cases h
  · intro key key' g h; cases h

/-- The state a successful erasure ends in: its key table relates every
global to its body and every root to its global, and its ids lie below
`next`, one key each. -/
theorem erase_spec_run {p : Src.Program} {ch : Src.Relevance.Checked} {L : Program}
    {st : Erase.Stats} (h : erase p ch = .ok (L, st)) :
    ∃ s : St, (Erase.run (Input.ofProgram p ch)).run {} = .ok (L.roots, s) ∧ IdsOk s ∧
      ProgR (Input.ofProgram p ch) (fun key g => keyOf s key = some g) L ∧
      L.known = (Input.ofProgram p ch).lamKnown ∧
      (∀ s', p.known.natSucc = some s' → (Input.ofProgram p ch).kept s' [] 0 = true) ∧
      Forall2 (RootR (Input.ofProgram p ch) (fun key g => keyOf s key = some g))
        (Input.ofProgram p ch).roots L.roots := by
  unfold erase at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  · next roots s hrun =>
    split at h
    · cases h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨s, hrun, ?_⟩
    have main : ∀ (s₀ : St) (hk : ∀ s₁, p.known.natSucc = some s₁ →
        (Input.ofProgram p ch).kept s₁ [] 0 = true),
        (do
          let roots ← List.mapM (rootId (Input.ofProgram p ch)) (Input.ofProgram p ch).roots
          loop (Input.ofProgram p ch) loopFuel
          registerRows (Input.ofProgram p ch)
            ((Input.ofProgram p ch).roots.flatMap (resultCtors (Input.ofProgram p ch)))
          pure roots : M (List GlobalId)).run s₀ = .ok (roots, s) → s₀ = {} →
        IdsOk s ∧ ProgR (Input.ofProgram p ch) (fun key g => keyOf s key = some g)
            { globals := s.globals, size := s.next, roots,
              ctors := s.ctorOrder.reverse.filterMap s.ctors.get?,
              known := (Input.ofProgram p ch).lamKnown } ∧
          (Input.ofProgram p ch).lamKnown = (Input.ofProgram p ch).lamKnown ∧
          (∀ s₁, p.known.natSucc = some s₁ → (Input.ofProgram p ch).kept s₁ [] 0 = true) ∧
          Forall2 (RootR (Input.ofProgram p ch) (fun key g => keyOf s key = some g))
            (Input.ofProgram p ch).roots roots := by
      intro s₀ hk e h0
      subst h0
      obtain ⟨rs, s_r, er, e'⟩ := Sound.bind_run e
      obtain ⟨_, s_l, el, e''⟩ := Sound.bind_run e'
      obtain ⟨_, s_w, ew, ep⟩ := Sound.bind_run e''
      simp only [StateT.run_pure] at ep
      injection ep with ep
      injection ep with hrs hs
      subst hrs hs
      -- registering the result rows changes only the constructor table
      obtain ⟨cs, co, rfl⟩ := registerRows_ctorsOnly _ ew
      obtain ⟨hgr, hroots⟩ := Sound.mapM (P := fun c g G => RootR (Input.ofProgram p ch) G c g)
        (fun c _ => sound_rootId _ c) _ _ s_r er
      have hinv : LoopInv (Input.ofProgram p ch) s_r := by
        refine ⟨hgr.ids idsOk_empty, fun key g hk => ?_,
          fun q hq => ?_⟩
        · rcases hgr.fresh key g hk with h | h
          · cases h
          · exact .inr (.inr h)
        · rcases hq with hq | hq
          · rw [hgr.front] at hq; cases hq
          · rcases hgr.backKeys q hq with h | h
            · cases h
            · exact h
      obtain ⟨hinv', hfr, hbk, hkeys⟩ := loop_sound _ loopFuel s_r _ el hinv
      refine ⟨hinv'.ids, fun key g hk => ?_, rfl, hk, ?_⟩
      · rcases hinv'.keys key g hk with ⟨gl, hgl, hkey, hB⟩ | hq | hq
        · exact ⟨gl, hgl, hkey, hB _ fun _ _ h => h⟩
        · rw [hfr] at hq; cases hq
        · rw [hbk] at hq; cases hq
      · exact hroots _ fun key g h => hkeys key g h
    unfold Erase.run at hrun
    dsimp only at hrun
    split at hrun
    · next s₁ hs =>
      by_cases hkept : (Input.ofProgram p ch).kept s₁ [] 0 = true
      · rw [if_pos hkept] at hrun
        exact main {} (fun s₂ h₂ => by
          have : s₂ = s₁ := by
            have h₂' : (Input.ofProgram p ch).known.natSucc = some s₂ := h₂
            rw [hs] at h₂'
            cases h₂'
            rfl
          subst this; exact hkept) hrun rfl
      · rw [if_neg hkept] at hrun
        exact ((Sound.decline_bind (Q := fun _ _ => False) _ _ _ hrun).2 (fun _ _ => True)
          fun _ _ _ => trivial).elim
    · next hs =>
      exact main {} (fun s₂ h₂ => by
        have h₂' : (Input.ofProgram p ch).known.natSucc = some s₂ := h₂
        rw [h₂'] at hs
        exact absurd rfl (hs s₂)) hrun rfl

/-- The setting a successful erasure provides: the final key table relates
every global to its body, every root to its global. -/
theorem erase_spec {p : Src.Program} {ch : Src.Relevance.Checked} {L : Program} {st : Erase.Stats}
    (h : erase p ch = .ok (L, st)) :
    ∃ G : Key.GKey → GlobalId → Prop, ProgR (Input.ofProgram p ch) G L ∧
      L.known = (Input.ofProgram p ch).lamKnown ∧
      (∀ s, p.known.natSucc = some s → (Input.ofProgram p ch).kept s [] 0 = true) ∧
      Forall2 (RootR (Input.ofProgram p ch) G) (Input.ofProgram p ch).roots L.roots := by
  obtain ⟨s, -, -, hprog, hknown, hsucc, hroots⟩ := erase_spec_run h
  exact ⟨_, hprog, hknown, hsucc, hroots⟩

end IxCC.Lam.Erase.Proof
