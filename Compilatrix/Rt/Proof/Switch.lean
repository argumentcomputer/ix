import Compilatrix.Rt.Proof.Chain

/-!
# Switches: the Lir side

`switch` lowers each alternative's edge (`switchAlt`, collected by
`MapRun`), then closes the block with one of three shapes:

* `natSwitch` (every key `Nat`'s): one zero test, `natPick`;
* `tagSwitch` without cells: a chain on the word;
* `tagSwitch` with cells: a chain on the tag loaded from the cell (only
  cells and no default), or the low bit first, then a chain on the loaded
  tag (even: a cell) or on the word (odd).

Each shape gets a lemma that runs Lir to the block taking the edge its
pick names (`ReachesEdge`). Which edge that is in Cfg's terms is
`Rt.Proof.SwitchLink`'s business.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Lower
open Compilatrix.Src (NatMap)

/-! ## Runs of `mapM` -/

/-- A run of `l.mapM g` from `st` to `st'` with results `r`, action by
action. -/
inductive MapRun {α β : Type} (g : α → M β) : List α → St → List β → St → Prop
  | nil {st : St} : MapRun g [] st [] st
  | cons {a : α} {l : List α} {st st₁ st' : St} {b : β} {r : List β} :
    (g a).run st = .ok (b, st₁) → MapRun g l st₁ r st' → MapRun g (a :: l) st (b :: r) st'

theorem mapM_run {α β : Type} {g : α → M β} :
    ∀ {l : List α} {st st' : St} {r : List β}, (l.mapM g).run st = .ok (r, st') → MapRun g l st r st'
  | [], st, st', r, h => by
    simp only [List.mapM_nil, StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .nil
  | a :: l, st, st', r, h => by
    simp only [List.mapM_cons, StateT.run, bind, StateT.bind, Except.bind] at h
    cases hg : g a st with
    | error e => simp [hg] at h
    | ok p =>
      obtain ⟨b, st₁⟩ := p
      simp only [hg] at h
      cases hl : List.mapM g l st₁ with
      | error e => simp [hl] at h
      | ok q =>
        obtain ⟨r', st₂⟩ := q
        simp only [hl, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .cons hg (mapM_run hl)

/-! ## The alternatives -/

theorem switchAlt_run {f : Fir.FunId} {T : Tables} {src : Nat} {ke : Key.CtorKey × Cfg.Edge}
    {kp : KeyKind × PEdge} {st st' : St} (h : (switchAlt f T src ke).run st = .ok (kp, st')) :
    keyKind T ke.1 = some kp.1 ∧ (edge f src ke.2).run st = .ok (kp.2, st') := by
  unfold switchAlt at h
  cases hk : keyKind T ke.1 with
  | none =>
    simp [hk, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.bind, StateT.run] at h
  | some kind =>
    simp only [hk, StateT.run, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at h
    cases he : edge f src ke.2 st with
    | error e => simp [he] at h
    | ok p =>
      simp only [he, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, by rw [StateT.run, he]⟩

/-- What a lowered alternative is in the final chunk. -/
def AltRel (C : List PBlock) (f : Fir.FunId) (T : Tables) (src : Nat) (ke : Key.CtorKey × Cfg.Edge)
    (kp : KeyKind × PEdge) : Prop :=
  keyKind T ke.1 = some kp.1 ∧ EdgeOk C f ke.2 kp.2 ∧ ke.2.back = decide (ke.2.target ≤ src)

/-- What the edges of a switch leave: the block still open with its code,
the cold blocks added, and each alternative's lowered edge. -/
theorem alts_run {f : Fir.FunId} {T : Tables} {src : Nat} :
    ∀ {alts : List (Key.CtorKey × Cfg.Edge)} {st st' : St} {es : List (KeyKind × PEdge)},
      MapRun (switchAlt f T src) alts st es st' → Labels st →
      Grows st st' ∧ Labels st' ∧ st'.cur = st.cur ∧ st'.acc = st.acc ∧ st'.params = st.params ∧
        st'.fresh = st.fresh ∧ (Open st → Open st') ∧
        ∀ {C : List PBlock} {stF : St}, Grows st' stF → Ext C stF → ListRel (AltRel C f T src) alts es
  | [], st, _, _, .nil, hl => ⟨Grows.refl _, hl, rfl, rfl, rfl, rfl, id, fun _ _ => .nil⟩
  | ke :: alts, st, st', _, .cons h hrest, hl => by
    obtain ⟨hk, he⟩ := switchAlt_run h
    obtain ⟨hb, hg₁, hl₁, hc₁, ha₁, hp₁, hf₁, ho₁, hok⟩ := edge_facts he hl
    obtain ⟨hg₂, hl₂, hc₂, ha₂, hp₂, hf₂, ho₂, hrel⟩ := alts_run hrest hl₁
    refine ⟨hg₁.trans hg₂, hl₂, hc₂.trans hc₁, ha₂.trans ha₁, hp₂.trans hp₁, hf₂.trans hf₁, ho₂ ∘ ho₁,
      fun hg hC => .cons ⟨hk, hok (hg₂.trans hg) hC, hb⟩ (hrel hg hC)⟩

/-- The default's lowered edge. -/
theorem dflt_run {f : Fir.FunId} {src : Nat} {d : Option Cfg.Edge} {st st' : St} {dd : Option PEdge}
    (h : (d.mapM (edge f src)).run st = .ok (dd, st')) (hl : Labels st) :
    Grows st st' ∧ Labels st' ∧ st'.cur = st.cur ∧ st'.acc = st.acc ∧ st'.params = st.params ∧
      st'.fresh = st.fresh ∧ (Open st → Open st') ∧
      ∀ {C : List PBlock} {stF : St}, Grows st' stF → Ext C stF →
        ((d = none ∧ dd = none) ∨
         ∃ e pe, d = some e ∧ dd = some pe ∧ EdgeOk C f e pe ∧ e.back = decide (e.target ≤ src)) := by
  cases d with
  | none =>
    simp only [Option.mapM_none, StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Grows.refl _, hl, rfl, rfl, rfl, rfl, id, fun _ _ => .inl ⟨rfl, rfl⟩⟩
  | some e =>
    simp only [Option.mapM_some, StateT.run, Functor.map, StateT.map, bind, StateT.bind, Except.bind, pure,
      StateT.pure, Except.pure] at h
    cases he : edge f src e st with
    | error err => simp [he] at h
    | ok p =>
      obtain ⟨pe, st₁⟩ := p
      simp only [he, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hb, hg, hl', hc, ha, hp, hf, ho, hok⟩ := edge_facts (st' := st₁) (by rw [StateT.run, he]) hl
      exact ⟨hg, hl', hc, ha, hp, hf, ho, fun hg' hC => .inr ⟨e, pe, rfl, rfl, hok hg' hC, hb⟩⟩

/-! ## Closing with a branch -/

/-- A block closed with `jump pe` reaches `pe`. -/
theorem closed_jump {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {mem : X86.Memory} {ctx : Word} {rest : List Lir.Frame} {st stF : St} {pe : PEdge}
    (hg : Grows (closeSt st (.jump pe)) stF) (hC : Ext C stF) (ρl : Lir.Env) :
    ∃ le, resolveEdge f off starts pe = .ok le ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest)
        le ρl := by
  obtain ⟨lb, hlb, -, hsize, hterm⟩ := closed_block hH (close_ext hg hC)
  simp only [resolveTerm, bind, Except.bind] at hterm
  cases hle : resolveEdge f off starts pe with
  | error err => simp [hle] at hterm
  | ok le =>
    simp only [hle, pure, Except.pure, Except.ok.injEq] at hterm
    refine ⟨le, rfl, ?_⟩
    rw [← hsize]
    exact reachesEdge_jump hF hlb hterm.symm

/-- A block closed with `br c a b t e` reaches the edge its condition
picks. -/
theorem closed_br {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {mem : X86.Memory} {ctx : Word} {rest : List Lir.Frame} {st stF : St} {c : Lir.Cond} {a b : Lir.Arg}
    {t e : PEdge} (hg : Grows (closeSt st (.br c a b t e)) stF) (hC : Ext C stF) {ρl : Lir.Env} {va vb : Word}
    (ha : a.eval ρl = some va) (hb : b.eval ρl = some vb) :
    ∃ lt le, resolveEdge f off starts t = .ok lt ∧ resolveEdge f off starts e = .ok le ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest)
        (if c.holds .w64 va vb then lt else le) ρl := by
  obtain ⟨lb, hlb, -, hsize, hterm⟩ := closed_block hH (close_ext hg hC)
  simp only [resolveTerm, bind, Except.bind] at hterm
  cases hlt : resolveEdge f off starts t with
  | error err => simp [hlt] at hterm
  | ok lt =>
    cases hle : resolveEdge f off starts e with
    | error err => simp [hlt, hle] at hterm
    | ok le =>
      simp only [hlt, hle, pure, Except.pure, Except.ok.injEq] at hterm
      refine ⟨lt, le, rfl, rfl, ?_⟩
      rw [← hsize]
      exact reachesEdge_br hF hlb hterm.symm ha hb

/-! ## `Nat` switches -/

/-- The first of three options that is some. -/
def pick3 (a b c : Option PEdge) : Option PEdge :=
  match a with
  | some e => some e
  | none => match b with
    | some e => some e
    | none => c

/-- The edge a `Nat` switch takes for the word `wx`; `none` for its
`trap`. -/
def natPick (wx : Word) (z s dd : Option PEdge) : Option PEdge :=
  if wx = 1 then pick3 z dd s else pick3 s dd z

theorem natSwitch_grows {x : Nat} {es : List (KeyKind × PEdge)} {dd : Option PEdge} {st st' : St}
    (h : (natSwitch x es dd).run st = .ok ((), st')) : ∃ t, st' = closeSt st t := by
  unfold natSwitch at h
  split at h <;> (rw [close_run] at h; simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h; exact ⟨_, h.symm⟩)

/-- **A `Nat` switch takes `natPick`'s edge.** -/
theorem natSwitch_reaches {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {mem : X86.Memory} {ctx : Word} {rest : List Lir.Frame} {x : Nat} {es : List (KeyKind × PEdge)}
    {dd : Option PEdge} {st st' stF : St} (h : (natSwitch x es dd).run st = .ok ((), st'))
    (hg : Grows st' stF) (hC : Ext C stF) {ρl : Lir.Env} {wx : Word} (hx : ρl[x]? = some wx) {pe : PEdge}
    (hpick : natPick wx (zeroEdge es) (succEdge es) dd = some pe) :
    ∃ le, resolveEdge f off starts pe = .ok le ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest)
        le ρl := by
  have hxv : (Lir.Arg.v x).eval ρl = some wx := hx
  have h1 : (Lir.Arg.imm 1).eval ρl = some 1 := rfl
  cases hz : zeroEdge es <;> cases hs : succEdge es <;> cases dd <;>
    simp only [natSwitch, hz, hs] at h <;> rw [close_run] at h <;>
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h <;> subst h <;>
    simp only [natPick, pick3, hz, hs] at hpick
  all_goals first
    | (obtain ⟨lt, le, hlt, hle, hr⟩ := closed_br hF hH hg hC (mem := mem) (ctx := ctx) (rest := rest) hxv h1
       by_cases hw : wx = 1
       · simp only [hw, ↓reduceIte, Option.some.injEq] at hpick
         subst hpick
         exact ⟨lt, hlt, by simpa [hw, Lir.holds_eq] using hr⟩
       · simp only [hw, ↓reduceIte, Option.some.injEq] at hpick
         subst hpick
         exact ⟨le, hle, by simpa [hw, Lir.holds_eq] using hr⟩)
    | (split at hpick <;> simp only [Option.some.injEq] at hpick <;> subst hpick <;>
        exact closed_jump hF hH hg hC ρl)
    | (split at hpick <;> simp at hpick)

end Compilatrix.Rt.Proof
