import IxCC.Anf.Proof.Pass.Shrink
import IxCC.Anf.Proof.Pass.Inline
import IxCC.Anf.Proof.Pass.Prune
import IxCC.Anf.Proof.Walk.Jump
import IxCC.Anf.WellFormed

/-! # First-order preservation for P2 shrink, P3 inline, and pruning

After P8 (`Anf.defun`), every post-P8 optimization step must preserve
`Anf.FirstOrder` (no `fn`, no `app`, no function-valued `glob`) so that
`Fir.lower` never declines for closures (`Anf.Pipeline.Proof.closures_firstOrder`).
This module proves `FirstOrder` preservation for `Walk.walk`, `Shrink.run`,
`Inline.round`, and `Prune.run`, plus `Prune.Proof.run_tables` (`known` and
`ctors` unchanged, without `Classical.choice`). -/

set_option autoImplicit false

namespace IxCC.Anf.PassProof

open Walk (Ent JEnt Here Cfg Kont Fires)

/-! ## `Walk` preserves `Exp.firstOrder` -/

/-- No `Ent.fn` in `σ` (a first-order program never introduces local functions). -/
def NoFnEnv (σ : List Ent) : Prop :=
  ∀ e ∈ σ, ∃ o, e = .opd o

/-- Every join entry in `jσ` has a first-order body and `NoFnEnv`. -/
inductive FoJEnv (isFn : GlobalId → Bool) : List JEnt → Prop
  | nil : FoJEnv isFn []
  | mk {lvl : Option Nat} {σ : List Ent} {jσ : List JEnt} {n : Nat} {r : Bool} {b : Exp} {id : Nat}
      {rest : List JEnt} :
      NoFnEnv σ → FoJEnv isFn jσ → b.firstOrder isFn = true → FoJEnv isFn rest →
      FoJEnv isFn (.mk lvl σ jσ n r b id :: rest)
  | pend {lvl : Nat} {σ : List Ent} {jσ : List JEnt} {b : Exp} {rest : List JEnt} :
      NoFnEnv σ → FoJEnv isFn jσ → b.firstOrder isFn = true → FoJEnv isFn rest →
      FoJEnv isFn (.pend lvl σ jσ b :: rest)

theorem NoFnEnv.nil : NoFnEnv [] := fun _ h => nomatch h

theorem NoFnEnv.cons {o : Opd} {σ : List Ent} (h : NoFnEnv σ) : NoFnEnv (.opd o :: σ) := by
  intro e he
  rcases List.mem_cons.1 he with rfl | hm
  · exact ⟨o, rfl⟩
  · exact h e hm

theorem NoFnEnv.append {σ₁ σ₂ : List Ent} (h₁ : NoFnEnv σ₁) (h₂ : NoFnEnv σ₂) : NoFnEnv (σ₁ ++ σ₂) := by
  intro e he
  rcases List.mem_append.1 he with hm | hm
  · exact h₁ e hm
  · exact h₂ e hm

theorem NoFnEnv.entsOf (os : List Opd) : NoFnEnv (Walk.entsOf os) := by
  intro e he
  obtain ⟨o, -, rfl⟩ := List.mem_map.1 he
  exact ⟨o, rfl⟩

theorem FoJEnv.get {isFn : GlobalId → Bool} : ∀ {jσ : List JEnt}, FoJEnv isFn jσ → ∀ {j : Nat} {je : JEnt},
    jσ[j]? = some je →
    match je with
    | .mk _ σ jσ' _ _ b _ => NoFnEnv σ ∧ FoJEnv isFn jσ' ∧ b.firstOrder isFn = true
    | .pend _ σ jσ' b => NoFnEnv σ ∧ FoJEnv isFn jσ' ∧ b.firstOrder isFn = true
  | _, .nil, _, _, h => by simp at h
  | _, .mk hσ hj hb _, 0, _, h => by simp at h; subst h; exact ⟨hσ, hj, hb⟩
  | _, .pend hσ hj hb _, 0, _, h => by simp at h; subst h; exact ⟨hσ, hj, hb⟩
  | _, .mk _ _ _ hr, j + 1, _, h => by simpa using hr.get h
  | _, .pend _ _ _ hr, j + 1, _, h => by simpa using hr.get h

/-- A walk continuation produces first-order code on every operand. -/
def FoKont (isFn : GlobalId → Bool) : Kont → Prop
  | .ret => True
  | .jump _ => True
  | .cont f => ∀ here o out s s', (f here o).run s = .ok (out, s') → out.firstOrder isFn = true

theorem pass_fo {isFn : GlobalId → Bool} {here : Here} {o : Opd} {k : Kont} {out : Exp} {s s' : Fires}
    (hk : FoKont isFn k) (h : (Walk.pass here o k).run s = .ok (out, s')) :
    out.firstOrder isFn = true := by
  cases k with
  | ret => obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h; rfl
  | jump l => obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h; rfl
  | cont f => exact hk here o out s s' h

theorem branch_fo {isFn : GlobalId → Bool} {here : Here} {k : Kont} {body : Here → Kont → Walk.M Exp}
    {out : Exp} {s s' : Fires} (hk : FoKont isFn k)
    (hb : ∀ here' k' out' s0 s1, FoKont isFn k' → (body here' k').run s0 = .ok (out', s1) →
      out'.firstOrder isFn = true)
    (h : (Walk.branch here k body).run s = .ok (out, s')) : out.firstOrder isFn = true := by
  cases k with
  | ret => exact hb here .ret out s s' trivial h
  | jump l => exact hb here (.jump l) out s s' trivial h
  | cont f =>
    simp only [Walk.branch] at h
    obtain ⟨jb, s1, h1, h2⟩ := Walk.run_bind_ok h
    obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h2
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
    simp only [Exp.firstOrder, Bool.and_eq_true]
    exact ⟨hk _ _ jb s s1 h1, hb _ (.jump _) e s1 s2 trivial h3⟩

theorem ticks_fo {isFn : GlobalId → Bool} : ∀ {m : Nat} {e : Exp},
    e.firstOrder isFn = true → (Walk.ticks m e).firstOrder isFn = true
  | 0, _, h => h
  | m + 1, e, h => ticks_fo (m := m) h

theorem stripTicks_fo {isFn : GlobalId → Bool} : ∀ {e : Exp},
    e.firstOrder isFn = true → (Walk.stripTicks e).2.firstOrder isFn = true
  | .tick e, h => stripTicks_fo (e := e) h
  | .bind .., h | .join .., h | .jump .., h | .case .., h | .ret _, h | .trap, h => h

theorem alts_fo_mem {isFn : GlobalId → Bool} : ∀ {alts : List Alt},
    Exp.altsFirstOrder isFn alts = true → ∀ a ∈ alts, a.body.firstOrder isFn = true
  | [], _, _, h => nomatch h
  | .mk _ _ b :: rest, h, a, hm => by
    simp only [Exp.altsFirstOrder, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hm with rfl | hmem
    · exact h.1
    · exact alts_fo_mem h.2 a hmem

theorem select_fo {isFn : GlobalId → Bool} {alts : List Alt} {dflt : Option Exp} {c : Key.CtorKey}
    {n : Nat} {isAlt : Bool} {e : Exp}
    (ha : Exp.altsFirstOrder isFn alts = true) (hd : Exp.optFirstOrder isFn dflt = true)
    (hs : Walk.select alts dflt c n = some (isAlt, e)) : e.firstOrder isFn = true := by
  unfold Walk.select at hs
  split at hs
  · next a hfind =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact alts_fo_mem ha a (List.mem_of_find?_eq_some hfind)
  · cases dflt with
    | none => cases hs
    | some d =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact hd

/-- Configuration whose program is first order under `isFn`. -/
def FoCfg (isFn : GlobalId → Bool) (C : Cfg) : Prop :=
  (∀ g gd, C.prog.global? g = some gd → gd.body.firstOrder isFn = true) ∧
  (∀ g, (C.prog.arity? g).any (· > 0) = isFn g)

theorem FoCfg.strip {isFn : GlobalId → Bool} {C : Cfg} (h : FoCfg isFn C) :
    FoCfg isFn { C with inline := [], redirect := none } := h

theorem sameArms_fo {isFn : GlobalId → Bool} {alts : List Alt} {dflt : Option Exp} {e0 : Exp}
    (ha : Exp.altsFirstOrder isFn alts = true)
    (hs : Walk.sameArms alts dflt = some e0) : e0.firstOrder isFn = true := by
  unfold Walk.sameArms at hs
  split at hs
  · cases hs
  · rename_i c0 b0 rest0
    have hite : ∀ (p : Prop) [Decidable p], (if p then some b0 else none) = some e0 → b0 = e0 := by
      intro p _ hp; split at hp
      · exact Option.some.inj hp
      · cases hp
    have heq := hite _ hs
    subst heq
    simp only [Exp.altsFirstOrder, Bool.and_eq_true] at ha
    exact ha.1
  · cases hs

theorem walk_fo_all {isFn : GlobalId → Bool} : ∀ (fuel : Nat),
    (∀ C env here e k out s s', FoCfg isFn C → NoFnEnv env.σ → FoJEnv isFn env.jσ →
      e.firstOrder isFn = true → FoKont isFn k →
      (Walk.walk C fuel env here e k).run s = .ok (out, s') → out.firstOrder isFn = true) ∧
    (∀ C env body k k' s s', FoCfg isFn C → NoFnEnv env.σ → FoJEnv isFn env.jσ →
      body.firstOrder isFn = true → FoKont isFn k →
      (Walk.after C fuel env body k).run s = .ok (k', s') → FoKont isFn k') ∧
    (∀ C env here xo alts k alts' s s', FoCfg isFn C → NoFnEnv env.σ → FoJEnv isFn env.jσ →
      Exp.altsFirstOrder isFn alts = true → FoKont isFn k →
      (Walk.walkAlts C fuel env here xo alts k).run s = .ok (alts', s') →
      Exp.altsFirstOrder isFn alts' = true)
  | 0 => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd h Walk.run_throw_ok,
          fun _ _ _ _ _ _ _ _ _ _ _ _ h => absurd h Walk.run_throw_ok,
          fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd h Walk.run_throw_ok⟩
  | fuel + 1 => by
    obtain ⟨ihW, ihA, ihAlts⟩ := walk_fo_all (isFn := isFn) fuel
    have hAfter : ∀ C env body k k' s s', FoCfg isFn C → NoFnEnv env.σ → FoJEnv isFn env.jσ →
        body.firstOrder isFn = true → FoKont isFn k →
        (Walk.after C (fuel + 1) env body k).run s = .ok (k', s') → FoKont isFn k' := by
      intro C env body k k' s s' hC hσ hJ hbody hk h
      rw [Walk.after.eq_def] at h
      dsimp only at h
      split at h
      · obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h; exact hk
      · split at h
        · obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h; trivial
        · obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
          intro here o out s0 s1 hw
          exact ihW C { env with σ := .opd o :: env.σ } here _ k out s0 s1 hC hσ.cons hJ hbody hk hw
      · obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
        intro here o out s0 s1 hw
        exact ihW C { env with σ := .opd o :: env.σ } here body k out s0 s1 hC hσ.cons hJ hbody hk hw
    have hAlts : ∀ C env here xo alts k alts' s s', FoCfg isFn C → NoFnEnv env.σ → FoJEnv isFn env.jσ →
        Exp.altsFirstOrder isFn alts = true → FoKont isFn k →
        (Walk.walkAlts C (fuel + 1) env here xo alts k).run s = .ok (alts', s') →
        Exp.altsFirstOrder isFn alts' = true := by
      intro C env here xo alts k alts' s s' hC hσ hJ halts hk h
      cases alts with
      | nil => obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h; rfl
      | cons a rest =>
        cases a with
        | mk key n b =>
          simp only [Exp.altsFirstOrder, Bool.and_eq_true] at halts
          rw [Walk.walkAlts.eq_def] at h
          dsimp only at h
          obtain ⟨b', s1, h1, h2⟩ := Walk.run_bind_ok h
          obtain ⟨rest', s2, h3, h4⟩ := Walk.run_bind_ok h2
          obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
          simp only [Exp.altsFirstOrder, Bool.and_eq_true]
          exact ⟨ihW C { env with σ := Walk.entsOf (paramOpds here.d n) ++ env.σ } _ b k b' s s1
                   hC ((NoFnEnv.entsOf _).append hσ) hJ halts.1 hk h1,
                 ihAlts C env here xo rest k rest' s1 s2 hC hσ hJ halts.2 hk h3⟩
    refine ⟨?_, hAfter, hAlts⟩
    intro C env here e k out s s' hC hσ hJ he hk h
    rw [Walk.walk] at h
    obtain ⟨_, s1, _, h⟩ := Walk.run_bind_ok h
    obtain ⟨_, s2, _, h⟩ := Walk.run_bind_ok h
    dsimp only at h
    cases e with
    | ret a =>
      obtain ⟨o, s3, _, h2⟩ := Walk.run_bind_ok h
      exact pass_fo hk h2
    | tick body =>
      obtain ⟨e', s3, h1, h2⟩ := Walk.run_bind_ok h
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h2
      exact ihW C env _ body k e' s2 s3 hC hσ hJ he hk h1
    | trap =>
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h; rfl
    | bind c b body =>
      simp only [Exp.firstOrder, Bool.and_eq_true] at he
      cases fuel with
      | zero => exact absurd h Walk.run_throw_ok
      | succ fuel' =>
        obtain ⟨ihW', ihA', _⟩ := walk_fo_all (isFn := isFn) fuel'
        have hEmit : ∀ {b' : Bind} {facts' : Src.NatMap Walk.Fact} {s0 s0' : Fires},
            Bind.firstOrder isFn b' = true →
            (do let e ← Walk.walk C fuel' { env with σ := .opd (.lvl here.d) :: env.σ }
                  { here with d := here.d + 1, lvl := here.lvl + 1, facts := facts' } body k
                pure (Exp.bind c b' e)).run s0 = .ok (out, s0') →
            out.firstOrder isFn = true := by
          intro b' facts' s0 s0' hb' hm
          obtain ⟨e', s3, h1, h2⟩ := Walk.run_bind_ok hm
          obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h2
          simp only [Exp.firstOrder, Bool.and_eq_true]
          exact ⟨hb', ihW' C { env with σ := .opd (.lvl here.d) :: env.σ } _ body k e' s0 s3 hC hσ.cons hJ he.2 hk h1⟩
        have hSkip : ∀ {o : Opd} {s0 s0' : Fires},
            (Walk.walk C fuel' { env with σ := .opd o :: env.σ }
              { here with lvl := here.lvl + 1 } body k).run s0 = .ok (out, s0') →
            out.firstOrder isFn = true :=
          fun hm => ihW' C { env with σ := .opd _ :: env.σ } _ body k out _ _ hC hσ.cons hJ he.2 hk hm
        dsimp only at h
        rw [Walk.walkBind.eq_def] at h
        dsimp only at h
        cases b with
        | atom a =>
          obtain ⟨o, s3, _, h2⟩ := Walk.run_bind_ok h
          split at h2
          · exact hSkip (WalkProof.run_fire_then h2)
          · exact hEmit rfl h2
        | con cc as =>
          obtain ⟨os, s3, _, h2⟩ := Walk.run_bind_ok h
          split at h2
          · exact hSkip (WalkProof.run_fire_then h2)
          · exact hEmit rfl h2
        | proj cc i x =>
          obtain ⟨xo, s3, _, h2⟩ := Walk.run_bind_ok h
          split at h2
          · exact hSkip (WalkProof.run_fire_then h2)
          · split at h2
            · exact hSkip (WalkProof.run_fire_then h2)
            · exact hEmit rfl h2
        | prim p as =>
          obtain ⟨os, s3, _, h2⟩ := Walk.run_bind_ok h
          split at h2
          · exact hSkip (WalkProof.run_fire_then h2)
          · split at h2
            · have h2' := WalkProof.run_fire_then h2
              split at h2'
              · exact hSkip h2'
              · exact hEmit rfl h2'
            · exact hEmit rfl h2
          · split at h2
            · exact hSkip (WalkProof.run_fire_then h2)
            · split at h2
              · exact hSkip (WalkProof.run_fire_then h2)
              · split at h2
                · exact hEmit rfl (WalkProof.run_fire_then h2)
                · exact hEmit rfl h2
        | glob g =>
          dsimp only at h
          split at h
          · next gd hgd =>
            split at h
            · split at h
              · have h' := WalkProof.run_fire_then h
                obtain ⟨k', s3, h3, h4⟩ := Walk.run_bind_ok h'
                obtain ⟨e', s4, h5, h6⟩ := Walk.run_bind_ok h4
                obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h6
                have hk' := ihA' C env body k k' _ s3 hC hσ hJ he.2 hk h3
                exact ihW' _ _ _ gd.body k' e' s3 s4 hC.strip NoFnEnv.nil .nil (hC.1 g gd hgd) hk' h5
              · exact hEmit he.1 h
            · next hd0 tl hps =>
              -- `glob g` with `gd.ps ≠ []` contradicts `he.1 : !isFn g = true`
              have hne : isFn g = true := by
                rw [← hC.2 g]
                simp [Program.arity?, hgd, GDef.arity, hps]
              simp [Bind.firstOrder, hne] at he
          · exact absurd h Walk.run_throw_ok
        | call g as =>
          dsimp only at h
          obtain ⟨os, s3, _, h2⟩ := Walk.run_bind_ok h
          split at h2
          · exact hEmit rfl (WalkProof.run_fire_then h2)
          · split at h2
            · next gd hgd =>
              split at h2
              · have h' := WalkProof.run_fire_then h2
                obtain ⟨k', s4, h3, h4⟩ := Walk.run_bind_ok h'
                obtain ⟨e', s5, h5, h6⟩ := Walk.run_bind_ok h4
                obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h6
                have hk' := ihA' C env body k k' _ s4 hC hσ hJ he.2 hk h3
                exact ihW' _ _ _ gd.body k' e' s4 s5 hC.strip (NoFnEnv.entsOf _) .nil (hC.1 g gd hgd) hk' h5
              · split at h2
                · next σ' alt hkd =>
                  have h' := WalkProof.run_fire_then h2
                  obtain ⟨k', s4, h3, h4⟩ := Walk.run_bind_ok h'
                  obtain ⟨e', s5, h5, h6⟩ := Walk.run_bind_ok h4
                  obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h6
                  have hk' := ihA' C env body k k' _ s4 hC hσ hJ he.2 hk h3
                  have hgdfo := hC.1 g gd hgd
                  split at hkd
                  · cases hbody : gd.body with
                    | bind _ _ _ | join _ _ _ _ | jump _ _ | ret _ | tick _ | trap => simp [hbody] at hkd
                    | case x alts dflt =>
                      cases x with
                      | lit _ | box => simp [hbody] at hkd
                      | var m =>
                        cases os with
                        | nil => simp [hbody] at hkd
                        | cons fo osRest =>
                          simp only [hbody] at hkd
                          split at hkd
                          · cases hkn : Walk.known C.prog.known _ fo with
                            | none => rw [hkn] at hkd; cases hkd
                            | some cfs =>
                              rw [hkn] at hkd
                              obtain ⟨⟨isAlt, alt0⟩, hsel, hpair⟩ := Option.map_eq_some_iff.1 hkd
                              simp only [Prod.mk.injEq] at hpair
                              obtain ⟨rfl, rfl⟩ := hpair
                              rw [hbody] at hgdfo
                              simp only [Exp.firstOrder, Bool.and_eq_true] at hgdfo
                              have haltfo := select_fo hgdfo.1 hgdfo.2 hsel
                              have hσ' : NoFnEnv ((if isAlt then Walk.entsOf cfs.2.reverse else []) ++
                                  Walk.entsOf (fo :: osRest).reverse) := by
                                cases isAlt <;> simp [NoFnEnv.append, NoFnEnv.entsOf, NoFnEnv.nil]
                              exact ihW' _ _ _ alt0 k' e' s4 s5 hC.strip hσ' .nil haltfo hk' h5
                          · cases hkd
                  · cases hkd
                · exact hEmit rfl h2
            · exact absurd h2 Walk.run_throw_ok
        | app _ _ => simp [Bind.firstOrder] at he
        | fn _ _ => simp [Bind.firstOrder] at he
    | join ar r b body =>
      simp only [Exp.firstOrder, Bool.and_eq_true] at he
      cases fuel with
      | zero => exact absurd h Walk.run_throw_ok
      | succ fuel' =>
        obtain ⟨ihW', _, _⟩ := walk_fo_all (isFn := isFn) fuel'
        dsimp only at h
        rw [Walk.walkJoin.eq_def] at h
        dsimp only at h
        split at h
        · have h' := WalkProof.run_fire_then h
          exact ihW' C { env with jσ := default :: env.jσ } _ body k out _ _ hC hσ
            (.mk NoFnEnv.nil .nil (by rfl : Exp.trap.firstOrder isFn = true) hJ) he.2 hk h'
        · split at h
          · obtain ⟨id, s3, _, h2⟩ := Walk.run_bind_ok h
            exact ihW' C { env with jσ := .mk none env.σ env.jσ ar false b id :: env.jσ } _ body k out _ _ hC hσ
              (.mk hσ hJ he.1 hJ) he.2 hk h2
          · refine branch_fo hk (fun here' k' out' s0 s1 hk' hm => ?_) h
            have hIf : ∀ {pend : Bool} {s3 : Fires},
                (if pend = true then do
                    modify fun (f : Fires) => { f with pending := f.pending.insert here'.dj .leaf }
                    let e' ← Walk.walk C fuel' { env with jσ := .pend here'.dj env.σ env.jσ b :: env.jσ }
                      { here' with dj := here'.dj + 1 } body k'
                    modify fun (f : Fires) => { f with pending := f.pending.erase here'.dj }
                    pure (Exp.join ar r .trap e')
                  else do
                    let self := Walk.JEnt.mk (some here'.dj) env.σ env.jσ ar r b 0
                    let b' ← Walk.walk C fuel'
                      { σ := Walk.entsOf (paramOpds here'.d ar) ++ env.σ, jσ := if r then self :: env.jσ else env.jσ }
                      { here' with d := here'.d + ar, dj := if r then here'.dj + 1 else here'.dj } b k'
                    let e' ← Walk.walk C fuel' { env with jσ := self :: env.jσ }
                      { here' with dj := here'.dj + 1 } body k'
                    pure (Exp.join ar r b' e')).run s3 = .ok (out', s1) →
                out'.firstOrder isFn = true := by
              intro pend s3 h2
              split at h2
              · obtain ⟨_, s4, _, h3⟩ := Walk.run_bind_ok h2
                obtain ⟨e', s5, h4, h5⟩ := Walk.run_bind_ok h3
                obtain ⟨_, s6, _, h6⟩ := Walk.run_bind_ok h5
                obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h6
                simp only [Exp.firstOrder, Bool.and_eq_true]
                exact ⟨trivial, ihW' C { env with jσ := .pend here'.dj env.σ env.jσ b :: env.jσ } _ body k' e' s4 s5
                  hC hσ (.pend hσ hJ he.1 hJ) he.2 hk' h4⟩
              · obtain ⟨b', s4, h3, h4⟩ := Walk.run_bind_ok h2
                obtain ⟨e', s5, h5, h6⟩ := Walk.run_bind_ok h4
                obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h6
                have hself : FoJEnv isFn (if r then .mk (some here'.dj) env.σ env.jσ ar r b 0 :: env.jσ else env.jσ) := by
                  cases r <;> simp [hJ, FoJEnv.mk hσ hJ he.1 hJ]
                simp only [Exp.firstOrder, Bool.and_eq_true]
                exact ⟨ihW' C _ _ b k' b' s3 s4 hC ((NoFnEnv.entsOf _).append hσ) hself he.1 hk' h3,
                       ihW' C { env with jσ := .mk (some here'.dj) env.σ env.jσ ar r b 0 :: env.jσ } _ body k' e' s4 s5
                         hC hσ (.mk hσ hJ he.1 hJ) he.2 hk' h5⟩
            split at hm
            · obtain ⟨_, s2', _, h1⟩ := Walk.run_bind_ok hm
              obtain ⟨pend, s3, _, h2⟩ := Walk.run_bind_ok h1
              exact hIf h2
            · obtain ⟨pend, s3, _, h2⟩ := Walk.run_bind_ok hm
              exact hIf h2
    | jump j as =>
      cases fuel with
      | zero => exact absurd h Walk.run_throw_ok
      | succ fuel' =>
        obtain ⟨ihW', _, _⟩ := walk_fo_all (isFn := isFn) fuel'
        dsimp only at h
        rw [Walk.walkJump.eq_def] at h
        dsimp only at h
        obtain ⟨os, s3, _, h2⟩ := Walk.run_bind_ok h
        cases hj : env.jσ[j]? with
        | none => rw [hj] at h2; exact absurd h2 Walk.run_throw_ok
        | some je =>
          rw [hj] at h2
          have hje := hJ.get hj
          cases je with
          | mk lvl σj jσj ar r b id =>
            obtain ⟨hσj, hJj, hbj⟩ := hje
            cases lvl with
            | none =>
              dsimp only at h2
              split at h2
              · have h' := WalkProof.run_fire_then h2
                obtain ⟨e', s4, h3, h4⟩ := Walk.run_bind_ok h'
                obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
                exact ihW' C { σ := Walk.entsOf os.reverse ++ σj, jσ := jσj } _ b k e' _ s4 hC
                  ((NoFnEnv.entsOf _).append hσj) hJj hbj hk h3
              · exact absurd h2 Walk.run_throw_ok
            | some l =>
              dsimp only at h2
              split at h2
              · have h' := WalkProof.run_fire_then h2
                obtain ⟨e', s4, h3, h4⟩ := Walk.run_bind_ok h'
                obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
                exact ihW' C { σ := Walk.entsOf os.reverse ++ σj, jσ := jσj } _ b k e' _ s4 hC
                  ((NoFnEnv.entsOf _).append hσj) hJj hbj hk h3
              · split at h2
                · next σ' alt hhit =>
                  have h' := WalkProof.run_fire_then h2
                  obtain ⟨e', s4, h3, h4⟩ := Walk.run_bind_ok h'
                  obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
                  have hbfo := stripTicks_fo hbj
                  split at hhit
                  · cases hsb : (Walk.stripTicks b).2 with
                    | bind _ _ _ | join _ _ _ _ | jump _ _ | ret _ | tick _ | trap => simp [hsb] at hhit
                    | case x alts dflt =>
                      cases x with
                      | lit _ | box => simp [hsb] at hhit
                      | var v =>
                        cases v with
                        | succ _ => simp [hsb] at hhit
                        | zero =>
                          cases os with
                          | nil => simp [hsb] at hhit
                          | cons o rest =>
                            cases rest with
                            | cons _ _ => simp [hsb] at hhit
                            | nil =>
                              simp only [hsb] at hhit
                              cases hkn : Walk.known C.prog.known _ o with
                              | none => rw [hkn] at hhit; cases hhit
                              | some cfs =>
                                rw [hkn] at hhit
                                dsimp only at hhit
                                cases hsel : Walk.select alts dflt cfs.1 cfs.2.length with
                                | none => rw [hsel] at hhit; cases hhit
                                | some p =>
                                  rw [hsel] at hhit
                                  dsimp only at hhit
                                  split at hhit
                                  · simp only [Option.some.injEq, Prod.mk.injEq] at hhit
                                    obtain ⟨rfl, rfl⟩ := hhit
                                    rw [hsb] at hbfo
                                    simp only [Exp.firstOrder, Bool.and_eq_true] at hbfo
                                    have haltfo := select_fo hbfo.1 hbfo.2 hsel
                                    have hσ' : NoFnEnv ((if p.1 then Walk.entsOf cfs.2.reverse else []) ++ .opd o :: σj) := by
                                      cases p.1 <;> simp [NoFnEnv.append, NoFnEnv.entsOf, NoFnEnv.cons, hσj]
                                    exact ticks_fo (ihW' C _ _ p.2 k e' _ s4 hC hσ' hJj haltfo hk h3)
                                  · cases hhit
                  · cases hhit
                · obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h2; rfl
          | pend l σj jσj b =>
            obtain ⟨hσj, hJj, hbj⟩ := hje
            dsimp only at h2
            split at h2
            · split at h2
              · next σ' alt i hhit =>
                have h' := WalkProof.run_fire_then h2
                obtain ⟨e', s4, h3, h4⟩ := Walk.run_bind_ok h'
                obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
                have hbfo := stripTicks_fo hbj
                cases hsb : (Walk.stripTicks b).2 with
                | bind _ _ _ | join _ _ _ _ | jump _ _ | ret _ | tick _ | trap => simp [hsb] at hhit
                | case x alts dflt =>
                  cases x with
                  | lit _ | box => simp [hsb] at hhit
                  | var v =>
                    cases v with
                    | succ _ => simp [hsb] at hhit
                    | zero =>
                      cases os with
                      | nil => simp [hsb] at hhit
                      | cons o rest =>
                        cases rest with
                        | cons _ _ => simp [hsb] at hhit
                        | nil =>
                          simp only [hsb] at hhit
                          cases hkn : Walk.known C.prog.known _ o with
                          | none => rw [hkn] at hhit; cases hhit
                          | some cfs =>
                            rw [hkn] at hhit
                            obtain ⟨⟨isAlt, alt0⟩, hsel, htrip⟩ := Option.map_eq_some_iff.1 hhit
                            simp only [Prod.mk.injEq] at htrip
                            obtain ⟨rfl, rfl, rfl⟩ := htrip
                            rw [hsb] at hbfo
                            simp only [Exp.firstOrder, Bool.and_eq_true] at hbfo
                            have haltfo := select_fo hbfo.1 hbfo.2 hsel
                            have hσ' : NoFnEnv ((if isAlt then Walk.entsOf cfs.2.reverse else []) ++ .opd o :: σj) := by
                              cases isAlt <;> simp [NoFnEnv.append, NoFnEnv.entsOf, NoFnEnv.cons, hσj]
                            exact ticks_fo (ihW' C _ _ alt0 k e' _ s4 hC hσ' hJj haltfo hk h3)
              · have h' := WalkProof.run_fire_then h2
                obtain ⟨e', s4, h3, h4⟩ := Walk.run_bind_ok h'
                obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
                exact ihW' C { σ := Walk.entsOf os.reverse ++ σj, jσ := jσj } _ b k e' _ s4 hC
                  ((NoFnEnv.entsOf _).append hσj) hJj hbj hk h3
            · exact absurd h2 Walk.run_throw_ok
    | case x alts dflt =>
      simp only [Exp.firstOrder, Bool.and_eq_true] at he
      cases fuel with
      | zero => exact absurd h Walk.run_throw_ok
      | succ fuel' =>
        obtain ⟨ihW', _, ihAlts'⟩ := walk_fo_all (isFn := isFn) fuel'
        dsimp only at h
        rw [Walk.walkCase.eq_def] at h
        dsimp only at h
        obtain ⟨xo, s3, _, h2⟩ := Walk.run_bind_ok h
        split at h2
        · next fields alt hsel =>
          have h' := WalkProof.run_fire_then h2
          split at hsel
          · cases hkn : Walk.known C.prog.known _ xo with
            | none => rw [hkn] at hsel; cases hsel
            | some cfs =>
              rw [hkn] at hsel
              obtain ⟨⟨isAlt, alt0⟩, hs, hpair⟩ := Option.map_eq_some_iff.1 hsel
              simp only [Prod.mk.injEq] at hpair
              obtain ⟨rfl, rfl⟩ := hpair
              have hσ' : NoFnEnv ((if isAlt then Walk.entsOf cfs.2.reverse else []) ++ env.σ) := by
                cases isAlt <;> simp [NoFnEnv.append, NoFnEnv.entsOf, hσ]
              exact ihW' C { env with σ := (if isAlt then Walk.entsOf cfs.2.reverse else []) ++ env.σ } _ alt0 k out _ _
                hC hσ' hJ (select_fo he.1 he.2 hs) hk h'
          · cases hsel
        · split at h2
          · next m tail hid =>
            have h' := WalkProof.run_fire_then h2
            cases tail with
            | none =>
              obtain ⟨e', s4, h3, h4⟩ := Walk.run_bind_ok h'
              obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
              exact ticks_fo (pass_fo hk h3)
            | some j =>
              obtain ⟨e', s4, h3, h4⟩ := Walk.run_bind_ok h'
              obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
              exact ticks_fo (ihW' C env _ (.jump j [x]) k e' _ s4 hC hσ hJ rfl hk h3)
          · split at h2
            · next e0 hsame =>
              have h' := WalkProof.run_fire_then h2
              split at hsame
              · exact ihW' C env _ e0 k out _ _ hC hσ hJ (sameArms_fo he.1 hsame) hk h'
              · cases hsame
            · have hgo : ∀ here' k' out' s0 s1, FoKont isFn k' →
                  (do let alts' ← Walk.walkAlts C fuel' env here' xo alts k'
                      let dflt' ← match dflt with
                        | some e => some <$> Walk.walk C fuel' env here' e k'
                        | none => pure none
                      pure (Exp.case (xo.atom here'.d) alts' dflt')).run s0 = .ok (out', s1) →
                  out'.firstOrder isFn = true := by
                intro here' k' out' s0 s1 hk' hm
                obtain ⟨alts', s4, h3, h4⟩ := Walk.run_bind_ok hm
                cases dflt with
                | none =>
                  dsimp only at h4
                  obtain ⟨dflt', s5, h5, h6⟩ := Walk.run_bind_ok h4
                  obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h5
                  obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h6
                  simp only [Exp.firstOrder, Bool.and_eq_true]
                  exact ⟨ihAlts' C env here' xo alts k' alts' s0 s4 hC hσ hJ he.1 hk' h3, rfl⟩
                | some d =>
                  dsimp only at h4
                  obtain ⟨dflt', s5, h5, h6⟩ := Walk.run_bind_ok h4
                  obtain ⟨d', hd', rfl⟩ := Walk.run_map_ok h5
                  obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h6
                  simp only [Exp.firstOrder, Bool.and_eq_true]
                  exact ⟨ihAlts' C env here' xo alts k' alts' s0 s4 hC hσ hJ he.1 hk' h3,
                         ihW' C env here' d k' d' s4 s5 hC hσ hJ he.2 hk' hd'⟩
              by_cases hbr : alts.length + (if dflt.isSome then 1 else 0) ≥ 2
              · rw [if_pos hbr] at h2
                exact branch_fo hk hgo h2
              · rw [if_neg hbr] at h2
                exact hgo _ k out _ _ hk h2

theorem walk_global_fo {isFn : GlobalId → Bool} {C : Cfg} {gd gd' : GDef} {s s' : Fires}
    (hC : FoCfg isFn C) (hgd : gd.body.firstOrder isFn = true)
    (h : (Walk.global C gd).run s = .ok (gd', s')) : gd'.body.firstOrder isFn = true := by
  unfold Walk.global at h
  obtain ⟨b', s1, h1, h2⟩ := Walk.run_bind_ok h
  obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h2
  exact (walk_fo_all Walk.fuel).1 C _ _ gd.body .ret b' s s1 hC (NoFnEnv.entsOf _) .nil hgd trivial h1

theorem foCfg_of_firstOrder {P : Program} (hw : P.WF) (hfo : FirstOrder P) (C : Cfg) (hP : C.prog = P) :
    FoCfg (fun g => (P.arity? g).any (· > 0)) C := by
  subst hP
  refine ⟨fun g gd hgd => ?_, fun _ => rfl⟩
  unfold FirstOrder firstOrder at hfo
  have hmem : (g, gd) ∈ C.prog.globalList := by
    unfold Program.globalList
    exact List.mem_filterMap.2 ⟨g, List.mem_range.2 (hw.1 g gd hgd), by simp [hgd]⟩
  exact List.all_eq_true.1 hfo (g, gd) hmem

/-! ## `Shrink.run`, `Inline.round`, `Prune.run` preserve `FirstOrder` -/

theorem shrink_firstOrder {P Q : Program} {p : Shrink.Params} {cert : Shrink.Cert}
    (hw : P.WF) (hfo : FirstOrder P) (h : Shrink.run p cert P = .ok Q) : FirstOrder Q := by
  obtain ⟨_, _, hsize, hQ⟩ := Shrink.Proof.run_global h
  have hC := foCfg_of_firstOrder hw hfo (Shrink.cfg P p) rfl
  have hiter : ∀ (gd : GDef) (k : Nat), gd.body.firstOrder (fun g => (P.arity? g).any (· > 0)) = true →
      (Shrink.Proof.iter P p gd k).body.firstOrder (fun g => (P.arity? g).any (· > 0)) = true := by
    intro gd k hgd
    induction k with
    | zero => exact hgd
    | succ k ih =>
      unfold Shrink.Proof.iter Shrink.Proof.roundOr Shrink.round
      cases hd : Walk.isDispatchDef (Shrink.Proof.iter P p gd k) with
      | true =>
        simp only [↓reduceIte, pure, Except.pure]
        exact ih
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · next gd' f hr => exact walk_global_fo hC ih hr
        · exact ih
  have har : ∀ g, (Q.arity? g).any (· > 0) = (P.arity? g).any (· > 0) := by
    intro g
    unfold Program.arity?
    rw [hQ g]
    split
    · next hlt =>
      cases hPg : P.global? g with
      | none => rfl
      | some gd =>
        have hps : ∀ k, (Shrink.Proof.iter P p gd k).ps = gd.ps := by
          intro k
          induction k with
          | zero => rfl
          | succ k ih => rw [Shrink.Proof.iter, Shrink.Proof.roundOr_ps, ih]
        simp [GDef.arity, hps]
    · next hlt =>
      cases hPg : P.global? g with
      | none => rfl
      | some gd => exact absurd (hw.1 g gd hPg) hlt
  have harFun : (fun g => (Q.arity? g).any (· > 0)) = (fun g => (P.arity? g).any (· > 0)) := funext har
  unfold FirstOrder firstOrder at hfo ⊢
  rw [harFun, List.all_eq_true]
  intro ⟨g, gd'⟩ hm
  unfold Program.globalList at hm
  obtain ⟨g', hg', hp⟩ := List.mem_filterMap.1 hm
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hp
  obtain ⟨gd1, h1, rfl, rfl⟩ := hp
  have hltP : g' < P.size := by rw [← hsize]; exact List.mem_range.1 hg'
  rw [hQ g', if_pos hltP] at h1
  cases hPg : P.global? g' with
  | none => rw [hPg] at h1; cases h1
  | some gd =>
    rw [hPg] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    subst h1
    have hmemP : (g', gd) ∈ P.globalList := by
      unfold Program.globalList
      exact List.mem_filterMap.2 ⟨g', List.mem_range.2 hltP, by simp [hPg]⟩
    exact hiter gd _ (List.all_eq_true.1 hfo (g', gd) hmemP)

theorem inline_firstOrder {P Q : Program} {r : Inline.Round} {f : Walk.Fires}
    (hw : P.WF) (hfo : FirstOrder P) (h : Inline.round P r = .ok (Q, f)) : FirstOrder Q := by
  obtain ⟨_, _, hsize, hQ⟩ := Inline.Proof.round_global h
  have hafter_ps : ∀ g gd, (Inline.Proof.after P r g gd).ps = gd.ps :=
    fun g gd => (Inline.Proof.after_walked g gd).1
  have har : ∀ g, (Q.arity? g).any (· > 0) = (P.arity? g).any (· > 0) := by
    intro g
    unfold Program.arity?
    rw [hQ g]
    split
    · cases P.global? g with
      | none => rfl
      | some gd => simp [GDef.arity, hafter_ps]
    · next hlt =>
      cases hPg : P.global? g with
      | none => rfl
      | some gd => exact absurd (hw.1 g gd hPg) hlt
  have harFun : (fun g => (Q.arity? g).any (· > 0)) = (fun g => (P.arity? g).any (· > 0)) := funext har
  unfold FirstOrder firstOrder at hfo ⊢
  rw [harFun, List.all_eq_true]
  intro ⟨g, gd'⟩ hm
  unfold Program.globalList at hm
  obtain ⟨g', hg', hp⟩ := List.mem_filterMap.1 hm
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hp
  obtain ⟨gd1, h1, rfl, rfl⟩ := hp
  have hltP : g' < P.size := by rw [← hsize]; exact List.mem_range.1 hg'
  rw [hQ g', if_pos hltP] at h1
  cases hPg : P.global? g' with
  | none => rw [hPg] at h1; cases h1
  | some gd =>
    rw [hPg] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    subst h1
    have hmemP : (g', gd) ∈ P.globalList := by
      unfold Program.globalList
      exact List.mem_filterMap.2 ⟨g', List.mem_range.2 hltP, by simp [hPg]⟩
    have hgdfo := List.all_eq_true.1 hfo (g', gd) hmemP
    dsimp only at hgdfo ⊢
    unfold Inline.Proof.after
    split
    · split
      · next cs gd'' f' hr => exact walk_global_fo (foCfg_of_firstOrder hw hfo _ rfl) hgdfo hr
      · exact hgdfo
    · exact hgdfo

/-! ## `Prune.run` preserves `FirstOrder` and tables (`known`, `ctors`) -/

theorem prune_tables (P : Program) : (Prune.run P).known = P.known ∧ (Prune.run P).ctors = P.ctors :=
  ⟨rfl, rfl⟩

mutual

theorem prune_rename_firstOrder {m : Src.NatMap Nat} {isFn₁ isFn₂ : GlobalId → Bool} :
    ∀ (e : Exp), (∀ g, g ∈ e.refs → isFn₂ (m.getD g g) = isFn₁ g) →
      e.firstOrder isFn₁ = true → (Prune.Exp.rename m e).firstOrder isFn₂ = true
  | .bind _ b e, h, hfo => by
    simp only [Prune.Exp.rename, Exp.firstOrder, Bool.and_eq_true] at hfo ⊢
    exact ⟨prune_renameBind_firstOrder b (fun g hg => h g (by simp [Exp.refs, hg])) hfo.1,
           prune_rename_firstOrder e (fun g hg => h g (by simp [Exp.refs, hg])) hfo.2⟩
  | .join _ _ b e, h, hfo => by
    simp only [Prune.Exp.rename, Exp.firstOrder, Bool.and_eq_true] at hfo ⊢
    exact ⟨prune_rename_firstOrder b (fun g hg => h g (by simp [Exp.refs, hg])) hfo.1,
           prune_rename_firstOrder e (fun g hg => h g (by simp [Exp.refs, hg])) hfo.2⟩
  | .jump .., _, _ | .ret _, _, _ | .trap, _, _ => rfl
  | .case _ alts d, h, hfo => by
    simp only [Prune.Exp.rename, Exp.firstOrder, Bool.and_eq_true] at hfo ⊢
    exact ⟨prune_renameAlts_firstOrder alts (fun g hg => h g (by simp [Exp.refs, hg])) hfo.1,
           prune_renameOpt_firstOrder d (fun g hg => h g (by simp [Exp.refs, hg])) hfo.2⟩
  | .tick e, h, hfo => prune_rename_firstOrder e h hfo

theorem prune_renameBind_firstOrder {m : Src.NatMap Nat} {isFn₁ isFn₂ : GlobalId → Bool} :
    ∀ (b : Bind), (∀ g, g ∈ b.refs → isFn₂ (m.getD g g) = isFn₁ g) →
      b.firstOrder isFn₁ = true → (Prune.Bind.rename m b).firstOrder isFn₂ = true
  | .glob g, h, hfo => by
    simp only [Prune.Bind.rename, Bind.firstOrder] at hfo ⊢
    rw [h g (by simp [Bind.refs])]; exact hfo
  | .atom _, _, _ | .con .., _, _ | .proj .., _, _ | .prim .., _, _ | .call .., _, _ => rfl
  | .app .., _, hfo => by simp [Bind.firstOrder] at hfo
  | .fn .., _, hfo => by simp [Bind.firstOrder] at hfo

theorem prune_renameAlts_firstOrder {m : Src.NatMap Nat} {isFn₁ isFn₂ : GlobalId → Bool} :
    ∀ (alts : List Alt), (∀ g, g ∈ Exp.altsRefs alts → isFn₂ (m.getD g g) = isFn₁ g) →
      Exp.altsFirstOrder isFn₁ alts = true →
      Exp.altsFirstOrder isFn₂ (Prune.Exp.renameAlts m alts) = true
  | [], _, _ => rfl
  | .mk _ _ b :: rest, h, hfo => by
    simp only [Prune.Exp.renameAlts, Exp.altsFirstOrder, Bool.and_eq_true] at hfo ⊢
    exact ⟨prune_rename_firstOrder b (fun g hg => h g (by simp [Exp.altsRefs, hg])) hfo.1,
           prune_renameAlts_firstOrder rest (fun g hg => h g (by simp [Exp.altsRefs, hg])) hfo.2⟩

theorem prune_renameOpt_firstOrder {m : Src.NatMap Nat} {isFn₁ isFn₂ : GlobalId → Bool} :
    ∀ (o : Option Exp), (∀ g, g ∈ Exp.optRefs o → isFn₂ (m.getD g g) = isFn₁ g) →
      Exp.optFirstOrder isFn₁ o = true →
      Exp.optFirstOrder isFn₂ (Prune.Exp.renameOpt m o) = true
  | none, _, _ => rfl
  | some e, h, hfo => prune_rename_firstOrder e h hfo

end

theorem prune_firstOrder {P : Program} (hw : P.WF) (hfo : FirstOrder P) : FirstOrder (Prune.run P) := by
  let X := Prune.Proof.setting hw.1 hw.2
  have hgl : ∀ i, (Prune.run P).global? i =
      ((Prune.Proof.keptOf P).filterMap fun g =>
        (P.global? g).map fun gd => { gd with body := Prune.Exp.rename (Prune.Proof.renOf P) gd.body })[i]? := by
    intro i; rw [Prune.Proof.run_eq' P]; exact Prune.Proof.withGlobals_global P _ i
  unfold FirstOrder firstOrder at hfo ⊢
  rw [List.all_eq_true]
  intro ⟨i, gd'⟩ hm
  unfold Program.globalList at hm
  obtain ⟨i', hi', hp⟩ := List.mem_filterMap.1 hm
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hp
  obtain ⟨gd1, h1, rfl, rfl⟩ := hp
  rw [hgl i'] at h1
  have hfm := Prune.Proof.filterMap_getElem? (l := Prune.Proof.keptOf P)
    (f := fun g => (P.global? g).map fun gd => { gd with body := Prune.Exp.rename (Prune.Proof.renOf P) gd.body })
    (fun x hx => by
      obtain ⟨hx1, _⟩ := List.mem_filter.1 hx
      obtain ⟨gdx, hgdx⟩ := hw.2 x (List.mem_range.1 hx1)
      exact ⟨_, by rw [hgdx]; rfl⟩) i'
  rw [hfm] at h1
  cases hk : (Prune.Proof.keptOf P)[i']? with
  | none => rw [hk] at h1; cases h1
  | some g =>
    rw [hk] at h1
    simp only [Option.bind_some, Option.map_eq_some_iff] at h1
    obtain ⟨gd, hPg, rfl⟩ := h1
    have hseen : (Prune.reach P (Prune.Proof.fuelOf P) P.roots .leaf).contains g = true :=
      (List.mem_filter.1 (List.mem_of_getElem? hk)).2
    have hmemP : (g, gd) ∈ P.globalList := by
      unfold Program.globalList
      exact List.mem_filterMap.2 ⟨g, List.mem_range.2 (hw.1 g gd hPg), by simp [hPg]⟩
    have hgdfo := List.all_eq_true.1 hfo (g, gd) hmemP
    refine prune_rename_firstOrder gd.body (fun h hh => ?_) hgdfo
    have hseenH := X.closed g gd hseen hPg h hh
    cases hPh : P.global? h with
    | none =>
      -- `h` is not in `P`; cannot have `arity > 0` in `P`, and `renOf P` maps `h` to itself;
      -- wait: could `h < (Prune.run P).size`? Only if `h` is not in `keptOf P` -> `renOf P` leaves `h` unchanged!
      -- Actually `h` can only be `none` in `P` if `h ≥ P.size` (by `hw.2`), and `(Prune.run P).size ≤ P.size`!
      have hge : P.size ≤ h := by
        by_cases hge : P.size ≤ h
        · exact hge
        · exfalso
          obtain ⟨gdh, hgdh⟩ := hw.2 h (by omega)
          rw [hPh] at hgdh; cases hgdh
      have hnotkept : h ∉ Prune.Proof.keptOf P := fun hm' => by
        have := List.mem_range.1 (List.mem_filter.1 hm').1; omega
      have hren : (Prune.Proof.renOf P).getD h h = h := by
        unfold Src.NatMap.getD Prune.Proof.renOf
        cases hget : (Src.NatMap.ofList (Prune.Proof.keptOf P).zipIdx).get? h with
        | none => rfl
        | some v =>
          have hmem' := Convert.Proof.natMap_ofList_mem
            (by rw [Prune.Proof.zipIdx_fst]; exact Prune.Proof.keptOf_nodup P) hget
          have := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hmem')
          exact absurd this hnotkept
      have hsizeLe : (Prune.run P).size ≤ P.size := by
        let f : GlobalId → Option GDef := fun g =>
          (P.global? g).map fun gd => { gd with body := Prune.Exp.rename (Prune.Proof.renOf P) gd.body }
        show ((Prune.Proof.keptOf P).filterMap f).length ≤ P.size
        have h1' : ((Prune.Proof.keptOf P).filterMap f).length ≤ (Prune.Proof.keptOf P).length :=
          List.length_filterMap_le f (Prune.Proof.keptOf P)
        have h2' : (Prune.Proof.keptOf P).length ≤ (List.range P.size).length :=
          List.length_filter_le _ _
        simp only [List.length_range] at h2'
        omega
      have hQnone : (Prune.run P).global? h = none := by
        cases hQh : (Prune.run P).global? h with
        | none => rfl
        | some gdh =>
          have hwfQ := (Prune.Proof.run_refines hw).1
          exact absurd (hwfQ.1 h gdh hQh) (Nat.not_lt.2 (Nat.le_trans hsizeLe hge))
      simp [hren, Program.arity?, hPh, hQnone]
    | some gdh =>
      have hQg := X.glob h gdh hseenH hPh
      dsimp only [X, Prune.Proof.setting] at hQg
      show ((Prune.run P).arity? ((Prune.Proof.renOf P).getD h h)).any (· > 0) = (P.arity? h).any (· > 0)
      unfold Program.arity?
      rw [hQg, hPh]
      rfl

end IxCC.Anf.PassProof
