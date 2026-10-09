import Ix.CompileCert.Image.SimBuild

/-!
# M7 L2a-syn: the relocation step from shifted counters

`buildRecApp` (at X1's table-free development, `buildRecAppW coreDev`) run from a counter and from
the counter shifted by `d`, with renamed indices and major, succeeds in both runs or in neither and
returns renamed terms:

* `mono_buildRecAppW`: the construction never decreases the counter;
* `sim_buildRecAppP`: **the relocation step from shifted counters**, for every fuel.

The proof follows the code's steps (§4.2 steps 1-5): the eliminator choice (`sim_findElim`), the slot
classes (equal: the motive types are compared with `alphaEq`, which the renaming keeps on fresh
names, `alphaEq_ren`), the canonical recursor's telescope, the motives, the minors with their
components and hypothesis values (the relocated hypotheses by the induction hypothesis), and the
final projection.

The hypotheses are those of the renaming simulation: the shift keeps `==` on the fresh names below
`B` (`InjOn`; from the fresh names below `B + d` hash-distinct, `NamesOK`, by `injOn_shift`; free at
`d = 0`), the context related to itself (`CtxRE`; from `CtxOK` when its names are below `s0`), the
environment's constants closed (`EnvClosed`). The two runs may use two developments related by
`DevRel` (`sim_buildRecAppW`); at X1's core on both sides, `sim_buildRecAppP`.
-/

namespace Ix.CompileCert.Img

open Ix (Name Level Expr ConstantInfo InductiveVal RecursorVal)
open Ix.Compile.Image (GenM GenState freshName Local telescope LCtx Elim LeanMinor)
open Ix.CompileCert.Conv

/-- Monotonicity of the counter, by the shape of the program: every step of the construction is
one of the monotone steps below. -/
syntax "mono_auto" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mono_auto) => `(tactic| first
    | done
    | with_reducible exact Mono.pure _
    | with_reducible exact Mono.throw _
    | with_reducible exact Mono.liftExcept _
    | with_reducible exact Mono.idx _ _ _
    | with_reducible exact Mono.trace _
    | with_reducible exact Mono.freshName
    | with_reducible exact mono_telescope _ _
    | with_reducible exact mono_findElim _ _
    | with_reducible exact mono_elimMotiveTypes _ _ _ _
    | with_reducible exact mono_analyzeCanonMinor _ _ _
    | with_reducible exact mono_analyzeLeanMinor _ _
    | with_reducible exact ih _ _ _ _
    | with_reducible exact mono_buildRecAppW _ _ _ _ _ _
    | with_reducible exact Mono.get
    | (with_reducible refine Mono.forIn'_range _ _ (fun _ _ _ => ?_) _ <;> mono_auto)
    | (with_reducible refine Mono.forIn_range _ _ (fun _ _ => ?_) _ <;> mono_auto)
    | (with_reducible refine Mono.forIn_array (fun _ _ => ?_) _ _ <;> mono_auto)
    | (with_reducible refine Mono.mapM_array _ (fun _ => ?_) _ <;> mono_auto)
    | (with_reducible refine Mono.bind ?_ (fun _ => ?_) <;> mono_auto)
    | (split <;> mono_auto)
    | (dsimp only <;> mono_auto))

set_option maxRecDepth 20000 in
theorem mono_buildRecAppW (D : DevOps) : ∀ fuel c t idx major, Mono (buildRecAppW D fuel c t idx major)
  | 0, c, t, idx, major => by unfold buildRecAppW; exact Mono.throw _
  | fuel + 1, c, t, idx, major => by
    have ih := mono_buildRecAppW D fuel
    unfold buildRecAppW
    mono_auto

theorem map_congr_eq {α β : Type} {xs ys : Array α} (hs : xs.size = ys.size) {F : α → β}
    (h : ∀ i (h1 : i < xs.size) (h2 : i < ys.size), F ys[i] = F xs[i]) : ys.map F = xs.map F := by
  apply Array.ext (by simp [hs])
  intro i h1 h2
  simp only [Array.getElem_map]
  exact h i (by simpa using h2) (by simpa using h1)

theorem filter_congr_mem {α : Type} {p q : α → Bool} {xs : Array α} (h : ∀ x ∈ xs, p x = q x) :
    xs.filter p = xs.filter q := by
  apply Array.toList_inj.1
  simp only [Array.toList_filter]
  exact List.filter_congr (fun x hx => h x (by simpa using hx))

section
variable {s0 d B : Nat}

theorem Sim.forIn'_range2 {β δ : Type} {R : β → δ → Prop} {n n' : Nat} (hn : n = n')
    (f : (a : Nat) → a ∈ [:n] → β → GenM (ForInStep β)) (g : (a : Nat) → a ∈ [:n'] → δ → GenM (ForInStep δ))
    (hfg : ∀ a (h : a ∈ [:n]) (h' : a ∈ [:n']) b b', R b b' → Sim s0 d B (StepRel R) (f a h b) (g a h' b'))
    (hm : ∀ a h b, Mono (f a h b)) {b : β} {b' : δ} (h : R b b') :
    Sim s0 d B R (forIn' [:n] b f) (forIn' [:n'] b' g) := by
  subst hn; exact Sim.forIn'_range _ f g (fun a h b b' hb => hfg a h h b b' hb) hm h

theorem RE.ofFix {l : Local} (h1 : shift s0 d l.fvar = l.fvar) (h2 : FreshBelow B l.fvar) :
    RE s0 d B l.expr l.expr :=
  ⟨by unfold Ix.Compile.Image.Local.expr; conv => rhs; rw [← h1]
      exact Ren.mkFVar' _, h2⟩

theorem CtxRE.ms_expr {c : LCtx} (hc : CtxRE s0 d B c) {l : Local} (hl : l ∈ c.ms) :
    RE s0 d B l.expr l.expr :=
  RE.ofFix (hc.1 l (by simp [hl])).1 (hc.1 l (by simp [hl])).2.1

theorem CtxRE.mins_expr {c : LCtx} (hc : CtxRE s0 d B c) {l : Local} (hl : l ∈ c.mins) :
    RE s0 d B l.expr l.expr :=
  RE.ofFix (hc.1 l (by simp [hl])).1 (hc.1 l (by simp [hl])).2.1

theorem RLs.extract_from {xs ys : Array Local} (h : RLs s0 d B xs ys) (a : Nat) :
    RLs s0 d B (xs.extract a) (ys.extract a) := by
  have := h.extract a xs.size
  rwa [show ys.extract a xs.size = ys.extract a ys.size by rw [h.1]] at this

theorem RL.expr {l l' : Local} (h : RL s0 d B l l') : RE s0 d B l.expr l'.expr :=
  ⟨by unfold Ix.Compile.Image.Local.expr; rw [h.1.1]; exact Ren.mkFVar' _, h.2.1⟩

theorem subst_exrel (hok : InjOn (shift s0 d) (FreshBelow B)) {xs xs' : Array Local} (hxs : RLs s0 d B xs xs')
    {vs vs' : Array Expr} (hv : ARE s0 d B vs vs') {e e' : Expr} (he : RE s0 d B e e') :
    ExRel (Ren (shift s0 d)) (coreDev.subst (xs.map (·.fvar)) vs e) (coreDev.subst (xs'.map (·.fvar)) vs' e') := by
  show ExRel _ (substFVarsP _ _ _) (substFVarsP _ _ _)
  rw [hxs.fvars]
  refine substFVarsP_ren hok _ (fun x hx => ?_) hv.1 he.1 he.2
  simp only [Array.mem_map] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  exact (hxs.fv l hl).1

theorem subst_fv (xs : Array Local) {vs vs' : Array Expr}
    (hv : ARE s0 d B vs vs') {e : Expr} (he : FvAll (FreshBelow B) e) :
    ∀ r, coreDev.subst (xs.map (·.fvar)) vs e = .ok r → FvAll (FreshBelow B) r :=
  fun _ hr => substFVarsP_fv hr he hv.2

/-- A development step of the second run succeeds, related, whenever the first's does (the
construction's two calls: the motives into the canonical minor types and the rule types; the rule
right-hand sides at the telescope). -/
structure DevRel (s0 d B : Nat) (D1 D2 : DevOps) : Prop where
  subst : ∀ {xs xs' : Array Local} {vs vs' : Array Expr} {e e' : Expr}, RLs s0 d B xs xs' →
    ARE s0 d B vs vs' → RE s0 d B e e' → ∀ r, D1.subst (xs.map (·.fvar)) vs e = .ok r →
      ∃ r', D2.subst (xs'.map (·.fvar)) vs' e' = .ok r' ∧ RE s0 d B r r'
  inst : ∀ {f f' : Expr} {args args' : Array Expr}, RE s0 d B f f' → ARE s0 d B args args' →
    ∀ r, D1.inst f args = .ok r → ∃ r', D2.inst f' args' = .ok r' ∧ RE s0 d B r r'

/-- X1's core is related to itself from shifted counters. -/
theorem devRel_core (hok : InjOn (shift s0 d) (FreshBelow B)) : DevRel s0 d B coreDev coreDev := by
  refine ⟨fun hxs hv he r hr => ?_, fun hf ha r hr => ?_⟩
  · obtain ⟨r', h1, h2⟩ := (subst_exrel hok hxs hv he).ok_of hr
    exact ⟨r', h1, h2, subst_fv _ hv he.2 r hr⟩
  · obtain ⟨r', h1, h2⟩ := (instantiateP_ren hf.1 ha.1).ok_of hr
    exact ⟨r', h1, h2, instantiateP_fv hr hf.2 ha.2⟩

/-- A step of the first run that succeeds is one of the second's, related. -/
theorem Sim.liftExcept' {α β : Type} {R : α → β → Prop} {x : Except String α} {y : Except String β}
    (h : ∀ a, x = .ok a → ∃ b, y = .ok b ∧ R a b) :
    Sim s0 d B R (Ix.Compile.Image.liftExcept x) (Ix.Compile.Image.liftExcept y) := by
  intro st st' a st1 hs hx _
  cases x with
  | error e => cases hx
  | ok a' =>
    obtain ⟨b, hb, hab⟩ := h a' rfl
    subst hb
    have : a' = a ∧ st = st1 := by
      simp only [Ix.Compile.Image.liftExcept] at hx
      cases hx; exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨b, st', rfl, hab, hs⟩

theorem instForall_exrel {ρ : Name → Name} {a b : Expr} {as bs : Array Expr} (h : Ren ρ a b)
    (hab : ARen ρ as bs) :
    ExRel (Ren ρ) (Ix.Compile.Image.instForall a as) (Ix.Compile.Image.instForall b bs) := by
  have := instForall_ren h hab
  revert this
  cases Ix.Compile.Image.instForall a as <;> cases Ix.Compile.Image.instForall b bs <;> simp [ExRel]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
/-- **The relocation step from shifted counters.** Run from related states (the second counter
shifted by `d`) with renamed indices and major, the two runs of `buildRecApp` at the core development
agree: when the first succeeds ending below `B`, so does the second, with the renamed result. The
program is long: its monotonicity side conditions are discharged by `mono_auto` at every bind. -/
theorem sim_buildRecAppW {D1 D2 : DevOps} (hD : DevRel s0 d B D1 D2)
    (hok : InjOn (shift s0 d) (FreshBelow B)) (c : LCtx) (hc : CtxRE s0 d B c)
    (hcl : EnvClosed c.const?) : ∀ (fuel t : Nat) {idx idx' : Array Expr} {major major' : Expr},
    ARE s0 d B idx idx' → RE s0 d B major major' →
    Sim s0 d B (RE s0 d B) (buildRecAppW D1 fuel c t idx major)
      (buildRecAppW D2 fuel c t idx' major')
  | 0, t, idx, idx', major, major', _, _ => by unfold buildRecAppW; exact Sim.throw _
  | fuel + 1, t, idx, idx', major, major', hidx, hmaj => by
    have ihs := sim_buildRecAppW hD hok c hc hcl fuel
    have ih := mono_buildRecAppW D1 fuel
    unfold buildRecAppW
    refine Sim.bind (sim_findElim hok c hc hcl t) (fun e e' he => ?_) (fun e => by mono_auto)
    obtain ⟨h1, h2, h3, hps, h5, h6⟩ := he
    rw [← h1, ← h2, ← h3, ← h5, ← h6]
    refine Sim.bind (Sim.liftExcept_same _) (fun rv rv' hrv => ?_) (fun _ => by mono_auto)
    obtain ⟨rfl, hrv⟩ := hrv
    refine Sim.bind (sim_elimMotiveTypes hok hcl _ _ hps) (fun mts mts' hm => ?_) (fun _ => by mono_auto)
    rw [map_congr_eq hm.size (fun i h1 h2 => ?_)]
    rotate_left
    · dsimp only
      refine congrArg _ (filter_congr_mem fun x hx => ?_)
      obtain ⟨ty, n⟩ := x
      have htr := hc.2 ty (Array.fst_mem_of_mem_zipIdx hx)
      exact alphaEq_ren hok htr.1 (hm.1.get i h1 h2) htr.2 (hm.2 _ (by simp))
    refine Sim.bind (R := fun _ _ => True) (Sim.forIn_array (Ra := Eq) (fun a a' u u' ha hu => ?_)
      (fun _ _ => by mono_auto) (LRel.refl_eq _) trivial) (fun _ _ _ => ?_) (fun _ => by mono_auto)
    · subst ha
      obtain ⟨cl, i⟩ := a
      dsimp only
      split
      · exact Sim.throw _
      · exact Sim.pure trivial
    extract_lets anyTuple luZero L packs us recC motives0 comps0 jp jp'
    split
    · exact Sim.of_fail (throw_bind_fail _ _)
    have hsub : RE s0 d B (Ix.Compile.Canon.substLevels rv.cnst.levelParams us rv.cnst.type)
        (Ix.Compile.Canon.substLevels rv.cnst.levelParams us rv.cnst.type) :=
      RE.closed (substLevels_fv _ _ (hcl _ _ (recOf_ok hrv)))
    refine Sim.bind (R := RE s0 d B) (Sim.liftRE (instForall_exrel hsub.1 hps.1)
      (fun r hr => instForall_fv hsub.2 hps.2 hr)) (fun rty rty' hrty => ?_) (fun _ => by mono_auto)
    refine Sim.bind (Sim.trace _) (fun _ _ _ => ?_) (fun _ => by mono_auto)
    refine Sim.bind (sim_telescope hok hrty _) (fun p q hpq => ?_) (fun _ => by mono_auto)
    obtain ⟨xs, _⟩ := p
    obtain ⟨xs', _⟩ := q
    obtain ⟨hxs, -⟩ := hpq
    have hmsC := hxs.extract 0 rv.numMotives
    have hminsC := hxs.extract_from rv.numMotives
    refine Sim.bind (R := ARE s0 d B) (Sim.forIn'_range2 hmsC.1 _ _ (fun i h h' mot mot' hmot => ?_)
      (fun _ _ _ => by mono_auto) ARE.empty) (fun motives motives' hmots => ?_) (fun _ => by mono_auto)
    · have hmi := hmsC.2 i h.upper h'.upper
      refine Sim.bind (sim_telescope' hok ⟨hmi.1.2.2.1, hmi.2.2⟩) (fun p q hpq => ?_) (fun _ => by mono_auto)
      obtain ⟨isy, _⟩ := p
      obtain ⟨isy', _⟩ := q
      obtain ⟨hisy, -⟩ := hpq
      refine Sim.bind (Sim.idx (R := Eq) rfl (fun _ _ _ => rfl) _ _) (fun cl cl' hcl => ?_)
        (fun _ => by mono_auto)
      subst hcl
      refine Sim.bind (Sim.mapM_array (Ra := Eq) (R := RE s0 d B) (fun j j' hj => ?_) (fun _ => by mono_auto)
        (LRel.refl_eq _)) (fun apps apps' happs => ?_) (fun _ => by mono_auto)
      · subst hj
        refine Sim.bind (Sim.idx (R := fun l l' => l = l' ∧ l ∈ c.ms) rfl
          (fun _ h1 _ => ⟨rfl, Array.getElem_mem h1⟩) _ _) (fun l l' hl => ?_) (fun _ => by mono_auto)
        obtain ⟨rfl, hl⟩ := hl
        exact Sim.pure (RE.mkAppN (hc.ms_expr hl) hisy.are)
      have hap := ARE.of_lrel happs
      refine Sim.bind (Sim.idx (R := Eq) rfl (fun _ _ _ => rfl) _ _) (fun pk pk' hpk => ?_)
        (fun _ => by mono_auto)
      subst hpk
      refine Sim.bind (Sim.liftRE (wrapTy_ren _ _ hap.1) (fun r hr => wrapTy_fv _ _ hap.2 hr))
        (fun w w' hw => ?_) (fun _ => by mono_auto)
      exact Sim.pure (show StepRel (ARE s0 d B) (.yield _) (.yield _) from
        hmot.push (RE.etaReduce (RE.mkLambda hok hisy hw)))
    refine Sim.bind (R := ARE s0 d B) (Sim.forIn_array (Ra := RL s0 d B)
      (fun minC minC' mns mns' hminC hmns => ?_) (fun _ _ => by mono_auto)
      (show ARel (RL s0 d B) _ _ from ⟨hminsC.1, hminsC.2⟩).lrel ARE.empty)
      (fun minors minors' hmins => ?_) (fun _ => by mono_auto)
    · refine Sim.bind (sim_analyzeCanonMinor hok _ hmsC ⟨hminC.1.2.2.1, hminC.2.2⟩) (fun a a' ha => ?_)
        (fun _ => by mono_auto)
      subst ha
      obtain ⟨mi, ctor, nf, ihFields⟩ := a
      refine Sim.bind (Sim.liftExcept' (hD.subst hmsC hmots ⟨hminC.1.2.2.1, hminC.2.2⟩))
        (fun mty mty' hmty => ?_) (fun _ => by mono_auto)
      refine Sim.bind (sim_telescope' hok hmty) (fun p q hpq => ?_) (fun _ => by mono_auto)
      obtain ⟨bs, _⟩ := p
      obtain ⟨bs', _⟩ := q
      obtain ⟨hbs, -⟩ := hpq
      simp only at hbs
      have hflds := hbs.extract 0 nf
      have hihsC := hbs.extract_from nf
      refine Sim.bind (Sim.idx (R := Eq) rfl (fun _ _ _ => rfl) _ _) (fun cl cl' hcl => ?_)
        (fun _ => by mono_auto)
      subst hcl
      refine Sim.bind (R := ARel (fun p q => RE s0 d B p.1 q.1 ∧ RE s0 d B p.2 q.2))
        (Sim.forIn_array (Ra := Eq) (fun j j' cs cs' hj hcs => ?_) (fun _ _ => by mono_auto)
          (LRel.refl_eq _) ARel.empty) (fun comps comps' hcomps => ?_) (fun _ => by mono_auto)
      · subst hj
        cases hlmi : Array.findIdx? (fun lm => lm.motive == j && lm.ctor == ctor) c.minors with
        | none => exact Sim.of_fail (fun _ => ⟨_, rfl⟩)
        | some lmi =>
          refine Sim.bind (Sim.idx (R := fun l l' => l = l' ∧ l ∈ c.mins) rfl
            (fun _ h1 _ => ⟨rfl, Array.getElem_mem h1⟩) _ _) (fun lm lm' hlm => ?_) (fun _ => by mono_auto)
          obtain ⟨rfl, hlm⟩ := hlm
          have hlmty : RE s0 d B lm.type lm.type := (hc.1 lm (by simp [hlm])).2.2
          refine Sim.bind (Sim.liftRE (instForall_exrel hlmty.1 hflds.are.1)
            (fun r hr => instForall_fv hlmty.2 hflds.are.2 hr)) (fun lty lty' hlty => ?_)
            (fun _ => by mono_auto)
          rw [forallArity_ren hlty.1]
          refine Sim.bind (R := fun s s' => RE s0 d B s.1 s'.1 ∧ ARE s0 d B s.2 s'.2)
            (Sim.forIn_range _ (fun _ st st' hst => ?_) (fun _ _ => by mono_auto) ⟨hlty, ARE.empty⟩)
            (fun st st' hst => ?_) (fun _ => by mono_auto)
          · obtain ⟨hl1, hl2⟩ := hst
            have hsm := stripMdata_ren hl1.1
            have hsmf := stripMdata_fv hl1.2
            dsimp only
            generalize Ix.Compile.Canon.stripMdata st.1 = a at hsm hsmf ⊢
            generalize Ix.Compile.Canon.stripMdata st'.1 = a' at hsm hsmf ⊢
            cases hsm
            case forallE n bt bt' body body' bi hh hh' hbt hbody =>
              refine Sim.bind (sim_telescope' hok ⟨hbt, hsmf.1⟩) (fun p q hpq => ?_) (fun _ => by mono_auto)
              obtain ⟨ys, cc⟩ := p
              obtain ⟨ys', cc'⟩ := q
              obtain ⟨hys, hcc⟩ := hpq
              simp only at hys hcc
              rw [RLs.idx_eq hok hc.ms hcc]
              cases ht : Ix.Compile.Image.fvarIdx? c.ms (Ix.Compile.Image.getAppFn cc) with
              | none => exact Sim.of_fail (fun _ => ⟨_, rfl⟩)
              | some t' =>
                have harg := appArg?_rel hcc
                revert harg
                cases ha1 : Ix.Compile.Image.appArg? cc <;> cases ha2 : Ix.Compile.Image.appArg? cc' <;>
                  intro harg
                · exact Sim.of_fail (fun _ => ⟨_, rfl⟩)
                · exact harg.elim
                · exact harg.elim
                rename_i arg arg'
                dsimp only
                have hidx2 : ARE s0 d B (Ix.Compile.Image.getAppArgs cc).pop
                    (Ix.Compile.Image.getAppArgs cc').pop := (getAppArgs_rel hcc).pop
                rw [RLs.idx_eq hok hflds harg]
                cases hf : Ix.Compile.Image.fvarIdx? (bs.extract 0 nf) (Ix.Compile.Image.getAppFn arg) with
                | none => exact Sim.of_fail (fun _ => ⟨_, rfl⟩)
                | some f =>
                  dsimp only
                  cases hq : Array.findIdx? (fun x => x.fst == f) ihFields with
                  | none =>
                    dsimp only
                    refine Sim.bind (ihs t' hidx2 harg) (fun v v' hv => ?_) (fun _ => by mono_auto)
                    refine Sim.bind (Sim.pure (R := RE s0 d B) (RE.mkLambda hok hys hv)) (fun v v' hv => ?_)
                      (fun _ => by mono_auto)
                    exact Sim.pure (show StepRel _ (.yield _) (.yield _) from
                      ⟨RE.instLocals (ARE.singleton hv) ⟨hbody, hsmf.2⟩, hl2.push hv⟩)
                  | some q =>
                    dsimp only
                    refine Sim.bind (Sim.idx (R := Eq) rfl (fun _ _ _ => rfl) _ _) (fun fq fq' hfq => ?_)
                      (fun _ => by mono_auto)
                    subst hfq
                    refine Sim.bind (Sim.idx (R := Eq) rfl (fun _ _ _ => rfl) _ _) (fun cl2 cl2' hcl2 => ?_)
                      (fun _ => by mono_auto)
                    subst hcl2
                    cases hpos : cl2.idxOf? t' with
                    | none => exact Sim.of_fail (fun _ => ⟨_, rfl⟩)
                    | some pos =>
                      dsimp only
                      refine Sim.bind (Sim.idx (R := Eq) rfl (fun _ _ _ => rfl) _ _) (fun pk pk' hpk => ?_)
                        (fun _ => by mono_auto)
                      subst hpk
                      refine Sim.bind (Sim.idx (R := RL s0 d B) hihsC.1 hihsC.2 _ _) (fun l l' hl => ?_)
                        (fun _ => by mono_auto)
                      refine Sim.bind (Sim.pure (R := RE s0 d B) (RE.mkLambda hok hys
                        (RE.unwrap _ _ _ (RE.mkAppN (RL.expr hl) hys.are)))) (fun v v' hv => ?_)
                        (fun _ => by mono_auto)
                      exact Sim.pure (show StepRel _ (.yield _) (.yield _) from
                        ⟨RE.instLocals (ARE.singleton hv) ⟨hbody, hsmf.2⟩, hl2.push hv⟩)
            all_goals exact Sim.of_fail (fun _ => ⟨_, rfl⟩)
          · exact Sim.pure (show StepRel _ (.yield _) (.yield _) from
              hcs.push ⟨RE.mkAppN (hc.mins_expr hlm) (hflds.are.append hst.2), hst.1⟩)
      · refine Sim.bind (Sim.idx (R := Eq) rfl (fun _ _ _ => rfl) _ _) (fun pk pk' hpk => ?_)
          (fun _ => by mono_auto)
        subst hpk
        refine Sim.bind (Sim.liftRE (wrapVal_ren _ _ hcomps.1
            (fun i h1 h2 => ⟨(hcomps.2 i h1 h2).1.1, (hcomps.2 i h1 h2).2.1⟩))
          (fun r hr => wrapVal_fv _ _ (fun v hv => ?_) hr)) (fun w w' hw => ?_) (fun _ => by mono_auto)
        · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
          have hi' : i < comps'.size := by rw [← hcomps.1]; exact hi
          exact ⟨(hcomps.2 i hi hi').1.2, (hcomps.2 i hi hi').2.2⟩
        exact Sim.pure (show StepRel _ (.yield _) (.yield _) from
          hmns.push (RE.etaReduce (RE.mkLambda hok hbs hw)))
    refine Sim.bind (Sim.idx (R := Eq) rfl (fun _ _ _ => rfl) _ _) (fun cl cl' hcl => ?_)
      (fun _ => by mono_auto)
    subst hcl
    cases hpos : cl.idxOf? t with
    | none => exact Sim.of_fail (fun _ => ⟨_, rfl⟩)
    | some pos =>
      dsimp only
      refine Sim.bind (Sim.idx (R := Eq) rfl (fun _ _ _ => rfl) _ _) (fun pk pk' hpk => ?_)
        (fun _ => by mono_auto)
      subst hpk
      exact Sim.pure (RE.unwrap _ _ _ (RE.mkAppN ⟨Ren.mkConst' _ _, FvAll.mkConst _ _⟩
        ((((hps.append hmots).append hmins).append hidx).append (ARE.singleton hmaj))))

/-- **The relocation step from shifted counters**, at X1's core development. -/
theorem sim_buildRecAppP (hok : InjOn (shift s0 d) (FreshBelow B)) (c : LCtx) (hc : CtxRE s0 d B c)
    (hcl : EnvClosed c.const?) (fuel t : Nat) {idx idx' : Array Expr} {major major' : Expr}
    (hidx : ARE s0 d B idx idx') (hmaj : RE s0 d B major major') :
    Sim s0 d B (RE s0 d B) (buildRecAppW coreDev fuel c t idx major)
      (buildRecAppW coreDev fuel c t idx' major') :=
  sim_buildRecAppW (devRel_core hok) hok c hc hcl fuel t hidx hmaj

end

end Ix.CompileCert.Img
