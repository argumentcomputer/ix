import Ix.CompileCert.Image.Dom

/-!
# M7 L2a-syn: totality of the image construction on `Dom` (L2a-1)

Nothing below assumes the block non-nested: `Dom` is the construction's own checks, whatever the block.

* `sim_imageProgW`: the construction run twice from the initial state, with two developments the
  second of which succeeds (related) wherever the first does (`DevRel` at `d = 0`), succeeds twice;
* `imageOfW_ok_of`: so a construction that succeeds with the first development succeeds with the
  second;
* `imageOfP_total` (**L2a-1**): on `Dom`, the image construction at X1's core with its constant
  fuel `defaultFuel = 2^16` succeeds (the development returns on every call it makes,
  `devRel_dom`);
* `imageOf_total_of`: the same for the executable, given that the tabled development agrees with
  the core where the core succeeds (X1's R-1);
* `blockView_expansion_total`: in the compiler, every auxiliary of a changed block gets its
  expansion (its image on `Dom`, Lean's value for a definition or theorem) or a decline naming it.

Hypotheses beyond `Dom`: the environment's constants and recursor rules have no free variable
(`EnvClosed`, `RecRulesClosed`): they are closed terms of the kernel.
-/

namespace Ix.CompileCert.Img

open Ix (Name Level Expr ConstantInfo InductiveVal RecursorVal)
open Ix.Compile.Image (GenM GenState freshName Local telescope LCtx Elim LeanMinor ImageSpec
  GenOptions Image)
open Ix.CompileCert.Conv

section
variable {s0 d B : Nat}

theorem Sim.and {α β : Type} {R S : α → β → Prop} {x : GenM α} {y : GenM β}
    (hR : Sim s0 d B R x y) (hS : Sim s0 d B S x y) : Sim s0 d B (fun a b => R a b ∧ S a b) x y := by
  intro st st' a st1 hs h hb
  obtain ⟨b, st1', hy, hr, hs1⟩ := hR st st' a st1 hs h hb
  obtain ⟨b', st1'', hy', hs', -⟩ := hS st st' a st1 hs h hb
  rw [hy] at hy'; cases hy'
  exact ⟨b, st1', hy, ⟨hr, hs'⟩, hs1⟩

theorem shift_zero_fresh (i : Nat) : shift s0 0 (fresh i) = fresh i := by
  rw [shift_fresh]; split <;> rfl

theorem RE.zero {e : Expr} (h : FvAll (FreshBelow B) e) : RE s0 0 B e e :=
  ⟨Ren.refl_of (FvAll.mono (fun _ ⟨i, _, hi⟩ => by subst hi; exact shift_zero_fresh i) h), h⟩

theorem CtxRE.zero {c : LCtx}
    (h1 : ∀ l ∈ c.ps ++ c.ms ++ c.mins, FreshBelow B l.fvar ∧ FvAll (FreshBelow B) l.type)
    (h2 : ∀ ty ∈ c.motiveTys, FvAll (FreshBelow B) ty) : CtxRE s0 0 B c :=
  ⟨fun l hl => ⟨by obtain ⟨i, _, hi⟩ := (h1 l hl).1; rw [hi]; exact shift_zero_fresh i,
      (h1 l hl).1, RE.zero (h1 l hl).2⟩, fun ty hty => RE.zero (h2 ty hty)⟩

end

theorem mem_of_mem_extract {α : Type} {xs : Array α} {a b : Nat} {l : α} (h : l ∈ xs.extract a b) :
    l ∈ xs := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 h
  simp only [Array.getElem_extract]
  exact Array.getElem_mem _

theorem ctorOf_ok {const? : Name → Option ConstantInfo} {n : Name} {cv : Ix.ConstructorVal}
    (h : Ix.Compile.Image.ctorOf const? n = .ok cv) : const? n = some (.ctorInfo cv) := by
  unfold Ix.Compile.Image.ctorOf at h
  split at h
  · cases h; assumption
  · cases h

theorem lfv_extract {P : Name → Prop} {xs : Array Expr} {a b : Nat} (h : LFv P xs.toList) :
    LFv P (xs.extract a b).toList := fun e he =>
  h e (Array.mem_toList_iff.2 (mem_of_mem_extract (Array.mem_toList_iff.1 he)))

theorem LRel.refl_mem {α : Type} (xs : Array α) :
    LRel (fun a b => a = b ∧ a ∈ xs) xs.toList xs.toList := by
  have : ∀ l : List α, (∀ a ∈ l, a ∈ xs) → LRel (fun a b => a = b ∧ a ∈ xs) l l := by
    intro l hl
    induction l with
    | nil => exact .nil
    | cons a l ih =>
      exact .cons ⟨rfl, hl a List.mem_cons_self⟩ (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))
  exact this _ fun a ha => by simpa using ha

/-- The recursors' rules mention no free variable (as their types, `EnvClosed`). -/
def RecRulesClosed (const? : Name → Option ConstantInfo) : Prop :=
  ∀ n rv, const? n = some (.recInfo rv) → ∀ rule ∈ rv.rules, FvAll (fun _ => False) rule.rhs

theorem canonicalizeConstNames_fv {P : Name → Prop} (m : Std.HashMap Name Name) {e : Expr}
    (h : FvAll P e) : FvAll P (Ix.Compile.Canon.canonicalizeConstNames m e) :=
  fv_of_self_ren (canonicalizeConstNames_ren m (self_ren_of_fv h))

theorem tr_fv {P : Name → Prop} (spec : ImageSpec) {e : Expr} (h : FvAll P e) : FvAll P (spec.tr e) :=
  canonicalizeConstNames_fv _ h

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem sim_imageProgW {B : Nat} {D1 D2 : DevOps} (hD : DevRel 0 0 B D1 D2) {opts : GenOptions}
    {const? : Name → Option ConstantInfo} (hcl : EnvClosed const?) (hrc : RecRulesClosed const?)
    (spec : ImageSpec) (r : Name) :
    Sim 0 0 B (fun _ _ => True) (imageProgW D1 opts const? spec r) (imageProgW D2 opts const? spec r) := by
  unfold imageProgW
  refine Sim.bind (Sim.liftExcept_same _) (fun rv rv' hrv => ?_) (fun _ => by mono_auto)
  obtain ⟨rfl, hrv⟩ := hrv
  have hty : FvAll (FreshBelow B) (spec.tr rv.cnst.type) :=
    FvAll.mono (fun _ h => h.elim) (tr_fv spec (hcl _ _ (recOf_ok hrv)))
  refine Sim.bind (Sim.and (Sim.refl0 (mono_telescope _ _))
    (sim_telescope' injOn_shift_zero (RE.zero hty))) (fun p p' hp => ?_) (fun _ => by mono_auto)
  obtain ⟨rfl, hxs, hbody⟩ := hp
  obtain ⟨xs, body⟩ := p
  simp only at hxs hbody
  dsimp only
  have hxf := hxs.fv
  cases hxb : xs.back? with
  | none => exact Sim.of_fail (fun _ => ⟨_, rfl⟩)
  | some x =>
    dsimp only
    have hx : x ∈ xs := by
      rw [Array.back?_eq_getElem?] at hxb
      exact Array.mem_of_getElem? hxb
    cases hm0 : (xs.extract rv.numParams (rv.numParams + rv.numMotives))[0]? with
    | none => exact Sim.of_fail (fun _ => ⟨_, rfl⟩)
    | some m0 =>
      dsimp only
      refine Sim.bind (Sim.refl0 (Mono.mapM_array _ (fun _ => mono_analyzeLeanMinor _ _) _))
        (fun mn mn' hmn => ?_) (fun _ => by mono_auto)
      subst hmn
      cases ha0 : rv.all[0]? with
      | none => exact Sim.of_fail (fun _ => ⟨_, rfl⟩)
      | some a0 =>
        dsimp only
        refine Sim.bind (Sim.refl0 (Mono.liftExcept _)) (fun ind ind' hind => ?_) (fun _ => by mono_auto)
        subst hind
        cases ht : Ix.Compile.Image.fvarIdx? (xs.extract rv.numParams (rv.numParams + rv.numMotives))
            (Ix.Compile.Image.getAppFn body) with
        | none => exact Sim.of_fail (fun _ => ⟨_, rfl⟩)
        | some t =>
          dsimp only
          have hsub : ∀ a b, ∀ l ∈ xs.extract a b, l ∈ xs := fun a b l hl => mem_of_mem_extract hl
          have hxsf : ∀ l ∈ xs, FreshBelow B l.fvar ∧ FvAll (FreshBelow B) l.type := hxf
          have hexpr : ∀ l ∈ xs, RE 0 0 B l.expr l.expr := fun l hl => RE.zero (hxsf l hl).1
          have hlocs : ∀ a b, RLs 0 0 B (xs.extract a b) (xs.extract a b) := fun a b =>
            RLs.refl' fun l hl => by
              obtain ⟨i, _, hi⟩ := (hxsf l (hsub a b l hl)).1
              exact ⟨by rw [hi]; exact shift_zero_fresh i, (hxsf l (hsub a b l hl)).1,
                RE.zero (hxsf l (hsub a b l hl)).2⟩
          refine Sim.bind (sim_buildRecAppW hD injOn_shift_zero _ (CtxRE.zero (fun l hl => ?_)
              (fun ty hty => ?_)) hcl _ _ (ARE.iff.2 ⟨rfl, fun i h1 _ => ?_⟩) (hexpr x hx))
            (fun v v' hv => ?_) (fun _ => by mono_auto)
          · simp only [Array.mem_append] at hl
            rcases hl with (hl | hl) | hl <;> exact hxsf l (hsub _ _ l hl)
          · simp only [Array.mem_map] at hty
            obtain ⟨m, hm, rfl⟩ := hty
            exact stripSort_fv (hxsf m (hsub _ _ m hm)).2
          · simp only [Array.getElem_map]
            exact hexpr _ (hsub _ _ _ (Array.getElem_mem _))
          cases hT : Ix.Compile.Image.headConst? x.type with
          | none => exact Sim.of_fail (fun _ => ⟨_, rfl⟩)
          | some p =>
            obtain ⟨hd0, tLvls⟩ := p
            dsimp only
            refine Sim.bind (R := fun _ _ => True) (Sim.forIn_array
              (Ra := fun a b => a = b ∧ a ∈ rv.rules) (fun rule rule' rs rs' hr _ => ?_)
              (fun _ _ => by mono_auto) (LRel.refl_mem _) trivial) (fun _ _ _ => ?_)
              (fun _ => by mono_auto)
            · obtain ⟨rfl, hrule⟩ := hr
              refine Sim.bind (Sim.liftExcept_same _) (fun cv cv' hcv => ?_) (fun _ => by mono_auto)
              obtain ⟨rfl, hcv⟩ := hcv
              have hcvc := ctorOf_ok hcv
              have hTf : FvAll (FreshBelow B) x.type := (hxsf x hx).2
              have hargs : LFv (FreshBelow B) ((Ix.Compile.Image.getAppArgs x.type).extract 0 cv.numParams).toList :=
                lfv_extract (getAppFnArgs_fv hTf).2
              refine Sim.bind (Sim.liftExcept_same _) (fun cty cty' hcty => ?_) (fun _ => by mono_auto)
              obtain ⟨rfl, hcty⟩ := hcty
              have hctyf : FvAll (FreshBelow B) cty :=
                instForall_fv (substLevels_fv _ _ (FvAll.mono (fun _ h => h.elim)
                  (tr_fv spec (hcl _ _ hcvc)))) hargs hcty
              refine Sim.bind (Sim.and (Sim.refl0 (mono_telescope _ _))
                (sim_telescope' injOn_shift_zero (RE.zero hctyf))) (fun p p' hp => ?_) (fun _ => by mono_auto)
              obtain ⟨rfl, hfl, hcres⟩ := hp
              obtain ⟨flds, cres⟩ := p
              simp only at hfl hcres
              have hpmm := (hlocs 0 (rv.numParams + rv.numMotives + rv.numMinors)).exprs
              have hfle := hfl.exprs
              have hrhs : FvAll (FreshBelow B) (Ix.Compile.Canon.canonicalizeConstNames
                  (Array.foldl (fun m r => m.insert r (spec.naming.img r)) ∅
                    (Ix.Compile.Image.blockRecursors const? ind)) (spec.tr rule.rhs)) :=
                canonicalizeConstNames_fv _ (tr_fv spec (FvAll.mono (fun _ h => h.elim)
                  (hrc _ _ (recOf_ok hrv) rule hrule)))
              refine Sim.bind (Sim.liftExcept' (hD.inst (RE.zero hrhs) (ARE.append hpmm hfle)))
                (fun rhs rhs' hrh => ?_) (fun _ => by mono_auto)
              have hidxf : LFv (FreshBelow B)
                  (((Ix.Compile.Image.getAppArgs cres).extract cv.numParams).toList) :=
                lfv_extract (getAppFnArgs_fv hcres.2).2
              have hmajf : FvAll (FreshBelow B) (Ix.Compile.Canon.mkAppN
                  (Expr.mkConst (spec.trName rule.ctor) tLvls)
                  ((Ix.Compile.Image.getAppArgs x.type).extract 0 cv.numParams ++
                    Array.map (fun x => x.expr) flds)) :=
                mkAppN_fv (FvAll.mkConst _ _) (by
                  intro a ha
                  simp only [Array.toList_append, List.mem_append] at ha
                  rcases ha with ha | ha
                  · exact hargs a ha
                  · exact hfle.2 a ha)
              refine Sim.bind (Sim.liftExcept' (hD.subst ((hlocs _ _).push ⟨⟨by
                  obtain ⟨i, _, hi⟩ := (hxsf x hx).1; rw [hi]; exact (shift_zero_fresh i).symm, rfl,
                  (RE.zero (hxsf x hx).2).1, rfl⟩, (hxsf x hx).1, (hxsf x hx).2⟩)
                (ARE.iff.2 ⟨rfl, fun i h1 _ => RE.zero (by
                  simp only [Array.size_push] at h1
                  by_cases hi : i < ((Ix.Compile.Image.getAppArgs cres).extract cv.numParams).size
                  · rw [Array.getElem_push_lt hi]; exact hidxf _ (Array.mem_toList_iff.2 (Array.getElem_mem hi))
                  · have : i = ((Ix.Compile.Image.getAppArgs cres).extract cv.numParams).size := by omega
                    subst this; rw [Array.getElem_push_eq]; exact hmajf)⟩) hbody))
                (fun α α' hα => ?_) (fun _ => by mono_auto)
              exact Sim.pure (show StepRel _ (.yield _) (.yield _) from trivial)
            · refine Sim.bind Sim.get (fun _ _ _ => Sim.pure trivial) (fun _ => by mono_auto)

/-- **A construction that succeeds with one development succeeds with another** that succeeds,
related, wherever the first does. -/
theorem imageOfW_ok_of {D1 D2 : DevOps} (hD : ∀ B, DevRel 0 0 B D1 D2) {opts : GenOptions}
    {const? : Name → Option ConstantInfo} (hcl : EnvClosed const?) (hrc : RecRulesClosed const?)
    {spec : ImageSpec} {r : Name} {img : Image} (h : imageOfW D1 opts const? spec r = .ok img) :
    ∃ img', imageOfW D2 opts const? spec r = .ok img' := by
  unfold imageOfW Ix.Compile.Image.GenM.run' StateT.run' at h ⊢
  cases hr : (imageProgW D1 opts const? spec r).run {} with
  | error e =>
    have e1 : imageProgW D1 opts const? spec r {} = .error e := hr
    rw [e1] at h; cases h
  | ok p =>
    obtain ⟨img1, st2⟩ := p
    obtain ⟨b, st2', hy, -, -⟩ := sim_imageProgW (hD st2.next) hcl hrc spec r {} {} img1 st2
      ⟨rfl, rfl, Nat.le_refl _⟩ hr (Nat.le_refl _)
    have e2 : imageProgW D2 opts const? spec r {} = .ok (b, st2') := hy
    exact ⟨b, by rw [e2]; rfl⟩

/-- **L2a-1: totality on `Dom`.** For a Lean recursor `r` in `Dom` (the construction's analyses
succeed and every development it makes is in the fuel classes), the image construction at X1's
core development, with its constant fuel `2^16`, succeeds. -/
theorem imageOfP_total {opts : GenOptions} {const? : Name → Option ConstantInfo} {spec : ImageSpec}
    {r : Name} (hdom : Dom opts const? spec r) (hcl : EnvClosed const?) (hrc : RecRulesClosed const?) :
    ∃ img, imageOfP opts const? spec r = .ok img := by
  unfold Dom at hdom
  cases h : imageOfW domDev opts const? spec r with
  | error e => rw [h] at hdom; cases hdom
  | ok img => exact imageOfW_ok_of (fun _ => devRel_dom injOn_shift_zero) hcl hrc h

/-- A development that succeeds wherever the second of a related pair does is related to the
first. -/
theorem DevRel.trans_ok {s0 d B : Nat} {D1 D2 D3 : DevOps} (h : DevRel s0 d B D1 D2)
    (hs : ∀ xs vs e r, D2.subst xs vs e = .ok r → D3.subst xs vs e = .ok r)
    (hi : ∀ f args r, D2.inst f args = .ok r → D3.inst f args = .ok r) : DevRel s0 d B D1 D3 := by
  refine ⟨fun hxs hv he r hr => ?_, fun hf ha r hr => ?_⟩
  · obtain ⟨r', h1, h2⟩ := h.subst hxs hv he r hr
    exact ⟨r', hs _ _ _ _ h1, h2⟩
  · obtain ⟨r', h1, h2⟩ := h.inst hf ha r hr
    exact ⟨r', hi _ _ _ h1, h2⟩

/-- **L2a-1 for the executable**, given X1's refactor R-1 in the direction it needs: the tabled
development returns the core's result wherever the core succeeds. -/
theorem imageOf_total_of
    (hR1s : ∀ xs vs e r, substFVarsP xs vs e = .ok r → Ix.Compile.Image.substFVars xs vs e = .ok r)
    (hR1i : ∀ f args r, instantiateP f args = .ok r → Ix.Compile.Image.instantiate f args = .ok r)
    {opts : GenOptions} {const? : Name → Option ConstantInfo} {spec : ImageSpec} {r : Name}
    (hdom : Dom opts const? spec r) (hcl : EnvClosed const?) (hrc : RecRulesClosed const?) :
    ∃ img, Ix.Compile.Image.imageOf opts const? spec r = .ok img := by
  rw [imageOf_eq]
  unfold Dom at hdom
  cases h : imageOfW domDev opts const? spec r with
  | error e => rw [h] at hdom; cases hdom
  | ok img =>
    exact imageOfW_ok_of (fun _ => (devRel_dom injOn_shift_zero).trans_ok (D3 := execDev) hR1s hR1i)
      hcl hrc h

/-- **Totality in the compiler** (Pass 3's view of a changed block, `BlockView.expansion`): every
auxiliary `a` gets its expansion — its image when it is a Lean recursor in `Dom`, Lean's value when
it is a definition or a theorem — or a decline naming it, when it is neither. Given R-1 as in
`imageOf_total_of`. -/
theorem blockView_expansion_total
    (hR1s : ∀ xs vs e r, substFVarsP xs vs e = .ok r → Ix.Compile.Image.substFVars xs vs e = .ok r)
    (hR1i : ∀ f args r, instantiateP f args = .ok r → Ix.Compile.Image.instantiate f args = .ok r)
    (inp : Ix.Compile.Pass.ViewInput) (v : Ix.Compile.Pass.BlockView) (a : Name)
    (hdom : ∀ rv, inp.const? a = some (.recInfo rv) → Dom {} (v.const? inp) v.spec a)
    (hcl : EnvClosed (v.const? inp)) (hrc : RecRulesClosed (v.const? inp)) :
    (∃ x, v.expansion inp a = .ok x) ∨
      v.expansion inp a = .error s!"Pass 3: {a.pretty} has no image (not a recursor or definition)" := by
  unfold Ix.Compile.Pass.BlockView.expansion
  split
  · rename_i rv hrv
    obtain ⟨img, himg⟩ := imageOf_total_of hR1s hR1i (hdom rv hrv) hcl hrc
    left
    unfold Ix.Compile.Pass.BlockView.image
    rw [himg]
    exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · right; rfl

end Ix.CompileCert.Img
