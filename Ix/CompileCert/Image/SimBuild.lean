import Ix.CompileCert.Image.SimFind

/-!
# M7 L2a-syn: the relocation step from shifted counters

`buildRecAppW coreDev` run from a counter and from the counter shifted by `d` (with related
indices and major) returns renamed terms (`sim_buildRecAppP`).
-/

namespace Ix.CompileCert.Img

open Ix (Name Level Expr ConstantInfo InductiveVal RecursorVal)
open Ix.Compile.Image (GenM GenState freshName Local telescope LCtx Elim LeanMinor Pack)
open Ix.CompileCert.Conv

section
variable {P : Name → Prop}

/-! ## Free variables of the development's results -/

theorem liftP_fv : ∀ {e : Expr} (n c : Nat), FvAll P e → FvAll P (liftP e n c)
  | e, n, c, h => by
    unfold liftP
    split
    · exact h
    split
    · exact h
    cases e with
    | bvar i _ =>
      by_cases hi : i ≥ c <;> simp only [hi, ↓reduceIte]
      · exact FvAll.mkBVar _
      · exact h
    | app f a _ => exact ⟨liftP_fv n c h.1, liftP_fv n c h.2⟩
    | lam _ t b _ _ => exact ⟨liftP_fv n c h.1, liftP_fv n (c + 1) h.2⟩
    | forallE _ t b _ _ => exact ⟨liftP_fv n c h.1, liftP_fv n (c + 1) h.2⟩
    | letE _ t v b _ _ => exact ⟨liftP_fv n c h.1, liftP_fv n c h.2.1, liftP_fv n (c + 1) h.2.2⟩
    | proj _ _ s _ => exact liftP_fv (e := s) n c h
    | mdata _ x _ => exact liftP_fv (e := x) n c h
    | fvar | mvar | sort | const | lit => exact h

theorem lowerP_fv : ∀ {e : Expr} (n c : Nat), FvAll P e → FvAll P (lowerP e n c)
  | e, n, c, h => by
    unfold lowerP
    split
    · exact h
    split
    · exact h
    cases e with
    | bvar i _ =>
      by_cases hi : i ≥ c + n <;> simp only [hi, ↓reduceIte]
      · exact FvAll.mkBVar _
      · exact h
    | app f a _ => exact ⟨lowerP_fv n c h.1, lowerP_fv n c h.2⟩
    | lam _ t b _ _ => exact ⟨lowerP_fv n c h.1, lowerP_fv n (c + 1) h.2⟩
    | forallE _ t b _ _ => exact ⟨lowerP_fv n c h.1, lowerP_fv n (c + 1) h.2⟩
    | letE _ t v b _ _ => exact ⟨lowerP_fv n c h.1, lowerP_fv n c h.2.1, lowerP_fv n (c + 1) h.2.2⟩
    | proj _ _ s _ => exact lowerP_fv (e := s) n c h
    | mdata _ x _ => exact lowerP_fv (e := x) n c h
    | fvar | mvar | sort | const | lit => exact h

theorem projCtor?_fv {s : Name} {i : Nat} {e f : Expr} (h : Ix.Compile.Image.projCtor? s i e = some f)
    (he : FvAll P e) : FvAll P f := by
  unfold Ix.Compile.Image.projCtor? at h
  have hg := getAppFnArgs_fv he
  generalize Ix.Compile.Canon.getAppFnArgs e = p at h hg
  obtain ⟨hd, args⟩ := p
  simp only at h hg
  split at h
  · split at h
    · exact hg.2 f (by
        simp only [Array.mem_toList_iff]
        exact Array.mem_of_getElem? h)
    · cases h
  · cases h

theorem lfv_of_mapM {fuel : Nat} {v : Expr} {k : Nat}
    (IH : ∀ e r c, hinstP fuel v k e = .ok (r, c) → FvAll P e → FvAll P r) :
    ∀ {l l' : List Expr}, EForall2 (fun a b => (Prod.fst <$> hinstP fuel v k a) = .ok b) l l' →
      LFv P l → LFv P l'
  | [], [], .nil, _ => fun _ hx => by cases hx
  | a :: _, _ :: _, .cons hab hs, hl => by
    obtain ⟨⟨b', cb⟩, hb, rfl⟩ := map_ok hab
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact IH _ _ _ hb (hl a List.mem_cons_self)
    · exact lfv_of_mapM IH hs (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x hx

theorem develop_fv : ∀ fuel : Nat,
    (∀ v k e r c, hinstP fuel v k e = .ok (r, c) → FvAll P v → FvAll P e → FvAll P r) ∧
    (∀ f args r, happP fuel f args = .ok r → FvAll P f → LFv P args → FvAll P r)
  | 0 => ⟨fun v k e r c h => (by rw [hinstP_zero] at h; cases h),
          fun f args r h => (by rw [happP_zero] at h; cases h)⟩
  | fuel + 1 => by
    have IH := develop_fv fuel
    refine ⟨fun v k e r c h hv he => ?_, fun f args r h hf ha => ?_⟩
    · unfold hinstP at h
      by_cases hr : looseRangeP e ≤ k
      · simp only [hr, ↓reduceIte] at h
        cases pure_ok h; exact he
      simp only [hr, ↓reduceIte] at h
      match e, h, he with
      | .bvar i _, h, he =>
        by_cases hik : i = k
        · subst hik
          simp only [beq_self_eq_true, ↓reduceIte] at h
          cases pure_ok h; exact liftP_fv _ _ hv
        · have hik' : (i == k) = false := by simp [hik]
          simp only [hik', Bool.false_eq_true, ↓reduceIte] at h
          by_cases hgt : i > k
          · simp only [hgt, ↓reduceIte] at h
            cases pure_ok h; exact FvAll.mkBVar _
          · simp only [hgt, ↓reduceIte] at h
            cases pure_ok h; exact he
      | .app f₀ a₀ hh, h, he =>
        obtain ⟨args', hargs, h⟩ := bind_ok h
        obtain ⟨⟨h', c'⟩, hh', h⟩ := bind_ok h
        have hg := getAppFnArgs_fv he
        have hA : LFv P args' := lfv_of_mapM (fun e r c h1 h2 => IH.1 v k e r c h1 hv h2)
          (mapM_ok hargs) hg.2
        have hH := IH.1 v k _ _ _ hh' hv hg.1
        have hA' : LFv P args'.toArray.toList := by simpa using hA
        dsimp only at h
        split at h
        · cases pure_ok h; exact mkAppN_fv hH hA'
        · obtain ⟨r', hr', h⟩ := bind_ok h
          cases pure_ok h; exact IH.2 _ _ _ hr' hH hA
        · cases pure_ok h; exact mkAppN_fv hH hA'
      | .proj s i x hh, h, he =>
        obtain ⟨⟨x', c'⟩, hx, h⟩ := bind_ok h
        have hX : FvAll P x' := IH.1 v k x x' c' hx hv he
        dsimp only at h
        split at h
        · cases pure_ok h; exact FvAll.mkProj s i hX
        · split at h
          · rename_i f hf
            cases pure_ok h; exact projCtor?_fv hf hX
          · cases pure_ok h; exact FvAll.mkProj s i hX
      | .lam n t b bi hh, h, he =>
        obtain ⟨⟨t', ct⟩, ht, h⟩ := bind_ok h
        obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
        have hT : FvAll P t' := IH.1 v k t t' ct ht hv he.1
        have hB : FvAll P b' := IH.1 v (k + 1) b b' cb hb hv he.2
        dsimp only at h
        split at h
        · rename_i f hb0 hf0
          split at h
          · cases pure_ok h
            exact lowerP_fv _ _ hB.1
          · cases pure_ok h; exact FvAll.mkLam n bi hT hB
        · cases pure_ok h; exact FvAll.mkLam n bi hT hB
      | .forallE n t b bi hh, h, he =>
        obtain ⟨⟨t', ct⟩, ht, h⟩ := bind_ok h
        obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
        cases pure_ok h
        exact FvAll.mkForallE n bi (IH.1 v k t t' ct ht hv he.1) (IH.1 v (k + 1) b b' cb hb hv he.2)
      | .letE n t x b nd hh, h, he =>
        obtain ⟨⟨t', ct⟩, ht, h⟩ := bind_ok h
        obtain ⟨⟨x', cx⟩, hx, h⟩ := bind_ok h
        obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
        cases pure_ok h
        exact FvAll.mkLetE n nd (IH.1 v k t t' ct ht hv he.1) (IH.1 v k x x' cx hx hv he.2.1)
          (IH.1 v (k + 1) b b' cb hb hv he.2.2)
      | .mdata md x hh, h, he =>
        obtain ⟨⟨x', cx⟩, hx, h⟩ := bind_ok h
        cases pure_ok h
        exact FvAll.mkMData md (IH.1 v k x x' cx hx hv he)
      | .fvar .., h, he | .mvar .., h, he | .sort .., h, he | .const .., h, he | .lit .., h, he =>
        cases pure_ok h; exact he
    · rw [happP_succ] at h
      split at h
      · obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
        exact IH.2 _ _ _ h (IH.1 _ _ _ _ _ hb (ha _ List.mem_cons_self) hf.2)
          (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      · cases pure_ok h
        exact mkAppN_fv hf (by simpa using ha)

theorem substFVarsP_fv {xs : Array Name} {vs : Array Expr} {e r : Expr}
    (h : substFVarsP xs vs e = .ok r) (he : FvAll P e) (hv : LFv P vs.toList) : FvAll P r := by
  unfold substFVarsP at h
  split at h
  · cases h
  · have hab := abstractFVars_fv xs he
    generalize Ix.Compile.Image.abstractFVars xs e = acc at hab h
    have hl : LFv P vs.toList.reverse := fun x hx => hv x (List.mem_reverse.1 hx)
    generalize vs.toList.reverse = l at hl h
    induction l generalizing acc with
    | nil => cases h; exact hab
    | cons v l ih =>
      rw [List.foldlM_cons] at h
      obtain ⟨acc', h1, h2⟩ := bind_ok h
      obtain ⟨⟨a, c⟩, ha, rfl⟩ := map_ok h1
      exact ih _ ((develop_fv _).1 _ _ _ _ _ ha (hl v List.mem_cons_self) hab)
        (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h2

theorem instantiateP_fv {f r : Expr} {args : Array Expr} (h : instantiateP f args = .ok r)
    (hf : FvAll P f) (ha : LFv P args.toList) : FvAll P r := by
  unfold instantiateP at h
  exact (develop_fv _).2 _ _ _ h hf ha

end

/-! ## Free variables through the renaming lemmas

A renaming that fixes exactly the names satisfying `P` relates a term to itself exactly when its
free variables satisfy `P`; so every renaming lemma is also a free-variable lemma. -/

open Classical in
/-- The renaming that fixes exactly the names satisfying `P`. -/
noncomputable def rhoP (P : Name → Prop) (n : Name) : Name := if P n then n else .str n "" default

theorem str_ne_self (n : Name) (s : String) (h : Address) : Name.str n s h ≠ n := by
  intro e
  have := congrArg sizeOf e
  simp only [Ix.Name.str.sizeOf_spec] at this
  omega

theorem rhoP_eq {P : Name → Prop} (n : Name) : rhoP P n = n ↔ P n := by
  unfold rhoP
  by_cases h : P n
  · simp [h]
  · simp only [h, ↓reduceIte, iff_false]; exact str_ne_self _ _ _

theorem Ren.fix_fv {ρ : Name → Name} : ∀ {a b : Expr}, Ren ρ a b → a = b → FvAll (fun n => ρ n = n) a
  | _, _, .bvar .., _ | _, _, .mvar .., _ | _, _, .sort .., _ | _, _, .const .., _
  | _, _, .lit .., _ => trivial
  | _, _, .fvar n _ _, e => (Expr.fvar.inj e).1.symm
  | _, _, .app _ _ h1 h2, e => by
    injection e with e1 e2; exact ⟨Ren.fix_fv h1 e1, Ren.fix_fv h2 e2⟩
  | _, _, .lam _ _ _ _ h1 h2, e => by
    injection e with e0 e1 e2; exact ⟨Ren.fix_fv h1 e1, Ren.fix_fv h2 e2⟩
  | _, _, .forallE _ _ _ _ h1 h2, e => by
    injection e with e0 e1 e2; exact ⟨Ren.fix_fv h1 e1, Ren.fix_fv h2 e2⟩
  | _, _, .letE _ _ _ _ h1 h2 h3, e => by
    injection e with e0 e1 e2 e3
    exact ⟨Ren.fix_fv h1 e1, Ren.fix_fv h2 e2, Ren.fix_fv h3 e3⟩
  | _, _, .mdata _ _ _ h1, e => by injection e with e0 e1; have := Ren.fix_fv h1 e1; exact this
  | _, _, .proj _ _ _ _ h1, e => by injection e with e0 e1 e2; have := Ren.fix_fv h1 e2; exact this

theorem fv_of_self_ren {P : Name → Prop} {a : Expr} (h : Ren (rhoP P) a a) : FvAll P a :=
  FvAll.mono (fun n hn => (rhoP_eq n).1 hn) (Ren.fix_fv h rfl)

theorem self_ren_of_fv {P : Name → Prop} {a : Expr} (h : FvAll P a) : Ren (rhoP P) a a :=
  Ren.refl_of (FvAll.mono (fun n hn => (rhoP_eq n).2 hn) h)

theorem LRen.self_of_lfv {P : Name → Prop} : ∀ {as : List Expr}, LFv P as → LRen (rhoP P) as as
  | [], _ => .nil
  | _ :: _, h => .cons (self_ren_of_fv (h _ List.mem_cons_self))
      (LRen.self_of_lfv fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem wrapTy_fv {P : Name → Prop} (p : Ix.Compile.Image.Pack) (lu : Level) {tys : Array Expr}
    (h : LFv P tys.toList) {r : Expr} (hr : Ix.Compile.Image.wrapTy p lu tys = .ok r) : FvAll P r := by
  have := wrapTy_ren (ρ := rhoP P) p lu (LRen.self_of_lfv h)
  rw [hr] at this
  exact fv_of_self_ren this

theorem wrapVal_fv {P : Name → Prop} (p : Ix.Compile.Image.Pack) (lu : Level) {vs : Array (Expr × Expr)}
    (h : ∀ v ∈ vs, FvAll P v.1 ∧ FvAll P v.2) {r : Expr}
    (hr : Ix.Compile.Image.wrapVal p lu vs = .ok r) : FvAll P r := by
  have := wrapVal_ren (ρ := rhoP P) p lu rfl (vs := vs) (fun i h1 _ =>
    ⟨self_ren_of_fv (h _ (Array.getElem_mem h1)).1, self_ren_of_fv (h _ (Array.getElem_mem h1)).2⟩)
  rw [hr] at this
  exact fv_of_self_ren this

theorem unwrap_fv {P : Name → Prop} (p : Ix.Compile.Image.Pack) (lz : Bool) (pos : Nat) {v : Expr}
    (h : FvAll P v) : FvAll P (Ix.Compile.Image.unwrap p lz pos v) :=
  fv_of_self_ren (unwrap_ren p lz pos (self_ren_of_fv h))

/-! ## The relations of the two runs, through the construction's operations -/

section
variable {s0 d B : Nat}

theorem ARE.iff {xs ys : Array Expr} : ARE s0 d B xs ys ↔ ARel (RE s0 d B) xs ys := by
  refine ⟨fun h => ⟨h.size, fun i h1 h2 => h.get i h1 h2⟩, fun h => ⟨?_, ?_⟩⟩
  · unfold ARen
    apply (LRel.of_getElem (R := Ren (shift s0 d)) _ _ (by simp [h.1]) fun i h1 h2 => ?_).rec
      (motive := fun l l' _ => LRen (shift s0 d) l l') .nil (fun hab _ ih => .cons hab ih)
    simp only [Array.getElem_toList]
    simp only [Array.length_toList] at h1 h2
    exact (h.2 i h1 h2).1
  · intro x hx
    simp only [Array.mem_toList_iff] at hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    exact (h.2 i hi (by rw [← h.1]; exact hi)).2

theorem ARE.empty : ARE s0 d B #[] #[] := ⟨.nil, fun x hx => by simp at hx⟩

theorem ARE.push {xs ys : Array Expr} (h : ARE s0 d B xs ys) {a b : Expr} (hab : RE s0 d B a b) :
    ARE s0 d B (xs.push a) (ys.push b) := ARE.iff.2 ((ARE.iff.1 h).push hab)

theorem ARE.pop {xs ys : Array Expr} (h : ARE s0 d B xs ys) : ARE s0 d B xs.pop ys.pop :=
  ARE.iff.2 (ARE.iff.1 h).pop

theorem ARE.append {xs ys xs' ys' : Array Expr} (h : ARE s0 d B xs ys) (h' : ARE s0 d B xs' ys') :
    ARE s0 d B (xs ++ xs') (ys ++ ys') := by
  refine ⟨?_, ?_⟩
  · unfold ARen; simp only [Array.toList_append]; exact LRen.append h.1 h'.1
  · intro x hx
    simp only [Array.toList_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact h.2 x hx
    · exact h'.2 x hx

theorem ARE.singleton {a b : Expr} (h : RE s0 d B a b) : ARE s0 d B #[a] #[b] := ARE.empty.push h

theorem RE.mkAppN {f f' : Expr} {as as' : Array Expr} (hf : RE s0 d B f f') (ha : ARE s0 d B as as') :
    RE s0 d B (Ix.Compile.Canon.mkAppN f as) (Ix.Compile.Canon.mkAppN f' as') :=
  ⟨mkAppN_ren hf.1 ha.1, mkAppN_fv hf.2 ha.2⟩

theorem RE.etaReduce {a b : Expr} (h : RE s0 d B a b) :
    RE s0 d B (Ix.Compile.Image.etaReduce a) (Ix.Compile.Image.etaReduce b) :=
  ⟨etaReduce_ren h.1, etaReduce_fv h.2⟩

theorem RE.unwrap (p : Ix.Compile.Image.Pack) (lz : Bool) (pos : Nat) {a b : Expr} (h : RE s0 d B a b) :
    RE s0 d B (Ix.Compile.Image.unwrap p lz pos a) (Ix.Compile.Image.unwrap p lz pos b) :=
  ⟨unwrap_ren p lz pos h.1, unwrap_fv p lz pos h.2⟩

theorem RE.mkLambda (hok : InjOn (shift s0 d) (FreshBelow B)) {xs ys : Array Local} (hxs : RLs s0 d B xs ys) {a b : Expr}
    (h : RE s0 d B a b) : RE s0 d B (Ix.Compile.Image.mkLambda xs a) (Ix.Compile.Image.mkLambda ys b) :=
  ⟨mkLambda_ren hok hxs.lsRen hxs.fv h.1 h.2,
    mkBinders_fv true xs (fun l hl => (hxs.fv l hl).2) h.2⟩

theorem RE.instLocals {as bs : Array Expr} (hab : ARE s0 d B as bs) {a b : Expr} (h : RE s0 d B a b) :
    RE s0 d B (Ix.Compile.Image.instLocals a as) (Ix.Compile.Image.instLocals b bs) :=
  ⟨instLocals_ren hab.1 h.1, instLocals_fv hab.2 h.2⟩

theorem RLs.are {xs ys : Array Local} (h : RLs s0 d B xs ys) :
    ARE s0 d B (xs.map (·.expr)) (ys.map (·.expr)) := h.exprs

theorem RLs.fvars {xs ys : Array Local} (h : RLs s0 d B xs ys) :
    ys.map (·.fvar) = (xs.map (·.fvar)).map (shift s0 d) := by
  apply Array.ext (by simp [h.1])
  intro i h1 h2
  simp only [Array.getElem_map]
  simp only [Array.size_map] at h1 h2
  exact (h.2 i h2 h1).1.1

/-- A development step of the two runs, as an `RE`-relation of the results. -/
theorem Sim.liftRE {x y : Except String Expr} (h : ExRel (Ren (shift s0 d)) x y)
    (hf : ∀ r, x = .ok r → FvAll (FreshBelow B) r) :
    Sim s0 d B (RE s0 d B) (Ix.Compile.Image.liftExcept x) (Ix.Compile.Image.liftExcept y) := by
  apply Sim.liftExcept
  cases x with
  | error e => cases y <;> simp_all [ExRel]
  | ok a =>
    cases y with
    | error e => simp_all [ExRel]
    | ok b => exact ⟨h, hf a rfl⟩

/-! ## Loops over ranges and `mapM` -/

theorem Mono.forIn'_list {α β : Type} : ∀ (l : List α) (f : (a : α) → a ∈ l → β → GenM (ForInStep β)),
    (∀ a h b, Mono (f a h b)) → ∀ b, Mono (forIn' l b f)
  | [], f, _, b => by simp only [List.forIn'_nil]; exact Mono.pure b
  | a :: l, f, hf, b => by
    simp only [List.forIn'_cons]
    refine Mono.bind (hf a _ b) fun r => ?_
    cases r with
    | done b' => exact Mono.pure b'
    | yield b' => exact Mono.forIn'_list l _ (fun a h b => hf a _ b) b'

theorem Mono.forIn'_range {β : Type} (r : Std.Legacy.Range)
    (f : (a : Nat) → a ∈ r → β → GenM (ForInStep β)) (hf : ∀ a h b, Mono (f a h b)) (b : β) :
    Mono (forIn' r b f) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact Mono.forIn'_list _ _ (fun a h b => hf a _ b) b

theorem Mono.forIn_range {β : Type} (r : Std.Legacy.Range) (f : Nat → β → GenM (ForInStep β))
    (hf : ∀ a b, Mono (f a b)) (b : β) : Mono (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact Mono.forIn_list hf _ b

theorem Mono.mapM_list {α β : Type} (f : α → GenM β) (hf : ∀ a, Mono (f a)) :
    ∀ (l : List α), Mono (l.mapM f)
  | [] => by simp only [List.mapM_nil]; exact Mono.pure _
  | a :: l => by
    simp only [List.mapM_cons]
    exact Mono.bind (hf a) fun b => Mono.bind (Mono.mapM_list f hf l) fun bs => Mono.pure _

theorem Mono.mapM_array {α β : Type} (f : α → GenM β) (hf : ∀ a, Mono (f a)) (xs : Array α) :
    Mono (xs.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact Mono.bind (Mono.mapM_list f hf _) fun _ => Mono.pure _

theorem Sim.forIn'_list {α β δ : Type} {R : β → δ → Prop} :
    ∀ (l : List α) (f : (a : α) → a ∈ l → β → GenM (ForInStep β))
      (g : (a : α) → a ∈ l → δ → GenM (ForInStep δ)),
    (∀ a h b b', R b b' → Sim s0 d B (StepRel R) (f a h b) (g a h b')) →
    (∀ a h b, Mono (f a h b)) → ∀ {b : β} {b' : δ}, R b b' → Sim s0 d B R (forIn' l b f) (forIn' l b' g)
  | [], f, g, _, _, b, b', h => by simp only [List.forIn'_nil]; exact Sim.pure h
  | a :: l, f, g, hfg, hm, b, b', h => by
    simp only [List.forIn'_cons]
    refine Sim.bind (hfg a _ b b' h) (fun r r' hr => ?_) (fun r => ?_)
    · cases r <;> cases r' <;> simp only [StepRel] at hr
      · exact Sim.pure hr
      · exact Sim.forIn'_list l _ _ (fun a h b b' hb => hfg a _ b b' hb) (fun a h b => hm a _ b) hr
    · cases r with
      | done b'' => exact Mono.pure b''
      | yield b'' => exact Mono.forIn'_list l _ (fun a h b => hm a _ b) b''

theorem Sim.forIn'_range {β δ : Type} {R : β → δ → Prop} (r : Std.Legacy.Range)
    (f : (a : Nat) → a ∈ r → β → GenM (ForInStep β)) (g : (a : Nat) → a ∈ r → δ → GenM (ForInStep δ))
    (hfg : ∀ a h b b', R b b' → Sim s0 d B (StepRel R) (f a h b) (g a h b'))
    (hm : ∀ a h b, Mono (f a h b)) {b : β} {b' : δ} (h : R b b') :
    Sim s0 d B R (forIn' r b f) (forIn' r b' g) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact Sim.forIn'_list _ _ _ (fun a h b b' hb => hfg a _ b b' hb) (fun a h b => hm a _ b) h

theorem Sim.forIn_range {β δ : Type} {R : β → δ → Prop} (r : Std.Legacy.Range)
    {f : Nat → β → GenM (ForInStep β)} {g : Nat → δ → GenM (ForInStep δ)}
    (hfg : ∀ a b b', R b b' → Sim s0 d B (StepRel R) (f a b) (g a b'))
    (hm : ∀ a b, Mono (f a b)) {b : β} {b' : δ} (h : R b b') :
    Sim s0 d B R (forIn r b f) (forIn r b' g) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact Sim.forIn_list (Ra := Eq) (fun a c b b' hac hb => by subst hac; exact hfg a b b' hb) hm
    (LRel.refl_eq _) h

theorem Sim.mapM_list {α γ β δ : Type} {Ra : α → γ → Prop} {R : β → δ → Prop}
    {f : α → GenM β} {g : γ → GenM δ} (hfg : ∀ a c, Ra a c → Sim s0 d B R (f a) (g c))
    (hm : ∀ a, Mono (f a)) : ∀ {l : List α} {l' : List γ}, LRel Ra l l' →
      Sim s0 d B (LRel R) (l.mapM f) (l'.mapM g)
  | [], [], .nil => by simp only [List.mapM_nil]; exact Sim.pure .nil
  | a :: l, c :: l', .cons hac hl => by
    simp only [List.mapM_cons]
    exact Sim.bind (hfg a c hac) (fun b b' hb => Sim.bind (Sim.mapM_list hfg hm hl)
      (fun bs bs' hbs => Sim.pure (.cons hb hbs)) (fun _ => Mono.pure _))
      (fun b => Mono.bind (Mono.mapM_list f hm l) fun _ => Mono.pure _)

theorem Sim.mapM_array {α γ β δ : Type} {Ra : α → γ → Prop} {R : β → δ → Prop}
    {f : α → GenM β} {g : γ → GenM δ} (hfg : ∀ a c, Ra a c → Sim s0 d B R (f a) (g c))
    (hm : ∀ a, Mono (f a)) {xs : Array α} {ys : Array γ} (h : LRel Ra xs.toList ys.toList) :
    Sim s0 d B (fun as bs => LRel R as.toList bs.toList) (xs.mapM f) (ys.mapM g) := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  exact Sim.bind (Sim.mapM_list hfg hm h) (fun bs bs' hbs => Sim.pure (by simpa using hbs))
    (fun _ => Mono.pure _)

theorem LRel.arel {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β}, LRel R l l' →
    ARel R l.toArray l'.toArray := by
  intro l l' h
  induction h with
  | nil => exact ⟨rfl, fun i h => by simp at h⟩
  | @cons a b as bs hab _ ih =>
    have hl : as.length = bs.length := by simpa using ih.1
    refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
    cases i with
    | zero => simpa using hab
    | succ i =>
      have := ih.2 i (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega)
      simpa using this

theorem ARE.of_lrel {xs ys : Array Expr} (h : LRel (RE s0 d B) xs.toList ys.toList) : ARE s0 d B xs ys :=
  ARE.iff.2 (by simpa using h.arel)

end

end Ix.CompileCert.Img
