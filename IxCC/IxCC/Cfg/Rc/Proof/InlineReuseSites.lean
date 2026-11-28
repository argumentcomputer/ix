import IxCC.Cfg.Rc.Proof.InlineSharedSites
import IxCC.X86.Memory

/-! # Single-site and fused-pair operational equivalence for Track A4 (`reset`/`reuse`)

Proves exact operational equivalence (with zero heap invariant) between the raw
`mkResetWrapper` / `mkResetUWrapper` / `mkReuseWrapper` / `mkReuseUWrapper` calls
and the inlined fast-path / fused-pair expansions in `Cfg.Rc.Inline`. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Inline

open IxCC.Cfg.Rc.Native

theorem reaches_of_star_reuse {σ α : Type} {st : σ → Sem.Step σ α} {s s' : σ} {c k : Nat}
    {r : Sem.Result α} (hstar : Sem.Star st s c s') (hr : Sem.Reaches st s' k r) :
    Sem.Reaches st s (c + k) r := by
  induction hstar with
  | refl => simpa using hr
  | free hs _ ih => exact .free hs (ih hr)
  | charge hs _ ih =>
    have := Sem.Reaches.charge hs (ih hr)
    rwa [Nat.add_right_comm] at this

theorem star_zero_split {σ α : Type} {st : σ → Sem.Step σ α} {s₁ s₂ : σ}
    (h : Sem.Star st s₁ 0 s₂) (hne : s₁ ≠ s₂) :
    ∃ s', st s₁ = .next s' false ∧ Sem.Star st s' 0 s₂ := by
  generalize hc : (0 : Nat) = c at h
  cases h with
  | refl => exact absurd rfl hne
  | free hs htail => subst hc; exact ⟨_, hs, htail⟩
  | charge _ _ => omega

theorem reaches_cast {σ α : Type} {st : σ → Sem.Step σ α} {s : σ} {k k' : Nat} {r : Sem.Result α}
    (h : Sem.Reaches st s k r) (hk : k = k') : Sem.Reaches st s k' r := hk ▸ h

theorem star_cast {σ α : Type} {st : σ → Sem.Step σ α} {s s' : σ} {c c' : Nat}
    (h : Sem.Star st s c s') (hc : c = c') : Sem.Star st s c' s' := hc ▸ h

/-- Index past a prefix of known length. -/
theorem getElem?_append_right_add {α : Type} (pre t : List α) {n : Nat} (k : Nat)
    (hn : pre.length = n) : (pre ++ t)[n + k]? = t[k]? := by
  rw [List.getElem?_append_right (by omega), hn, Nat.add_sub_cancel_left]

/-- Transport a block lookup along an index equation (stated at `Nat`, for `omega`). -/
theorem blocks_idx_cast {F : Lir.Func} {i j : Nat} {blk : Lir.Block}
    (h : F.blocks[i]? = some blk) (hij : i = j) : F.blocks[j]? = some blk := hij ▸ h

/-- A lookup that succeeds is in range. -/
theorem lt_length_of_getElem?_eq_some {α : Type} {xs : List α} {k : Nat} {a : α}
    (h : xs[k]? = some a) : k < xs.length := by
  rcases Nat.lt_or_ge k xs.length with hlt | hge
  · exact hlt
  · rw [List.getElem?_eq_none hge] at h; cases h

/-! ## Runtime lookup helpers on `inlineProgram l raw` -/

theorem inlineProgram_resetWrap (l : Layout) (p : Lir.Program) (hr : RuntimeFuncs l p)
    {i : Nat} {c : Lam.CtorInfo} {cls : Nat}
    (hc : l.ctors[i]? = some c)
    (hcls : (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? = some cls) :
    (inlineProgram l p).funcs[l.resetWrapper i]? =
      some (mkResetWrapper l.isUniqueProc l.incProc l.decProc
        (Rt.Rc.CellLayout.ofFields c.arity c.tag) cls) := by
  rw [inlineProgram_get_ge l p (by simp [Layout.resetWrapper, Layout.init, Layout.incProc]; omega)]
  exact hr.resetWrap i c cls hc hcls

theorem inlineProgram_reuseWrap (l : Layout) (p : Lir.Program) (hr : RuntimeFuncs l p)
    {i : Nat} {c : Lam.CtorInfo} {cls : Nat}
    (hc : l.ctors[i]? = some c)
    (hcls : (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? = some cls) :
    (inlineProgram l p).funcs[l.reuseWrapper i]? =
      some (mkReuseWrapper (l.allocProc i)
        (Rt.Rc.CellLayout.ofFields c.arity c.tag) cls) := by
  rw [inlineProgram_get_ge l p (by simp [Layout.reuseWrapper, Layout.init, Layout.incProc]; omega)]
  exact hr.reuseWrap i c cls hc hcls

/-! ## Inversion lemmas for `classify` (reuse sites) and `classifyPair` -/

private theorem classify_inc_ne {dst : Lir.VReg} {as : List Lir.Arg} {site : RcSite}
    (hne : ∀ d x, site ≠ .inc d x) :
    (match as with | [.v x, .imm _] => some (RcSite.inc dst x) | _ => none) ≠ some site := by
  cases as with
  | nil => intro h; cases h
  | cons a1 as1 =>
    cases a1 with
    | imm _ => intro h; cases h
    | v x =>
      cases as1 with
      | nil => intro h; cases h
      | cons a2 as2 =>
        cases a2 with
        | v _ => intro h; cases h
        | imm _ =>
          cases as2 with
          | cons _ _ => intro h; cases h
          | nil => intro h; cases h; exact hne dst x rfl

private theorem classify_dec_ne {dst : Lir.VReg} {as : List Lir.Arg} {site : RcSite}
    (hne : ∀ d x, site ≠ .dec d x) :
    (match as with | [.v x] => some (RcSite.dec dst x) | _ => none) ≠ some site := by
  cases as with
  | nil => intro h; cases h
  | cons a1 as1 =>
    cases a1 with
    | imm _ => intro h; cases h
    | v x =>
      cases as1 with
      | cons _ _ => intro h; cases h
      | nil => intro h; cases h; exact hne dst x rfl

private theorem classify_alloc_ne {l : Layout} {dst : Lir.VReg} {f : Lir.FunId} {as : List Lir.Arg}
    {site : RcSite} (hne : ∀ d i lay cls a, site ≠ .alloc d i lay cls a) :
    (match l.ctors[f - l.allocWrapper 0]? with
     | some c =>
       match (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
       | some cls =>
         if as.length == c.arity && (Rt.Rc.CellLayout.ofFields c.arity c.tag).ok && !argsContainVReg dst as then
           some (RcSite.alloc dst (f - l.allocWrapper 0) (Rt.Rc.CellLayout.ofFields c.arity c.tag) cls as)
         else none
       | none => none
     | none => none) ≠ some site := by
  intro h
  cases hc : l.ctors[f - l.allocWrapper 0]? with
  | none => simp [hc] at h
  | some c =>
    simp only [hc] at h
    cases hcls : (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
    | none => simp [hcls] at h
    | some cls =>
      simp only [hcls] at h
      split at h
      · cases h; exact hne _ _ _ _ _ rfl
      · cases h

private theorem classify_reset_ne {l : Layout} {dst : Lir.VReg} {f : Lir.FunId} {as : List Lir.Arg}
    {site : RcSite} (hne : ∀ d x i lay cls m, site ≠ .reset d x i lay cls m) :
    (match l.ctors[f - l.resetWrapper 0]?, as with
     | some c, [.v x, .imm mask] =>
       match (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
       | some cls =>
         if (Rt.Rc.CellLayout.ofFields c.arity c.tag).ok && dst != x then
           some (RcSite.reset dst x (f - l.resetWrapper 0) (Rt.Rc.CellLayout.ofFields c.arity c.tag) cls mask)
         else none
       | none => none
     | _, _ => none) ≠ some site := by
  intro h
  cases hc : l.ctors[f - l.resetWrapper 0]? with
  | none => simp [hc] at h
  | some c =>
    cases as with
    | nil => simp [hc] at h
    | cons a1 as1 =>
      cases a1 with
      | imm _ => simp [hc] at h
      | v x =>
        cases as1 with
        | nil => simp [hc] at h
        | cons a2 as2 =>
          cases a2 with
          | v _ => simp [hc] at h
          | imm mask =>
            cases as2 with
            | cons _ _ => simp [hc] at h
            | nil =>
              simp only [hc] at h
              cases hcls : (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
              | none => simp [hcls] at h
              | some cls =>
                simp only [hcls] at h
                split at h
                · cases h; exact hne _ _ _ _ _ _ rfl
                · cases h

private theorem classify_resetU_ne {l : Layout} {dst : Lir.VReg} {f : Lir.FunId} {as : List Lir.Arg}
    {site : RcSite} (hne : ∀ d x i lay cls m, site ≠ .resetU d x i lay cls m) :
    (match l.ctors[f - l.resetUWrapper 0]?, as with
     | some c, [.v x, .imm mask] =>
       match (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
       | some cls =>
         if (Rt.Rc.CellLayout.ofFields c.arity c.tag).ok && dst != x then
           some (RcSite.resetU dst x (f - l.resetUWrapper 0) (Rt.Rc.CellLayout.ofFields c.arity c.tag) cls mask)
         else none
       | none => none
     | _, _ => none) ≠ some site := by
  intro h
  cases hc : l.ctors[f - l.resetUWrapper 0]? with
  | none => simp [hc] at h
  | some c =>
    cases as with
    | nil => simp [hc] at h
    | cons a1 as1 =>
      cases a1 with
      | imm _ => simp [hc] at h
      | v x =>
        cases as1 with
        | nil => simp [hc] at h
        | cons a2 as2 =>
          cases a2 with
          | v _ => simp [hc] at h
          | imm mask =>
            cases as2 with
            | cons _ _ => simp [hc] at h
            | nil =>
              simp only [hc] at h
              cases hcls : (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
              | none => simp [hcls] at h
              | some cls =>
                simp only [hcls] at h
                split at h
                · cases h; exact hne _ _ _ _ _ _ rfl
                · cases h

private theorem classify_reuse_ne {l : Layout} {dst : Lir.VReg} {f : Lir.FunId} {as : List Lir.Arg}
    {site : RcSite} (hne : ∀ d s i lay cls a, site ≠ .reuse d s i lay cls a) :
    (match l.ctors[f - l.reuseWrapper 0]?, as with
     | some c, .v slot :: args =>
       match (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
       | some cls =>
         if args.length == c.arity && (Rt.Rc.CellLayout.ofFields c.arity c.tag).ok &&
             dst != slot && !argsContainVReg dst args then
           some (RcSite.reuse dst slot (f - l.reuseWrapper 0) (Rt.Rc.CellLayout.ofFields c.arity c.tag) cls args)
         else none
       | none => none
     | _, _ => none) ≠ some site := by
  intro h
  cases hc : l.ctors[f - l.reuseWrapper 0]? with
  | none => simp [hc] at h
  | some c =>
    cases as with
    | nil => simp [hc] at h
    | cons a1 args =>
      cases a1 with
      | imm _ => simp [hc] at h
      | v slot =>
        simp only [hc] at h
        cases hcls : (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
        | none => simp [hcls] at h
        | some cls =>
          simp only [hcls] at h
          split at h
          · cases h; exact hne _ _ _ _ _ _ rfl
          · cases h

private theorem classify_reuseU_ne {l : Layout} {dst : Lir.VReg} {f : Lir.FunId} {as : List Lir.Arg}
    {site : RcSite} (hne : ∀ d s i lay cls a, site ≠ .reuseU d s i lay cls a) :
    (match l.ctors[f - l.reuseUWrapper 0]?, as with
     | some c, .v slot :: args =>
       match (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
       | some cls =>
         if args.length == c.arity && (Rt.Rc.CellLayout.ofFields c.arity c.tag).ok &&
             dst != slot && !argsContainVReg dst args then
           some (RcSite.reuseU dst slot (f - l.reuseUWrapper 0) (Rt.Rc.CellLayout.ofFields c.arity c.tag) cls args)
         else none
       | none => none
     | _, _ => none) ≠ some site := by
  intro h
  cases hc : l.ctors[f - l.reuseUWrapper 0]? with
  | none => simp [hc] at h
  | some c =>
    cases as with
    | nil => simp [hc] at h
    | cons a1 args =>
      cases a1 with
      | imm _ => simp [hc] at h
      | v slot =>
        simp only [hc] at h
        cases hcls : (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
        | none => simp [hcls] at h
        | some cls =>
          simp only [hcls] at h
          split at h
          · cases h; exact hne _ _ _ _ _ _ rfl
          · cases h

theorem classify_eq_reset {l : Layout} {s : Lir.Stmt} {dst x : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {mask : UInt64}
    (h : classify l s = some (.reset dst x idx lay cls mask)) :
    ∃ c, l.ctors[idx]? = some c ∧
      s = .call [dst] (l.resetWrapper idx) [.v x, .imm mask] ∧
      lay = Rt.Rc.CellLayout.ofFields c.arity c.tag ∧
      lay.cls? = some cls ∧ lay.ok = true ∧ dst ≠ x := by
  unfold classify at h
  cases s with
  | assign _ _ | limb _ _ _ | store _ _ _ => cases h
  | call rs f as =>
    cases rs with
    | nil => cases h
    | cons d rs' =>
      cases rs' with
      | cons _ _ => cases h
      | nil =>
        by_cases h1 : (f == l.incWrapper) = true
        · simp only [h1, ↓reduceIte] at h; exact absurd h (classify_inc_ne fun _ _ hc => by cases hc)
        simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h2 : (f == l.decWrapper) = true
        · simp only [h2, ↓reduceIte] at h; exact absurd h (classify_dec_ne fun _ _ hc => by cases hc)
        simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h3 : (l.allocWrapper 0 ≤ f && f < l.allocWrapper l.ctors.length) = true
        · simp only [h3, ↓reduceIte] at h; exact absurd h (classify_alloc_ne fun _ _ _ _ _ hc => by cases hc)
        simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h4 : (l.resetWrapper 0 ≤ f && f < l.resetWrapper l.ctors.length) = true
        · simp only [h4, ↓reduceIte] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
          cases hc : l.ctors[f - l.resetWrapper 0]? with
          | none => simp [hc] at h
          | some c =>
            cases as with
            | nil => simp [hc] at h
            | cons a1 as1 =>
              cases a1 with
              | imm _ => simp [hc] at h
              | v x' =>
                cases as1 with
                | nil => simp [hc] at h
                | cons a2 as2 =>
                  cases a2 with
                  | v _ => simp [hc] at h
                  | imm m' =>
                    cases as2 with
                    | cons _ _ => simp [hc] at h
                    | nil =>
                      simp only [hc] at h
                      cases hcls : (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
                      | none => simp [hcls] at h
                      | some cls' =>
                        simp only [hcls] at h
                        split at h
                        · rename_i hcond
                          simp only [Option.some.injEq, RcSite.reset.injEq] at h
                          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
                          simp only [Bool.and_eq_true, bne_iff_ne] at hcond
                          have hfEq : (f : Nat) = l.resetWrapper (f - l.resetWrapper 0) := by
                            dsimp only [Lir.FunId, Layout.resetWrapper] at h4 ⊢; omega
                          exact ⟨c, hc, by rw [← hfEq], rfl, hcls, hcond.1, hcond.2⟩
                        · cases h
        simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h5 : (l.resetUWrapper 0 ≤ f && f < l.resetUWrapper l.ctors.length) = true
        · simp only [h5, ↓reduceIte] at h; exact absurd h (classify_resetU_ne fun _ _ _ _ _ _ hc => by cases hc)
        simp only [h5, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h6 : (l.reuseWrapper 0 ≤ f && f < l.reuseWrapper l.ctors.length) = true
        · simp only [h6, ↓reduceIte] at h; exact absurd h (classify_reuse_ne fun _ _ _ _ _ _ hc => by cases hc)
        simp only [h6, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h7 : (l.reuseUWrapper 0 ≤ f && f < l.reuseUWrapper l.ctors.length) = true
        · simp only [h7, ↓reduceIte] at h; exact absurd h (classify_reuseU_ne fun _ _ _ _ _ _ hc => by cases hc)
        simp only [h7, Bool.false_eq_true, ↓reduceIte] at h; cases h

theorem classify_eq_resetU {l : Layout} {s : Lir.Stmt} {dst x : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {mask : UInt64}
    (h : classify l s = some (.resetU dst x idx lay cls mask)) :
    ∃ c, l.ctors[idx]? = some c ∧
      s = .call [dst] (l.resetUWrapper idx) [.v x, .imm mask] ∧
      lay = Rt.Rc.CellLayout.ofFields c.arity c.tag ∧
      lay.cls? = some cls ∧ lay.ok = true ∧ dst ≠ x := by
  unfold classify at h
  cases s with
  | assign _ _ | limb _ _ _ | store _ _ _ => cases h
  | call rs f as =>
    cases rs with
    | nil => cases h
    | cons d rs' =>
      cases rs' with
      | cons _ _ => cases h
      | nil =>
        by_cases h1 : (f == l.incWrapper) = true
        · simp only [h1, ↓reduceIte] at h; exact absurd h (classify_inc_ne fun _ _ hc => by cases hc)
        simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h2 : (f == l.decWrapper) = true
        · simp only [h2, ↓reduceIte] at h; exact absurd h (classify_dec_ne fun _ _ hc => by cases hc)
        simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h3 : (l.allocWrapper 0 ≤ f && f < l.allocWrapper l.ctors.length) = true
        · simp only [h3, ↓reduceIte] at h; exact absurd h (classify_alloc_ne fun _ _ _ _ _ hc => by cases hc)
        simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h4 : (l.resetWrapper 0 ≤ f && f < l.resetWrapper l.ctors.length) = true
        · simp only [h4, ↓reduceIte] at h; exact absurd h (classify_reset_ne fun _ _ _ _ _ _ hc => by cases hc)
        simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h5 : (l.resetUWrapper 0 ≤ f && f < l.resetUWrapper l.ctors.length) = true
        · simp only [h5, ↓reduceIte] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h5
          cases hc : l.ctors[f - l.resetUWrapper 0]? with
          | none => simp [hc] at h
          | some c =>
            cases as with
            | nil => simp [hc] at h
            | cons a1 as1 =>
              cases a1 with
              | imm _ => simp [hc] at h
              | v x' =>
                cases as1 with
                | nil => simp [hc] at h
                | cons a2 as2 =>
                  cases a2 with
                  | v _ => simp [hc] at h
                  | imm m' =>
                    cases as2 with
                    | cons _ _ => simp [hc] at h
                    | nil =>
                      simp only [hc] at h
                      cases hcls : (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
                      | none => simp [hcls] at h
                      | some cls' =>
                        simp only [hcls] at h
                        split at h
                        · rename_i hcond
                          simp only [Option.some.injEq, RcSite.resetU.injEq] at h
                          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
                          simp only [Bool.and_eq_true, bne_iff_ne] at hcond
                          have hfEq : (f : Nat) = l.resetUWrapper (f - l.resetUWrapper 0) := by
                            dsimp only [Lir.FunId, Layout.resetUWrapper] at h5 ⊢; omega
                          exact ⟨c, hc, by rw [← hfEq], rfl, hcls, hcond.1, hcond.2⟩
                        · cases h
        simp only [h5, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h6 : (l.reuseWrapper 0 ≤ f && f < l.reuseWrapper l.ctors.length) = true
        · simp only [h6, ↓reduceIte] at h; exact absurd h (classify_reuse_ne fun _ _ _ _ _ _ hc => by cases hc)
        simp only [h6, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h7 : (l.reuseUWrapper 0 ≤ f && f < l.reuseUWrapper l.ctors.length) = true
        · simp only [h7, ↓reduceIte] at h; exact absurd h (classify_reuseU_ne fun _ _ _ _ _ _ hc => by cases hc)
        simp only [h7, Bool.false_eq_true, ↓reduceIte] at h; cases h

theorem classify_eq_reuse {l : Layout} {s : Lir.Stmt} {dst slot : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    (h : classify l s = some (.reuse dst slot idx lay cls args)) :
    ∃ c, l.ctors[idx]? = some c ∧
      s = .call [dst] (l.reuseWrapper idx) (.v slot :: args) ∧
      lay = Rt.Rc.CellLayout.ofFields c.arity c.tag ∧
      lay.cls? = some cls ∧ args.length = c.arity ∧ lay.ok = true ∧
      dst ≠ slot ∧ argsContainVReg dst args = false := by
  unfold classify at h
  cases s with
  | assign _ _ | limb _ _ _ | store _ _ _ => cases h
  | call rs f as =>
    cases rs with
    | nil => cases h
    | cons d rs' =>
      cases rs' with
      | cons _ _ => cases h
      | nil =>
        by_cases h1 : (f == l.incWrapper) = true
        · simp only [h1, ↓reduceIte] at h; exact absurd h (classify_inc_ne fun _ _ hc => by cases hc)
        simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h2 : (f == l.decWrapper) = true
        · simp only [h2, ↓reduceIte] at h; exact absurd h (classify_dec_ne fun _ _ hc => by cases hc)
        simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h3 : (l.allocWrapper 0 ≤ f && f < l.allocWrapper l.ctors.length) = true
        · simp only [h3, ↓reduceIte] at h; exact absurd h (classify_alloc_ne fun _ _ _ _ _ hc => by cases hc)
        simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h4 : (l.resetWrapper 0 ≤ f && f < l.resetWrapper l.ctors.length) = true
        · simp only [h4, ↓reduceIte] at h; exact absurd h (classify_reset_ne fun _ _ _ _ _ _ hc => by cases hc)
        simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h5 : (l.resetUWrapper 0 ≤ f && f < l.resetUWrapper l.ctors.length) = true
        · simp only [h5, ↓reduceIte] at h; exact absurd h (classify_resetU_ne fun _ _ _ _ _ _ hc => by cases hc)
        simp only [h5, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h6 : (l.reuseWrapper 0 ≤ f && f < l.reuseWrapper l.ctors.length) = true
        · simp only [h6, ↓reduceIte] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h6
          cases hc : l.ctors[f - l.reuseWrapper 0]? with
          | none => simp [hc] at h
          | some c =>
            cases as with
            | nil => simp [hc] at h
            | cons a1 args' =>
              cases a1 with
              | imm _ => simp [hc] at h
              | v slot' =>
                simp only [hc] at h
                cases hcls : (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
                | none => simp [hcls] at h
                | some cls' =>
                  simp only [hcls] at h
                  split at h
                  · rename_i hcond
                    simp only [Option.some.injEq, RcSite.reuse.injEq] at h
                    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
                    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, Bool.not_eq_true'] at hcond
                    have hfEq : (f : Nat) = l.reuseWrapper (f - l.reuseWrapper 0) := by
                      dsimp only [Lir.FunId, Layout.reuseWrapper] at h6 ⊢; omega
                    exact ⟨c, hc, by rw [← hfEq], rfl, hcls, hcond.1.1.1, hcond.1.1.2, hcond.1.2, hcond.2⟩
                  · cases h
        simp only [h6, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h7 : (l.reuseUWrapper 0 ≤ f && f < l.reuseUWrapper l.ctors.length) = true
        · simp only [h7, ↓reduceIte] at h; exact absurd h (classify_reuseU_ne fun _ _ _ _ _ _ hc => by cases hc)
        simp only [h7, Bool.false_eq_true, ↓reduceIte] at h; cases h

theorem classify_eq_reuseU {l : Layout} {s : Lir.Stmt} {dst slot : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    (h : classify l s = some (.reuseU dst slot idx lay cls args)) :
    ∃ c, l.ctors[idx]? = some c ∧
      s = .call [dst] (l.reuseUWrapper idx) (.v slot :: args) ∧
      lay = Rt.Rc.CellLayout.ofFields c.arity c.tag ∧
      lay.cls? = some cls ∧ args.length = c.arity ∧ lay.ok = true ∧
      dst ≠ slot ∧ argsContainVReg dst args = false := by
  unfold classify at h
  cases s with
  | assign _ _ | limb _ _ _ | store _ _ _ => cases h
  | call rs f as =>
    cases rs with
    | nil => cases h
    | cons d rs' =>
      cases rs' with
      | cons _ _ => cases h
      | nil =>
        by_cases h1 : (f == l.incWrapper) = true
        · simp only [h1, ↓reduceIte] at h; exact absurd h (classify_inc_ne fun _ _ hc => by cases hc)
        simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h2 : (f == l.decWrapper) = true
        · simp only [h2, ↓reduceIte] at h; exact absurd h (classify_dec_ne fun _ _ hc => by cases hc)
        simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h3 : (l.allocWrapper 0 ≤ f && f < l.allocWrapper l.ctors.length) = true
        · simp only [h3, ↓reduceIte] at h; exact absurd h (classify_alloc_ne fun _ _ _ _ _ hc => by cases hc)
        simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h4 : (l.resetWrapper 0 ≤ f && f < l.resetWrapper l.ctors.length) = true
        · simp only [h4, ↓reduceIte] at h; exact absurd h (classify_reset_ne fun _ _ _ _ _ _ hc => by cases hc)
        simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h5 : (l.resetUWrapper 0 ≤ f && f < l.resetUWrapper l.ctors.length) = true
        · simp only [h5, ↓reduceIte] at h; exact absurd h (classify_resetU_ne fun _ _ _ _ _ _ hc => by cases hc)
        simp only [h5, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h6 : (l.reuseWrapper 0 ≤ f && f < l.reuseWrapper l.ctors.length) = true
        · simp only [h6, ↓reduceIte] at h; exact absurd h (classify_reuse_ne fun _ _ _ _ _ _ hc => by cases hc)
        simp only [h6, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h7 : (l.reuseUWrapper 0 ≤ f && f < l.reuseUWrapper l.ctors.length) = true
        · simp only [h7, ↓reduceIte] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h7
          cases hc : l.ctors[f - l.reuseUWrapper 0]? with
          | none => simp [hc] at h
          | some c =>
            cases as with
            | nil => simp [hc] at h
            | cons a1 args' =>
              cases a1 with
              | imm _ => simp [hc] at h
              | v slot' =>
                simp only [hc] at h
                cases hcls : (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
                | none => simp [hcls] at h
                | some cls' =>
                  simp only [hcls] at h
                  split at h
                  · rename_i hcond
                    simp only [Option.some.injEq, RcSite.reuseU.injEq] at h
                    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
                    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, Bool.not_eq_true'] at hcond
                    have hfEq : (f : Nat) = l.reuseUWrapper (f - l.reuseUWrapper 0) := by
                      dsimp only [Lir.FunId, Layout.reuseUWrapper] at h7 ⊢; omega
                    exact ⟨c, hc, by rw [← hfEq], rfl, hcls, hcond.1.1.1, hcond.1.1.2, hcond.1.2, hcond.2⟩
                  · cases h
        simp only [h7, Bool.false_eq_true, ↓reduceIte] at h; cases h

theorem classifyPair_eq_fusedResetReuse {l : Layout} {s1 s2 : Lir.Stmt}
    {slot x dst : Lir.VReg} {idx1 : Nat} {lay1 : Rt.Rc.CellLayout} {mask : UInt64}
    {idx2 : Nat} {lay2 : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    (h : classifyPair l s1 s2 = some (.fusedResetReuse slot x dst idx1 lay1 mask idx2 lay2 cls args)) :
    classify l s1 = some (.reset slot x idx1 lay1 cls mask) ∧
    classify l s2 = some (.reuse dst slot idx2 lay2 cls args) ∧
    lay1.nobj ≤ lay2.nobj ∧
    (deadFields lay1.nobj mask).isEmpty = true ∧
    dst ≠ x ∧ slot ≠ x ∧ dst ≠ slot ∧
    argsContainVReg dst args = false ∧ argsContainVReg slot args = false := by
  unfold classifyPair at h
  cases h1 : classify l s1 with
  | none => simp [h1] at h
  | some site1 =>
    cases h2 : classify l s2 with
    | none => simp [h1, h2] at h
    | some site2 =>
      simp only [h1, h2] at h
      cases site1 <;> cases site2 <;> try (simp at h)
      · obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1e, h2e⟩, hle⟩, hdead⟩, hdx⟩, hsx⟩, hds⟩, hnd⟩, hns⟩,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
        subst h1e; subst h2e
        exact ⟨rfl, rfl, hle, by simp [hdead], hdx, hsx, hds, hnd, hns⟩
      · obtain ⟨-, h⟩ := h
        split at h <;> simp at h

theorem classifyPair_eq_fusedResetUReuseU {l : Layout} {s1 s2 : Lir.Stmt}
    {slot x dst : Lir.VReg} {lay2 : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    (h : classifyPair l s1 s2 = some (.fusedResetUReuseU slot x dst lay2 cls args)) :
    ∃ idx1 lay1 mask idx2,
      classify l s1 = some (.resetU slot x idx1 lay1 cls mask) ∧
      classify l s2 = some (.reuseU dst slot idx2 lay2 cls args) ∧
      lay1.nobj ≤ lay2.nobj ∧
      (deadFields lay1.nobj mask).isEmpty = true ∧
      dst ≠ x ∧ slot ≠ x ∧ dst ≠ slot ∧
      argsContainVReg dst args = false ∧ argsContainVReg slot args = false := by
  unfold classifyPair at h
  cases h1 : classify l s1 with
  | none => simp [h1] at h
  | some site1 =>
    cases h2 : classify l s2 with
    | none => simp [h1, h2] at h
    | some site2 =>
      simp only [h1, h2] at h
      cases site1 <;> cases site2 <;> try (simp at h)
      rename_i sl1 x1 idx1 lay1 cls1 m1 d2 sl2 idx2 lay2' cls2 args2
      obtain ⟨hcond, h⟩ := h
      cases hd : deadFields lay1.nobj m1 with
      | nil =>
        simp only [hd, Option.some.injEq, RcPair.fusedResetUReuseU.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
        obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, hle⟩, hdx⟩, hsx⟩, hds⟩, hnd⟩, hns⟩ := hcond
        exact ⟨idx1, lay1, m1, idx2, rfl, rfl, hle, by simp [hd], hdx, hsx, hds, hnd, hns⟩
      | cons d1 ds =>
        cases ds with
        | nil => simp [hd] at h
        | cons _ _ => simp [hd] at h

theorem classifyPair_eq_fusedResetUReuseU1 {l : Layout} {s1 s2 : Lir.Stmt}
    {slot x dst : Lir.VReg} {lay1 : Rt.Rc.CellLayout} {mask : UInt64} {deadIdx : Nat}
    {lay2 : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    (h : classifyPair l s1 s2 = some (.fusedResetUReuseU1 slot x dst lay1 mask deadIdx lay2 cls args)) :
    ∃ idx1 idx2,
      classify l s1 = some (.resetU slot x idx1 lay1 cls mask) ∧
      classify l s2 = some (.reuseU dst slot idx2 lay2 cls args) ∧
      lay1.nobj ≤ lay2.nobj ∧
      deadFields lay1.nobj mask = [deadIdx] ∧
      dst ≠ x ∧ slot ≠ x ∧ dst ≠ slot ∧
      argsContainVReg dst args = false ∧ argsContainVReg slot args = false := by
  unfold classifyPair at h
  cases h1 : classify l s1 with
  | none => simp [h1] at h
  | some site1 =>
    cases h2 : classify l s2 with
    | none => simp [h1, h2] at h
    | some site2 =>
      simp only [h1, h2] at h
      cases site1 <;> cases site2 <;> try (simp at h)
      rename_i sl1 x1 idx1 lay1' cls1 m1 d2 sl2 idx2 lay2' cls2 args2
      obtain ⟨hcond, h⟩ := h
      cases hd : deadFields lay1'.nobj m1 with
      | nil => simp [hd] at h
      | cons d1 ds =>
        cases ds with
        | nil =>
          simp only [hd, Option.some.injEq, RcPair.fusedResetUReuseU1.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
          obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, hle⟩, hdx⟩, hsx⟩, hds⟩, hnd⟩, hns⟩ := hcond
          exact ⟨idx1, idx2, rfl, rfl, hle, hd, hdx, hsx, hds, hnd, hns⟩
        | cons _ _ => simp [hd] at h

/-! ## Pure memory models for shell writes, reuse writes, and overwrite fusion -/

/-- Write header `hdr` at `addr + 0` and field words `vals` at `addr + 8 * (j + 1)`. -/
def writeReuseMem (mem : X86.Memory) (addr hdr : Lir.Word) (vals : List Lir.Word) : Option X86.Memory :=
  match mem.write? .w64 (addr + Lir.dispWord 0) hdr with
  | .ok mem₁ => writeFieldsMem mem₁ addr 0 vals
  | .error _ => none

/-- Write `resetShell`: header `hdr` at `addr + 0` and `n` words of `1` at `addr + 8 * (j + 1)`. -/
def writeShellMem (mem : X86.Memory) (addr hdr : Lir.Word) (n : Nat) : Option X86.Memory :=
  writeReuseMem mem addr hdr (List.replicate n 1)

private theorem write?_w64_eq_iff (mem : X86.Memory) (addr val : X86.Word) :
    (mem.write? .w64 addr val = .ok (mem.write64 addr val) ∧
      X86.Memory.rangeAllowed mem.writable addr 8 = true) ∨
    (∃ e, mem.write? .w64 addr val = .error e ∧
      X86.Memory.rangeAllowed mem.writable addr 8 = false) := by
  cases h : X86.Memory.rangeAllowed mem.writable addr 8 with
  | true =>
    left
    exact ⟨by simp [X86.Memory.write?, X86.Width.bytes, h, X86.Memory.write, X86.Memory.write64], rfl⟩
  | false =>
    right
    exact ⟨{ access := .write, address := addr, bytes := 8 }, by simp [X86.Memory.write?, X86.Width.bytes, h], rfl⟩

private theorem writeFieldsMem_preserves_meta {addr : Lir.Word} :
    ∀ {j : Nat} {vals : List Lir.Word} {mem mem' : X86.Memory},
      writeFieldsMem mem addr j vals = some mem' →
      mem'.readable = mem.readable ∧ mem'.writable = mem.writable ∧
      ∀ p, (∀ i < vals.length, ∀ o < 8,
        p ≠ addr + Lir.dispWord (Int.ofNat (8 * (j + i + 1))) + UInt64.ofNat o) →
        mem'.bytes p = mem.bytes p
  | _, [], mem, mem', h => by
    simp only [writeFieldsMem, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | j, v :: vs, mem, mem', h => by
    simp only [writeFieldsMem] at h
    rcases write?_w64_eq_iff mem (addr + Lir.dispWord (Int.ofNat (8 * (j + 1)))) v with
      ⟨hw, _⟩ | ⟨e, hw, _⟩
    · rw [hw] at h
      obtain ⟨hr, hw', hb⟩ := writeFieldsMem_preserves_meta (j := j + 1) (vals := vs) h
      refine ⟨hr, hw', fun p hp => ?_⟩
      rw [hb p (fun i hi o ho => by
        have h1 := hp (i + 1) (by simp; omega) o ho
        have hidx : j + (i + 1) + 1 = j + 1 + i + 1 := by omega
        rwa [hidx] at h1)]
      exact X86.Memory.write64_bytes_outside mem _ v p (fun o ho => by
        simpa using hp 0 (by simp) o ho)
    · rw [hw] at h; cases h

private theorem writeFieldsMem_congr_outside {addr : Lir.Word} :
    ∀ {j : Nat} {vals : List Lir.Word} {m₁ m₂ : X86.Memory},
      m₁.readable = m₂.readable → m₁.writable = m₂.writable →
      (∀ p, (∀ i < vals.length, ∀ o < 8,
        p ≠ addr + Lir.dispWord (Int.ofNat (8 * (j + i + 1))) + UInt64.ofNat o) →
        m₁.bytes p = m₂.bytes p) →
      writeFieldsMem m₁ addr j vals = writeFieldsMem m₂ addr j vals
  | _, [], m₁, m₂, hr, hw, hb => by
    have heq : m₁ = m₂ := by
      cases m₁; cases m₂; simp only at hr hw hb; subst hr hw
      congr; funext p; exact hb p (fun _ hi => by simp at hi)
    simp [writeFieldsMem, heq]
  | j, v :: vs, m₁, m₂, hr, hw, hb => by
    simp only [writeFieldsMem]
    let a := addr + Lir.dispWord (Int.ofNat (8 * (j + 1)))
    rcases write?_w64_eq_iff m₁ a v with ⟨hw1, hal1⟩ | ⟨e1, hw1, hal1⟩
    · have hal2 : X86.Memory.rangeAllowed m₂.writable a 8 = true := by rw [← hw]; exact hal1
      have hw2 : m₂.write? .w64 a v = .ok (m₂.write64 a v) := by
        unfold X86.Memory.write? X86.Width.bytes; simp [hal2, X86.Memory.write64]
      rw [hw1, hw2]
      exact writeFieldsMem_congr_outside (j := j + 1) (vals := vs) hr hw (fun p hp => by
        by_cases hin : ∃ o < 8, p = a + UInt64.ofNat o
        · obtain ⟨o, ho, rfl⟩ := hin
          change (m₁.writeLittle a v 8).bytes (a + UInt64.ofNat o) =
            (m₂.writeLittle a v 8).bytes (a + UInt64.ofNat o)
          rw [X86.Memory.writeLittle_bytes m₁ a v (Nat.le_refl 8) ho,
            X86.Memory.writeLittle_bytes m₂ a v (Nat.le_refl 8) ho]
        · have hout : ∀ o < 8, p ≠ a + UInt64.ofNat o := fun o ho heq => hin ⟨o, ho, heq⟩
          rw [X86.Memory.write64_bytes_outside m₁ a v p hout,
            X86.Memory.write64_bytes_outside m₂ a v p hout]
          apply hb p
          intro i hi o ho
          cases i with
          | zero => simpa [a] using hout o ho
          | succ i' =>
            have h1 := hp i' (by simp at hi; omega) o ho
            have hidx : j + 1 + i' + 1 = j + (i' + 1) + 1 := by omega
            rwa [hidx] at h1)
    · have hal2 : X86.Memory.rangeAllowed m₂.writable a 8 = false := by rw [← hw]; exact hal1
      have hw2 : ∃ e2, m₂.write? .w64 a v = .error e2 := by
        simp only [X86.Memory.write?, X86.Width.bytes, hal2, Bool.false_eq_true, ↓reduceIte]; exact ⟨_, rfl⟩
      obtain ⟨e2, hw2⟩ := hw2
      rw [hw1, hw2]

/-- **Core overwrite-fusion theorem (zero heap invariant):** if writing the `n1`-field `resetShell`
succeeded (`mem → mem₁`) and `n1 ≤ vals.length`, then writing the `vals`-field `reuse` cell onto
`mem₁` produces the exact same `Option X86.Memory` as writing it directly onto `mem`. -/
theorem writeReuseMem_after_writeShellMem {mem mem₁ : X86.Memory} {addr hdr1 hdr2 : Lir.Word}
    {n1 : Nat} {vals : List Lir.Word} (hle : n1 ≤ vals.length)
    (hshell : writeShellMem mem addr hdr1 n1 = some mem₁) :
    writeReuseMem mem₁ addr hdr2 vals = writeReuseMem mem addr hdr2 vals := by
  unfold writeShellMem at hshell
  unfold writeReuseMem at hshell ⊢
  rcases write?_w64_eq_iff mem (addr + Lir.dispWord 0) hdr1 with ⟨hw1, hal1⟩ | ⟨e1, hw1, _⟩
  · rw [hw1] at hshell
    obtain ⟨hr, hw, hb⟩ := writeFieldsMem_preserves_meta (j := 0) (vals := List.replicate n1 1) hshell
    have hr' : mem₁.readable = mem.readable := hr
    have hw' : mem₁.writable = mem.writable := hw
    have hw1' : mem₁.write? .w64 (addr + Lir.dispWord 0) hdr2 =
        .ok (mem₁.write64 (addr + Lir.dispWord 0) hdr2) := by
      unfold X86.Memory.write? X86.Width.bytes; simp [hw', hal1, X86.Memory.write64]
    have hw2' : mem.write? .w64 (addr + Lir.dispWord 0) hdr2 =
        .ok (mem.write64 (addr + Lir.dispWord 0) hdr2) := by
      unfold X86.Memory.write? X86.Width.bytes; simp [hal1, X86.Memory.write64]
    rw [hw1', hw2']
    exact writeFieldsMem_congr_outside (j := 0) (vals := vals) hr' hw' (fun p hp => by
      by_cases hin : ∃ o < 8, p = addr + Lir.dispWord 0 + UInt64.ofNat o
      · obtain ⟨o, ho, rfl⟩ := hin
        change (mem₁.writeLittle _ hdr2 8).bytes _ = (mem.writeLittle _ hdr2 8).bytes _
        rw [X86.Memory.writeLittle_bytes mem₁ _ hdr2 (Nat.le_refl 8) ho,
          X86.Memory.writeLittle_bytes mem _ hdr2 (Nat.le_refl 8) ho]
      · have hout0 : ∀ o < 8, p ≠ addr + Lir.dispWord 0 + UInt64.ofNat o :=
          fun o ho heq => hin ⟨o, ho, heq⟩
        rw [X86.Memory.write64_bytes_outside mem₁ _ hdr2 p hout0,
          X86.Memory.write64_bytes_outside mem _ hdr2 p hout0]
        rw [hb p (fun i hi o ho => by
          simp only [List.length_replicate] at hi
          exact hp i (by omega) o ho)]
        exact X86.Memory.write64_bytes_outside mem _ hdr1 p hout0)
  · rw [hw1] at hshell; cases hshell

/-! ## Helper: loading fields and writing shell / reuse stores in blocks -/

/-- Pure specification of loading `.w64` fields at indices `js` from `addr`. -/
def loadFieldsMem (mem : X86.Memory) (addr : Lir.Word) : List Nat → Option (List Lir.Word)
  | [] => some []
  | j :: rest => do
    let w ← Lir.loadWord mem .w64 .zero (addr + Lir.dispWord (Int.ofNat (8 * (j + 1))))
    let ws ← loadFieldsMem mem addr rest
    pure (w :: ws)

theorem loadFieldsMem_length {mem : X86.Memory} {addr : Lir.Word} :
    ∀ {js : List Nat} {ws : List Lir.Word},
      loadFieldsMem mem addr js = some ws → ws.length = js.length
  | [], ws, h => by simp [loadFieldsMem] at h; subst h; rfl
  | j :: js, ws, h => by
    simp only [loadFieldsMem, Option.bind_eq_bind] at h
    cases hl : Lir.loadWord mem .w64 .zero (addr + Lir.dispWord (Int.ofNat (8 * (j + 1)))) with
    | none => rw [hl] at h; simp at h
    | some w =>
      rw [hl] at h; simp only [Option.bind_some] at h
      cases hr : loadFieldsMem mem addr js with
      | none => rw [hr] at h; simp at h
      | some ws' =>
        rw [hr] at h; simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        simp [loadFieldsMem_length hr]

theorem loadFieldsMem_get {mem : X86.Memory} {addr : Lir.Word} :
    ∀ {js : List Nat} {ws : List Lir.Word} (hload : loadFieldsMem mem addr js = some ws),
      ∀ i, (hi : i < js.length) →
        Lir.loadWord mem .w64 .zero (addr + Lir.dispWord (Int.ofNat (8 * (js[i] + 1)))) =
          some (ws[i]'(by rw [loadFieldsMem_length hload]; exact hi))
  | [], _, _, _, hi => by simp at hi
  | j :: js, ws, h, i, hi => by
    simp only [loadFieldsMem, Option.bind_eq_bind] at h
    cases hl : Lir.loadWord mem .w64 .zero (addr + Lir.dispWord (Int.ofNat (8 * (j + 1)))) with
    | none => rw [hl] at h; simp at h
    | some w =>
      rw [hl] at h; simp only [Option.bind_some] at h
      cases hr : loadFieldsMem mem addr js with
      | none => rw [hr] at h; simp at h
      | some ws' =>
        rw [hr] at h; simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        cases i with
        | zero => exact hl
        | succ i' => exact loadFieldsMem_get hr i' (by simp at hi; omega)

theorem loadFieldsMem_sublist {mem : X86.Memory} {addr : Lir.Word} {n : Nat} {allVals : List Lir.Word}
    (hall : loadFieldsMem mem addr (List.range n) = some allVals) :
    ∀ (js : List Nat) (hlt : ∀ j ∈ js, j < n),
      ∃ ws, loadFieldsMem mem addr js = some ws ∧ ∃ hwlen : ws.length = js.length,
        ∀ i, (hi : i < js.length) →
          ws[i]'(by omega) = allVals[js[i]]'(by
            have hlen := loadFieldsMem_length hall
            simp only [List.length_range] at hlen
            have := hlt js[i] (List.getElem_mem hi)
            omega)
  | [], _ => ⟨[], rfl, rfl, fun _ hi => by simp at hi⟩
  | j :: js, hlt => by
    have hj : j < n := hlt j (by simp)
    have hlenAll : allVals.length = n := by simpa using loadFieldsMem_length hall
    have hlj := loadFieldsMem_get hall j (by simp [hj])
    simp only [List.getElem_range] at hlj
    obtain ⟨ws, hws, hwlen, hget⟩ := loadFieldsMem_sublist hall js (fun k hk => hlt k (by simp [hk]))
    refine ⟨allVals[j]'(by omega) :: ws, ?_, by simp [hwlen], ?_⟩
    · simp only [loadFieldsMem, Option.bind_eq_bind, hlj, Option.bind_some, hws, Option.pure_def]
    · intro i hi
      cases i with
      | zero => rfl
      | succ i' => exact hget i' (by simp at hi; omega)

theorem mkShellStores_length (x : Lir.VReg) (hdr : UInt64) (n : Nat) :
    (mkShellStores x hdr n).length = 1 + n := by
  simp [mkShellStores]; omega

theorem mkDeadLoads_length (x baseTmp : Lir.VReg) :
    ∀ (dead : List Nat), (mkDeadLoads x baseTmp dead).length = dead.length
  | [] => rfl
  | _ :: rest => by simp [mkDeadLoads, mkDeadLoads_length x (baseTmp + 1) rest]

theorem mkDeadDecs_length (decProc : Nat) (baseTmp : Lir.VReg) :
    ∀ (dead : List Nat), (mkDeadDecs decProc baseTmp dead).length = dead.length
  | [] => rfl
  | _ :: rest => by simp [mkDeadDecs, mkDeadDecs_length decProc (baseTmp + 1) rest]

theorem deadFields_lt (n : Nat) (mask : UInt64) {j : Nat} (hj : j ∈ deadFields n mask) : j < n := by
  unfold deadFields at hj
  have := (List.mem_filter.mp hj).1
  exact List.mem_range.mp this

theorem deadFields_bit_zero (n : Nat) (mask : UInt64) {j : Nat} (hj : j ∈ deadFields n mask) :
    (mask &&& UInt64.ofNat (2 ^ (j + 1))) = 0 := by
  unfold deadFields at hj
  exact beq_iff_eq.mp (List.mem_filter.mp hj).2

/-- Execute `mkDeadLoads x baseTmp js` inside a block, loading `ws` into `baseTmp + i` (`i < js.length`). -/
theorem exec_mkDeadLoads {p : Lir.Program} {F : Lir.Func} {B : Lir.Block} {fn lbl : Nat}
    {x : Lir.VReg} {xVal ctx : Lir.Word} {rest : List Lir.Frame}
    (hf : p.funcs[fn]? = some F) (hb : F.blocks[lbl]? = some B) :
    ∀ {pre post : List Lir.Stmt} {baseTmp : Lir.VReg} {js : List Nat} {ws : List Lir.Word}
      {env : Lir.Env} {mem : X86.Memory},
      (x : Nat) < baseTmp →
      env[x]? = some xVal →
      B.body.toList = pre ++ mkDeadLoads x baseTmp js ++ post →
      (hload : loadFieldsMem mem xVal js = some ws) →
      ∃ env',
        Sem.Star (Lir.semStep p)
          { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } 0
          { mem, ctx, stack := { fn, label := lbl, pos := pre.length + js.length, env := env', dsts := [] } :: rest } ∧
        (∀ r < baseTmp, env'[r]? = env[r]?) ∧
        (∀ i, (hi : i < js.length) →
          env'[baseTmp + i]? = some (ws[i]'(by rw [loadFieldsMem_length hload]; exact hi)))
  | pre, post, baseTmp, [], ws, env, mem, _, _, _, hload => by
    simp only [loadFieldsMem, Option.some.injEq] at hload
    subst hload
    exact ⟨env, .refl _, fun _ _ => rfl, fun _ hi => by simp at hi⟩
  | pre, post, baseTmp, j :: js, ws, env, mem, hxLt, hx, hbody, hload => by
    simp only [loadFieldsMem, Option.bind_eq_bind] at hload
    cases hl : Lir.loadWord mem .w64 .zero (xVal + Lir.dispWord (Int.ofNat (8 * (j + 1)))) with
    | none => rw [hl] at hload; simp at hload
    | some w =>
      rw [hl] at hload; simp only [Option.bind_some] at hload
      cases hlr : loadFieldsMem mem xVal js with
      | none => rw [hlr] at hload; simp at hload
      | some ws' =>
        rw [hlr] at hload; simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at hload
        subst hload
        have hpos : pre.length < B.body.size := by
          have := congrArg List.length hbody
          simp only [Array.length_toList, mkDeadLoads, List.length_append, List.length_cons] at this
          omega
        have hget : B.body[pre.length] =
            .assign baseTmp (.load .w64 .zero (cellAddr x (Int.ofNat (8 * (j + 1))))) := by
          have : B.body.toList[pre.length]? =
              some (.assign baseTmp (.load .w64 .zero (cellAddr x (Int.ofNat (8 * (j + 1)))))) := by
            rw [hbody]; simp [mkDeadLoads]
          simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hpos, Option.some.injEq] at this
          exact this
        let env1 := env.insert baseTmp w
        have hstep : Lir.semStep p
            { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } =
            .next { mem, ctx, stack := { fn, label := lbl, pos := pre.length + 1, env := env1, dsts := [] } :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fn, label := lbl, pos := pre.length, env, dsts := [] })
            hf hb hpos hget rfl (by
              simp only [Lir.Stmt.exec, Lir.Rhs.eval, cellAddr, addr_cell env ctx x xVal _ hx,
                Option.bind_eq_bind, Option.bind_some, hl, env1])
        have hx1 : env1[x]? = some xVal := by
          rw [Lir.env_insert_ne _ _ (by dsimp only [Lir.VReg] at hxLt ⊢; omega), hx]
        have hbody' : B.body.toList =
            (pre ++ [.assign baseTmp (.load .w64 .zero (cellAddr x (Int.ofNat (8 * (j + 1)))))]) ++
              mkDeadLoads x (baseTmp + 1) js ++ post := by
          simpa [mkDeadLoads, List.append_assoc] using hbody
        obtain ⟨env', hstar, hag, hvals⟩ :=
          exec_mkDeadLoads (ctx := ctx) (rest := rest) hf hb (baseTmp := baseTmp + 1)
            (by dsimp only [Lir.VReg] at hxLt ⊢; omega) hx1 hbody' hlr
        refine ⟨env', .free hstep (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hstar),
          fun r hr => by
            have hr' : (r : Nat) < (baseTmp : Nat) := hr
            rw [hag r (by dsimp only [Lir.VReg] at hr' ⊢; omega),
              Lir.env_insert_ne _ _ (by dsimp only [Lir.VReg] at hr' ⊢; omega)], ?_⟩
        intro i hi
        cases i with
        | zero =>
          rw [Nat.add_zero, hag baseTmp (by dsimp only [Lir.VReg]; omega)]
          simp [env1]
        | succ i' =>
          have h1 := hvals i' (by simp at hi; omega)
          have hidx : baseTmp + (i' + 1) = baseTmp + 1 + i' := by dsimp only [Lir.VReg]; omega
          simpa [hidx] using h1

/-- Execute `(List.range' k m).map (fun j => .assign (oldBase + j) (.load ...))` inside a wrapper block. -/
theorem exec_loadOld {p : Lir.Program} {F : Lir.Func} {B : Lir.Block} {fn lbl : Nat}
    {xVal ctx : Lir.Word} {rest : List Lir.Frame} {oldBase : Nat}
    (hf : p.funcs[fn]? = some F) (hb : F.blocks[lbl]? = some B)
    (hold : 1 < oldBase) :
    ∀ {pre post : List Lir.Stmt} {k m : Nat} {env : Lir.Env} {mem : X86.Memory},
      env[0]? = some xVal →
      B.body.toList = pre ++ ((List.range' k m).map fun j =>
        Lir.Stmt.assign (oldBase + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })) ++ post →
      match loadFieldsMem mem xVal (List.range' k m) with
      | some ws =>
        ∃ env',
          Sem.Star (Lir.semStep p)
            { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } 0
            { mem, ctx, stack := { fn, label := lbl, pos := pre.length + m, env := env', dsts := [] } :: rest } ∧
          (∀ r < oldBase + k, env'[r]? = env[r]?) ∧
          (∀ i < m, env'[oldBase + k + i]? = ws[i]?)
      | none =>
        Sem.Reaches (Lir.semStep p)
          { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } 0 .stuck
  | pre, post, k, 0, env, mem, _, _ => by
    simp only [List.range'_zero, loadFieldsMem, Nat.add_zero]
    exact ⟨env, .refl _, fun _ _ => rfl, fun _ hi => by omega⟩
  | pre, post, k, m + 1, env, mem, hx, hbody => by
    simp only [List.range'_succ, List.map_cons] at hbody ⊢
    simp only [loadFieldsMem, Option.bind_eq_bind]
    have hpos : pre.length < B.body.size := by
      have := congrArg List.length hbody
      simp only [Array.length_toList, List.length_append, List.length_cons] at this
      omega
    have hget : B.body[pre.length] =
        .assign (oldBase + k) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (k + 1)) }) := by
      have : B.body.toList[pre.length]? =
          some (.assign (oldBase + k) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (k + 1)) })) := by
        rw [hbody]; simp
      simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hpos, Option.some.injEq] at this
      exact this
    cases hl : Lir.loadWord mem .w64 .zero (xVal + Lir.dispWord (Int.ofNat (8 * (k + 1)))) with
    | none =>
      apply Sem.Reaches.final
      have hst : Lir.step p { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } = .stuck := by
        unfold Lir.step
        have hl' : Lir.loadWord mem .w64 .zero (xVal + Lir.dispWord (8 * (↑k + 1))) = none := by simpa using hl
        simp [hf, hb, hpos, hget, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell env ctx 0 xVal _ hx, hl']
      rw [Lir.semStep, hst]; exact .stuck
    | some w =>
      simp only [Option.bind_some]
      let env1 := env.insert (oldBase + k) w
      have hx1 : env1[0]? = some xVal := by rw [Lir.env_insert_ne _ _ (by omega), hx]
      have hstep : Lir.semStep p
          { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } =
          .next { mem, ctx, stack := { fn, label := lbl, pos := pre.length + 1, env := env1, dsts := [] } :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fn, label := lbl, pos := pre.length, env, dsts := [] })
          hf hb hpos hget rfl (by
            simp only [Lir.Stmt.exec, Lir.Rhs.eval, addr_cell env ctx 0 xVal _ hx,
              Option.bind_eq_bind, Option.bind_some, hl, env1])
      have hbody' : B.body.toList =
          (pre ++ [.assign (oldBase + k) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (k + 1)) })]) ++
            ((List.range' (k + 1) m).map fun j =>
              Lir.Stmt.assign (oldBase + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })) ++ post := by
        simpa [List.append_assoc] using hbody
      have ih := exec_loadOld (ctx := ctx) (rest := rest) hf hb hold (k := k + 1) (m := m) hx1 hbody' (mem := mem)
      cases hlr : loadFieldsMem mem xVal (List.range' (k + 1) m) with
      | none =>
        rw [hlr] at ih
        exact .free hstep (by simpa using ih)
      | some ws' =>
        rw [hlr] at ih
        obtain ⟨env', hstar, hag, hvals⟩ := ih
        refine ⟨env', .free hstep (by simpa [Nat.add_assoc, Nat.add_comm 1] using hstar),
          fun r hr => by rw [hag r (by omega), Lir.env_insert_ne _ _ (by omega)], ?_⟩
        intro i hi
        cases i with
        | zero =>
          rw [Nat.add_zero, hag (oldBase + k) (by omega)]
          simp [env1]
        | succ i' =>
          have h1 := hvals i' (by omega)
          have hidx : oldBase + k + (i' + 1) = oldBase + (k + 1) + i' := by omega
          simpa [hidx] using h1

/-- Execute `mkShellStores x hdr n` (identical to `.store hdr` + `n` `.store 1`s) inside any block. -/
theorem exec_mkShellStores {p : Lir.Program} {F : Lir.Func} {B : Lir.Block} {fn lbl : Nat}
    {x : Lir.VReg} {xVal hdr ctx : Lir.Word} {rest : List Lir.Frame} {env : Lir.Env}
    (hf : p.funcs[fn]? = some F) (hb : F.blocks[lbl]? = some B)
    (hx : env[x]? = some xVal)
    {pre post : List Lir.Stmt} {n : Nat} {mem : X86.Memory}
    (hbody : B.body.toList = pre ++ mkShellStores x hdr n ++ post) :
    match writeShellMem mem xVal hdr n with
    | some mem' =>
      Sem.Star (Lir.semStep p)
        { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } 0
        { mem := mem', ctx, stack := { fn, label := lbl, pos := pre.length + (1 + n), env, dsts := [] } :: rest }
    | none =>
      Sem.Reaches (Lir.semStep p)
        { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } 0 .stuck := by
  have hpos0 : pre.length < B.body.size := by
    have := congrArg List.length hbody
    simp only [Array.length_toList, mkShellStores, List.length_append, List.length_cons] at this
    omega
  have hget0 : B.body[pre.length] = .store .w64 (cellAddr x 0) (.imm hdr) := by
    have : B.body.toList[pre.length]? = some (.store .w64 (cellAddr x 0) (.imm hdr)) := by
      rw [hbody]; simp [mkShellStores]
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hpos0, Option.some.injEq] at this
    exact this
  have hones : ((List.range n).map fun j =>
      Lir.Stmt.store .w64 (cellAddr x (Int.ofNat (8 * (j + 1)))) (.imm 1)) =
      mkFieldStores x 0 (List.replicate n (.imm 1)) := by
    have haux : ∀ k m, ((List.range' k m).map fun j =>
        Lir.Stmt.store .w64 (cellAddr x (Int.ofNat (8 * (j + 1)))) (.imm 1)) =
        mkFieldStores x k (List.replicate m (.imm 1)) := by
      intro k m; induction m generalizing k with
      | zero => rfl
      | succ m ih =>
        simp only [List.range'_succ, List.replicate_succ, List.map_cons, mkFieldStores]
        exact congrArg _ (ih (k + 1))
    rw [List.range_eq_range']; exact haux 0 n
  have heval1 : Lir.evalArgs env (List.replicate n (.imm 1)) = some (List.replicate n (1 : Lir.Word)) := by
    have haux : ∀ k, Lir.evalArgs env (List.replicate k (.imm 1)) = some (List.replicate k (1 : Lir.Word)) := by
      intro k; induction k with
      | zero => rfl
      | succ m ih =>
        simp only [List.replicate_succ, Lir.evalArgs, List.mapM_cons, Lir.Arg.eval,
          Option.pure_def, Option.bind_eq_bind, Option.bind_some]
        rw [show List.mapM (Lir.Arg.eval env) (List.replicate m (.imm 1)) = some (List.replicate m 1) from ih]
        rfl
    exact haux n
  unfold writeShellMem writeReuseMem
  cases hw0 : mem.write? .w64 (xVal + Lir.dispWord 0) hdr with
  | error e =>
    dsimp only
    apply Sem.Reaches.final
    have hst : Lir.step p { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } = .stuck := by
      unfold Lir.step
      simp [hf, hb, hpos0, hget0, Lir.Stmt.exec, cellAddr, addr_cell env ctx x xVal 0 hx, Lir.Arg.eval, hw0]
    rw [Lir.semStep, hst]; exact .stuck
  | ok mem₁ =>
    dsimp only
    have s0 : Lir.semStep p
        { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } =
        .next { mem := mem₁, ctx, stack := { fn, label := lbl, pos := pre.length + 1, env, dsts := [] } :: rest } false := by
      apply Lir.semStep_next.mpr
      exact Lir.step_stmt (fr := { fn, label := lbl, pos := pre.length, env, dsts := [] })
        hf hb hpos0 hget0 rfl (by
          simp [Lir.Stmt.exec, cellAddr, addr_cell env ctx x xVal 0 hx, Lir.Arg.eval, hw0])
    have hbody' : B.body.toList = (pre ++ [.store .w64 (cellAddr x 0) (.imm hdr)]) ++
        mkFieldStores x 0 (List.replicate n (.imm 1)) ++ post := by
      rw [← hones]; simpa [mkShellStores, List.append_assoc] using hbody
    have hfs := exec_mkFieldStores (ctx := ctx) (rest := rest) hf hb hx hbody' heval1 (mem := mem₁)
    cases hwf : writeFieldsMem mem₁ xVal 0 (List.replicate n 1) with
    | none =>
      rw [hwf] at hfs
      exact .free s0 (by simpa using hfs)
    | some mem' =>
      rw [hwf] at hfs
      have := Sem.Star.free s0 (by simpa [List.length_replicate, Nat.add_assoc] using hfs)
      simpa [Nat.add_assoc] using this

/-- Execute `.store .w64 [base+0] hdr :: mkFieldStores base 0 args` inside any block. -/
theorem exec_writeReuse {p : Lir.Program} {F : Lir.Func} {B : Lir.Block} {fn lbl : Nat}
    {base : Lir.VReg} {addr hdr ctx : Lir.Word} {rest : List Lir.Frame} {env : Lir.Env}
    (hf : p.funcs[fn]? = some F) (hb : F.blocks[lbl]? = some B)
    (hbase : env[base]? = some addr)
    {pre post : List Lir.Stmt} {args : List Lir.Arg} {vals : List Lir.Word} {mem : X86.Memory}
    (hbody : B.body.toList = pre ++ (.store .w64 (cellAddr base 0) (.imm hdr) :: mkFieldStores base 0 args) ++ post)
    (hargs : Lir.evalArgs env args = some vals) :
    match writeReuseMem mem addr hdr vals with
    | some mem' =>
      Sem.Star (Lir.semStep p)
        { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } 0
        { mem := mem', ctx, stack := { fn, label := lbl, pos := pre.length + (1 + args.length), env, dsts := [] } :: rest }
    | none =>
      Sem.Reaches (Lir.semStep p)
        { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } 0 .stuck := by
  have hpos0 : pre.length < B.body.size := by
    have := congrArg List.length hbody
    simp only [Array.length_toList, List.length_append, List.length_cons] at this
    omega
  have hget0 : B.body[pre.length] = .store .w64 (cellAddr base 0) (.imm hdr) := by
    have : B.body.toList[pre.length]? = some (.store .w64 (cellAddr base 0) (.imm hdr)) := by
      rw [hbody]; simp
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hpos0, Option.some.injEq] at this
    exact this
  unfold writeReuseMem
  cases hw0 : mem.write? .w64 (addr + Lir.dispWord 0) hdr with
  | error e =>
    dsimp only
    apply Sem.Reaches.final
    have hst : Lir.step p { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } = .stuck := by
      unfold Lir.step
      simp [hf, hb, hpos0, hget0, Lir.Stmt.exec, cellAddr, addr_cell env ctx base addr 0 hbase, Lir.Arg.eval, hw0]
    rw [Lir.semStep, hst]; exact .stuck
  | ok mem₁ =>
    dsimp only
    have s0 : Lir.semStep p
        { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } =
        .next { mem := mem₁, ctx, stack := { fn, label := lbl, pos := pre.length + 1, env, dsts := [] } :: rest } false := by
      apply Lir.semStep_next.mpr
      exact Lir.step_stmt (fr := { fn, label := lbl, pos := pre.length, env, dsts := [] })
        hf hb hpos0 hget0 rfl (by
          simp [Lir.Stmt.exec, cellAddr, addr_cell env ctx base addr 0 hbase, Lir.Arg.eval, hw0])
    have hbody' : B.body.toList = (pre ++ [.store .w64 (cellAddr base 0) (.imm hdr)]) ++
        mkFieldStores base 0 args ++ post := by
      simpa [List.append_assoc] using hbody
    have hfs := exec_mkFieldStores (ctx := ctx) (rest := rest) hf hb hbase hbody' hargs (mem := mem₁)
    cases hwf : writeFieldsMem mem₁ addr 0 vals with
    | none =>
      rw [hwf] at hfs
      exact .free s0 (by simpa using hfs)
    | some mem' =>
      rw [hwf] at hfs
      have := Sem.Star.free s0 (by simpa [Nat.add_assoc] using hfs)
      simpa [Nat.add_assoc] using this

/-! ## 4. `reuseU` and `reuse` (hot & cold) execution -/

private theorem mkReuseU_stores_eq (n : Nat) (hdr : UInt64) :
    (Lir.Stmt.store .w64 { base := some (.v 0), disp := 0 } (.imm hdr) ::
      (List.range n).map fun j =>
        Lir.Stmt.store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.v (j + 1))) =
      Lir.Stmt.store .w64 (cellAddr 0 0) (.imm hdr) ::
        mkFieldStores 0 0 ((List.range n).map fun j => Lir.Arg.v (j + 1)) := by
  congr 1
  have haux : ∀ k m, ((List.range' k m).map fun j =>
      Lir.Stmt.store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.v (j + 1))) =
      mkFieldStores 0 k ((List.range' k m).map fun j => Lir.Arg.v (j + 1)) := by
    intro k m; induction m generalizing k with
    | zero => rfl
    | succ m ih =>
      simp only [List.range'_succ, List.map_cons, mkFieldStores, cellAddr]
      exact congrArg _ (ih (k + 1))
  rw [List.range_eq_range']; exact haux 0 n

private theorem evalArgs_range_v (ρ : Lir.Env) :
    ∀ (k : Nat) (vs : List Lir.Word),
      (∀ i, (hi : i < vs.length) → ρ[k + i + 1]? = some vs[i]) →
      Lir.evalArgs ρ ((List.range' k vs.length).map fun j => Lir.Arg.v (j + 1)) = some vs
  | _, [], _ => rfl
  | k, v :: vs, h => by
    simp only [List.length_cons, List.range'_succ, List.map_cons, Lir.evalArgs, List.mapM_cons,
      Lir.Arg.eval, Option.bind_eq_bind]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0]; simp only [Option.bind_some]
    have ih := evalArgs_range_v ρ (k + 1) vs (fun i hi => by
      have := h (i + 1) (by simp; omega)
      have hidx : k + (i + 1) + 1 = k + 1 + i + 1 := by omega
      simpa [hidx] using this)
    rw [show List.mapM (Lir.Arg.eval ρ) ((List.range' (k + 1) vs.length).map fun j => Lir.Arg.v (j + 1)) =
      some vs from ih]
    rfl

theorem raw_reuseU_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {dst slot : Lir.VReg} {idx : Nat} {c : Lam.CtorInfo}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    {slotVal : Lir.Word} {vals : List Lir.Word}
    (hF : raw.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B)
    (hpos : fr.pos < B.body.size)
    (hc : l.ctors[idx]? = some c)
    (hlay : lay = Rt.Rc.CellLayout.ofFields c.arity c.tag)
    (hcls : lay.cls? = some cls) (hlen : args.length = c.arity)
    (hstmt : B.body[fr.pos] = .call [dst] (l.reuseUWrapper idx) (.v slot :: args))
    (hslot : fr.env[slot]? = some slotVal)
    (hargs : Lir.evalArgs fr.env args = some vals) :
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    match writeReuseMem mem slotVal hdr vals with
    | some mem' =>
      ∃ s₁, Lir.semStep raw { mem, ctx, stack := fr :: rest } = .next s₁ true ∧
        Sem.Star (Lir.semStep raw) s₁ 0
          { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst slotVal, dsts := [] } :: rest }
    | none =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 1 .stuck := by
  intro hdr
  have hvlen : vals.length = c.arity := by have := evalArgs_length hargs; omega
  have hfullArgs : Lir.evalArgs fr.env (.v slot :: args) = some (slotVal :: vals) := by
    simp only [Lir.evalArgs, List.mapM_cons, Lir.Arg.eval, hslot, Option.bind_eq_bind, Option.bind_some]
    rw [show List.mapM (Lir.Arg.eval fr.env) args = some vals from hargs]; rfl
  obtain ⟨wEnv, hwBind, _, hwLookup⟩ :=
    bindParams_range_lookup (c.arity + 1) 0 (slotVal :: vals) {} (by simp [hvlen])
  rw [← List.range_eq_range'] at hwBind
  have hwrapF : raw.funcs[l.reuseUWrapper idx]? = some (mkReuseUWrapper lay cls) := by
    rw [hlay]; exact hr.reuseUWrap idx c cls hc (by rwa [← hlay])
  have hnobj : lay.nobj = c.arity := by rw [hlay]; rfl
  let caller' : Lir.Frame := { fr with pos := fr.pos + 1, dsts := [dst] }
  let wFr0 : Lir.Frame := { fn := l.reuseUWrapper idx, label := 0, pos := 0, env := wEnv }
  have hstep1 : Lir.semStep raw { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := wFr0 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call hF hB hpos hstmt hfullArgs
      (by simp [Lir.enter, hwrapF, mkReuseUWrapper, hnobj, hwBind, wFr0])
  have hw0 : wEnv[0]? = some slotVal := by simpa using hwLookup 0 (by omega)
  have hwa : Lir.evalArgs wEnv ((List.range c.arity).map fun j => Lir.Arg.v (j + 1)) = some vals := by
    rw [List.range_eq_range', ← hvlen]
    exact evalArgs_range_v wEnv 0 vals (fun i hi => by
      have h1 := hwLookup (i + 1) (by omega)
      simpa [Nat.add_comm] using h1)
  have hblk0 : (mkReuseUWrapper lay cls).blocks[0]? = some (mkReuseUWrapper lay cls).blocks[0]! := rfl
  have hbody0 : (mkReuseUWrapper lay cls).blocks[0]!.body.toList =
      [] ++ (.store .w64 (cellAddr 0 0) (.imm hdr) ::
        mkFieldStores 0 0 ((List.range c.arity).map fun j => Lir.Arg.v (j + 1))) ++ [] := by
    simp only [mkReuseUWrapper, hnobj, List.nil_append, List.append_nil, Array.getElem!_eq_getD,
      Array.getD, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_lt_succ, ↓reduceDIte]
    simpa [hdr, hnobj] using mkReuseU_stores_eq c.arity hdr
  have hwr := exec_writeReuse (p := raw) (F := mkReuseUWrapper lay cls)
    (B := (mkReuseUWrapper lay cls).blocks[0]!) (fn := l.reuseUWrapper idx) (lbl := 0)
    (base := 0) (addr := slotVal) (hdr := hdr) (ctx := ctx) (rest := caller' :: rest)
    hwrapF hblk0 hw0 hbody0 hwa (mem := mem)
  cases hwm : writeReuseMem mem slotVal hdr vals with
  | none =>
    rw [hwm] at hwr
    exact .charge hstep1 (by simpa [wFr0] using hwr)
  | some mem' =>
    rw [hwm] at hwr
    have sRet : Lir.semStep raw
        { mem := mem', ctx, stack := { fn := l.reuseUWrapper idx, label := 0, pos := 1 + c.arity, env := wEnv, dsts := [] } :: caller' :: rest } =
        .next { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst slotVal, dsts := [] } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := l.reuseUWrapper idx, label := 0, pos := 1 + c.arity, env := wEnv, dsts := [] })
        hwrapF hblk0 (by simp [mkReuseUWrapper, hnobj]; omega)]
      simp [mkReuseUWrapper, Lir.evalArgs, Lir.Arg.eval, hw0, Lir.bindParams, caller']
    have hwr' : Sem.Star (Lir.semStep raw) { mem, ctx, stack := wFr0 :: caller' :: rest } 0
        { mem := mem', ctx, stack := { fn := l.reuseUWrapper idx, label := 0, pos := 1 + c.arity, env := wEnv, dsts := [] } :: caller' :: rest } := by
      simpa [wFr0, List.length_map, List.length_range] using hwr
    exact ⟨_, hstep1, hwr'.trans (.free sRet (.refl _))⟩

theorem inl_reuseU_exec {l : Layout} {raw : Lir.Program}
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 restStmts : List Lir.Stmt} {dst slot : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    {slotVal : Lir.Word} {vals : List Lir.Word}
    (hltFn : fr.fn < l.sourceCount) (hF : raw.funcs[fr.fn]? = some F)
    (hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = .call [dst] (l.reuseUWrapper idx) (.v slot :: args) :: restStmts)
    (hclsSite : classify l (.call [dst] (l.reuseUWrapper idx) (.v slot :: args)) =
      some (.reuseU dst slot idx lay cls args))
    (hposB : rawPos < B.body.size)
    (hgetB : B.body[rawPos] = .call [dst] (l.reuseUWrapper idx) (.v slot :: args))
    (hslot : fr.env[slot]? = some slotVal)
    (hargs : Lir.evalArgs fr.env args = some vals) :
    let inl := inlineProgram l raw
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    ChunkPos l F b B (rawPos + 1) fr.label (fr.pos + (2 + args.length)) ∧
    match writeReuseMem mem slotVal hdr vals with
    | some mem' =>
      ∃ s₂, Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₂ false ∧
        Sem.Star (Lir.semStep inl) s₂ 0
          { mem := mem', ctx, stack := { fr with pos := fr.pos + (2 + args.length), env := fr.env.insert dst slotVal, dsts := [] } :: rest }
    | none =>
      Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 .stuck := by
  intro inl hdr
  have hnp : ∀ s2 rest2, restStmts = s2 :: rest2 →
      classifyPair l (.call [dst] (l.reuseUWrapper idx) (.v slot :: args)) s2 = none :=
    fun s2 _ _ => by simp [classifyPair, hclsSite]
  let bodyStmts : List Lir.Stmt :=
    .store .w64 (cellAddr slot 0) (.imm hdr) :: mkFieldStores slot 0 args ++ [.assign dst (.arg (.v slot))]
  have hbodyLen : bodyStmts.length = 2 + args.length := by
    simp [bodyStmts, mkFieldStores_length]; omega
  have hexp : expandStmts l (newLabel l F) B.term B.cold rest0 fr.label tmp params acc =
      expandStmts l (newLabel l F) B.term B.cold restStmts fr.label tmp params (bodyStmts.reverse ++ acc) := by
    rw [hrest, expandStmts_cons_single _ _ _ _ _ _ _ _ _ _ hnp]
    simp [stepSingle, hclsSite, bodyStmts, hdr]
  have cpNext : ChunkAt l F b B (rawPos + 1) fr.label (fr.pos + (2 + args.length)) tmp params
      (bodyStmts.reverse ++ acc) restStmts := {
    bLookup := hcp.bLookup
    tmpGe := hcp.tmpGe
    split := by
      have htake : B.body.toList.take (rawPos + 1) =
          B.body.toList.take rawPos ++ [.call [dst] (l.reuseUWrapper idx) (.v slot :: args)] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB, hgetB]; simp
      rw [htake, List.append_assoc]; simpa [hrest] using hcp.split
    posLe := by omega
    blocksMatch := fun k blk hk => hcp.blocksMatch k blk (by rw [hexp]; exact hk)
    inPosEq := by rw [hcp.inPosEq, List.length_append, List.length_reverse, hbodyLen]; omega
    endLbl := by
      have := hcp.endLbl
      rw [hrest, stmtsExtra_cons_nonPair hnp, stmtExtra, hclsSite] at this
      simpa [siteExtra] using this }
  refine ⟨⟨_, _, _, _, cpNext⟩, ?_⟩
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  obtain ⟨blk, post, h0, _, hblkBody, _, _⟩ :=
    ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold restStmts fr.label tmp params
      (bodyStmts.reverse ++ acc)
  have hblk : (inlineFunc l F).blocks[fr.label]? = some blk := by
    simpa using cpNext.blocksMatch 0 blk h0
  have hbodySplit : blk.body.toList = acc.reverse ++
      (.store .w64 (cellAddr slot 0) (.imm hdr) :: mkFieldStores slot 0 args) ++
      ([.assign dst (.arg (.v slot))] ++ post) := by
    simpa [bodyStmts, List.reverse_append, List.reverse_reverse, List.append_assoc] using hblkBody
  have hwr := exec_writeReuse (p := inl) (F := inlineFunc l F) (B := blk) (fn := fr.fn) (lbl := fr.label)
    (base := slot) (addr := slotVal) (hdr := hdr) (ctx := ctx) (rest := rest)
    hF' hblk hslot hbodySplit hargs (mem := mem)
  have hpreLen : acc.reverse.length = fr.pos := by rw [List.length_reverse, ← hcp.inPosEq]
  have hfrEq : ({ fn := fr.fn, label := fr.label, pos := acc.reverse.length, env := fr.env, dsts := [] } : Lir.Frame) = fr := by
    cases fr; simp only [hpreLen] at *; subst hdsts; rfl
  cases hwm : writeReuseMem mem slotVal hdr vals with
  | none =>
    rw [hwm] at hwr
    rwa [hfrEq] at hwr
  | some mem' =>
    rw [hwm] at hwr
    have hposAsn : fr.pos + (1 + args.length) < blk.body.size := by
      have := congrArg List.length hbodySplit
      simp only [Array.length_toList, List.length_append, List.length_cons, mkFieldStores_length, hpreLen] at this
      omega
    have hgetAsn : blk.body[fr.pos + (1 + args.length)] = .assign dst (.arg (.v slot)) := by
      have h1 : blk.body.toList[fr.pos + (1 + args.length)]? = some (.assign dst (.arg (.v slot))) := by
        rw [hbodySplit]
        have hlen1 : (acc.reverse ++ (.store .w64 (cellAddr slot 0) (.imm hdr) :: mkFieldStores slot 0 args)).length =
            fr.pos + (1 + args.length) := by
          simp [hpreLen, mkFieldStores_length]; omega
        rw [List.getElem?_append_right (by omega), hlen1, Nat.sub_self]; rfl
      simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hposAsn, Option.some.injEq] at h1
      exact h1
    have sAsn : Lir.semStep inl
        { mem := mem', ctx, stack := { fr with pos := fr.pos + (1 + args.length), dsts := [] } :: rest } =
        .next { mem := mem', ctx, stack := { fr with pos := fr.pos + (2 + args.length), env := fr.env.insert dst slotVal, dsts := [] } :: rest } false := by
      apply Lir.semStep_next.mpr
      have h1 := Lir.step_stmt (fr := { fr with pos := fr.pos + (1 + args.length), dsts := [] })
        (mem := mem') (ctx := ctx) (rest := rest) (ρ' := fr.env.insert dst slotVal) (mem' := mem')
        hF' hblk hposAsn hgetAsn rfl (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, hslot])
      have hidx : fr.pos + (1 + args.length) + 1 = fr.pos + (2 + args.length) := by omega
      simpa [hidx] using h1
    have hstar : Sem.Star (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0
        { mem := mem', ctx, stack := { fr with pos := fr.pos + (2 + args.length), env := fr.env.insert dst slotVal, dsts := [] } :: rest } := by
      have hwr' : Sem.Star (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0
          { mem := mem', ctx, stack := { fr with pos := fr.pos + (1 + args.length), dsts := [] } :: rest } := by
        have h2 : { fn := fr.fn, label := fr.label, pos := acc.reverse.length + (1 + args.length), env := fr.env, dsts := [] } =
            { fr with pos := fr.pos + (1 + args.length), dsts := [] } := by
          cases fr; simp [hpreLen]
        rwa [hfrEq, h2] at hwr
      exact hwr'.trans (.free sAsn (.refl _))
    exact star_zero_split hstar (fun heq => by
      have hst := congrArg (fun s => (s.stack.head?.map (·.pos))) heq
      simp at hst)

/-- Dynamic `reuse` raw execution on the hot path (`slotVal & 1 == 0`). -/
theorem raw_reuse_hot_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {dst slot : Lir.VReg} {idx : Nat} {c : Lam.CtorInfo}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    {slotVal : Lir.Word} {vals : List Lir.Word}
    (hF : raw.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B)
    (hpos : fr.pos < B.body.size)
    (hc : l.ctors[idx]? = some c)
    (hlay : lay = Rt.Rc.CellLayout.ofFields c.arity c.tag)
    (hcls : lay.cls? = some cls) (hlen : args.length = c.arity)
    (hstmt : B.body[fr.pos] = .call [dst] (l.reuseWrapper idx) (.v slot :: args))
    (hslot : fr.env[slot]? = some slotVal)
    (hargs : Lir.evalArgs fr.env args = some vals)
    (hcell : Lir.Cond.holds .tnz .w64 slotVal 1 = false) :
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    match writeReuseMem mem slotVal hdr vals with
    | some mem' =>
      ∃ s₁, Lir.semStep raw { mem, ctx, stack := fr :: rest } = .next s₁ true ∧
        Sem.Star (Lir.semStep raw) s₁ 0
          { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst slotVal, dsts := [] } :: rest }
    | none =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 1 .stuck := by
  intro hdr
  have hvlen : vals.length = c.arity := by have := evalArgs_length hargs; omega
  have hfullArgs : Lir.evalArgs fr.env (.v slot :: args) = some (slotVal :: vals) := by
    simp only [Lir.evalArgs, List.mapM_cons, Lir.Arg.eval, hslot, Option.bind_eq_bind, Option.bind_some]
    rw [show List.mapM (Lir.Arg.eval fr.env) args = some vals from hargs]; rfl
  obtain ⟨wEnv, hwBind, _, hwLookup⟩ :=
    bindParams_range_lookup (c.arity + 1) 0 (slotVal :: vals) {} (by simp [hvlen])
  rw [← List.range_eq_range'] at hwBind
  have hwrapF : raw.funcs[l.reuseWrapper idx]? = some (mkReuseWrapper (l.allocProc idx) lay cls) := by
    rw [hlay]; exact hr.reuseWrap idx c cls hc (by rwa [← hlay])
  have hnobj : lay.nobj = c.arity := by rw [hlay]; rfl
  let caller' : Lir.Frame := { fr with pos := fr.pos + 1, dsts := [dst] }
  let wFr0 : Lir.Frame := { fn := l.reuseWrapper idx, label := 0, pos := 0, env := wEnv }
  have hstep1 : Lir.semStep raw { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := wFr0 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call hF hB hpos hstmt hfullArgs
      (by simp [Lir.enter, hwrapF, mkReuseWrapper, hnobj, hwBind, wFr0])
  have hw0 : wEnv[0]? = some slotVal := by simpa using hwLookup 0 (by omega)
  have hblk0 : (mkReuseWrapper (l.allocProc idx) lay cls).blocks[0]? =
      some { term := .br .tnz .w64 (.v 0) (.imm 1) ⟨2, []⟩ ⟨1, []⟩ } := rfl
  have hblk1 : (mkReuseWrapper (l.allocProc idx) lay cls).blocks[1]? =
      some (mkReuseWrapper (l.allocProc idx) lay cls).blocks[1]! := rfl
  have hstepBr : Lir.semStep raw { mem, ctx, stack := wFr0 :: caller' :: rest } =
      .next { mem, ctx, stack := { fn := l.reuseWrapper idx, label := 1, pos := 0, env := wEnv } :: caller' :: rest } false := by
    apply Lir.semStep_next.mpr
    rw [Lir.step_term (fr := wFr0) hwrapF hblk0 rfl]
    simp [wFr0, Lir.Arg.eval, hw0, hcell, Lir.takeEdge, Lir.evalArgs, mkReuseWrapper, Lir.bindParams]
  have hwa : Lir.evalArgs wEnv ((List.range c.arity).map fun j => Lir.Arg.v (j + 1)) = some vals := by
    rw [List.range_eq_range', ← hvlen]
    exact evalArgs_range_v wEnv 0 vals (fun i hi => by
      have h1 := hwLookup (i + 1) (by omega)
      simpa [Nat.add_comm] using h1)
  have hbody1 : (mkReuseWrapper (l.allocProc idx) lay cls).blocks[1]!.body.toList =
      [] ++ (.store .w64 (cellAddr 0 0) (.imm hdr) ::
        mkFieldStores 0 0 ((List.range c.arity).map fun j => Lir.Arg.v (j + 1))) ++ [] := by
    simp only [mkReuseWrapper, hnobj, List.nil_append, List.append_nil, Array.getElem!_eq_getD,
      Array.getD, List.size_toArray, List.length_cons, List.length_nil,
      show 1 < 3 by decide, ↓reduceDIte]
    simpa [hdr, hnobj] using mkReuseU_stores_eq c.arity hdr
  have hwr := exec_writeReuse (p := raw) (F := mkReuseWrapper (l.allocProc idx) lay cls)
    (B := (mkReuseWrapper (l.allocProc idx) lay cls).blocks[1]!) (fn := l.reuseWrapper idx) (lbl := 1)
    (base := 0) (addr := slotVal) (hdr := hdr) (ctx := ctx) (rest := caller' :: rest)
    hwrapF hblk1 hw0 hbody1 hwa (mem := mem)
  cases hwm : writeReuseMem mem slotVal hdr vals with
  | none =>
    rw [hwm] at hwr
    exact .charge hstep1 (.free hstepBr (by simpa using hwr))
  | some mem' =>
    rw [hwm] at hwr
    have sRet : Lir.semStep raw
        { mem := mem', ctx, stack := { fn := l.reuseWrapper idx, label := 1, pos := 1 + c.arity, env := wEnv, dsts := [] } :: caller' :: rest } =
        .next { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst slotVal, dsts := [] } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := l.reuseWrapper idx, label := 1, pos := 1 + c.arity, env := wEnv, dsts := [] })
        hwrapF hblk1 (by simp [mkReuseWrapper, hnobj]; omega)]
      simp [mkReuseWrapper, Lir.evalArgs, Lir.Arg.eval, hw0, Lir.bindParams, caller']
    have hwr' : Sem.Star (Lir.semStep raw)
        { mem, ctx, stack := { fn := l.reuseWrapper idx, label := 1, pos := 0, env := wEnv } :: caller' :: rest } 0
        { mem := mem', ctx, stack := { fn := l.reuseWrapper idx, label := 1, pos := 1 + c.arity, env := wEnv, dsts := [] } :: caller' :: rest } := by
      simpa [List.length_map, List.length_range] using hwr
    exact ⟨_, hstep1, .free hstepBr (hwr'.trans (.free sRet (.refl _)))⟩

/-- Dynamic `reuse` raw execution on the cold path (`slotVal & 1 != 0`, fresh allocation). -/
theorem raw_reuse_cold_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {dst slot : Lir.VReg} {idx : Nat} {c : Lam.CtorInfo}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    {slotVal : Lir.Word} {vals : List Lir.Word}
    (hF : raw.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B)
    (hpos : fr.pos < B.body.size)
    (hc : l.ctors[idx]? = some c)
    (hlay : lay = Rt.Rc.CellLayout.ofFields c.arity c.tag)
    (hcls : lay.cls? = some cls) (hok : lay.ok = true) (hlen : args.length = c.arity)
    (hstmt : B.body[fr.pos] = .call [dst] (l.reuseWrapper idx) (.v slot :: args))
    (hslot : fr.env[slot]? = some slotVal)
    (hargs : Lir.evalArgs fr.env args = some vals)
    (himm : Lir.Cond.holds .tnz .w64 slotVal 1 = true) :
    match evalAllocReserve lay cls mem ctx with
    | .ok addr mem₂ =>
      match writeFieldsMem mem₂ addr 0 vals with
      | some mem' =>
        ∃ s₁, Lir.semStep raw { mem, ctx, stack := fr :: rest } = .next s₁ true ∧
          Sem.Star (Lir.semStep raw) s₁ 1
            { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst addr, dsts := [] } :: rest }
      | none =>
        Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 2 .stuck
    | .oom =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 2 (.resource .heap)
    | .stuck =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 2 .stuck := by
  have hvlen : vals.length = c.arity := by have := evalArgs_length hargs; omega
  have hfullArgs : Lir.evalArgs fr.env (.v slot :: args) = some (slotVal :: vals) := by
    simp only [Lir.evalArgs, List.mapM_cons, Lir.Arg.eval, hslot, Option.bind_eq_bind, Option.bind_some]
    rw [show List.mapM (Lir.Arg.eval fr.env) args = some vals from hargs]; rfl
  obtain ⟨wEnv, hwBind, _, hwLookup⟩ :=
    bindParams_range_lookup (c.arity + 1) 0 (slotVal :: vals) {} (by simp [hvlen])
  rw [← List.range_eq_range'] at hwBind
  have hwrapF : raw.funcs[l.reuseWrapper idx]? = some (mkReuseWrapper (l.allocProc idx) lay cls) := by
    rw [hlay]; exact hr.reuseWrap idx c cls hc (by rwa [← hlay])
  have hprocF : raw.funcs[l.allocProc idx]? = some (Rt.Rc.Gen.allocFunc lay cls) := by
    have := hr.allocProc idx c hc
    rw [← hlay, Rt.Rc.Gen.alloc_eq hok hcls] at this
    exact this
  have hnobj : lay.nobj = c.arity := by rw [hlay]; rfl
  let caller' : Lir.Frame := { fr with pos := fr.pos + 1, dsts := [dst] }
  let wFr0 : Lir.Frame := { fn := l.reuseWrapper idx, label := 0, pos := 0, env := wEnv }
  have hstep1 : Lir.semStep raw { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := wFr0 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call hF hB hpos hstmt hfullArgs
      (by simp [Lir.enter, hwrapF, mkReuseWrapper, hnobj, hwBind, wFr0])
  have hw0 : wEnv[0]? = some slotVal := by simpa using hwLookup 0 (by omega)
  have hblk0 : (mkReuseWrapper (l.allocProc idx) lay cls).blocks[0]? =
      some { term := .br .tnz .w64 (.v 0) (.imm 1) ⟨2, []⟩ ⟨1, []⟩ } := rfl
  have hblk2 : (mkReuseWrapper (l.allocProc idx) lay cls).blocks[2]? =
      some (mkReuseWrapper (l.allocProc idx) lay cls).blocks[2]! := rfl
  have hstepBr : Lir.semStep raw { mem, ctx, stack := wFr0 :: caller' :: rest } =
      .next { mem, ctx, stack := { fn := l.reuseWrapper idx, label := 2, pos := 0, env := wEnv } :: caller' :: rest } false := by
    apply Lir.semStep_next.mpr
    rw [Lir.step_term (fr := wFr0) hwrapF hblk0 rfl]
    simp [wFr0, Lir.Arg.eval, hw0, himm, Lir.takeEdge, Lir.evalArgs, mkReuseWrapper, Lir.bindParams]
  let pFr0 : Lir.Frame := { fn := l.allocProc idx, label := 0, pos := 0, env := {} }
  let wRet : Lir.Frame := { fn := l.reuseWrapper idx, label := 2, pos := 1, env := wEnv, dsts := [c.arity + 1] }
  have hstepCall : Lir.semStep raw
      { mem, ctx, stack := { fn := l.reuseWrapper idx, label := 2, pos := 0, env := wEnv } :: caller' :: rest } =
      .next { mem, ctx, stack := pFr0 :: wRet :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (fr := { fn := l.reuseWrapper idx, label := 2, pos := 0, env := wEnv })
      (rs := [c.arity + 1]) (g := l.allocProc idx) (as := []) (vs := [])
      hwrapF hblk2 (by simp [mkReuseWrapper]) (by simp [mkReuseWrapper, hnobj])
      (by simp [Lir.evalArgs]) (by simp [Lir.enter, hprocF, Rt.Rc.Gen.allocFunc, Lir.bindParams, pFr0])
  have halloc := raw_allocProc_exec hr hc hlay hcls hok (ctx := ctx) (mem := mem)
    (caller := wRet) (rest := caller' :: rest) (dst := c.arity + 1) rfl
  cases hres : evalAllocReserve lay cls mem ctx with
  | oom =>
    dsimp only
    rw [hres] at halloc
    exact .charge hstep1 (.free hstepBr (.charge hstepCall halloc))
  | stuck =>
    dsimp only
    rw [hres] at halloc
    exact .charge hstep1 (.free hstepBr (.charge hstepCall halloc))
  | ok addr mem₂ =>
    dsimp only
    rw [hres] at halloc
    let wEnv1 := wEnv.insert (c.arity + 1) addr
    have hw1Addr : wEnv1[c.arity + 1]? = some addr := by simp [wEnv1]
    have hwa1 : Lir.evalArgs wEnv1 ((List.range c.arity).map fun j => Lir.Arg.v (j + 1)) = some vals := by
      rw [List.range_eq_range', ← hvlen]
      exact evalArgs_range_v wEnv1 0 vals (fun i hi => by
        rw [Lir.env_insert_ne _ _ (by omega)]
        have h1 := hwLookup (i + 1) (by omega)
        simpa [Nat.add_comm] using h1)
    have hstoresEq : ((List.range c.arity).map fun j =>
        Lir.Stmt.store .w64 { base := some (.v (c.arity + 1)), disp := Int.ofNat (8 * (j + 1)) } (.v (j + 1))) =
        mkFieldStores (c.arity + 1) 0 ((List.range c.arity).map fun j => Lir.Arg.v (j + 1)) := by
      have haux : ∀ k m, ((List.range' k m).map fun j =>
          Lir.Stmt.store .w64 { base := some (.v (c.arity + 1)), disp := Int.ofNat (8 * (j + 1)) } (.v (j + 1))) =
          mkFieldStores (c.arity + 1) k ((List.range' k m).map fun j => Lir.Arg.v (j + 1)) := by
        intro k m; induction m generalizing k with
        | zero => rfl
        | succ m ih =>
          simp only [List.range'_succ, List.map_cons, mkFieldStores, cellAddr]
          exact congrArg _ (ih (k + 1))
      rw [List.range_eq_range']; exact haux 0 c.arity
    have hbody2 : (mkReuseWrapper (l.allocProc idx) lay cls).blocks[2]!.body.toList =
        [Lir.Stmt.call [c.arity + 1] (l.allocProc idx) []] ++
          mkFieldStores (c.arity + 1) 0 ((List.range c.arity).map fun j => Lir.Arg.v (j + 1)) ++ [] := by
      simp only [mkReuseWrapper, hnobj, List.cons_append, List.nil_append, List.append_nil,
        Array.getElem!_eq_getD, Array.getD, List.size_toArray, List.length_cons, List.length_nil,
        show 2 < 3 by decide, ↓reduceDIte]
      rw [hstoresEq]
      rfl
    have hfs := exec_mkFieldStores (p := raw) (F := mkReuseWrapper (l.allocProc idx) lay cls)
      (B := (mkReuseWrapper (l.allocProc idx) lay cls).blocks[2]!)
      (fn := l.reuseWrapper idx) (lbl := 2) (dst := c.arity + 1) (addr := addr)
      (ctx := ctx) (rest := caller' :: rest) (env := wEnv1)
      hwrapF hblk2 hw1Addr hbody2 hwa1 (mem := mem₂)
    cases hwf : writeFieldsMem mem₂ addr 0 vals with
    | none =>
      dsimp only
      rw [hwf] at hfs
      exact .charge hstep1 (.free hstepBr (.charge hstepCall
        (star_reaches halloc (by simpa [wRet, wEnv1] using hfs))))
    | some mem' =>
      dsimp only
      rw [hwf] at hfs
      have sRet : Lir.semStep raw
          { mem := mem', ctx, stack := { fn := l.reuseWrapper idx, label := 2, pos := 1 + c.arity, env := wEnv1, dsts := [] } :: caller' :: rest } =
          .next { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst addr, dsts := [] } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := l.reuseWrapper idx, label := 2, pos := 1 + c.arity, env := wEnv1, dsts := [] })
          hwrapF hblk2 (by simp [mkReuseWrapper, hnobj]; omega)]
        simp [mkReuseWrapper, hnobj, Lir.evalArgs, Lir.Arg.eval, hw1Addr, Lir.bindParams, caller']
      have hfs' : Sem.Star (Lir.semStep raw)
          { mem := mem₂, ctx, stack := { wRet with env := wEnv1, dsts := [] } :: caller' :: rest } 0
          { mem := mem', ctx, stack := { fn := l.reuseWrapper idx, label := 2, pos := 1 + c.arity, env := wEnv1, dsts := [] } :: caller' :: rest } := by
        simpa [wRet, wEnv1, List.length_map, List.length_range] using hfs
      exact ⟨_, hstep1, .free hstepBr (.charge hstepCall (halloc.trans (hfs'.trans (.free sRet (.refl _)))))⟩

/-- Dynamic `reuse` inlined execution (hot path `slotVal & 1 == 0` OR inlined 6-block fresh alloc). -/
theorem inl_reuse_exec {l : Layout} {raw : Lir.Program}
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 restStmts : List Lir.Stmt} {dst slot : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    {slotVal : Lir.Word} {vals : List Lir.Word}
    (hltFn : fr.fn < l.sourceCount) (hF : raw.funcs[fr.fn]? = some F)
    (hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = .call [dst] (l.reuseWrapper idx) (.v slot :: args) :: restStmts)
    (hclsSite : classify l (.call [dst] (l.reuseWrapper idx) (.v slot :: args)) =
      some (.reuse dst slot idx lay cls args))
    (hposB : rawPos < B.body.size)
    (hgetB : B.body[rawPos] = .call [dst] (l.reuseWrapper idx) (.v slot :: args))
    (hslot : fr.env[slot]? = some slotVal)
    (hargs : Lir.evalArgs fr.env args = some vals)
    (hargsLt : argsMax args 0 < freshBase F) :
    let inl := inlineProgram l raw
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    ChunkPos l F b B (rawPos + 1) (fr.label + 7) (1 + args.length) ∧
    (Lir.Cond.holds .tnz .w64 slotVal 1 = false →
      match writeReuseMem mem slotVal hdr vals with
      | some mem' =>
        ∃ s₂, Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₂ false ∧
          Sem.Star (Lir.semStep inl) s₂ 0
            { mem := mem', ctx, stack := { fr with label := fr.label + 7, pos := 1 + args.length, env := fr.env.insert dst slotVal, dsts := [] } :: rest }
      | none =>
        Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 .stuck) ∧
    (Lir.Cond.holds .tnz .w64 slotVal 1 = true →
      match evalAllocReserve lay cls mem ctx with
      | .ok addr mem₂ =>
        match writeFieldsMem mem₂ addr 0 vals with
        | some mem' =>
          ∃ env' s₂,
            Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₂ false ∧
            Sem.Star (Lir.semStep inl) s₂ 0
              { mem := mem', ctx, stack := { fr with label := fr.label + 7, pos := 1 + args.length, env := env', dsts := [] } :: rest } ∧
            AgreeBelow (freshBase F) (fr.env.insert dst addr) env'
        | none =>
          Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 .stuck
      | .oom =>
        Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 (.resource .heap)
      | .stuck =>
        Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 .stuck) := by
  intro inl hdr
  obtain ⟨c, hc, _, hlay, hclsOk, hlen, _, _, hnoDst⟩ := classify_eq_reuse hclsSite
  have hnp : ∀ s2 rest2, restStmts = s2 :: rest2 →
      classifyPair l (.call [dst] (l.reuseWrapper idx) (.v slot :: args)) s2 = none :=
    fun s2 _ _ => by simp [classifyPair, hclsSite]
  let pubInit : List Lir.Stmt :=
    Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr) :: mkFieldStores dst 0 args
  have hpubLen : pubInit.length = 1 + args.length := by
    simp only [pubInit, List.length_cons, mkFieldStores_length]; omega
  have hexp : expandStmts l (newLabel l F) B.term B.cold rest0 fr.label tmp params acc =
      let r := stepSingle l B.cold (.call [dst] (l.reuseWrapper idx) (.v slot :: args)) fr.label tmp params acc
      let t := expandStmts l (newLabel l F) B.term B.cold restStmts r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
      (r.1 ++ t.1, t.2) := by
    rw [hrest, expandStmts_cons_single _ _ _ _ _ _ _ _ _ _ hnp]
  have cpNext : ChunkAt l F b B (rawPos + 1) (fr.label + 7) (1 + args.length) (tmp + 5) [dst] pubInit.reverse restStmts := {
    bLookup := hcp.bLookup
    tmpGe := by have := hcp.tmpGe; omega
    split := by
      have htake : B.body.toList.take (rawPos + 1) =
          B.body.toList.take rawPos ++ [.call [dst] (l.reuseWrapper idx) (.v slot :: args)] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB, hgetB]; simp
      rw [htake, List.append_assoc]; simpa [hrest] using hcp.split
    posLe := by omega
    blocksMatch := fun k blk hk => by
      have h := hcp.blocksMatch (7 + k) blk (by
        rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; dsimp only
        rw [Nat.add_comm 7 k]; exact hk)
      simpa [Nat.add_assoc] using h
    inPosEq := by rw [List.length_reverse, hpubLen]
    endLbl := by
      have := hcp.endLbl
      rw [hrest, stmtsExtra_cons_nonPair hnp, stmtExtra, hclsSite] at this
      simp only [siteExtra] at this
      dsimp only [Lir.Label] at this ⊢; omega }
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  have hb0 : (inlineFunc l F).blocks[fr.label]? = some ({
      params, body := acc.reverse.toArray,
      term := .br .tnz .w64 (.v slot) (.imm 1) ⟨fr.label + 1, []⟩ ⟨fr.label + 7, [.v slot]⟩, cold := B.cold } : Lir.Block) := by
    simpa using hcp.blocksMatch 0 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; rfl)
  have hb1 : (inlineFunc l F).blocks[fr.label + 1]? = some ({
      body := #[.assign tmp (.load .w64 .zero (ctxAddr (Int.ofNat (8 * cls))))],
      term := .br .eq .w64 (.v tmp) (.imm 0) ⟨fr.label + 3, []⟩ ⟨fr.label + 2, []⟩, cold := true } : Lir.Block) :=
    hcp.blocksMatch 1 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; rfl)
  have hb2 : (inlineFunc l F).blocks[fr.label + 2]? = some ({
      body := #[.assign (tmp + 1) (.load .w64 .zero (cellAddr tmp)),
        .store .w64 (ctxAddr (Int.ofNat (8 * cls))) (.v (tmp + 1))],
      term := .jump ⟨fr.label + 7, [.v tmp]⟩, cold := true } : Lir.Block) :=
    hcp.blocksMatch 2 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; rfl)
  have hb3 : (inlineFunc l F).blocks[fr.label + 3]? = some ({
      body := #[.assign (tmp + 2) (.load .w64 .zero (ctxAddr Rt.bumpOff)),
        .assign (tmp + 3) (.load .w64 .zero (ctxAddr Rt.limitOff))],
      term := .brOvf .addC (tmp + 4) (.v (tmp + 2)) (.imm (UInt64.ofNat (Rt.Rc.classBytes cls)))
        ⟨fr.label + 4, []⟩ ⟨fr.label + 6, []⟩, cold := true } : Lir.Block) :=
    hcp.blocksMatch 3 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; rfl)
  have hb4 : (inlineFunc l F).blocks[fr.label + 4]? = some ({
      body := #[],
      term := .br .ule .w64 (.v (tmp + 4)) (.v (tmp + 3)) ⟨fr.label + 5, []⟩ ⟨fr.label + 6, []⟩,
      cold := true } : Lir.Block) :=
    hcp.blocksMatch 4 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; rfl)
  have hb5 : (inlineFunc l F).blocks[fr.label + 5]? = some ({
      body := #[.store .w64 (ctxAddr Rt.bumpOff) (.v (tmp + 4))],
      term := .jump ⟨fr.label + 7, [.v (tmp + 2)]⟩, cold := true } : Lir.Block) :=
    hcp.blocksMatch 5 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; rfl)
  have hb6 : (inlineFunc l F).blocks[fr.label + 6]? = some ({
      body := #[], term := .fail .heap, cold := true } : Lir.Block) :=
    hcp.blocksMatch 6 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; rfl)
  obtain ⟨pubBlk, postJ, hpub0, hpubP, hpubBody0, _, _⟩ :=
    ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold restStmts (fr.label + 7) (tmp + 5) [dst] pubInit.reverse
  have hpub : (inlineFunc l F).blocks[fr.label + 7]? = some pubBlk := by
    simpa using cpNext.blocksMatch 0 pubBlk hpub0
  have hpubBody : pubBlk.body.toList = [.store .w64 (cellAddr dst) (.imm hdr)] ++ mkFieldStores dst 0 args ++ postJ := by
    simpa [pubInit, List.reverse_reverse, List.cons_append] using hpubBody0
  have hpos0 : fr.pos = acc.reverse.toArray.size := by simp [hcp.inPosEq]
  refine ⟨⟨_, _, _, _, cpNext⟩, ?_, ?_⟩
  · intro hcell
    have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
        .next { mem, ctx, stack := { fr with label := fr.label + 7, pos := 0, env := fr.env.insert dst slotVal } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term hF' hb0 hpos0]
      have hfwd : ¬ (fr.label + 7 ≤ fr.label) := by dsimp only [Lir.Label]; omega
      simp [Lir.Arg.eval, hslot, hcell, Lir.takeEdge, Lir.evalArgs, hpub, hpubP, Lir.bindParams, hfwd]
    have hargsIns : Lir.evalArgs (fr.env.insert dst slotVal) args = some vals := by
      rw [evalArgs_insert_not_mem (argsContainVReg_false hnoDst), hargs]
    have hpubBody' : pubBlk.body.toList =
        [] ++ (.store .w64 (cellAddr dst 0) (.imm hdr) :: mkFieldStores dst 0 args) ++ postJ := by
      simpa [cellAddr] using hpubBody
    have hwr := exec_writeReuse (p := inl) (F := inlineFunc l F) (B := pubBlk)
      (fn := fr.fn) (lbl := fr.label + 7) (base := dst) (addr := slotVal) (hdr := hdr)
      (ctx := ctx) (rest := rest) (env := fr.env.insert dst slotVal)
      hF' hpub (by simp) hpubBody' hargsIns (mem := mem)
    have hfrPub : ({ fn := fr.fn, label := fr.label + 7, pos := 0, env := fr.env.insert dst slotVal, dsts := [] } : Lir.Frame) =
        { fr with label := fr.label + 7, pos := 0, env := fr.env.insert dst slotVal } := by
      cases fr; dsimp only at hdsts; subst hdsts; rfl
    cases hwm : writeReuseMem mem slotVal hdr vals with
    | none =>
      rw [hwm] at hwr
      exact .free s1 (by simpa [hfrPub] using hwr)
    | some mem' =>
      rw [hwm] at hwr
      exact ⟨_, s1, by simpa [hfrPub] using hwr⟩
  · intro himm
    have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
        .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term hF' hb0 hpos0]
      have hfwd : ¬ (fr.label + 1 ≤ fr.label) := by dsimp only [Lir.Label]; omega
      simp [Lir.Arg.eval, hslot, himm, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams, hfwd]
    have hall := exec_inlineAlloc_blocks (p := inl) (F' := inlineFunc l F) (pubBlk := pubBlk)
      (fn := fr.fn) (base := fr.label + 1) (pubLbl := fr.label + 7)
      (aBase := tmp) (bound := freshBase F) (dst := dst) (lay := lay) (cls := cls)
      (args := args) (vals := vals) (postJ := postJ) (pre := none)
      (env0 := fr.env) (mem := mem) (ctx := ctx) (rest := rest)
      hF' (by dsimp only [Lir.Label]; omega) hcp.tmpGe hargsLt hnoDst (fun _ _ _ h => by cases h)
      hargs hpubP hpubBody hb1
      (by simpa [Nat.add_assoc] using hb2)
      (by simpa [Nat.add_assoc] using hb3)
      (by simpa [Nat.add_assoc] using hb4)
      (by simpa [Nat.add_assoc] using hb5)
      (by simpa [Nat.add_assoc] using hb6) hpub
    have hfr1 : ({ fn := fr.fn, label := fr.label + 1, pos := 0, env := fr.env } : Lir.Frame) =
        { fr with label := fr.label + 1, pos := 0 } := by
      cases fr; dsimp only at hdsts; subst hdsts; rfl
    cases hres : evalAllocReserve lay cls mem ctx with
    | oom =>
      dsimp only
      rw [hres] at hall
      exact .free s1 (by simpa [hfr1] using hall)
    | stuck =>
      dsimp only
      rw [hres] at hall
      exact .free s1 (by simpa [hfr1] using hall)
    | ok addr mem₂ =>
      dsimp only
      rw [hres] at hall
      dsimp only at hall
      cases hwf : writeFieldsMem mem₂ addr 0 vals with
      | none =>
        dsimp only
        rw [hwf] at hall
        exact .free s1 (by simpa [hfr1] using hall)
      | some mem' =>
        dsimp only
        rw [hwf] at hall
        dsimp only at hall
        obtain ⟨env', hstar, hag⟩ := hall
        exact ⟨env', _, s1, by simpa [hfr1] using hstar, hag⟩

/-! ## 5. `isUnique` + `reset` / `resetU` dec-loop helpers -/

/-- Outcome of the `isUnique` check (`x & 1 == 0 ∧ *(w32)(x+4) == 0`). -/
inductive UniqueCheck where
  | unique
  | shared
  | stuck
  deriving DecidableEq

def evalUniqueCheck (xVal : Lir.Word) (mem : X86.Memory) : UniqueCheck :=
  if Lir.Cond.holds .tnz .w64 xVal 1 then .shared
  else match Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none => .stuck
    | some cnt => if (X86.Width.w32.truncate cnt).toNat = 0 then .unique else .shared

theorem exec_isUniqueProc {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {xVal ctx : Lir.Word} {mem : X86.Memory} {caller : Lir.Frame} {rest : List Lir.Frame}
    {dst : Lir.VReg} (hdst : caller.dsts = [dst]) :
    let uFr : Lir.Frame := { fn := l.isUniqueProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal }
    match evalUniqueCheck xVal mem with
    | .unique =>
      Sem.Star (Lir.semStep raw) { mem, ctx, stack := uFr :: caller :: rest } 0
        { mem, ctx, stack := { caller with env := caller.env.insert dst 1, dsts := [] } :: rest }
    | .shared =>
      Sem.Star (Lir.semStep raw) { mem, ctx, stack := uFr :: caller :: rest } 0
        { mem, ctx, stack := { caller with env := caller.env.insert dst 0, dsts := [] } :: rest }
    | .stuck =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := uFr :: caller :: rest } 0 .stuck := by
  intro uFr
  have huF := hr.isUniqueProc
  unfold evalUniqueCheck
  by_cases htag : Lir.Cond.holds .tnz .w64 xVal 1 = true
  · simp only [htag, ↓reduceIte]
    have s0 : Lir.semStep raw { mem, ctx, stack := uFr :: caller :: rest } =
        .next { mem, ctx, stack := { uFr with label := 3 } :: caller :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := uFr) huF rfl rfl]
      simp [Rt.Rc.Gen.isUnique, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, uFr,
        Lir.Arg.eval, htag, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
    have s1 : Lir.semStep raw { mem, ctx, stack := { uFr with label := 3 } :: caller :: rest } =
        .next { mem, ctx, stack := { caller with env := caller.env.insert dst 0, dsts := [] } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { uFr with label := 3 }) huF rfl rfl]
      simp [Rt.Rc.Gen.isUnique, Rt.Rc.Procs.i, Lir.evalArgs, Lir.Arg.eval, hdst, Lir.bindParams]
    exact .free s0 (.free s1 (.refl _))
  · have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by simpa using htag
    simp only [htagF, Bool.false_eq_true, ↓reduceIte]
    have s0 : Lir.semStep raw { mem, ctx, stack := uFr :: caller :: rest } =
        .next { mem, ctx, stack := { uFr with label := 1 } :: caller :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := uFr) huF rfl rfl]
      simp [Rt.Rc.Gen.isUnique, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, uFr,
        Lir.Arg.eval, htagF, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
    have hub1 : Rt.Rc.Gen.isUnique.blocks[1]? =
        some { body := #[.assign 1 (.load .w32 .zero (Rt.Rc.Procs.cellAddr 0 4))],
               term := .br .eq .w32 (.v 1) (.imm 0) ⟨2, []⟩ ⟨3, []⟩ } := rfl
    cases hload : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none =>
      dsimp only
      refine .free s0 (.final ?_)
      have hst : Lir.step raw { mem, ctx, stack := { uFr with label := 1 } :: caller :: rest } = .stuck := by
        unfold Lir.step
        simp [uFr, huF, hub1, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
          addr_cell uFr.env ctx 0 xVal 4 (by simp [uFr]), hload]
      rw [Lir.semStep, hst]; exact .stuck
    | some cnt =>
      dsimp only
      let env1 := uFr.env.insert 1 cnt
      have s1 : Lir.semStep raw { mem, ctx, stack := { uFr with label := 1 } :: caller :: rest } =
          .next { mem, ctx, stack := { uFr with label := 1, pos := 1, env := env1 } :: caller :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { uFr with label := 1 }) (ρ' := env1) (mem' := mem)
          huF hub1 (by simp [uFr]) rfl rfl
          (by simp [uFr, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
            addr_cell uFr.env ctx 0 xVal 4 (by simp [uFr]), hload, env1])
      by_cases hz : (X86.Width.w32.truncate cnt).toNat = 0
      · simp only [hz, ↓reduceIte]
        have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = true := by rw [w32_eq_zero]; simp [hz]
        have s2 : Lir.semStep raw { mem, ctx, stack := { uFr with label := 1, pos := 1, env := env1 } :: caller :: rest } =
            .next { mem, ctx, stack := { uFr with label := 2, pos := 0, env := env1 } :: caller :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { uFr with label := 1, pos := 1, env := env1 }) huF rfl rfl]
          simp [Rt.Rc.Gen.isUnique, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
            env1, heq0, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        have s3 : Lir.semStep raw { mem, ctx, stack := { uFr with label := 2, pos := 0, env := env1 } :: caller :: rest } =
            .next { mem, ctx, stack := { caller with env := caller.env.insert dst 1, dsts := [] } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { uFr with label := 2, pos := 0, env := env1 }) huF rfl rfl]
          simp [Rt.Rc.Gen.isUnique, Rt.Rc.Procs.i, Lir.evalArgs, Lir.Arg.eval, hdst, Lir.bindParams]
        exact .free s0 (.free s1 (.free s2 (.free s3 (.refl _))))
      · simp only [hz, ↓reduceIte]
        have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = false := by rw [w32_eq_zero]; simp [hz]
        have s2 : Lir.semStep raw { mem, ctx, stack := { uFr with label := 1, pos := 1, env := env1 } :: caller :: rest } =
            .next { mem, ctx, stack := { uFr with label := 3, pos := 0, env := env1 } :: caller :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { uFr with label := 1, pos := 1, env := env1 }) huF rfl rfl]
          simp [Rt.Rc.Gen.isUnique, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
            env1, heq0, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        have s3 : Lir.semStep raw { mem, ctx, stack := { uFr with label := 3, pos := 0, env := env1 } :: caller :: rest } =
            .next { mem, ctx, stack := { caller with env := caller.env.insert dst 0, dsts := [] } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { uFr with label := 3, pos := 0, env := env1 }) huF rfl rfl]
          simp [Rt.Rc.Gen.isUnique, Rt.Rc.Procs.i, Lir.evalArgs, Lir.Arg.eval, hdst, Lir.bindParams]
        exact .free s0 (.free s1 (.free s2 (.free s3 (.refl _))))

/-- Dead fields of `mask` starting from index `k` up to `n`. -/
def deadFrom (n : Nat) (mask : UInt64) (k : Nat) : List Nat :=
  (List.range' k (n - k)).filter fun j => (mask &&& UInt64.ofNat (2 ^ (j + 1))) == 0

theorem deadFrom_zero (n : Nat) (mask : UInt64) : deadFrom n mask 0 = deadFields n mask := by
  simp [deadFrom, deadFields, List.range_eq_range']

theorem deadFrom_eq_nil (n : Nat) (mask : UInt64) {k : Nat} (hk : n ≤ k) :
    deadFrom n mask k = [] := by
  have : n - k = 0 := by omega
  simp [deadFrom, this]

theorem deadFrom_step {n k : Nat} (mask : UInt64) (hk : k < n) :
    deadFrom n mask k =
      if (mask &&& UInt64.ofNat (2 ^ (k + 1))) == 0 then k :: deadFrom n mask (k + 1)
      else deadFrom n mask (k + 1) := by
  unfold deadFrom
  have hsub : n - k = (n - (k + 1)) + 1 := by omega
  rw [hsub, List.range'_succ, List.filter_cons]

theorem deadFields_singleton_split {n d : Nat} {mask : UInt64}
    (hd : deadFields n mask = [d]) :
    d < n ∧ deadFrom n mask 0 = [d] ∧ deadFrom n mask (d + 1) = [] := by
  have hlt : d < n := deadFields_lt n mask (by rw [hd]; simp)
  have h0 : deadFrom n mask 0 = [d] := by rw [deadFrom_zero, hd]
  have hbit : (mask &&& UInt64.ofNat (2 ^ (d + 1))) == 0 :=
    beq_iff_eq.mpr (deadFields_bit_zero n mask (by rw [hd]; simp))
  have htail : deadFrom n mask (d + 1) = [] := by
    let p : Nat → Bool := fun j => (mask &&& UInt64.ofNat (2 ^ (j + 1))) == 0
    have hsplit : List.range' 0 n = List.range' 0 (d + 1) ++ List.range' (d + 1) (n - (d + 1)) := by
      have h := List.range'_append (s := 0) (m := d + 1) (n := n - (d + 1)) (step := 1)
      simpa [show d + 1 + (n - (d + 1)) = n by omega] using h.symm
    have hlen : ((List.range' 0 (d + 1)).filter p).length +
        ((List.range' (d + 1) (n - (d + 1))).filter p).length = 1 := by
      have h1 : (List.range' 0 n).filter p = [d] := by
        simpa [deadFields, List.range_eq_range', p] using hd
      rw [hsplit, List.filter_append] at h1
      have h2 := congrArg List.length h1
      simpa [List.length_append] using h2
    have hdMem : d ∈ (List.range' 0 (d + 1)).filter p := by
      rw [List.mem_filter, List.mem_range']
      exact ⟨⟨d, by omega, by omega⟩, hbit⟩
    have hpos : 0 < ((List.range' 0 (d + 1)).filter p).length := List.length_pos_of_mem hdMem
    have hzero : ((List.range' (d + 1) (n - (d + 1))).filter p).length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero hzero
  exact ⟨hlt, h0, htail⟩

/-- Abstract block-layout interface shared by `mkResetWrapper` (`base = 2, oldBase = 3`)
and `mkResetUWrapper` (`base = 1, oldBase = 2`) for the dead-field `decProc` loop. -/
structure DecLoopShape (decProc n base oldBase : Nat) (F : Lir.Func) : Prop where
  brBlk : ∀ j, j < n →
    F.blocks[base + 2 * j]? = some
      { term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (j + 1))))
          ⟨base + 2 * j + 2, []⟩ ⟨base + 2 * j + 1, []⟩ }
  callBlk : ∀ j, j < n →
    F.blocks[base + 2 * j + 1]? = some
      { body := #[.call [] decProc [.v (oldBase + j)]], term := .jump ⟨base + 2 * j + 2, []⟩ }
  retBlk : F.blocks[base + 2 * n]? = some { term := .ret [.v 0] }

private theorem w64_truncate_eq (w : Lir.Word) : X86.Width.w64.truncate w = w := by
  apply UInt64.eq_of_toBitVec_eq
  change w.toBitVec &&& (0xffffffffffffffff : UInt64).toBitVec = w.toBitVec
  have hall : (0xffffffffffffffff : UInt64).toBitVec = BitVec.allOnes 64 := by decide
  rw [hall, BitVec.and_allOnes]

private theorem flatMap_pair_get {α : Type} (f g : Nat → α) :
    ∀ (k m j : Nat), j < m →
      ((List.range' k m).flatMap fun i => [f i, g i])[2 * j]? = some (f (k + j)) ∧
      ((List.range' k m).flatMap fun i => [f i, g i])[2 * j + 1]? = some (g (k + j))
  | _, 0, _, hj => by omega
  | k, m + 1, 0, _ => by simp [List.range'_succ]
  | k, m + 1, j + 1, hj => by
    simp only [List.range'_succ, List.flatMap_cons, List.cons_append, List.nil_append]
    have ih := flatMap_pair_get f g (k + 1) m j (by omega)
    have h1 : 2 * (j + 1) = (2 * j) + 2 := by omega
    have h2 : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
    rw [h2, h1]
    simpa [Nat.add_assoc, Nat.add_comm 1] using ih

private theorem flatMap_pair_length {α : Type} (f g : Nat → α) (xs : List Nat) :
    (xs.flatMap fun i => [f i, g i]).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [List.flatMap_cons, ih]; omega

theorem mkResetWrapper_decLoopShape (isUniqueProc incProc decProc : Nat)
    (lay : Rt.Rc.CellLayout) (cls : Nat) :
    DecLoopShape decProc lay.nobj 2 3 (mkResetWrapper isUniqueProc incProc decProc lay cls) := by
  let n := lay.nobj
  let f : Nat → Lir.Block := fun j =>
    { term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (j + 1))))
        ⟨2 + 2 * j + 2, []⟩ ⟨2 + 2 * j + 1, []⟩ }
  let g : Nat → Lir.Block := fun j =>
    { body := #[.call [] decProc [.v (3 + j)]], term := .jump ⟨2 + 2 * j + 2, []⟩ }
  let mid := (List.range n).flatMap fun j => [f j, g j]
  have hmidLen : mid.length = 2 * n := by
    dsimp [mid]; rw [flatMap_pair_length, List.length_range]
  refine ⟨fun j hj => ?_, fun j hj => ?_, ?_⟩
  · have hfg := (flatMap_pair_get f g 0 n j hj).1
    rw [← List.range_eq_range', Nat.zero_add] at hfg
    simp only [mkResetWrapper, List.getElem?_toArray, List.cons_append, List.nil_append, List.append_assoc]
    have hidx : 2 + 2 * j = (2 * j) + 1 + 1 := by omega
    conv => lhs; rw [hidx]
    simp only [List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by rw [hmidLen]; omega)]
    exact hfg
  · have hfg := (flatMap_pair_get f g 0 n j hj).2
    rw [← List.range_eq_range', Nat.zero_add] at hfg
    simp only [mkResetWrapper, List.getElem?_toArray, List.cons_append, List.nil_append, List.append_assoc]
    have hidx : 2 + 2 * j + 1 = (2 * j + 1) + 1 + 1 := by omega
    conv => lhs; rw [hidx]
    simp only [List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by rw [hmidLen]; omega)]
    exact hfg
  · simp only [mkResetWrapper, List.getElem?_toArray, List.cons_append, List.nil_append, List.append_assoc]
    have hidx : 2 + 2 * n = 2 * n + 1 + 1 := by omega
    conv => lhs; rw [hidx]
    simp only [List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by rw [hmidLen]; omega), hmidLen, Nat.sub_self]
    rfl

theorem mkResetUWrapper_decLoopShape (decProc : Nat) (lay : Rt.Rc.CellLayout) (cls : Nat) :
    DecLoopShape decProc lay.nobj 1 2 (mkResetUWrapper decProc lay cls) := by
  let n := lay.nobj
  let f : Nat → Lir.Block := fun j =>
    { term := .br .tnz .w64 (.v 1) (.imm (UInt64.ofNat (2 ^ (j + 1))))
        ⟨1 + 2 * j + 2, []⟩ ⟨1 + 2 * j + 1, []⟩ }
  let g : Nat → Lir.Block := fun j =>
    { body := #[.call [] decProc [.v (2 + j)]], term := .jump ⟨1 + 2 * j + 2, []⟩ }
  let mid := (List.range n).flatMap fun j => [f j, g j]
  have hmidLen : mid.length = 2 * n := by
    dsimp [mid]; rw [flatMap_pair_length, List.length_range]
  refine ⟨fun j hj => ?_, fun j hj => ?_, ?_⟩
  · have hfg := (flatMap_pair_get f g 0 n j hj).1
    rw [← List.range_eq_range', Nat.zero_add] at hfg
    simp only [mkResetUWrapper, List.getElem?_toArray, List.cons_append, List.nil_append]
    have hidx : 1 + 2 * j = (2 * j) + 1 := by omega
    conv => lhs; rw [hidx]
    simp only [List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by rw [hmidLen]; omega)]
    exact hfg
  · have hfg := (flatMap_pair_get f g 0 n j hj).2
    rw [← List.range_eq_range', Nat.zero_add] at hfg
    simp only [mkResetUWrapper, List.getElem?_toArray, List.cons_append, List.nil_append]
    have hidx : 1 + 2 * j + 1 = (2 * j + 1) + 1 := by omega
    conv => lhs; rw [hidx]
    simp only [List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by rw [hmidLen]; omega)]
    exact hfg
  · simp only [mkResetUWrapper, List.getElem?_toArray, List.cons_append, List.nil_append]
    have hidx : 1 + 2 * n = 2 * n + 1 := by omega
    conv => lhs; rw [hidx]
    simp only [List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by rw [hmidLen]; omega), hmidLen, Nat.sub_self]
    rfl

/-- Advance the raw reset wrapper's `dec` loop from index `k ≤ n` until either the next dead
field `j` (stopping right after calling `decProc` on `wEnv[oldBase + j]`, charging 1 tick)
or the end of the loop (returning `xVal` to `caller` with `dsts = [dst]`, charging 0 ticks). -/
theorem raw_decLoop_step {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {wrapFn n base oldBase : Nat} {W : Lir.Func}
    (hW : raw.funcs[wrapFn]? = some W)
    (hshape : DecLoopShape l.decProc n base oldBase W)
    {wEnv : Lir.Env} {xVal mask ctx : Lir.Word} {mem : X86.Memory}
    {caller : Lir.Frame} {rest : List Lir.Frame} {dst : Lir.VReg}
    (hw0 : wEnv[0]? = some xVal) (hw1 : wEnv[1]? = some mask) (hdst : caller.dsts = [dst])
    (hvals : ∀ j < n, ∃ v, wEnv[oldBase + j]? = some v) :
    ∀ k, k ≤ n →
      match deadFrom n mask k with
      | [] =>
        Sem.Star (Lir.semStep raw)
          { mem, ctx, stack := { fn := wrapFn, label := base + 2 * k, pos := 0, env := wEnv } :: caller :: rest } 0
          { mem, ctx, stack := { caller with env := caller.env.insert dst xVal, dsts := [] } :: rest }
      | j :: rem =>
        ∃ _hj : j < n, ∃ val, wEnv[oldBase + j]? = some val ∧
          rem = deadFrom n mask (j + 1) ∧
          Sem.Star (Lir.semStep raw)
            { mem, ctx, stack := { fn := wrapFn, label := base + 2 * k, pos := 0, env := wEnv } :: caller :: rest } 1
            { mem, ctx, stack :=
              { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 val } ::
              { fn := wrapFn, label := base + 2 * j + 1, pos := 1, env := wEnv, dsts := [] } :: caller :: rest } := by
  intro k hk
  induction hd : n - k generalizing k with
  | zero =>
    have hkn : k = n := by omega
    subst k
    rw [deadFrom_eq_nil n mask (Nat.le_refl n)]
    have sRet : Lir.semStep raw
        { mem, ctx, stack := { fn := wrapFn, label := base + 2 * n, pos := 0, env := wEnv } :: caller :: rest } =
        .next { mem, ctx, stack := { caller with env := caller.env.insert dst xVal, dsts := [] } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := wrapFn, label := base + 2 * n, pos := 0, env := wEnv }) hW hshape.retBlk rfl]
      simp [Lir.evalArgs, Lir.Arg.eval, hw0, hdst, Lir.bindParams]
    exact .free sRet (.refl _)
  | succ d ih =>
    have hlt : k < n := by omega
    rw [deadFrom_step mask hlt]
    by_cases hbit : (mask &&& UInt64.ofNat (2 ^ (k + 1))) == 0
    · simp only [hbit, ↓reduceIte]
      have htnz : Lir.Cond.holds .tnz .w64 mask (UInt64.ofNat (2 ^ (k + 1))) = false := by
        simp [Lir.Cond.holds, w64_truncate_eq, beq_iff_eq.mp hbit]
      have sBr : Lir.semStep raw
          { mem, ctx, stack := { fn := wrapFn, label := base + 2 * k, pos := 0, env := wEnv } :: caller :: rest } =
          .next { mem, ctx, stack := { fn := wrapFn, label := base + 2 * k + 1, pos := 0, env := wEnv } :: caller :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := wrapFn, label := base + 2 * k, pos := 0, env := wEnv }) hW (hshape.brBlk k hlt) rfl]
        have hfwd : ¬ (base + 2 * k + 1 ≤ base + 2 * k) := by omega
        simp [Lir.Arg.eval, hw1, htnz, Lir.takeEdge, Lir.evalArgs, hshape.callBlk k hlt, Lir.bindParams, hfwd]
      obtain ⟨val, hval⟩ := hvals k hlt
      have sCall : Lir.semStep raw
          { mem, ctx, stack := { fn := wrapFn, label := base + 2 * k + 1, pos := 0, env := wEnv } :: caller :: rest } =
          .next { mem, ctx, stack :=
            { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 val } ::
            { fn := wrapFn, label := base + 2 * k + 1, pos := 1, env := wEnv, dsts := [] } :: caller :: rest } true := by
        apply Lir.semStep_next.mpr
        exact Lir.step_call (fr := { fn := wrapFn, label := base + 2 * k + 1, pos := 0, env := wEnv })
          (vs := [val]) hW (hshape.callBlk k hlt) (by simp) rfl
          (by simp [Lir.evalArgs, Lir.Arg.eval, hval])
          (by simp [Lir.enter, hr.decProc, Rt.Rc.Gen.dec, Lir.bindParams])
      exact ⟨hlt, val, hval, by simp, .free sBr (.charge sCall (.refl _))⟩
    · simp only [hbit, Bool.false_eq_true, ↓reduceIte]
      have hne0 : (mask &&& UInt64.ofNat (2 ^ (k + 1))) ≠ 0 := by
        intro heq; exact hbit (beq_iff_eq.mpr heq)
      have htnz : Lir.Cond.holds .tnz .w64 mask (UInt64.ofNat (2 ^ (k + 1))) = true := by
        simp [Lir.Cond.holds, w64_truncate_eq, hne0]
      have hnextBlk : ∃ nb, W.blocks[base + 2 * (k + 1)]? = some nb ∧ nb.params = [] := by
        by_cases hkn : k + 1 < n
        · exact ⟨_, hshape.brBlk (k + 1) hkn, rfl⟩
        · have heq : k + 1 = n := by omega
          rw [heq]; exact ⟨_, hshape.retBlk, rfl⟩
      obtain ⟨nb, hnb, hnbp⟩ := hnextBlk
      have sBr : Lir.semStep raw
          { mem, ctx, stack := { fn := wrapFn, label := base + 2 * k, pos := 0, env := wEnv } :: caller :: rest } =
          .next { mem, ctx, stack := { fn := wrapFn, label := base + 2 * (k + 1), pos := 0, env := wEnv } :: caller :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := wrapFn, label := base + 2 * k, pos := 0, env := wEnv }) hW (hshape.brBlk k hlt) rfl]
        have heq2 : base + 2 * k + 2 = base + 2 * (k + 1) := by omega
        simp [Lir.Arg.eval, hw1, htnz, Lir.takeEdge, Lir.evalArgs, heq2, hnb, hnbp, Lir.bindParams]
      have hrec := ih (k + 1) (by omega) (by omega)
      cases hdf : deadFrom n mask (k + 1) with
      | nil =>
        rw [hdf] at hrec
        exact .free sBr hrec
      | cons j rem =>
        rw [hdf] at hrec
        obtain ⟨hj, val, hval, hrem, hst⟩ := hrec
        exact ⟨hj, val, hval, hrem, .free sBr hst⟩

/-- Jump from a finished `call [] decProc` block `(base + 2 * j + 1, pos = 1)` to `(base + 2 * (j + 1), pos = 0)`. -/
theorem raw_decLoop_after_call {l : Layout} {raw : Lir.Program}
    {wrapFn n base oldBase j : Nat} {W : Lir.Func}
    (hW : raw.funcs[wrapFn]? = some W)
    (hshape : DecLoopShape l.decProc n base oldBase W)
    (hj : j < n) {wEnv : Lir.Env} {mem : X86.Memory} {ctx : Lir.Word}
    {caller : Lir.Frame} {rest : List Lir.Frame} :
    Lir.semStep raw
      { mem, ctx, stack := { fn := wrapFn, label := base + 2 * j + 1, pos := 1, env := wEnv, dsts := [] } :: caller :: rest } =
      .next { mem, ctx, stack := { fn := wrapFn, label := base + 2 * (j + 1), pos := 0, env := wEnv, dsts := [] } :: caller :: rest } false := by
  have hnextBlk : ∃ nb, W.blocks[base + 2 * (j + 1)]? = some nb ∧ nb.params = [] := by
    by_cases hjn : j + 1 < n
    · exact ⟨_, hshape.brBlk (j + 1) hjn, rfl⟩
    · have heq : j + 1 = n := by omega
      rw [heq]; exact ⟨_, hshape.retBlk, rfl⟩
  obtain ⟨nb, hnb, hnbp⟩ := hnextBlk
  apply Lir.semStep_next.mpr
  rw [Lir.step_term (fr := { fn := wrapFn, label := base + 2 * j + 1, pos := 1, env := wEnv, dsts := [] })
    hW (hshape.callBlk j hj) rfl]
  have heq2 : base + 2 * j + 2 = base + 2 * (j + 1) := by omega
  simp [Lir.takeEdge, Lir.evalArgs, heq2, hnb, hnbp, Lir.bindParams]
  omega

/-! ## 6. Raw `reset` (hot) and `resetU` prefix execution (to block `base` of `dec` loop) -/

theorem raw_reset_hot_prefix {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {dst x : Lir.VReg} {idx : Nat} {c : Lam.CtorInfo}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {mask xVal : Lir.Word}
    (hF : raw.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B)
    (hpos : fr.pos < B.body.size)
    (hc : l.ctors[idx]? = some c)
    (hlay : lay = Rt.Rc.CellLayout.ofFields c.arity c.tag)
    (hcls : lay.cls? = some cls)
    (hstmt : B.body[fr.pos] = .call [dst] (l.resetWrapper idx) [.v x, .imm mask])
    (hx : fr.env[x]? = some xVal)
    (huniq : evalUniqueCheck xVal mem = .unique) :
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    let caller' : Lir.Frame := { fr with pos := fr.pos + 1, dsts := [dst] }
    match loadFieldsMem mem xVal (List.range lay.nobj) with
    | none =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 2 .stuck
    | some allVals =>
      match writeShellMem mem xVal hdr lay.nobj with
      | none =>
        Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 2 .stuck
      | some mem₁ =>
        ∃ wEnv s₁,
          wEnv[0]? = some xVal ∧ wEnv[1]? = some mask ∧
          (∀ j < lay.nobj, wEnv[3 + j]? = allVals[j]?) ∧
          Lir.semStep raw { mem, ctx, stack := fr :: rest } = .next s₁ true ∧
          Sem.Star (Lir.semStep raw) s₁ 1
            { mem := mem₁, ctx, stack := { fn := l.resetWrapper idx, label := 2, pos := 0, env := wEnv } :: caller' :: rest } := by
  intro hdr caller'
  have hwrapF : raw.funcs[l.resetWrapper idx]? =
      some (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls) := by
    rw [hlay]; exact hr.resetWrap idx c cls hc (by rwa [← hlay])
  let e0 : Lir.Env := (({} : Lir.Env).insert 0 xVal).insert 1 mask
  have he0_0 : e0[0]? = some xVal := by rw [Lir.env_insert_ne _ _ (by decide)]; simp
  have he0_1 : e0[1]? = some mask := by simp [e0]
  let wFr0 : Lir.Frame := { fn := l.resetWrapper idx, label := 0, pos := 0, env := e0 }
  let wFr0' : Lir.Frame := { fn := l.resetWrapper idx, label := 0, pos := 1, env := e0, dsts := [2] }
  let uFr : Lir.Frame := { fn := l.isUniqueProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal }
  have sCallWrap : Lir.semStep raw { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := wFr0 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (vs := [xVal, mask]) hF hB hpos hstmt
      (by simp [Lir.evalArgs, Lir.Arg.eval, hx])
      (by simp [Lir.enter, hwrapF, mkResetWrapper, Lir.bindParams, e0, wFr0])
  have sCallU : Lir.semStep raw { mem, ctx, stack := wFr0 :: caller' :: rest } =
      .next { mem, ctx, stack := uFr :: wFr0' :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (fr := wFr0) (g := l.isUniqueProc) (as := [.v 0]) (vs := [xVal])
      hwrapF rfl (by simp [wFr0, mkResetWrapper])
      (by simp [wFr0, mkResetWrapper]) (by simp [wFr0, Lir.evalArgs, Lir.Arg.eval, he0_0])
      (by simp [Lir.enter, hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.bindParams, uFr])
  have hUstar := exec_isUniqueProc hr (xVal := xVal) (ctx := ctx) (mem := mem)
    (caller := wFr0') (rest := caller' :: rest) (dst := 2) rfl
  rw [huniq] at hUstar
  let e1 := e0.insert 2 1
  have he1_0 : e1[0]? = some xVal := by rw [Lir.env_insert_ne _ _ (by decide)]; exact he0_0
  have he1_1 : e1[1]? = some mask := by rw [Lir.env_insert_ne _ _ (by decide)]; exact he0_1
  have hblk0 : (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls).blocks[0]? =
      some { body := #[.call [2] l.isUniqueProc [.v 0]],
             term := .br .eq .w64 (.v 2) (.imm 1) ⟨1, []⟩ ⟨3 + 2 * lay.nobj, []⟩ } := rfl
  let loadStmts1 : List Lir.Stmt := (List.range lay.nobj).map fun j =>
    Lir.Stmt.assign (3 + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })
  let blk1 : Lir.Block :=
    { body := (loadStmts1 ++ mkShellStores 0 hdr lay.nobj).toArray
      term := .jump ⟨2, []⟩ }
  have hblk1 : (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls).blocks[1]? = some blk1 := by
    simp [mkResetWrapper, blk1, loadStmts1, mkShellStores, cellAddr, hdr]
  have sBr1 : Lir.semStep raw
      { mem, ctx, stack := { wFr0' with env := e1, dsts := [] } :: caller' :: rest } =
      .next { mem, ctx, stack := { fn := l.resetWrapper idx, label := 1, pos := 0, env := e1 } :: caller' :: rest } false := by
    apply Lir.semStep_next.mpr
    rw [Lir.step_term (fr := { wFr0' with env := e1, dsts := [] }) hwrapF hblk0 rfl]
    simp [wFr0', Lir.Arg.eval, e1, Lir.Cond.holds, w64_truncate_eq,
      Lir.takeEdge, Lir.evalArgs, hblk1, blk1, Lir.bindParams]
  have hbody1 : blk1.body.toList =
      [] ++ ((List.range' 0 lay.nobj).map fun j =>
        Lir.Stmt.assign (3 + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })) ++
        mkShellStores 0 hdr lay.nobj := by
    simp [blk1, loadStmts1, List.range_eq_range']
  have hlo := exec_loadOld (p := raw) (F := mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls)
    (fn := l.resetWrapper idx) (lbl := 1) (xVal := xVal) (ctx := ctx) (rest := caller' :: rest)
    (oldBase := 3) hwrapF hblk1 (by omega) (k := 0) (m := lay.nobj) he1_0 hbody1 (mem := mem)
  rw [← List.range_eq_range'] at hlo
  cases hlf : loadFieldsMem mem xVal (List.range lay.nobj) with
  | none =>
    rw [hlf] at hlo
    exact .charge sCallWrap (.charge sCallU (reaches_of_star_reuse hUstar (.free sBr1 (by simpa using hlo))))
  | some allVals =>
    rw [hlf] at hlo
    obtain ⟨wEnv, hloStar, hagW, hvalsW⟩ := hlo
    have hw0 : wEnv[0]? = some xVal := by rw [hagW 0 (by omega)]; exact he1_0
    have hw1 : wEnv[1]? = some mask := by rw [hagW 1 (by omega)]; exact he1_1
    have hbody1' : blk1.body.toList = loadStmts1 ++ mkShellStores 0 hdr lay.nobj ++ [] := by
      simp [blk1]
    have hsh := exec_mkShellStores (p := raw) (F := mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls)
      (fn := l.resetWrapper idx) (lbl := 1) (x := 0) (xVal := xVal) (hdr := hdr) (ctx := ctx)
      (rest := caller' :: rest) hwrapF hblk1 hw0 hbody1' (mem := mem)
    have hpreLen : loadStmts1.length = lay.nobj := by simp [loadStmts1]
    cases hws : writeShellMem mem xVal hdr lay.nobj with
    | none =>
      rw [hws] at hsh
      have htot := hUstar.trans (.free sBr1 (by simpa using hloStar))
      exact .charge sCallWrap (.charge sCallU (reaches_of_star_reuse htot (by simpa [hpreLen] using hsh)))
    | some mem₁ =>
      rw [hws] at hsh
      have hshape := mkResetWrapper_decLoopShape l.isUniqueProc l.incProc l.decProc lay cls
      have hblk2 : ∃ b2, (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls).blocks[2]? = some b2 ∧ b2.params = [] := by
        cases h0 : lay.nobj with
        | zero => exact ⟨_, by simpa [h0] using hshape.retBlk, rfl⟩
        | succ m => exact ⟨_, by simpa using hshape.brBlk 0 (by omega), rfl⟩
      obtain ⟨b2, hb2, hb2p⟩ := hblk2
      have sJmp2 : Lir.semStep raw
          { mem := mem₁, ctx, stack := { fn := l.resetWrapper idx, label := 1, pos := lay.nobj + (1 + lay.nobj), env := wEnv, dsts := [] } :: caller' :: rest } =
          .next { mem := mem₁, ctx, stack := { fn := l.resetWrapper idx, label := 2, pos := 0, env := wEnv, dsts := [] } :: caller' :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := l.resetWrapper idx, label := 1, pos := lay.nobj + (1 + lay.nobj), env := wEnv, dsts := [] })
          hwrapF hblk1 (by simp [blk1, loadStmts1, mkShellStores_length])]
        simp [blk1, Lir.takeEdge, Lir.evalArgs, hb2, hb2p, Lir.bindParams]
      have hloStar' : Sem.Star (Lir.semStep raw)
          { mem, ctx, stack := { fn := l.resetWrapper idx, label := 1, pos := 0, env := e1 } :: caller' :: rest } 0
          { mem, ctx, stack := { fn := l.resetWrapper idx, label := 1, pos := lay.nobj, env := wEnv, dsts := [] } :: caller' :: rest } := by
        simpa using hloStar
      have hsh' : Sem.Star (Lir.semStep raw)
          { mem, ctx, stack := { fn := l.resetWrapper idx, label := 1, pos := lay.nobj, env := wEnv, dsts := [] } :: caller' :: rest } 0
          { mem := mem₁, ctx, stack := { fn := l.resetWrapper idx, label := 1, pos := lay.nobj + (1 + lay.nobj), env := wEnv, dsts := [] } :: caller' :: rest } := by
        simpa [hpreLen] using hsh
      have htot1 : Sem.Star (Lir.semStep raw) { mem, ctx, stack := wFr0 :: caller' :: rest } 1
          { mem := mem₁, ctx, stack := { fn := l.resetWrapper idx, label := 2, pos := 0, env := wEnv } :: caller' :: rest } := by
        have h1 := Sem.Star.charge sCallU (hUstar.trans (.free sBr1 (hloStar'.trans (hsh'.trans (.free sJmp2 (.refl _))))))
        simpa using h1
      refine ⟨wEnv, _, hw0, hw1, fun j hj => ?_, sCallWrap, htot1⟩
      simpa using hvalsW j hj

theorem raw_resetU_prefix {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {dst x : Lir.VReg} {idx : Nat} {c : Lam.CtorInfo}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {mask xVal : Lir.Word}
    (hF : raw.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B)
    (hpos : fr.pos < B.body.size)
    (hc : l.ctors[idx]? = some c)
    (hlay : lay = Rt.Rc.CellLayout.ofFields c.arity c.tag)
    (hcls : lay.cls? = some cls)
    (hstmt : B.body[fr.pos] = .call [dst] (l.resetUWrapper idx) [.v x, .imm mask])
    (hx : fr.env[x]? = some xVal) :
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    let caller' : Lir.Frame := { fr with pos := fr.pos + 1, dsts := [dst] }
    match loadFieldsMem mem xVal (List.range lay.nobj) with
    | none =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 1 .stuck
    | some allVals =>
      match writeShellMem mem xVal hdr lay.nobj with
      | none =>
        Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 1 .stuck
      | some mem₁ =>
        ∃ wEnv s₁,
          wEnv[0]? = some xVal ∧ wEnv[1]? = some mask ∧
          (∀ j < lay.nobj, wEnv[2 + j]? = allVals[j]?) ∧
          Lir.semStep raw { mem, ctx, stack := fr :: rest } = .next s₁ true ∧
          Sem.Star (Lir.semStep raw) s₁ 0
            { mem := mem₁, ctx, stack := { fn := l.resetUWrapper idx, label := 1, pos := 0, env := wEnv } :: caller' :: rest } := by
  intro hdr caller'
  have hwrapF : raw.funcs[l.resetUWrapper idx]? =
      some (mkResetUWrapper l.decProc lay cls) := by
    rw [hlay]; exact hr.resetUWrap idx c cls hc (by rwa [← hlay])
  let e0 : Lir.Env := (({} : Lir.Env).insert 0 xVal).insert 1 mask
  have he0_0 : e0[0]? = some xVal := by rw [Lir.env_insert_ne _ _ (by decide)]; simp
  have he0_1 : e0[1]? = some mask := by simp [e0]
  let wFr0 : Lir.Frame := { fn := l.resetUWrapper idx, label := 0, pos := 0, env := e0 }
  have sCallWrap : Lir.semStep raw { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := wFr0 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (vs := [xVal, mask]) hF hB hpos hstmt
      (by simp [Lir.evalArgs, Lir.Arg.eval, hx])
      (by simp [Lir.enter, hwrapF, mkResetUWrapper, Lir.bindParams, e0, wFr0])
  let loadStmts0 : List Lir.Stmt := (List.range lay.nobj).map fun j =>
    Lir.Stmt.assign (2 + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })
  let blk0 : Lir.Block :=
    { body := (loadStmts0 ++ mkShellStores 0 hdr lay.nobj).toArray
      term := .jump ⟨1, []⟩ }
  have hblk0 : (mkResetUWrapper l.decProc lay cls).blocks[0]? = some blk0 := by
    simp [mkResetUWrapper, blk0, loadStmts0, mkShellStores, cellAddr, hdr]
  have hbody0 : blk0.body.toList =
      [] ++ ((List.range' 0 lay.nobj).map fun j =>
        Lir.Stmt.assign (2 + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })) ++
        mkShellStores 0 hdr lay.nobj := by
    simp [blk0, loadStmts0, List.range_eq_range']
  have hlo := exec_loadOld (p := raw) (F := mkResetUWrapper l.decProc lay cls)
    (fn := l.resetUWrapper idx) (lbl := 0) (xVal := xVal) (ctx := ctx) (rest := caller' :: rest)
    (oldBase := 2) hwrapF hblk0 (by omega) (k := 0) (m := lay.nobj) he0_0 hbody0 (mem := mem)
  rw [← List.range_eq_range'] at hlo
  cases hlf : loadFieldsMem mem xVal (List.range lay.nobj) with
  | none =>
    rw [hlf] at hlo
    exact .charge sCallWrap (by simpa [wFr0] using hlo)
  | some allVals =>
    rw [hlf] at hlo
    obtain ⟨wEnv, hloStar, hagW, hvalsW⟩ := hlo
    have hw0 : wEnv[0]? = some xVal := by rw [hagW 0 (by omega)]; exact he0_0
    have hw1 : wEnv[1]? = some mask := by rw [hagW 1 (by omega)]; exact he0_1
    have hbody0' : blk0.body.toList = loadStmts0 ++ mkShellStores 0 hdr lay.nobj ++ [] := by
      simp [blk0]
    have hsh := exec_mkShellStores (p := raw) (F := mkResetUWrapper l.decProc lay cls)
      (fn := l.resetUWrapper idx) (lbl := 0) (x := 0) (xVal := xVal) (hdr := hdr) (ctx := ctx)
      (rest := caller' :: rest) hwrapF hblk0 hw0 hbody0' (mem := mem)
    have hpreLen : loadStmts0.length = lay.nobj := by simp [loadStmts0]
    cases hws : writeShellMem mem xVal hdr lay.nobj with
    | none =>
      rw [hws] at hsh
      exact .charge sCallWrap (reaches_of_star_reuse (by simpa [wFr0] using hloStar) (by simpa [hpreLen] using hsh))
    | some mem₁ =>
      rw [hws] at hsh
      have hshape := mkResetUWrapper_decLoopShape l.decProc lay cls
      have hblk1 : ∃ b1, (mkResetUWrapper l.decProc lay cls).blocks[1]? = some b1 ∧ b1.params = [] := by
        cases h0 : lay.nobj with
        | zero => exact ⟨_, by simpa [h0] using hshape.retBlk, rfl⟩
        | succ m => exact ⟨_, by simpa using hshape.brBlk 0 (by omega), rfl⟩
      obtain ⟨b1, hb1, hb1p⟩ := hblk1
      have sJmp1 : Lir.semStep raw
          { mem := mem₁, ctx, stack := { fn := l.resetUWrapper idx, label := 0, pos := lay.nobj + (1 + lay.nobj), env := wEnv, dsts := [] } :: caller' :: rest } =
          .next { mem := mem₁, ctx, stack := { fn := l.resetUWrapper idx, label := 1, pos := 0, env := wEnv, dsts := [] } :: caller' :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := l.resetUWrapper idx, label := 0, pos := lay.nobj + (1 + lay.nobj), env := wEnv, dsts := [] })
          hwrapF hblk0 (by simp [blk0, loadStmts0, mkShellStores_length])]
        simp [blk0, Lir.takeEdge, Lir.evalArgs, hb1, hb1p, Lir.bindParams]
      have hloStar' : Sem.Star (Lir.semStep raw) { mem, ctx, stack := wFr0 :: caller' :: rest } 0
          { mem, ctx, stack := { fn := l.resetUWrapper idx, label := 0, pos := lay.nobj, env := wEnv, dsts := [] } :: caller' :: rest } := by
        simpa [wFr0] using hloStar
      have hsh' : Sem.Star (Lir.semStep raw)
          { mem, ctx, stack := { fn := l.resetUWrapper idx, label := 0, pos := lay.nobj, env := wEnv, dsts := [] } :: caller' :: rest } 0
          { mem := mem₁, ctx, stack := { fn := l.resetUWrapper idx, label := 0, pos := lay.nobj + (1 + lay.nobj), env := wEnv, dsts := [] } :: caller' :: rest } := by
        simpa [hpreLen] using hsh
      refine ⟨wEnv, _, hw0, hw1, fun j hj => ?_, sCallWrap, ?_⟩
      · simpa using hvalsW j hj
      · exact hloStar'.trans (hsh'.trans (.free sJmp1 (.refl _)))

/-- Raw `reset` wrapper execution on the shared path (`evalUniqueCheck xVal mem = .shared`):
runs `isUniqueProc` (returns `0`), shared live-field `incProc` loop, and `decProc xVal`. -/
theorem raw_reset_shared_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {dst x : Lir.VReg} {idx : Nat} {c : Lam.CtorInfo}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {mask xVal : Lir.Word}
    (hF : raw.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B)
    (hpos : fr.pos < B.body.size)
    (hc : l.ctors[idx]? = some c)
    (hlay : lay = Rt.Rc.CellLayout.ofFields c.arity c.tag)
    (hcls : lay.cls? = some cls)
    (hstmt : B.body[fr.pos] = .call [dst] (l.resetWrapper idx) [.v x, .imm mask])
    (hx : fr.env[x]? = some xVal)
    (hshared : evalUniqueCheck xVal mem = .shared) :
    let live := liveFields lay.nobj mask
    let caller' : Lir.Frame := { fr with pos := fr.pos + 1, dsts := [dst] }
    let pFr0 : Lir.Frame := { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal }
    match evalSharedIncList xVal live mem with
    | .oom =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } (2 + live.length) (.resource .heap)
    | .stuck =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } (2 + live.length) .stuck
    | .ok mem₁ =>
      match evalDecSite xVal mem₁ with
      | .stuck =>
        Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } (3 + live.length) .stuck
      | .ok mem' =>
        ∃ s₁, Lir.semStep raw { mem, ctx, stack := fr :: rest } = .next s₁ true ∧
          Sem.Star (Lir.semStep raw) s₁ (2 + live.length)
            { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst 1, dsts := [] } :: rest }
      | .free =>
        ∃ wEnv' s₁,
          Lir.semStep raw { mem, ctx, stack := fr :: rest } = .next s₁ true ∧
          Sem.Star (Lir.semStep raw) s₁ (2 + live.length)
            { mem := mem₁, ctx, stack := pFr0 ::
              { fn := l.resetWrapper idx, label := (3 + 2 * lay.nobj) + 2 * lay.nobj, pos := 1, env := wEnv', dsts := [] } ::
              caller' :: rest } := by
  intro live caller' pFr0
  have hwrapF : raw.funcs[l.resetWrapper idx]? =
      some (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls) := by
    rw [hlay]; exact hr.resetWrap idx c cls hc (by rwa [← hlay])
  let e0 : Lir.Env := (({} : Lir.Env).insert 0 xVal).insert 1 mask
  have he0_0 : e0[0]? = some xVal := by rw [Lir.env_insert_ne _ _ (by decide)]; simp
  have he0_1 : e0[1]? = some mask := by simp [e0]
  let wFr0 : Lir.Frame := { fn := l.resetWrapper idx, label := 0, pos := 0, env := e0 }
  let wFr0' : Lir.Frame := { fn := l.resetWrapper idx, label := 0, pos := 1, env := e0, dsts := [2] }
  let uFr : Lir.Frame := { fn := l.isUniqueProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal }
  have sCallWrap : Lir.semStep raw { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := wFr0 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (vs := [xVal, mask]) hF hB hpos hstmt
      (by simp [Lir.evalArgs, Lir.Arg.eval, hx])
      (by simp [Lir.enter, hwrapF, mkResetWrapper, Lir.bindParams, e0, wFr0])
  have sCallU : Lir.semStep raw { mem, ctx, stack := wFr0 :: caller' :: rest } =
      .next { mem, ctx, stack := uFr :: wFr0' :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (fr := wFr0) (g := l.isUniqueProc) (as := [.v 0]) (vs := [xVal])
      hwrapF rfl (by simp [wFr0, mkResetWrapper])
      (by simp [wFr0, mkResetWrapper]) (by simp [wFr0, Lir.evalArgs, Lir.Arg.eval, he0_0])
      (by simp [Lir.enter, hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.bindParams, uFr])
  have hUstar := exec_isUniqueProc hr (xVal := xVal) (ctx := ctx) (mem := mem)
    (caller := wFr0') (rest := caller' :: rest) (dst := 2) rfl
  rw [hshared] at hUstar
  let e1 := e0.insert 2 0
  have he1_0 : e1[0]? = some xVal := by rw [Lir.env_insert_ne _ _ (by decide)]; exact he0_0
  have he1_1 : e1[1]? = some mask := by rw [Lir.env_insert_ne _ _ (by decide)]; exact he0_1
  have hblk0 : (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls).blocks[0]? =
      some { body := #[.call [2] l.isUniqueProc [.v 0]],
             term := .br .eq .w64 (.v 2) (.imm 1) ⟨1, []⟩ ⟨3 + 2 * lay.nobj, []⟩ } := rfl
  have hsharedBlk : ∃ sb, (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls).blocks[3 + 2 * lay.nobj]? = some sb ∧
      sb.params = [] := by
    rcases Nat.eq_zero_or_pos lay.nobj with h0 | hpos0
    · have hret := mkResetWrapper_shared_ret_block l.isUniqueProc l.incProc l.decProc lay cls
      exact ⟨_, by simpa [h0] using hret, rfl⟩
    · have hinc := (mkResetWrapper_shared_inc_blocks l.isUniqueProc l.incProc l.decProc lay cls (j := 0) hpos0).1
      exact ⟨_, by simpa using hinc, rfl⟩
  obtain ⟨sb, hsb, hsbp⟩ := hsharedBlk
  have sBrShared : Lir.semStep raw
      { mem, ctx, stack := { wFr0' with env := e1, dsts := [] } :: caller' :: rest } =
      .next { mem, ctx, stack := { fn := l.resetWrapper idx, label := 3 + 2 * lay.nobj, pos := 0, env := e1 } :: caller' :: rest } false := by
    apply Lir.semStep_next.mpr
    rw [Lir.step_term (fr := { wFr0' with env := e1, dsts := [] }) hwrapF hblk0 rfl]
    have hneq : Lir.Cond.holds .eq .w64 0 1 = false := by decide
    simp [wFr0', Lir.Arg.eval, e1, hneq, Lir.takeEdge, Lir.evalArgs, hsb, hsbp, Lir.bindParams]
  have hloop := raw_reset_shared_inc_loop hr hc hlay hcls (xVal := xVal) (mask := mask) (ctx := ctx)
    (caller := caller') (rest := rest) 0 (Nat.zero_le _) e1 mem he1_0 he1_1
  rw [liveFrom_zero] at hloop
  have hpref1 : Sem.Star (Lir.semStep raw) { mem, ctx, stack := wFr0 :: caller' :: rest } 1
      { mem, ctx, stack := { fn := l.resetWrapper idx, label := 3 + 2 * lay.nobj, pos := 0, env := e1 } :: caller' :: rest } :=
    .charge sCallU (hUstar.trans (.free sBrShared (.refl _)))
  cases hinc : evalSharedIncList xVal live mem with
  | oom =>
    dsimp only
    rw [hinc] at hloop
    have h1 := Sem.Reaches.charge sCallWrap (star_reaches hpref1 (by simpa using hloop))
    exact reaches_cast h1 (by first | omega | (simp only [live]; omega))
  | stuck =>
    dsimp only
    rw [hinc] at hloop
    have h1 := Sem.Reaches.charge sCallWrap (star_reaches hpref1 (by simpa using hloop))
    exact reaches_cast h1 (by first | omega | (simp only [live]; omega))
  | ok mem₁ =>
    dsimp only
    rw [hinc] at hloop
    obtain ⟨wEnv', hw'0, _, hincStar⟩ := hloop
    have hretBlk := mkResetWrapper_shared_ret_block l.isUniqueProc l.incProc l.decProc lay cls
    let wRet : Lir.Frame :=
      { fn := l.resetWrapper idx, label := (3 + 2 * lay.nobj) + 2 * lay.nobj, pos := 1, env := wEnv', dsts := [] }
    have sCallDec : Lir.semStep raw
        { mem := mem₁, ctx, stack := { fn := l.resetWrapper idx, label := (3 + 2 * lay.nobj) + 2 * lay.nobj, pos := 0, env := wEnv' } :: caller' :: rest } =
        .next { mem := mem₁, ctx, stack := pFr0 :: wRet :: caller' :: rest } true := by
      apply Lir.semStep_next.mpr
      exact Lir.step_call (fr := { fn := l.resetWrapper idx, label := (3 + 2 * lay.nobj) + 2 * lay.nobj, pos := 0, env := wEnv' })
        (rs := []) (g := l.decProc) (as := [.v 0]) (vs := [xVal])
        hwrapF hretBlk (by simp) rfl
        (by simp [Lir.evalArgs, Lir.Arg.eval, hw'0])
        (by simp [Lir.enter, hr.decProc, Rt.Rc.Gen.dec, Lir.bindParams, pFr0])
    have hincStar' : Sem.Star (Lir.semStep raw)
        { mem, ctx, stack := { fn := l.resetWrapper idx, label := 3 + 2 * lay.nobj, pos := 0, env := e1 } :: caller' :: rest }
        live.length
        { mem := mem₁, ctx, stack := { fn := l.resetWrapper idx, label := (3 + 2 * lay.nobj) + 2 * lay.nobj, pos := 0, env := wEnv' } :: caller' :: rest } :=
      hincStar
    have htoDec : Sem.Star (Lir.semStep raw) { mem, ctx, stack := wFr0 :: caller' :: rest } (2 + live.length)
        { mem := mem₁, ctx, stack := pFr0 :: wRet :: caller' :: rest } :=
      star_cast (hpref1.trans (hincStar'.trans (.charge sCallDec (.refl _)))) (by omega)
    have hdec := raw_decProc_exec hr (xVal := xVal) (ctx := ctx) (mem := mem₁)
      (caller := wRet) (rest := caller' :: rest) rfl
    cases hdev : evalDecSite xVal mem₁ with
    | stuck =>
      dsimp only
      rw [hdev] at hdec
      have h1 := Sem.Reaches.charge sCallWrap (star_reaches htoDec hdec)
      exact reaches_cast h1 (by omega)
    | free =>
      dsimp only
      exact ⟨wEnv', _, sCallWrap, htoDec⟩
    | ok mem' =>
      dsimp only
      rw [hdev] at hdec
      have sRet1 : Lir.semStep raw { mem := mem', ctx, stack := wRet :: caller' :: rest } =
          .next { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst 1, dsts := [] } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := wRet) hwrapF hretBlk rfl]
        simp [Lir.evalArgs, Lir.Arg.eval, Lir.bindParams, caller', wRet]
      exact ⟨_, sCallWrap, by simpa using htoDec.trans (hdec.trans (.free sRet1 (.refl _)))⟩

/-! ## 7. Inlined `reset`, `resetU`, `fusedResetUReuseU`, and `fusedResetReuse` execution -/

/-- Helper: advance `inl` on `reset` (dynamic) when `evalUniqueCheck xVal mem = .unique` and
`loadFieldsMem` + `writeShellMem` succeeded, stopping at the start of `mkDeadDecs` in block `fr.label + 2`. -/
theorem inl_reset_hot_prefix {l : Layout} {raw : Lir.Program}
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem mem₁ : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 restStmts : List Lir.Stmt} {dst x : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {mask xVal : Lir.Word} {allVals : List Lir.Word}
    (hltFn : fr.fn < l.sourceCount) (hF : raw.funcs[fr.fn]? = some F)
    (hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = .call [dst] (l.resetWrapper idx) [.v x, .imm mask] :: restStmts)
    (hnp : ∀ s2 rest2, restStmts = s2 :: rest2 →
      classifyPair l (.call [dst] (l.resetWrapper idx) [.v x, .imm mask]) s2 = none)
    (hclsSite : classify l (.call [dst] (l.resetWrapper idx) [.v x, .imm mask]) =
      some (.reset dst x idx lay cls mask))
    (hposB : rawPos < B.body.size)
    (hgetB : B.body[rawPos] = .call [dst] (l.resetWrapper idx) [.v x, .imm mask])
    (hx : fr.env[x]? = some xVal) (hxLt : (x : Nat) < freshBase F)
    (huniq : evalUniqueCheck xVal mem = .unique)
    (hlf : loadFieldsMem mem xVal (List.range lay.nobj) = some allVals)
    (hws : writeShellMem mem xVal (Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1) lay.nobj = some mem₁) :
    let inl := inlineProgram l raw
    let dead := deadFields lay.nobj mask
    let live := liveFields lay.nobj mask
    let joinLbl := if live.length ≤ maxInlineResetLive then fr.label + 8 + 5 * live.length else fr.label + 4
    let deadBase := if live.length ≤ maxInlineResetLive then tmp + 1 else tmp + 2
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    let hotBody : List Lir.Stmt :=
      mkDeadLoads x deadBase dead ++ mkShellStores x hdr lay.nobj ++ mkDeadDecs l.decProc deadBase dead
    ChunkPos l F b B (rawPos + 1) joinLbl 0 ∧
    (inlineFunc l F).blocks[fr.label + 2]? =
      some { body := hotBody.toArray, term := .jump ⟨joinLbl, [.v x]⟩, cold := B.cold } ∧
    (∃ jb, (inlineFunc l F).blocks[joinLbl]? = some jb ∧ jb.params = [dst]) ∧
    ∃ env' s₂,
      Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₂ false ∧
      Sem.Star (Lir.semStep inl) s₂ 0
        { mem := mem₁, ctx, stack :=
          { fr with label := fr.label + 2, pos := dead.length + (1 + lay.nobj), env := env', dsts := [] } :: rest } ∧
      AgreeBelow (freshBase F) fr.env env' ∧
      env'[x]? = some xVal ∧
      (∀ i, (hi : i < dead.length) →
        env'[deadBase + i]? = some (allVals[dead[i]]'(by
          have h1 := loadFieldsMem_length hlf; simp at h1
          have h2 := deadFields_lt lay.nobj mask (List.getElem_mem hi); omega))) := by
  intro inl dead live joinLbl deadBase hdr hotBody
  have hexp : expandStmts l (newLabel l F) B.term B.cold rest0 fr.label tmp params acc =
      let r := stepSingle l B.cold (.call [dst] (l.resetWrapper idx) [.v x, .imm mask]) fr.label tmp params acc
      let t := expandStmts l (newLabel l F) B.term B.cold restStmts r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
      (r.1 ++ t.1, t.2) := by
    rw [hrest, expandStmts_cons_single _ _ _ _ _ _ _ _ _ _ hnp]
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  have hsetup :
      ChunkPos l F b B (rawPos + 1) joinLbl 0 ∧
      (inlineFunc l F).blocks[fr.label]? = some {
        params, body := acc.reverse.toArray,
        term := .br .tnz .w64 (.v x) (.imm 1) ⟨fr.label + 3, []⟩ ⟨fr.label + 1, []⟩, cold := B.cold } ∧
      (inlineFunc l F).blocks[fr.label + 1]? = some {
        body := #[.assign tmp (.load .w32 .zero (cellAddr x 4))],
        term := .br .eq .w32 (.v tmp) (.imm 0) ⟨fr.label + 2, []⟩ ⟨fr.label + 3, []⟩, cold := B.cold } ∧
      (inlineFunc l F).blocks[fr.label + 2]? = some {
        body := hotBody.toArray, term := .jump ⟨joinLbl, [.v x]⟩, cold := B.cold } ∧
      (∃ jb, (inlineFunc l F).blocks[joinLbl]? = some jb ∧ jb.params = [dst]) := by
    by_cases hle : live.length ≤ maxInlineResetLive
    · have hjEq : joinLbl = fr.label + 8 + 5 * live.length := by simp [joinLbl, hle]
      have hdEq : deadBase = tmp + 1 := by simp [deadBase, hle]
      have hle' : (liveFields lay.nobj mask).length ≤ maxInlineResetLive := hle
      have cpNext : ChunkAt l F b B (rawPos + 1) (fr.label + 8 + 5 * live.length) 0
          (tmp + 3 + dead.length + 3 * live.length) [dst] [] restStmts := {
        bLookup := hcp.bLookup
        tmpGe := by have := hcp.tmpGe; omega
        split := by
          have htake : B.body.toList.take (rawPos + 1) =
              B.body.toList.take rawPos ++ [.call [dst] (l.resetWrapper idx) [.v x, .imm mask]] := by
            rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB, hgetB]; simp
          rw [htake, List.append_assoc]; simpa [hrest] using hcp.split
        posLe := by omega
        blocksMatch := fun k blk hk => by
          have h := hcp.blocksMatch ((8 + 5 * live.length) + k) blk (by
            rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; simp only [hle', ↓reduceIte]
            refine (getElem?_append_right_add _ _ k ?_).trans hk
            simp only [List.length_append, List.length_cons, List.length_nil,
              mkSharedIncBlocks_length, mkSharedDecBlocks_length, live]
            omega)
          simpa [Nat.add_assoc] using h
        inPosEq := rfl
        endLbl := by
          have := hcp.endLbl
          rw [hrest, stmtsExtra_cons_nonPair hnp, stmtExtra, hclsSite] at this
          simp only [siteExtra, hle', ↓reduceIte] at this
          dsimp only [Lir.Label, live] at this ⊢; omega }
      obtain ⟨jb, _, hj0, hjp, _, _, _⟩ :=
        ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold restStmts
          (fr.label + 8 + 5 * live.length) (tmp + 3 + dead.length + 3 * live.length) [dst] []
      have hbJ : (inlineFunc l F).blocks[fr.label + 8 + 5 * live.length]? = some jb := by
        simpa using cpNext.blocksMatch 0 jb hj0
      refine ⟨hjEq ▸ ⟨_, _, _, _, cpNext⟩, ?_, ?_, ?_, hjEq ▸ ⟨jb, hbJ, hjp⟩⟩
      · simpa using hcp.blocksMatch 0 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; simp only [hle', ↓reduceIte]; rfl)
      · exact hcp.blocksMatch 1 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; simp only [hle', ↓reduceIte]; rfl)
      · have h2 := hcp.blocksMatch 2 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; simp only [hle', ↓reduceIte]; rfl)
        have hhot : hotBody = mkDeadLoads x (tmp + 1) dead ++ mkShellStores x hdr lay.nobj ++
            mkDeadDecs l.decProc (tmp + 1) dead := by simp only [hotBody, hdEq]
        rw [hjEq, hhot]; exact h2
    · have hjEq : joinLbl = fr.label + 4 := by simp [joinLbl, hle]
      have hdEq : deadBase = tmp + 2 := by simp [deadBase, hle]
      have hle' : ¬ (liveFields lay.nobj mask).length ≤ maxInlineResetLive := hle
      have cpNext : ChunkAt l F b B (rawPos + 1) (fr.label + 4) 0 (tmp + 2 + dead.length) [dst] [] restStmts := {
        bLookup := hcp.bLookup
        tmpGe := by have := hcp.tmpGe; omega
        split := by
          have htake : B.body.toList.take (rawPos + 1) =
              B.body.toList.take rawPos ++ [.call [dst] (l.resetWrapper idx) [.v x, .imm mask]] := by
            rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB, hgetB]; simp
          rw [htake, List.append_assoc]; simpa [hrest] using hcp.split
        posLe := by omega
        blocksMatch := fun k blk hk => by
          have h := hcp.blocksMatch (4 + k) blk (by
            rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; simp only [hle', ↓reduceIte]
            rw [Nat.add_comm 4 k]; exact hk)
          simpa [Nat.add_assoc] using h
        inPosEq := rfl
        endLbl := by
          have := hcp.endLbl
          rw [hrest, stmtsExtra_cons_nonPair hnp, stmtExtra, hclsSite] at this
          simp only [siteExtra, hle', ↓reduceIte] at this
          dsimp only [Lir.Label, live] at this ⊢; omega }
      obtain ⟨jb, _, hj0, hjp, _, _, _⟩ :=
        ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold restStmts (fr.label + 4) (tmp + 2 + dead.length) [dst] []
      have hbJ : (inlineFunc l F).blocks[fr.label + 4]? = some jb := by
        simpa using cpNext.blocksMatch 0 jb hj0
      refine ⟨hjEq ▸ ⟨_, _, _, _, cpNext⟩, ?_, ?_, ?_, hjEq ▸ ⟨jb, hbJ, hjp⟩⟩
      · simpa using hcp.blocksMatch 0 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; simp only [hle', ↓reduceIte]; rfl)
      · exact hcp.blocksMatch 1 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; simp only [hle', ↓reduceIte]; rfl)
      · have h2 := hcp.blocksMatch 2 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; simp only [hle', ↓reduceIte]; rfl)
        have hhot : hotBody = mkDeadLoads x (tmp + 2) dead ++ mkShellStores x hdr lay.nobj ++
            mkDeadDecs l.decProc (tmp + 2) dead := by simp only [hotBody, hdEq]
        rw [hjEq, hhot]; exact h2
  obtain ⟨hcpNext, hb0, hb1, hb2, hjoin⟩ := hsetup
  have hdeadGe : tmp + 1 ≤ deadBase := by dsimp only [deadBase]; split <;> omega
  have hpos0 : fr.pos = acc.reverse.toArray.size := by simp [hcp.inPosEq]
  unfold evalUniqueCheck at huniq
  have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by
    cases ht : Lir.Cond.holds .tnz .w64 xVal 1
    · rfl
    · simp [ht] at huniq
  simp only [htagF, Bool.false_eq_true, ↓reduceIte] at huniq
  cases hlc : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
  | none => simp [hlc] at huniq
  | some cnt =>
    simp only [hlc] at huniq
    have hz : (X86.Width.w32.truncate cnt).toNat = 0 := by
      by_cases h0 : (X86.Width.w32.truncate cnt).toNat = 0
      · exact h0
      · simp [h0] at huniq
    have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = true := by rw [w32_eq_zero]; simp [hz]
    have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
        .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term hF' hb0 hpos0]
      simp [Lir.Arg.eval, hx, htagF, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams]
    let env1 := fr.env.insert tmp cnt
    have hx1 : env1[x]? = some xVal := by
      rw [Lir.env_insert_ne _ _ (by dsimp only [Lir.VReg] at hxLt ⊢; have := hcp.tmpGe; omega), hx]
    have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } =
        .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } false := by
      apply Lir.semStep_next.mpr
      exact Lir.step_stmt (fr := { fr with label := fr.label + 1, pos := 0 }) (ρ' := env1) (mem' := mem)
        hF' hb1 (by simp) rfl rfl
        (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell fr.env ctx x xVal 4 hx, hlc, env1])
    have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } =
        .next { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0, env := env1 } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fr with label := fr.label + 1, pos := 1, env := env1 }) hF' hb1 rfl]
      simp [Lir.Arg.eval, env1, heq0, Lir.takeEdge, Lir.evalArgs, hb2, Lir.bindParams]
    obtain ⟨deadVals, hdeadLoad, _, hdeadGet⟩ :=
      loadFieldsMem_sublist hlf dead (fun j hj => deadFields_lt lay.nobj mask hj)
    have hbody2L : ({ body := hotBody.toArray, term := .jump ⟨joinLbl, [.v x]⟩, cold := B.cold } : Lir.Block).body.toList =
        [] ++ mkDeadLoads x deadBase dead ++ (mkShellStores x hdr lay.nobj ++ mkDeadDecs l.decProc deadBase dead) := by
      simp [hotBody, List.append_assoc]
    obtain ⟨env', hdlStar, hagD, hvalsD⟩ :=
      exec_mkDeadLoads (p := inl) (F := inlineFunc l F) (fn := fr.fn) (lbl := fr.label + 2)
        (x := x) (xVal := xVal) (ctx := ctx) (rest := rest) hF' hb2
        (by dsimp only [Lir.VReg] at hxLt ⊢; have := hcp.tmpGe; omega) hx1 hbody2L hdeadLoad
    have hx' : env'[x]? = some xVal := by
      rw [hagD x (by dsimp only [Lir.VReg] at hxLt ⊢; have := hcp.tmpGe; omega)]; exact hx1
    have hbody2S : ({ body := hotBody.toArray, term := .jump ⟨joinLbl, [.v x]⟩, cold := B.cold } : Lir.Block).body.toList =
        mkDeadLoads x deadBase dead ++ mkShellStores x hdr lay.nobj ++ mkDeadDecs l.decProc deadBase dead := by
      simp [hotBody]
    have hsh := exec_mkShellStores (p := inl) (F := inlineFunc l F) (fn := fr.fn) (lbl := fr.label + 2)
      (x := x) (xVal := xVal) (hdr := hdr) (ctx := ctx) (rest := rest) hF' hb2 hx' hbody2S (mem := mem)
    rw [hws] at hsh
    have hfr2 : ({ fn := fr.fn, label := fr.label + 2, pos := 0, env := env1, dsts := [] } : Lir.Frame) =
        { fr with label := fr.label + 2, pos := 0, env := env1 } := by
      cases fr; dsimp only at hdsts; subst hdsts; rfl
    have hdlStar' : Sem.Star (Lir.semStep inl)
        { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0, env := env1 } :: rest } 0
        { mem, ctx, stack := { fr with label := fr.label + 2, pos := dead.length, env := env', dsts := [] } :: rest } := by
      simpa [hfr2] using hdlStar
    have hsh' : Sem.Star (Lir.semStep inl)
        { mem, ctx, stack := { fr with label := fr.label + 2, pos := dead.length, env := env', dsts := [] } :: rest } 0
        { mem := mem₁, ctx, stack := { fr with label := fr.label + 2, pos := dead.length + (1 + lay.nobj), env := env', dsts := [] } :: rest } := by
      simpa [mkDeadLoads_length] using hsh
    refine ⟨hcpNext, hb2, hjoin, env', _, s1,
      .free s2 (.free s3 (hdlStar'.trans hsh')),
      fun r hr => by
        rw [hagD r (by dsimp only [Lir.VReg]; have := hcp.tmpGe; omega),
          Lir.env_insert_ne _ _ (by have := hcp.tmpGe; omega)],
      hx', fun i hi => by rw [hvalsD i hi, hdeadGet i hi]⟩

/-- Helper: advance `inl` on `reset` (dynamic, inlined shared path `live.length ≤ maxInlineResetLive`)
when `evalUniqueCheck xVal mem = .shared`, running `mkSharedIncBlocks` + `mkSharedDecBlocks`. -/
theorem inl_reset_shared_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 restStmts : List Lir.Stmt} {dst x : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {mask xVal : Lir.Word}
    (hltFn : fr.fn < l.sourceCount) (hF : raw.funcs[fr.fn]? = some F)
    (hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = .call [dst] (l.resetWrapper idx) [.v x, .imm mask] :: restStmts)
    (hnp : ∀ s2 rest2, restStmts = s2 :: rest2 →
      classifyPair l (.call [dst] (l.resetWrapper idx) [.v x, .imm mask]) s2 = none)
    (hclsSite : classify l (.call [dst] (l.resetWrapper idx) [.v x, .imm mask]) =
      some (.reset dst x idx lay cls mask))
    (hposB : rawPos < B.body.size)
    (hgetB : B.body[rawPos] = .call [dst] (l.resetWrapper idx) [.v x, .imm mask])
    (hx : fr.env[x]? = some xVal) (hxLt : (x : Nat) < freshBase F)
    (hshared : evalUniqueCheck xVal mem = .shared)
    (hle : (liveFields lay.nobj mask).length ≤ maxInlineResetLive) :
    let inl := inlineProgram l raw
    let live := liveFields lay.nobj mask
    let decLbl := fr.label + 3 + 5 * live.length
    let joinLbl := fr.label + 8 + 5 * live.length
    let pFr0 : Lir.Frame := { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal }
    ChunkPos l F b B (rawPos + 1) joinLbl 0 ∧
    (∃ jb, (inlineFunc l F).blocks[joinLbl]? = some jb ∧ jb.params = [dst]) ∧
    (inlineFunc l F).blocks[decLbl + 2]? =
      some { body := #[.call [] l.decProc [.v x]], term := .jump ⟨joinLbl, [.imm 1]⟩, cold := true } ∧
    match evalSharedIncList xVal live mem with
    | .oom =>
      Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 (.resource .heap)
    | .stuck =>
      Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 .stuck
    | .ok mem₁ =>
      match evalDecSite xVal mem₁ with
      | .stuck =>
        Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 .stuck
      | .ok mem' =>
        ∃ envD s₂,
          Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₂ false ∧
          Sem.Star (Lir.semStep inl) s₂ 0
            { mem := mem', ctx, stack := { fr with label := joinLbl, pos := 0, env := envD, dsts := [] } :: rest } ∧
          AgreeBelow (freshBase F) (fr.env.insert dst 1) envD
      | .free =>
        ∃ env1 s₂,
          Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₂ false ∧
          Sem.Star (Lir.semStep inl) s₂ 1
            { mem := mem₁, ctx, stack := pFr0 :: { fr with label := decLbl + 2, pos := 1, env := env1, dsts := [] } :: rest } ∧
          AgreeBelow (freshBase F) fr.env env1 := by
  intro inl live decLbl joinLbl pFr0
  let dead := deadFields lay.nobj mask
  let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
  let sharedLbl := fr.label + 3
  let incBlks := mkSharedIncBlocks x sharedLbl (tmp + 1 + dead.length) live
  let decBlks := mkSharedDecBlocks l.decProc x decLbl (tmp + 1 + dead.length + 3 * live.length) ⟨joinLbl, [.imm 1]⟩
  have hincLen : incBlks.length = 5 * live.length := mkSharedIncBlocks_length ..
  have hdecLen : decBlks.length = 5 := mkSharedDecBlocks_length ..
  have hexp : expandStmts l (newLabel l F) B.term B.cold rest0 fr.label tmp params acc =
      let r := stepSingle l B.cold (.call [dst] (l.resetWrapper idx) [.v x, .imm mask]) fr.label tmp params acc
      let t := expandStmts l (newLabel l F) B.term B.cold restStmts r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
      (r.1 ++ t.1, t.2) := by
    rw [hrest, expandStmts_cons_single _ _ _ _ _ _ _ _ _ _ hnp]
  have hexp1 : (expandStmts l (newLabel l F) B.term B.cold rest0 fr.label tmp params acc).1 =
      [({ params, body := acc.reverse.toArray,
          term := .br .tnz .w64 (.v x) (.imm 1) ⟨sharedLbl, []⟩ ⟨fr.label + 1, []⟩, cold := B.cold } : Lir.Block),
       { body := #[.assign tmp (.load .w32 .zero (cellAddr x 4))],
         term := .br .eq .w32 (.v tmp) (.imm 0) ⟨fr.label + 2, []⟩ ⟨sharedLbl, []⟩, cold := B.cold },
       { body := (mkDeadLoads x (tmp + 1) dead ++ mkShellStores x hdr lay.nobj ++
           mkDeadDecs l.decProc (tmp + 1) dead).toArray,
         term := .jump ⟨joinLbl, [.v x]⟩, cold := B.cold }] ++
      (incBlks ++ (decBlks ++
        (expandStmts l (newLabel l F) B.term B.cold restStmts joinLbl
          (tmp + 3 + dead.length + 3 * live.length) [dst] []).1)) := by
    rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]
    simp only [hle, ↓reduceIte, List.append_assoc]
    first | rfl | done
  have cpNext : ChunkAt l F b B (rawPos + 1) joinLbl 0
      (tmp + 3 + dead.length + 3 * live.length) [dst] [] restStmts := {
    bLookup := hcp.bLookup
    tmpGe := by have := hcp.tmpGe; omega
    split := by
      have htake : B.body.toList.take (rawPos + 1) =
          B.body.toList.take rawPos ++ [.call [dst] (l.resetWrapper idx) [.v x, .imm mask]] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB, hgetB]; simp
      rw [htake, List.append_assoc]; simpa [hrest] using hcp.split
    posLe := by omega
    blocksMatch := fun k blk hk => by
      have h := hcp.blocksMatch (3 + (5 * live.length + (5 + k))) blk (by
        rw [hexp1]
        refine (getElem?_append_right_add _ _ _ (by rfl)).trans ?_
        refine (getElem?_append_right_add _ _ _ hincLen).trans ?_
        exact (getElem?_append_right_add _ _ k hdecLen).trans hk)
      exact blocks_idx_cast h (by simp only [joinLbl]; omega)
    inPosEq := rfl
    endLbl := by
      have := hcp.endLbl
      rw [hrest, stmtsExtra_cons_nonPair hnp, stmtExtra, hclsSite] at this
      simp only [siteExtra, hle, ↓reduceIte] at this
      dsimp only [Lir.Label, joinLbl, live] at this ⊢; omega }
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  have hb0 : (inlineFunc l F).blocks[fr.label]? = some ({
      params, body := acc.reverse.toArray,
      term := .br .tnz .w64 (.v x) (.imm 1) ⟨sharedLbl, []⟩ ⟨fr.label + 1, []⟩, cold := B.cold } : Lir.Block) := by
    simpa using hcp.blocksMatch 0 _ (by rw [hexp1]; rfl)
  have hb1 : (inlineFunc l F).blocks[fr.label + 1]? = some ({
      body := #[.assign tmp (.load .w32 .zero (cellAddr x 4))],
      term := .br .eq .w32 (.v tmp) (.imm 0) ⟨fr.label + 2, []⟩ ⟨sharedLbl, []⟩, cold := B.cold } : Lir.Block) :=
    hcp.blocksMatch 1 _ (by rw [hexp1]; rfl)
  have hincBlks : ∀ k blk, incBlks[k]? = some blk → (inlineFunc l F).blocks[sharedLbl + k]? = some blk := by
    intro k blk hk
    have hkLt : k < incBlks.length := lt_length_of_getElem?_eq_some hk
    have h := hcp.blocksMatch (3 + k) blk (by
      rw [hexp1]
      refine (getElem?_append_right_add _ _ k (by rfl)).trans ?_
      exact (List.getElem?_append_left hkLt).trans hk)
    exact blocks_idx_cast h (by simp only [sharedLbl]; omega)
  have hdecBlks : ∀ k blk, decBlks[k]? = some blk → (inlineFunc l F).blocks[decLbl + k]? = some blk := by
    intro k blk hk
    have hkLt : k < decBlks.length := lt_length_of_getElem?_eq_some hk
    have h := hcp.blocksMatch (3 + (5 * live.length + k)) blk (by
      rw [hexp1]
      refine (getElem?_append_right_add _ _ _ (by rfl)).trans ?_
      refine (getElem?_append_right_add _ _ k hincLen).trans ?_
      exact (List.getElem?_append_left hkLt).trans hk)
    exact blocks_idx_cast h (by simp only [decLbl]; omega)
  obtain ⟨jb, _, hj0, hjp, _, _, _⟩ :=
    ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold restStmts
      joinLbl (tmp + 3 + dead.length + 3 * live.length) [dst] []
  have hbJ : (inlineFunc l F).blocks[joinLbl]? = some jb := by
    simpa using cpNext.blocksMatch 0 jb hj0
  have hdec2 : (inlineFunc l F).blocks[decLbl + 2]? =
      some { body := #[.call [] l.decProc [.v x]], term := .jump ⟨joinLbl, [.imm 1]⟩, cold := true } :=
    hdecBlks 2 _ rfl
  have hdec0 : ∃ nb, (inlineFunc l F).blocks[sharedLbl + 5 * live.length]? = some nb ∧ nb.params = [] :=
    ⟨_, by simpa [decLbl, sharedLbl, Nat.add_assoc] using hdecBlks 0 _ rfl, rfl⟩
  have hsharedBlk : ∃ sb, (inlineFunc l F).blocks[sharedLbl]? = some sb ∧ sb.params = [] := by
    cases hlv : live with
    | nil =>
      have ⟨nb, hnb, hnbp⟩ := hdec0
      rw [hlv] at hnb; exact ⟨nb, by simpa using hnb, hnbp⟩
    | cons j tl =>
      have h0 : (mkSharedIncBlocks x sharedLbl (tmp + 1 + dead.length) (j :: tl))[0]? = some _ := rfl
      exact ⟨_, by simpa using hincBlks 0 _ (by simpa [incBlks, hlv] using h0), rfl⟩
  obtain ⟨sb, hsb, hsbp⟩ := hsharedBlk
  have hpos0 : fr.pos = acc.reverse.toArray.size := by simp [hcp.inPosEq]
  refine ⟨⟨_, _, _, _, cpNext⟩, ⟨jb, hbJ, hjp⟩, hdec2, ?_⟩
  have htoShared : ∃ envS s₂,
      AgreeBelow (freshBase F) fr.env envS ∧
      Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₂ false ∧
      Sem.Star (Lir.semStep inl) s₂ 0
        { mem, ctx, stack := { fn := fr.fn, label := sharedLbl, pos := 0, env := envS } :: rest } := by
    unfold evalUniqueCheck at hshared
    by_cases htag : Lir.Cond.holds .tnz .w64 xVal 1 = true
    · have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
          .next { mem, ctx, stack := { fn := fr.fn, label := sharedLbl, pos := 0, env := fr.env } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term hF' hb0 hpos0]
        have hfwd : ¬ (sharedLbl ≤ fr.label) := by dsimp only [sharedLbl, Lir.Label]; omega
        have hfrS : ({ fr with label := sharedLbl, pos := 0 } : Lir.Frame) =
            { fn := fr.fn, label := sharedLbl, pos := 0, env := fr.env } := by
          cases fr; dsimp only at hdsts; subst hdsts; rfl
        rw [← hfrS]
        simp [Lir.Arg.eval, hx, htag, Lir.takeEdge, Lir.evalArgs, hsb, hsbp, Lir.bindParams, hfwd]
      exact ⟨fr.env, _, AgreeBelow.refl, s1, .refl _⟩
    · have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by simpa using htag
      simp only [htagF, Bool.false_eq_true, ↓reduceIte] at hshared
      cases hlc : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
      | none => simp [hlc] at hshared
      | some cnt =>
        simp only [hlc] at hshared
        have hnz : (X86.Width.w32.truncate cnt).toNat ≠ 0 := by intro hz; simp [hz] at hshared
        have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = false := by rw [w32_eq_zero]; simp [hnz]
        have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
            .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term hF' hb0 hpos0]
          simp [Lir.Arg.eval, hx, htagF, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams]
        let env1 := fr.env.insert tmp cnt
        have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } =
            .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fr with label := fr.label + 1, pos := 0 }) (ρ' := env1) (mem' := mem)
            hF' hb1 (by simp) rfl rfl
            (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell fr.env ctx x xVal 4 hx, hlc, env1])
        have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fn := fr.fn, label := sharedLbl, pos := 0, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fr with label := fr.label + 1, pos := 1, env := env1 }) hF' hb1 rfl]
          have hfwd : ¬ (sharedLbl ≤ fr.label + 1) := by dsimp only [sharedLbl, Lir.Label]; omega
          have hfrS : ({ fr with label := sharedLbl, pos := 0, env := env1 } : Lir.Frame) =
              { fn := fr.fn, label := sharedLbl, pos := 0, env := env1 } := by
            cases fr; dsimp only at hdsts; subst hdsts; rfl
          rw [← hfrS]
          simp [Lir.Arg.eval, env1, heq0, Lir.takeEdge, Lir.evalArgs, hsb, hsbp, Lir.bindParams, hfwd]
        exact ⟨env1, _, AgreeBelow.refl.insert_ge hcp.tmpGe cnt, s1, .free s2 (.free s3 (.refl _))⟩
  obtain ⟨envS, s₂, hagS, hs₂, hstarS⟩ := htoShared
  have hxS : envS[x]? = some xVal := by rw [← hagS x hxLt, hx]
  have hinc := inl_sharedIncBlocks_exec (p := inl) (F' := inlineFunc l F) (fn := fr.fn)
    (x := x) (xVal := xVal) (ctx := ctx) (rest := rest) (bound := freshBase F)
    hF' hxLt live sharedLbl (tmp + 1 + dead.length) envS mem (by have := hcp.tmpGe; omega) hxS hincBlks hdec0
  cases hincEv : evalSharedIncList xVal live mem with
  | oom =>
    dsimp only
    rw [hincEv] at hinc
    exact .free hs₂ (by simpa using star_reaches hstarS hinc)
  | stuck =>
    dsimp only
    rw [hincEv] at hinc
    exact .free hs₂ (by simpa using star_reaches hstarS hinc)
  | ok mem₁ =>
    dsimp only
    rw [hincEv] at hinc
    obtain ⟨envI, hagI, hincStar⟩ := hinc
    have hagSI : AgreeBelow (freshBase F) fr.env envI := fun r hr => (hagS r hr).trans (hagI r hr)
    have hxI : envI[x]? = some xVal := by rw [← hagSI x hxLt, hx]
    have hdec := inl_sharedDecBlocks_exec hr (F' := inlineFunc l F) (fn := fr.fn)
      (decLbl := decLbl) (doneLbl := joinLbl) (tmp := tmp + 1 + dead.length + 3 * live.length)
      (bound := freshBase F) (x := x) (xVal := xVal) (ctx := ctx) (doneSlot := some dst) (doneBlk := jb)
      (env0 := envI) (mem := mem₁) (rest := rest)
      hF' hxLt (by have := hcp.tmpGe; omega) hxI (by dsimp only [decLbl, joinLbl, Lir.Label]; omega)
      hbJ hjp hdecBlks
    have hincStar' : Sem.Star (Lir.semStep inl) s₂ 0
        { mem := mem₁, ctx, stack := { fn := fr.fn, label := decLbl, pos := 0, env := envI } :: rest } := by
      simpa [decLbl, sharedLbl, Nat.add_assoc] using hstarS.trans hincStar
    cases hdev : evalDecSite xVal mem₁ with
    | stuck =>
      dsimp only
      rw [hdev] at hdec
      exact .free hs₂ (by simpa using star_reaches hincStar' hdec)
    | ok mem' =>
      dsimp only
      rw [hdev] at hdec
      obtain ⟨envD, hdecStar, hagD⟩ := hdec
      have hagFD : AgreeBelow (freshBase F) (fr.env.insert dst 1) envD :=
        fun r hr => ((hagSI.insert_same dst 1) r hr).trans (hagD r hr)
      have hfrJ : ({ fn := fr.fn, label := joinLbl, pos := 0, env := envD } : Lir.Frame) =
          { fr with label := joinLbl, pos := 0, env := envD, dsts := [] } := by cases fr; rfl
      exact ⟨envD, s₂, hs₂, by simpa [hfrJ] using hincStar'.trans hdecStar, hagFD⟩
    | free =>
      dsimp only
      rw [hdev] at hdec
      obtain ⟨env1, hag1, hdecStar⟩ := hdec
      have hagF1 : AgreeBelow (freshBase F) fr.env env1 := fun r hr => (hagSI r hr).trans (hag1 r hr)
      have hfrD : ({ fn := fr.fn, label := decLbl + 2, pos := 1, env := env1, dsts := [] } : Lir.Frame) =
          { fr with label := decLbl + 2, pos := 1, env := env1, dsts := [] } := by cases fr; rfl
      exact ⟨env1, s₂, hs₂, by simpa [hfrD] using hincStar'.trans hdecStar, hagF1⟩

/-- Helper: advance `inl` on `reset` (dynamic, fallback `live.length > maxInlineResetLive`) when `evalUniqueCheck xVal mem = .shared`,
redirecting straight to `call [tmp + 1] (l.resetWrapper idx) [.v x, .imm mask]` in cold block `fr.label + 3`. -/
theorem inl_reset_cold_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 restStmts : List Lir.Stmt} {dst x : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {mask xVal : Lir.Word}
    (hltFn : fr.fn < l.sourceCount) (hF : raw.funcs[fr.fn]? = some F)
    (_hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = .call [dst] (l.resetWrapper idx) [.v x, .imm mask] :: restStmts)
    (hnp : ∀ s2 rest2, restStmts = s2 :: rest2 →
      classifyPair l (.call [dst] (l.resetWrapper idx) [.v x, .imm mask]) s2 = none)
    (hclsSite : classify l (.call [dst] (l.resetWrapper idx) [.v x, .imm mask]) =
      some (.reset dst x idx lay cls mask))
    (hposB : rawPos < B.body.size)
    (hgetB : B.body[rawPos] = .call [dst] (l.resetWrapper idx) [.v x, .imm mask])
    (hx : fr.env[x]? = some xVal) (hxLt : (x : Nat) < freshBase F)
    (hshared : evalUniqueCheck xVal mem = .shared)
    (hgt : ¬ (liveFields lay.nobj mask).length ≤ maxInlineResetLive) :
    let inl := inlineProgram l raw
    ChunkPos l F b B (rawPos + 1) (fr.label + 4) 0 ∧
    (∃ jb, (inlineFunc l F).blocks[fr.label + 4]? = some jb ∧ jb.params = [dst]) ∧
    (inlineFunc l F).blocks[fr.label + 3]? =
      some { body := #[.call [tmp + 1] (l.resetWrapper idx) [.v x, .imm mask]],
             term := .jump ⟨fr.label + 4, [.v (tmp + 1)]⟩, cold := true } ∧
    ∃ callee env' s₂,
      Lir.enter raw (l.resetWrapper idx) [xVal, mask] = some callee ∧
      AgreeBelow (freshBase F) fr.env env' ∧
      Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₂ false ∧
      Sem.Star (Lir.semStep inl) s₂ 1
        { mem, ctx, stack := callee :: { fr with label := fr.label + 3, pos := 1, env := env', dsts := [tmp + 1] } :: rest } := by
  intro inl
  obtain ⟨c, hc, _, hlay, hclsOk, _, _⟩ := classify_eq_reset hclsSite
  let dead := deadFields lay.nobj mask
  have hexp : expandStmts l (newLabel l F) B.term B.cold rest0 fr.label tmp params acc =
      let r := stepSingle l B.cold (.call [dst] (l.resetWrapper idx) [.v x, .imm mask]) fr.label tmp params acc
      let t := expandStmts l (newLabel l F) B.term B.cold restStmts r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
      (r.1 ++ t.1, t.2) := by
    rw [hrest, expandStmts_cons_single _ _ _ _ _ _ _ _ _ _ hnp]
  have cpNext : ChunkAt l F b B (rawPos + 1) (fr.label + 4) 0 (tmp + 2 + dead.length) [dst] [] restStmts := {
    bLookup := hcp.bLookup
    tmpGe := by have := hcp.tmpGe; omega
    split := by
      have htake : B.body.toList.take (rawPos + 1) =
          B.body.toList.take rawPos ++ [.call [dst] (l.resetWrapper idx) [.v x, .imm mask]] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB, hgetB]; simp
      rw [htake, List.append_assoc]; simpa [hrest] using hcp.split
    posLe := by omega
    blocksMatch := fun k blk hk => by
      have h := hcp.blocksMatch (4 + k) blk (by
        rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; simp only [hgt, ↓reduceIte]
        rw [Nat.add_comm 4 k]; exact hk)
      simpa [Nat.add_assoc] using h
    inPosEq := rfl
    endLbl := by
      have := hcp.endLbl
      rw [hrest, stmtsExtra_cons_nonPair hnp, stmtExtra, hclsSite] at this
      simp only [siteExtra, hgt, ↓reduceIte] at this
      dsimp only [Lir.Label] at this ⊢; omega }
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  have hb0 : (inlineFunc l F).blocks[fr.label]? = some {
      params, body := acc.reverse.toArray,
      term := .br .tnz .w64 (.v x) (.imm 1) ⟨fr.label + 3, []⟩ ⟨fr.label + 1, []⟩, cold := B.cold } := by
    simpa using hcp.blocksMatch 0 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; simp only [hgt, ↓reduceIte]; rfl)
  have hb1 : (inlineFunc l F).blocks[fr.label + 1]? = some {
      body := #[.assign tmp (.load .w32 .zero (cellAddr x 4))],
      term := .br .eq .w32 (.v tmp) (.imm 0) ⟨fr.label + 2, []⟩ ⟨fr.label + 3, []⟩, cold := B.cold } := by
    exact hcp.blocksMatch 1 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; simp only [hgt, ↓reduceIte]; rfl)
  have hb3 : (inlineFunc l F).blocks[fr.label + 3]? = some {
      body := #[.call [tmp + 1] (l.resetWrapper idx) [.v x, .imm mask]],
      term := .jump ⟨fr.label + 4, [.v (tmp + 1)]⟩, cold := true } := by
    exact hcp.blocksMatch 3 _ (by rw [hexp]; dsimp only [stepSingle]; rw [hclsSite]; simp only [hgt, ↓reduceIte]; rfl)
  obtain ⟨jb, _, hj0, hjp, _, _, _⟩ :=
    ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold restStmts (fr.label + 4) (tmp + 2 + dead.length) [dst] []
  have hb4 : (inlineFunc l F).blocks[fr.label + 4]? = some jb := by
    simpa using cpNext.blocksMatch 0 jb hj0
  have hpos0 : fr.pos = acc.reverse.toArray.size := by simp [hcp.inPosEq]
  have hwrapRaw : raw.funcs[l.resetWrapper idx]? =
      some (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls) := by
    rw [hlay]; exact hr.resetWrap idx c cls hc (by rwa [← hlay])
  have hwrapInl : inl.funcs[l.resetWrapper idx]? =
      some (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls) := by
    rw [hlay]; exact inlineProgram_resetWrap l raw hr hc (by rwa [← hlay])
  let eW : Lir.Env := (({} : Lir.Env).insert 0 xVal).insert 1 mask
  let callee : Lir.Frame := { fn := l.resetWrapper idx, label := 0, pos := 0, env := eW }
  have hentRaw : Lir.enter raw (l.resetWrapper idx) [xVal, mask] = some callee := by
    simp [Lir.enter, hwrapRaw, mkResetWrapper, Lir.bindParams, eW, callee]
  have hentInl : Lir.enter inl (l.resetWrapper idx) [xVal, mask] = some callee := by
    simp [Lir.enter, hwrapInl, mkResetWrapper, Lir.bindParams, eW, callee]
  refine ⟨⟨_, _, _, _, cpNext⟩, ⟨jb, hb4, hjp⟩, hb3, ?_⟩
  unfold evalUniqueCheck at hshared
  by_cases htag : Lir.Cond.holds .tnz .w64 xVal 1 = true
  · have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
        .next { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0 } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term hF' hb0 hpos0]
      simp [Lir.Arg.eval, hx, htag, Lir.takeEdge, Lir.evalArgs, hb3, Lir.bindParams]
    have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0 } :: rest } =
        .next { mem, ctx, stack := callee :: { fr with label := fr.label + 3, pos := 1, dsts := [tmp + 1] } :: rest } true := by
      apply Lir.semStep_next.mpr
      exact Lir.step_call (fr := { fr with label := fr.label + 3, pos := 0 }) hF' hb3 (by simp) rfl
        (by simp [Lir.evalArgs, Lir.Arg.eval, hx]) hentInl
    exact ⟨callee, fr.env, _, hentRaw, AgreeBelow.refl, s1, .charge s2 (.refl _)⟩
  · have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by simpa using htag
    simp only [htagF, Bool.false_eq_true, ↓reduceIte] at hshared
    cases hlc : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none => simp [hlc] at hshared
    | some cnt =>
      simp only [hlc] at hshared
      have hnz : (X86.Width.w32.truncate cnt).toNat ≠ 0 := by
        intro hz; simp [hz] at hshared
      have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = false := by rw [w32_eq_zero]; simp [hnz]
      have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term hF' hb0 hpos0]
        simp [Lir.Arg.eval, hx, htagF, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams]
      let env1 := fr.env.insert tmp cnt
      have hx1 : env1[x]? = some xVal := by
        rw [Lir.env_insert_ne _ _ (by dsimp only [Lir.VReg] at hxLt ⊢; have := hcp.tmpGe; omega), hx]
      have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fr with label := fr.label + 1, pos := 0 }) (ρ' := env1) (mem' := mem)
          hF' hb1 (by simp) rfl rfl
          (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell fr.env ctx x xVal 4 hx, hlc, env1])
      have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0, env := env1 } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fr with label := fr.label + 1, pos := 1, env := env1 }) hF' hb1 rfl]
        simp [Lir.Arg.eval, env1, heq0, Lir.takeEdge, Lir.evalArgs, hb3, Lir.bindParams]
      have s4 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0, env := env1 } :: rest } =
          .next { mem, ctx, stack := callee :: { fr with label := fr.label + 3, pos := 1, env := env1, dsts := [tmp + 1] } :: rest } true := by
        apply Lir.semStep_next.mpr
        exact Lir.step_call (fr := { fr with label := fr.label + 3, pos := 0, env := env1 }) hF' hb3 (by simp) rfl
          (by simp [Lir.evalArgs, Lir.Arg.eval, hx1]) hentInl
      exact ⟨callee, env1, _, hentRaw, AgreeBelow.refl.insert_ge hcp.tmpGe cnt, s1,
        .free s2 (.free s3 (.charge s4 (.refl _)))⟩

/-- Helper: advance `inl` on `resetU` (static unique, 0 extra blocks!) through `mkDeadLoads` + `mkShellStores`,
stopping right before `mkDeadDecs ++ [.assign dst (.arg (.v x))]`. -/
theorem inl_resetU_prefix {l : Layout} {raw : Lir.Program}
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem mem₁ : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 restStmts : List Lir.Stmt} {dst x : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {mask xVal : Lir.Word} {allVals : List Lir.Word}
    (hltFn : fr.fn < l.sourceCount) (hF : raw.funcs[fr.fn]? = some F)
    (hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = .call [dst] (l.resetUWrapper idx) [.v x, .imm mask] :: restStmts)
    (hnp : ∀ s2 rest2, restStmts = s2 :: rest2 →
      classifyPair l (.call [dst] (l.resetUWrapper idx) [.v x, .imm mask]) s2 = none)
    (hclsSite : classify l (.call [dst] (l.resetUWrapper idx) [.v x, .imm mask]) =
      some (.resetU dst x idx lay cls mask))
    (hposB : rawPos < B.body.size)
    (hgetB : B.body[rawPos] = .call [dst] (l.resetUWrapper idx) [.v x, .imm mask])
    (hx : fr.env[x]? = some xVal) (hxLt : (x : Nat) < freshBase F)
    (hlf : loadFieldsMem mem xVal (List.range lay.nobj) = some allVals)
    (hws : writeShellMem mem xVal (Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1) lay.nobj = some mem₁) :
    let inl := inlineProgram l raw
    let dead := deadFields lay.nobj mask
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    let endPos := fr.pos + (dead.length + (1 + lay.nobj) + dead.length + 1)
    ChunkPos l F b B (rawPos + 1) fr.label endPos ∧
    ∃ blk post env' s₂,
      (inlineFunc l F).blocks[fr.label]? = some blk ∧
      blk.body.toList = acc.reverse ++ mkDeadLoads x tmp dead ++ mkShellStores x hdr lay.nobj ++
        mkDeadDecs l.decProc tmp dead ++ [.assign dst (.arg (.v x))] ++ post ∧
      Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₂ false ∧
      Sem.Star (Lir.semStep inl) s₂ 0
        { mem := mem₁, ctx, stack :=
          { fr with pos := fr.pos + (dead.length + (1 + lay.nobj)), env := env', dsts := [] } :: rest } ∧
      AgreeBelow (freshBase F) fr.env env' ∧
      env'[x]? = some xVal ∧
      (∀ i, (hi : i < dead.length) →
        env'[tmp + i]? = some (allVals[dead[i]]'(by
          have h1 := loadFieldsMem_length hlf; simp at h1
          have h2 := deadFields_lt lay.nobj mask (List.getElem_mem hi); omega))) := by
  intro inl dead hdr endPos
  let bodyStmts : List Lir.Stmt :=
    mkDeadLoads x tmp dead ++ mkShellStores x hdr lay.nobj ++
      mkDeadDecs l.decProc tmp dead ++ [.assign dst (.arg (.v x))]
  have hbodyLen : bodyStmts.length = dead.length + (1 + lay.nobj) + dead.length + 1 := by
    simp [bodyStmts, mkDeadLoads_length, mkShellStores_length, mkDeadDecs_length]; omega
  have hexp : expandStmts l (newLabel l F) B.term B.cold rest0 fr.label tmp params acc =
      expandStmts l (newLabel l F) B.term B.cold restStmts fr.label (tmp + dead.length) params
        (bodyStmts.reverse ++ acc) := by
    rw [hrest, expandStmts_cons_single _ _ _ _ _ _ _ _ _ _ hnp]
    simp [stepSingle, hclsSite, bodyStmts, dead, hdr]
  have cpNext : ChunkAt l F b B (rawPos + 1) fr.label endPos (tmp + dead.length) params
      (bodyStmts.reverse ++ acc) restStmts := {
    bLookup := hcp.bLookup
    tmpGe := by have := hcp.tmpGe; omega
    split := by
      have htake : B.body.toList.take (rawPos + 1) =
          B.body.toList.take rawPos ++ [.call [dst] (l.resetUWrapper idx) [.v x, .imm mask]] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB, hgetB]; simp
      rw [htake, List.append_assoc]; simpa [hrest] using hcp.split
    posLe := by omega
    blocksMatch := fun k blk hk => hcp.blocksMatch k blk (by rw [hexp]; exact hk)
    inPosEq := by dsimp only [endPos]; rw [hcp.inPosEq, List.length_append, List.length_reverse, hbodyLen]; omega
    endLbl := by
      have := hcp.endLbl
      rw [hrest, stmtsExtra_cons_nonPair hnp, stmtExtra, hclsSite] at this
      simpa [siteExtra] using this }
  refine ⟨⟨_, _, _, _, cpNext⟩, ?_⟩
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  obtain ⟨blk, post, h0, _, hblkBody, _, _⟩ :=
    ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold restStmts fr.label
      (tmp + dead.length) params (bodyStmts.reverse ++ acc)
  have hblk : (inlineFunc l F).blocks[fr.label]? = some blk := by
    simpa using cpNext.blocksMatch 0 blk h0
  have hfull : blk.body.toList = acc.reverse ++ mkDeadLoads x tmp dead ++ mkShellStores x hdr lay.nobj ++
      mkDeadDecs l.decProc tmp dead ++ [.assign dst (.arg (.v x))] ++ post := by
    simpa [bodyStmts, List.reverse_append, List.reverse_reverse, List.append_assoc] using hblkBody
  obtain ⟨deadVals, hdeadLoad, _, hdeadGet⟩ :=
    loadFieldsMem_sublist hlf dead (fun j hj => deadFields_lt lay.nobj mask hj)
  have hbodyL : blk.body.toList = acc.reverse ++ mkDeadLoads x tmp dead ++
      (mkShellStores x hdr lay.nobj ++ mkDeadDecs l.decProc tmp dead ++ [.assign dst (.arg (.v x))] ++ post) := by
    simpa [List.append_assoc] using hfull
  obtain ⟨env', hdlStar, hagD, hvalsD⟩ :=
    exec_mkDeadLoads (p := inl) (F := inlineFunc l F) (fn := fr.fn) (lbl := fr.label)
      (x := x) (xVal := xVal) (ctx := ctx) (rest := rest) hF' hblk
      (by dsimp only [Lir.VReg] at hxLt ⊢; have := hcp.tmpGe; omega) hx hbodyL hdeadLoad
  have hx' : env'[x]? = some xVal := by
    rw [hagD x (by dsimp only [Lir.VReg] at hxLt ⊢; have := hcp.tmpGe; omega)]; exact hx
  have hbodyS : blk.body.toList = (acc.reverse ++ mkDeadLoads x tmp dead) ++ mkShellStores x hdr lay.nobj ++
      (mkDeadDecs l.decProc tmp dead ++ [.assign dst (.arg (.v x))] ++ post) := by
    simpa [List.append_assoc] using hfull
  have hsh := exec_mkShellStores (p := inl) (F := inlineFunc l F) (fn := fr.fn) (lbl := fr.label)
    (x := x) (xVal := xVal) (hdr := hdr) (ctx := ctx) (rest := rest) hF' hblk hx' hbodyS (mem := mem)
  rw [hws] at hsh
  have hpreLen : acc.reverse.length = fr.pos := by rw [List.length_reverse, ← hcp.inPosEq]
  have hfrEq : ({ fn := fr.fn, label := fr.label, pos := acc.reverse.length, env := fr.env, dsts := [] } : Lir.Frame) = fr := by
    cases fr; simp only [hpreLen] at *; subst hdsts; rfl
  have hfrMid : ({ fn := fr.fn, label := fr.label, pos := acc.reverse.length + dead.length, env := env', dsts := [] } : Lir.Frame) =
      { fr with pos := fr.pos + dead.length, env := env', dsts := [] } := by
    cases fr; simp [hpreLen]
  have htot : Sem.Star (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0
      { mem := mem₁, ctx, stack := { fr with pos := fr.pos + (dead.length + (1 + lay.nobj)), env := env', dsts := [] } :: rest } := by
    have h1 : Sem.Star (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0
        { mem, ctx, stack := { fr with pos := fr.pos + dead.length, env := env', dsts := [] } :: rest } := by
      rwa [hfrEq, hfrMid] at hdlStar
    have h2 : Sem.Star (Lir.semStep inl)
        { mem, ctx, stack := { fr with pos := fr.pos + dead.length, env := env', dsts := [] } :: rest } 0
        { mem := mem₁, ctx, stack := { fr with pos := fr.pos + (dead.length + (1 + lay.nobj)), env := env', dsts := [] } :: rest } := by
      simpa [List.length_append, hpreLen, mkDeadLoads_length, Nat.add_assoc] using hsh
    exact h1.trans h2
  obtain ⟨_, hs, htail⟩ := star_zero_split htot (fun heq => by
    have hst := congrArg (fun s => (s.stack.head?.map (·.pos))) heq
    simp at hst)
  exact ⟨blk, post, env', _, hblk, hfull, hs, htail,
    fun r hr => (hagD r (by dsimp only [Lir.VReg] at hr ⊢; have := hcp.tmpGe; omega)).symm,
    hx', fun i hi => by rw [hvalsD i hi, hdeadGet i hi]⟩

/-- Helper: fused static `@unique` `resetU` + `reuseU` inlined execution (0 extra blocks, 0 ticks). -/
theorem inl_fusedResetUReuseU_exec {l : Layout} {raw : Lir.Program}
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem mem' : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 rest2 : List Lir.Stmt} {s1 s2 : Lir.Stmt}
    {slot x dst : Lir.VReg} {lay2 : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    {xVal : Lir.Word} {vals : List Lir.Word}
    (hltFn : fr.fn < l.sourceCount) (hF : raw.funcs[fr.fn]? = some F)
    (hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = s1 :: s2 :: rest2)
    (hp : classifyPair l s1 s2 = some (.fusedResetUReuseU slot x dst lay2 cls args))
    (hposB1 : rawPos < B.body.size) (hgetB1 : B.body[rawPos] = s1)
    (hposB2 : rawPos + 1 < B.body.size) (hgetB2 : B.body[rawPos + 1] = s2)
    (hx : fr.env[x]? = some xVal)
    (hargs : Lir.evalArgs fr.env args = some vals)
    (hwr : writeReuseMem mem xVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals = some mem') :
    let inl := inlineProgram l raw
    let env' := (fr.env.insert slot xVal).insert dst xVal
    ChunkPos l F b B (rawPos + 2) fr.label (fr.pos + (3 + args.length)) ∧
    ∃ s', Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s' false ∧
      Sem.Star (Lir.semStep inl) s' 0
        { mem := mem', ctx, stack := { fr with pos := fr.pos + (3 + args.length), env := env', dsts := [] } :: rest } := by
  intro inl env'
  obtain ⟨_, _, _, _, _, _, _, _, _, hsx, _, _, _⟩ := classifyPair_eq_fusedResetUReuseU hp
  let hdr2 := Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1
  let fused : List Lir.Stmt :=
    .store .w64 (cellAddr x 0) (.imm hdr2) :: mkFieldStores x 0 args ++
      [.assign slot (.arg (.v x)), .assign dst (.arg (.v x))]
  have hfLen : fused.length = 3 + args.length := by simp [fused, mkFieldStores_length]; omega
  have hexp : expandStmts l (newLabel l F) B.term B.cold rest0 fr.label tmp params acc =
      expandStmts l (newLabel l F) B.term B.cold rest2 fr.label tmp params (fused.reverse ++ acc) := by
    rw [hrest, expandStmts_cons_pair _ _ _ _ _ _ _ _ _ _ _ hp]
    simp [stepPair, fused, hdr2]
  have cpNext : ChunkAt l F b B (rawPos + 2) fr.label (fr.pos + (3 + args.length)) tmp params
      (fused.reverse ++ acc) rest2 := {
    bLookup := hcp.bLookup
    tmpGe := hcp.tmpGe
    split := by
      have htake1 : B.body.toList.take (rawPos + 1) = B.body.toList.take rawPos ++ [s1] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB1, hgetB1]; simp
      have htake2 : B.body.toList.take (rawPos + 2) = B.body.toList.take (rawPos + 1) ++ [s2] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB2, hgetB2]; simp
      rw [htake2, htake1, List.append_assoc, List.append_assoc]; simpa [hrest] using hcp.split
    posLe := by omega
    blocksMatch := fun k blk hk => hcp.blocksMatch k blk (by rw [hexp]; exact hk)
    inPosEq := by rw [hcp.inPosEq, List.length_append, List.length_reverse, hfLen]; omega
    endLbl := by
      have := hcp.endLbl
      rw [hrest, stmtsExtra_cons_pair _ _ _ _ hp] at this
      simpa [pairExtra] using this }
  refine ⟨⟨_, _, _, _, cpNext⟩, ?_⟩
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  obtain ⟨blk, post, h0, _, hblkBody, _, _⟩ :=
    ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold rest2 fr.label tmp params
      (fused.reverse ++ acc)
  have hblk : (inlineFunc l F).blocks[fr.label]? = some blk := by
    simpa using cpNext.blocksMatch 0 blk h0
  have hbodySplit : blk.body.toList = acc.reverse ++
      (.store .w64 (cellAddr x 0) (.imm hdr2) :: mkFieldStores x 0 args) ++
      ([.assign slot (.arg (.v x)), .assign dst (.arg (.v x))] ++ post) := by
    simpa [fused, List.reverse_append, List.reverse_reverse, List.append_assoc] using hblkBody
  have hwrStar := exec_writeReuse (p := inl) (F := inlineFunc l F) (B := blk) (fn := fr.fn) (lbl := fr.label)
    (base := x) (addr := xVal) (hdr := hdr2) (ctx := ctx) (rest := rest)
    hF' hblk hx hbodySplit hargs (mem := mem)
  rw [hwr] at hwrStar
  have hpreLen : acc.reverse.length = fr.pos := by rw [List.length_reverse, ← hcp.inPosEq]
  have hfrEq : ({ fn := fr.fn, label := fr.label, pos := acc.reverse.length, env := fr.env, dsts := [] } : Lir.Frame) = fr := by
    cases fr; simp only [hpreLen] at *; subst hdsts; rfl
  have hpos1 : fr.pos + (1 + args.length) < blk.body.size := by
    have := congrArg List.length hbodySplit
    simp only [Array.length_toList, List.length_append, List.length_cons, mkFieldStores_length, hpreLen] at this
    omega
  have hpos2 : fr.pos + (2 + args.length) < blk.body.size := by
    have := congrArg List.length hbodySplit
    simp only [Array.length_toList, List.length_append, List.length_cons, mkFieldStores_length, hpreLen] at this
    omega
  have hget1 : blk.body[fr.pos + (1 + args.length)] = .assign slot (.arg (.v x)) := by
    have h1 : blk.body.toList[fr.pos + (1 + args.length)]? = some (.assign slot (.arg (.v x))) := by
      rw [hbodySplit]
      have hl : (acc.reverse ++ (.store .w64 (cellAddr x 0) (.imm hdr2) :: mkFieldStores x 0 args)).length =
          fr.pos + (1 + args.length) := by simp [hpreLen, mkFieldStores_length]; omega
      rw [List.getElem?_append_right (by omega), hl, Nat.sub_self]; rfl
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hpos1, Option.some.injEq] at h1
    exact h1
  have hget2 : blk.body[fr.pos + (2 + args.length)] = .assign dst (.arg (.v x)) := by
    have h1 : blk.body.toList[fr.pos + (2 + args.length)]? = some (.assign dst (.arg (.v x))) := by
      rw [hbodySplit]
      have hl : (acc.reverse ++ (.store .w64 (cellAddr x 0) (.imm hdr2) :: mkFieldStores x 0 args)).length =
          fr.pos + (1 + args.length) := by simp [hpreLen, mkFieldStores_length]; omega
      rw [List.getElem?_append_right (by omega), hl]
      have hsub : fr.pos + (2 + args.length) - (fr.pos + (1 + args.length)) = 1 := by omega
      rw [hsub]; rfl
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hpos2, Option.some.injEq] at h1
    exact h1
  let env1 := fr.env.insert slot xVal
  have hx1 : env1[x]? = some xVal := by rw [Lir.env_insert_ne _ _ hsx, hx]
  have sAsn1 : Lir.semStep inl
      { mem := mem', ctx, stack := { fr with pos := fr.pos + (1 + args.length), dsts := [] } :: rest } =
      .next { mem := mem', ctx, stack := { fr with pos := fr.pos + (2 + args.length), env := env1, dsts := [] } :: rest } false := by
    apply Lir.semStep_next.mpr
    have h1 := Lir.step_stmt (fr := { fr with pos := fr.pos + (1 + args.length), dsts := [] })
      (mem := mem') (ctx := ctx) (rest := rest) (ρ' := env1) (mem' := mem')
      hF' hblk hpos1 hget1 rfl (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, hx, env1])
    have hidx : fr.pos + (1 + args.length) + 1 = fr.pos + (2 + args.length) := by omega
    simpa [hidx] using h1
  have sAsn2 : Lir.semStep inl
      { mem := mem', ctx, stack := { fr with pos := fr.pos + (2 + args.length), env := env1, dsts := [] } :: rest } =
      .next { mem := mem', ctx, stack := { fr with pos := fr.pos + (3 + args.length), env := env', dsts := [] } :: rest } false := by
    apply Lir.semStep_next.mpr
    have h1 := Lir.step_stmt (fr := { fr with pos := fr.pos + (2 + args.length), env := env1, dsts := [] })
      (mem := mem') (ctx := ctx) (rest := rest) (ρ' := env') (mem' := mem')
      hF' hblk hpos2 hget2 rfl (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, hx1, env', env1])
    have hidx : fr.pos + (2 + args.length) + 1 = fr.pos + (3 + args.length) := by omega
    simpa [hidx] using h1
  have htot : Sem.Star (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0
      { mem := mem', ctx, stack := { fr with pos := fr.pos + (3 + args.length), env := env', dsts := [] } :: rest } := by
    have hwr' : Sem.Star (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0
        { mem := mem', ctx, stack := { fr with pos := fr.pos + (1 + args.length), dsts := [] } :: rest } := by
      have h2 : { fn := fr.fn, label := fr.label, pos := acc.reverse.length + (1 + args.length), env := fr.env, dsts := [] } =
          { fr with pos := fr.pos + (1 + args.length), dsts := [] } := by
        cases fr; simp [hpreLen]
      rwa [hfrEq, h2] at hwrStar
    exact hwr'.trans (.free sAsn1 (.free sAsn2 (.refl _)))
  exact star_zero_split htot (fun heq => by
    have hst := congrArg (fun s => (s.stack.head?.map (·.pos))) heq
    simp at hst)

/-- Bundled block-layout witness for the 6 inline free-list/bump allocation blocks at
`allocLbl .. allocLbl + 5` and their shared publish block `pubLbl` (with params `[slot, dst]`). -/
structure InlineAllocShape (F' : Lir.Func) (allocLbl pubLbl : Lir.Label) (aBase : Nat)
    (slot dst : Lir.VReg) (slotArg : Lir.Arg) (lay : Rt.Rc.CellLayout) (cls : Nat)
    (args : List Lir.Arg) (pubBlk : Lir.Block) (postJ : List Lir.Stmt) : Prop where
  pubGt : allocLbl + 5 < pubLbl
  pubLookup : F'.blocks[pubLbl]? = some pubBlk
  pubParams : pubBlk.params = [slot, dst]
  pubBody : pubBlk.body.toList =
    [.store .w64 (cellAddr dst) (.imm (Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1))] ++
      mkFieldStores dst 0 args ++ postJ
  b0 : F'.blocks[allocLbl]? = some {
    body := #[.assign aBase (.load .w64 .zero (ctxAddr (Int.ofNat (8 * cls))))],
    term := .br .eq .w64 (.v aBase) (.imm 0) ⟨allocLbl + 2, []⟩ ⟨allocLbl + 1, []⟩, cold := true }
  b1 : F'.blocks[allocLbl + 1]? = some {
    body := #[.assign (aBase + 1) (.load .w64 .zero (cellAddr aBase)),
      .store .w64 (ctxAddr (Int.ofNat (8 * cls))) (.v (aBase + 1))],
    term := .jump ⟨pubLbl, [slotArg, .v aBase]⟩, cold := true }
  b2 : F'.blocks[allocLbl + 2]? = some {
    body := #[.assign (aBase + 2) (.load .w64 .zero (ctxAddr Rt.bumpOff)),
      .assign (aBase + 3) (.load .w64 .zero (ctxAddr Rt.limitOff))],
    term := .brOvf .addC (aBase + 4) (.v (aBase + 2)) (.imm (UInt64.ofNat (Rt.Rc.classBytes cls)))
      ⟨allocLbl + 3, []⟩ ⟨allocLbl + 5, []⟩, cold := true }
  b3 : F'.blocks[allocLbl + 3]? = some {
    body := #[],
    term := .br .ule .w64 (.v (aBase + 4)) (.v (aBase + 3)) ⟨allocLbl + 4, []⟩ ⟨allocLbl + 5, []⟩,
    cold := true }
  b4 : F'.blocks[allocLbl + 4]? = some {
    body := #[.store .w64 (ctxAddr Rt.bumpOff) (.v (aBase + 4))],
    term := .jump ⟨pubLbl, [slotArg, .v (aBase + 2)]⟩, cold := true }
  b5 : F'.blocks[allocLbl + 5]? = some { body := #[], term := .fail .heap, cold := true }

/-- Helper: fused dynamic `reset` + `reuse` inlined execution when `live.length ≤ maxInlineResetLive`
(inlined hot unique path OR inlined shared inc+dec path arriving at `allocLbl`). -/
theorem inl_fusedResetReuse_inline_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 rest2 : List Lir.Stmt} {s1 s2 : Lir.Stmt}
    {slot x dst : Lir.VReg} {idx1 : Nat} {lay1 : Rt.Rc.CellLayout} {mask : UInt64}
    {idx2 : Nat} {lay2 : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    {xVal : Lir.Word}
    (hltFn : fr.fn < l.sourceCount) (hF : raw.funcs[fr.fn]? = some F)
    (hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = s1 :: s2 :: rest2)
    (hp : classifyPair l s1 s2 = some (.fusedResetReuse slot x dst idx1 lay1 mask idx2 lay2 cls args))
    (hposB1 : rawPos < B.body.size) (hgetB1 : B.body[rawPos] = s1)
    (hposB2 : rawPos + 1 < B.body.size) (hgetB2 : B.body[rawPos + 1] = s2)
    (hx : fr.env[x]? = some xVal) (hxLt : (x : Nat) < freshBase F)
    (hargsLt : argsMax args 0 < freshBase F)
    (hle : (liveFields lay1.nobj mask).length ≤ maxInlineResetLive) :
    let inl := inlineProgram l raw
    let live := liveFields lay1.nobj mask
    let decLbl := fr.label + 2 + 5 * live.length
    let allocLbl := fr.label + 7 + 5 * live.length
    let pubLbl := fr.label + 13 + 5 * live.length
    let aBase := tmp + 3 + 3 * live.length
    let hdr2 := Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1
    let pFr0 : Lir.Frame := { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal }
    ChunkPos l F b B (rawPos + 2) pubLbl (1 + args.length) ∧
    (∃ pubBlk postJ, InlineAllocShape (inlineFunc l F) allocLbl pubLbl aBase slot dst (.imm 1) lay2 cls args pubBlk postJ) ∧
    (inlineFunc l F).blocks[decLbl + 2]? =
      some { body := #[.call [] l.decProc [.v x]], term := .jump ⟨allocLbl, []⟩, cold := true } ∧
    (∀ {vals mem'}, evalUniqueCheck xVal mem = .unique →
      Lir.evalArgs fr.env args = some vals →
      writeReuseMem mem xVal hdr2 vals = some mem' →
      ∃ env' s',
        AgreeBelow (freshBase F) ((fr.env.insert slot xVal).insert dst xVal) env' ∧
        Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s' false ∧
        Sem.Star (Lir.semStep inl) s' 0
          { mem := mem', ctx, stack := { fr with label := pubLbl, pos := 1 + args.length, env := env', dsts := [] } :: rest }) ∧
    (evalUniqueCheck xVal mem = .shared →
      match evalSharedIncList xVal live mem with
      | .oom =>
        Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 (.resource .heap)
      | .stuck =>
        Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 .stuck
      | .ok mem₁ =>
        match evalDecSite xVal mem₁ with
        | .stuck =>
          Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 .stuck
        | .ok mem_dec =>
          ∃ envD s',
            Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s' false ∧
            Sem.Star (Lir.semStep inl) s' 0
              { mem := mem_dec, ctx, stack := { fn := fr.fn, label := allocLbl, pos := 0, env := envD } :: rest } ∧
            AgreeBelow (freshBase F) fr.env envD
        | .free =>
          ∃ env1 s',
            Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s' false ∧
            Sem.Star (Lir.semStep inl) s' 1
              { mem := mem₁, ctx, stack := pFr0 :: { fr with label := decLbl + 2, pos := 1, env := env1, dsts := [] } :: rest } ∧
            AgreeBelow (freshBase F) fr.env env1) := by
  intro inl live decLbl allocLbl pubLbl aBase hdr2 pFr0
  obtain ⟨_, _, _, _, _, _, _, hnd, hns⟩ := classifyPair_eq_fusedResetReuse hp
  let sharedLbl := fr.label + 2
  let headOff := Int.ofNat (8 * cls)
  let bytes := UInt64.ofNat (Rt.Rc.classBytes cls)
  let pubInit : List Lir.Stmt := Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr2) :: mkFieldStores dst 0 args
  have hpubLen : pubInit.length = 1 + args.length := by
    simp only [pubInit, List.length_cons, mkFieldStores_length]; omega
  let incBlks := mkSharedIncBlocks x sharedLbl (tmp + 1) live
  let decBlks := mkSharedDecBlocks l.decProc x decLbl (tmp + 1 + 3 * live.length) ⟨allocLbl, []⟩
  have hincLen : incBlks.length = 5 * live.length := mkSharedIncBlocks_length ..
  have hdecLen : decBlks.length = 5 := mkSharedDecBlocks_length ..
  let allocBlks : List Lir.Block := [
    { body := #[.assign aBase (.load .w64 .zero (ctxAddr headOff))],
      term := .br .eq .w64 (.v aBase) (.imm 0) ⟨allocLbl + 2, []⟩ ⟨allocLbl + 1, []⟩, cold := true },
    { body := #[.assign (aBase + 1) (.load .w64 .zero (cellAddr aBase)),
        .store .w64 (ctxAddr headOff) (.v (aBase + 1))],
      term := .jump ⟨pubLbl, [.imm 1, .v aBase]⟩, cold := true },
    { body := #[.assign (aBase + 2) (.load .w64 .zero (ctxAddr Rt.bumpOff)),
        .assign (aBase + 3) (.load .w64 .zero (ctxAddr Rt.limitOff))],
      term := .brOvf .addC (aBase + 4) (.v (aBase + 2)) (.imm bytes) ⟨allocLbl + 3, []⟩ ⟨allocLbl + 5, []⟩, cold := true },
    { body := #[], term := .br .ule .w64 (.v (aBase + 4)) (.v (aBase + 3)) ⟨allocLbl + 4, []⟩ ⟨allocLbl + 5, []⟩, cold := true },
    { body := #[.store .w64 (ctxAddr Rt.bumpOff) (.v (aBase + 4))],
      term := .jump ⟨pubLbl, [.imm 1, .v (aBase + 2)]⟩, cold := true },
    { body := #[], term := .fail .heap, cold := true }]
  have hexp : expandStmts l (newLabel l F) B.term B.cold rest0 fr.label tmp params acc =
      let r := stepPair l B.cold (.fusedResetReuse slot x dst idx1 lay1 mask idx2 lay2 cls args) fr.label tmp params acc
      let t := expandStmts l (newLabel l F) B.term B.cold rest2 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
      (r.1 ++ t.1, t.2) := by
    rw [hrest, expandStmts_cons_pair _ _ _ _ _ _ _ _ _ _ _ hp]
  have hexp1 : (expandStmts l (newLabel l F) B.term B.cold rest0 fr.label tmp params acc).1 =
      [({ params, body := acc.reverse.toArray,
          term := .br .tnz .w64 (.v x) (.imm 1) ⟨sharedLbl, []⟩ ⟨fr.label + 1, []⟩, cold := B.cold } : Lir.Block),
       { body := #[.assign tmp (.load .w32 .zero (cellAddr x 4))],
         term := .br .eq .w32 (.v tmp) (.imm 0) ⟨pubLbl, [.v x, .v x]⟩ ⟨sharedLbl, []⟩, cold := B.cold }] ++
      (incBlks ++ (decBlks ++ (allocBlks ++
        (expandStmts l (newLabel l F) B.term B.cold rest2 pubLbl
          (tmp + 8 + 3 * live.length) [slot, dst] pubInit.reverse).1))) := by
    rw [hexp]; dsimp only [stepPair]
    simp only [hle, ↓reduceIte, List.append_assoc]
    first | rfl | done
  have cpNext : ChunkAt l F b B (rawPos + 2) pubLbl (1 + args.length)
      (tmp + 8 + 3 * live.length) [slot, dst] pubInit.reverse rest2 := {
    bLookup := hcp.bLookup
    tmpGe := by have := hcp.tmpGe; omega
    split := by
      have htake1 : B.body.toList.take (rawPos + 1) = B.body.toList.take rawPos ++ [s1] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB1, hgetB1]; simp
      have htake2 : B.body.toList.take (rawPos + 2) = B.body.toList.take (rawPos + 1) ++ [s2] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB2, hgetB2]; simp
      rw [htake2, htake1, List.append_assoc, List.append_assoc]; simpa [hrest] using hcp.split
    posLe := by omega
    blocksMatch := fun k blk hk => by
      have h := hcp.blocksMatch (2 + (5 * live.length + (5 + (6 + k)))) blk (by
        rw [hexp1]
        refine (getElem?_append_right_add _ _ _ (by rfl)).trans ?_
        refine (getElem?_append_right_add _ _ _ hincLen).trans ?_
        refine (getElem?_append_right_add _ _ _ hdecLen).trans ?_
        exact (getElem?_append_right_add _ _ k (by rfl)).trans hk)
      exact blocks_idx_cast h (by simp only [pubLbl]; omega)
    inPosEq := by rw [List.length_reverse, hpubLen]
    endLbl := by
      have := hcp.endLbl
      rw [hrest, stmtsExtra_cons_pair _ _ _ _ hp] at this
      simp only [pairExtra, hle, ↓reduceIte] at this
      dsimp only [Lir.Label, pubLbl, live] at this ⊢; omega }
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  have hb0 : (inlineFunc l F).blocks[fr.label]? = some ({
      params, body := acc.reverse.toArray,
      term := .br .tnz .w64 (.v x) (.imm 1) ⟨sharedLbl, []⟩ ⟨fr.label + 1, []⟩, cold := B.cold } : Lir.Block) := by
    simpa using hcp.blocksMatch 0 _ (by rw [hexp1]; rfl)
  have hb1 : (inlineFunc l F).blocks[fr.label + 1]? = some ({
      body := #[.assign tmp (.load .w32 .zero (cellAddr x 4))],
      term := .br .eq .w32 (.v tmp) (.imm 0) ⟨pubLbl, [.v x, .v x]⟩ ⟨sharedLbl, []⟩, cold := B.cold } : Lir.Block) :=
    hcp.blocksMatch 1 _ (by rw [hexp1]; rfl)
  have hincBlks : ∀ k blk, incBlks[k]? = some blk → (inlineFunc l F).blocks[sharedLbl + k]? = some blk := by
    intro k blk hk
    have hkLt : k < incBlks.length := lt_length_of_getElem?_eq_some hk
    have h := hcp.blocksMatch (2 + k) blk (by
      rw [hexp1]
      refine (getElem?_append_right_add _ _ k (by rfl)).trans ?_
      exact (List.getElem?_append_left hkLt).trans hk)
    exact blocks_idx_cast h (by simp only [sharedLbl]; omega)
  have hdecBlks : ∀ k blk, decBlks[k]? = some blk → (inlineFunc l F).blocks[decLbl + k]? = some blk := by
    intro k blk hk
    have hkLt : k < decBlks.length := lt_length_of_getElem?_eq_some hk
    have h := hcp.blocksMatch (2 + (5 * live.length + k)) blk (by
      rw [hexp1]
      refine (getElem?_append_right_add _ _ _ (by rfl)).trans ?_
      refine (getElem?_append_right_add _ _ k hincLen).trans ?_
      exact (List.getElem?_append_left hkLt).trans hk)
    exact blocks_idx_cast h (by simp only [decLbl]; omega)
  have hallocBlks : ∀ k blk, allocBlks[k]? = some blk → (inlineFunc l F).blocks[allocLbl + k]? = some blk := by
    intro k blk hk
    have hkLt : k < allocBlks.length := lt_length_of_getElem?_eq_some hk
    have h := hcp.blocksMatch (2 + (5 * live.length + (5 + k))) blk (by
      rw [hexp1]
      refine (getElem?_append_right_add _ _ _ (by rfl)).trans ?_
      refine (getElem?_append_right_add _ _ _ hincLen).trans ?_
      refine (getElem?_append_right_add _ _ k hdecLen).trans ?_
      exact (List.getElem?_append_left hkLt).trans hk)
    exact blocks_idx_cast h (by simp only [allocLbl]; omega)
  obtain ⟨pubBlk, postJ, hpub0, hpubP, hpubBody0, _, _⟩ :=
    ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold rest2
      pubLbl (tmp + 8 + 3 * live.length) [slot, dst] pubInit.reverse
  have hpub : (inlineFunc l F).blocks[pubLbl]? = some pubBlk := by
    simpa using cpNext.blocksMatch 0 pubBlk hpub0
  have hpubBody : pubBlk.body.toList = [.store .w64 (cellAddr dst) (.imm hdr2)] ++ mkFieldStores dst 0 args ++ postJ := by
    simpa [pubInit, List.reverse_reverse, List.cons_append] using hpubBody0
  have hshape : InlineAllocShape (inlineFunc l F) allocLbl pubLbl aBase slot dst (.imm 1) lay2 cls args pubBlk postJ := {
    pubGt := by dsimp only [allocLbl, pubLbl, Lir.Label]; omega
    pubLookup := hpub
    pubParams := hpubP
    pubBody := hpubBody
    b0 := by simpa [headOff] using hallocBlks 0 _ rfl
    b1 := by simpa [headOff] using hallocBlks 1 _ rfl
    b2 := by simpa [bytes] using hallocBlks 2 _ rfl
    b3 := hallocBlks 3 _ rfl
    b4 := hallocBlks 4 _ rfl
    b5 := hallocBlks 5 _ rfl }
  have hdec2 : (inlineFunc l F).blocks[decLbl + 2]? =
      some { body := #[.call [] l.decProc [.v x]], term := .jump ⟨allocLbl, []⟩, cold := true } :=
    hdecBlks 2 _ rfl
  have hdec0 : ∃ nb, (inlineFunc l F).blocks[sharedLbl + 5 * live.length]? = some nb ∧ nb.params = [] :=
    ⟨_, by simpa [decLbl, sharedLbl, Nat.add_assoc] using hdecBlks 0 _ rfl, rfl⟩
  have hsharedBlk : ∃ sb, (inlineFunc l F).blocks[sharedLbl]? = some sb ∧ sb.params = [] := by
    cases hlv : live with
    | nil =>
      have ⟨nb, hnb, hnbp⟩ := hdec0
      rw [hlv] at hnb; exact ⟨nb, by simpa using hnb, hnbp⟩
    | cons j tl =>
      have h0 : (mkSharedIncBlocks x sharedLbl (tmp + 1) (j :: tl))[0]? = some _ := rfl
      exact ⟨_, by simpa using hincBlks 0 _ (by simpa [incBlks, hlv] using h0), rfl⟩
  obtain ⟨sb, hsb, hsbp⟩ := hsharedBlk
  have hpos0 : fr.pos = acc.reverse.toArray.size := by simp [hcp.inPosEq]
  refine ⟨⟨_, _, _, _, cpNext⟩, ⟨pubBlk, postJ, hshape⟩, hdec2, ?_, ?_⟩
  · intro vals mem' huniq hargs hwr
    unfold evalUniqueCheck at huniq
    have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by
      cases ht : Lir.Cond.holds .tnz .w64 xVal 1
      · rfl
      · simp [ht] at huniq
    simp only [htagF, Bool.false_eq_true, ↓reduceIte] at huniq
    cases hlc : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none => simp [hlc] at huniq
    | some cnt =>
      simp only [hlc] at huniq
      have hz : (X86.Width.w32.truncate cnt).toNat = 0 := by
        by_cases h0 : (X86.Width.w32.truncate cnt).toNat = 0
        · exact h0
        · simp [h0] at huniq
      have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = true := by rw [w32_eq_zero]; simp [hz]
      have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term hF' hb0 hpos0]
        simp [Lir.Arg.eval, hx, htagF, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams]
      let env1 := fr.env.insert tmp cnt
      have hx1 : env1[x]? = some xVal := by
        rw [Lir.env_insert_ne _ _ (by dsimp only [Lir.VReg] at hxLt ⊢; have := hcp.tmpGe; omega), hx]
      have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fr with label := fr.label + 1, pos := 0 }) (ρ' := env1) (mem' := mem)
          hF' hb1 (by simp) rfl rfl
          (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell fr.env ctx x xVal 4 hx, hlc, env1])
      let env2 := (env1.insert slot xVal).insert dst xVal
      have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } =
          .next { mem, ctx, stack := { fr with label := pubLbl, pos := 0, env := env2 } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fr with label := fr.label + 1, pos := 1, env := env1 }) hF' hb1 rfl]
        have hfwd : ¬ (pubLbl ≤ fr.label + 1) := by dsimp only [pubLbl, Lir.Label]; omega
        simp [Lir.Arg.eval, env1, hx1, heq0, Lir.takeEdge, Lir.evalArgs, hpub, hpubP, Lir.bindParams, hfwd, env2]
      have hargs2 : Lir.evalArgs env2 args = some vals := by
        simp only [env2]
        rw [evalArgs_insert_not_mem (argsContainVReg_false hnd),
          evalArgs_insert_not_mem (argsContainVReg_false hns),
          ← (AgreeBelow.refl.insert_ge hcp.tmpGe cnt).evalArgs_eq hargsLt, hargs]
      have hpubBody' : pubBlk.body.toList =
          [] ++ (.store .w64 (cellAddr dst 0) (.imm hdr2) :: mkFieldStores dst 0 args) ++ postJ := by
        simpa [cellAddr] using hpubBody
      have hwrStar := exec_writeReuse (p := inl) (F := inlineFunc l F) (B := pubBlk)
        (fn := fr.fn) (lbl := pubLbl) (base := dst) (addr := xVal) (hdr := hdr2)
        (ctx := ctx) (rest := rest) (env := env2) hF' hpub (by simp [env2]) hpubBody' hargs2 (mem := mem)
      rw [hwr] at hwrStar
      have hfrPub : ({ fn := fr.fn, label := pubLbl, pos := 0, env := env2, dsts := [] } : Lir.Frame) =
          { fr with label := pubLbl, pos := 0, env := env2 } := by
        cases fr; dsimp only at hdsts; subst hdsts; rfl
      refine ⟨env2, _, ((AgreeBelow.refl.insert_ge hcp.tmpGe cnt).insert_same slot xVal).insert_same dst xVal,
        s1, .free s2 (.free s3 (by simpa [hfrPub] using hwrStar))⟩
  · intro hshared
    have htoShared : ∃ envS s₂,
        AgreeBelow (freshBase F) fr.env envS ∧
        Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₂ false ∧
        Sem.Star (Lir.semStep inl) s₂ 0
          { mem, ctx, stack := { fn := fr.fn, label := sharedLbl, pos := 0, env := envS } :: rest } := by
      unfold evalUniqueCheck at hshared
      by_cases htag : Lir.Cond.holds .tnz .w64 xVal 1 = true
      · have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
            .next { mem, ctx, stack := { fn := fr.fn, label := sharedLbl, pos := 0, env := fr.env } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term hF' hb0 hpos0]
          have hfwd : ¬ (sharedLbl ≤ fr.label) := by dsimp only [sharedLbl, Lir.Label]; omega
          have hfrS : ({ fr with label := sharedLbl, pos := 0 } : Lir.Frame) =
              { fn := fr.fn, label := sharedLbl, pos := 0, env := fr.env } := by
            cases fr; dsimp only at hdsts; subst hdsts; rfl
          rw [← hfrS]
          simp [Lir.Arg.eval, hx, htag, Lir.takeEdge, Lir.evalArgs, hsb, hsbp, Lir.bindParams, hfwd]
        exact ⟨fr.env, _, AgreeBelow.refl, s1, .refl _⟩
      · have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by simpa using htag
        simp only [htagF, Bool.false_eq_true, ↓reduceIte] at hshared
        cases hlc : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
        | none => simp [hlc] at hshared
        | some cnt =>
          simp only [hlc] at hshared
          have hnz : (X86.Width.w32.truncate cnt).toNat ≠ 0 := by intro hz; simp [hz] at hshared
          have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = false := by rw [w32_eq_zero]; simp [hnz]
          have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
              .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term hF' hb0 hpos0]
            simp [Lir.Arg.eval, hx, htagF, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams]
          let env1 := fr.env.insert tmp cnt
          have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } =
              .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fr with label := fr.label + 1, pos := 0 }) (ρ' := env1) (mem' := mem)
              hF' hb1 (by simp) rfl rfl
              (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell fr.env ctx x xVal 4 hx, hlc, env1])
          have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } =
              .next { mem, ctx, stack := { fn := fr.fn, label := sharedLbl, pos := 0, env := env1 } :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fr with label := fr.label + 1, pos := 1, env := env1 }) hF' hb1 rfl]
            have hfwd : ¬ (sharedLbl ≤ fr.label + 1) := by dsimp only [sharedLbl, Lir.Label]; omega
            have hfrS : ({ fr with label := sharedLbl, pos := 0, env := env1 } : Lir.Frame) =
                { fn := fr.fn, label := sharedLbl, pos := 0, env := env1 } := by
              cases fr; dsimp only at hdsts; subst hdsts; rfl
            rw [← hfrS]
            simp [Lir.Arg.eval, env1, heq0, Lir.takeEdge, Lir.evalArgs, hsb, hsbp, Lir.bindParams, hfwd]
          exact ⟨env1, _, AgreeBelow.refl.insert_ge hcp.tmpGe cnt, s1, .free s2 (.free s3 (.refl _))⟩
    obtain ⟨envS, s₂, hagS, hs₂, hstarS⟩ := htoShared
    have hxS : envS[x]? = some xVal := by rw [← hagS x hxLt, hx]
    have hinc := inl_sharedIncBlocks_exec (p := inl) (F' := inlineFunc l F) (fn := fr.fn)
      (x := x) (xVal := xVal) (ctx := ctx) (rest := rest) (bound := freshBase F)
      hF' hxLt live sharedLbl (tmp + 1) envS mem (by have := hcp.tmpGe; omega) hxS hincBlks hdec0
    cases hincEv : evalSharedIncList xVal live mem with
    | oom =>
      dsimp only
      rw [hincEv] at hinc
      exact .free hs₂ (by simpa using star_reaches hstarS hinc)
    | stuck =>
      dsimp only
      rw [hincEv] at hinc
      exact .free hs₂ (by simpa using star_reaches hstarS hinc)
    | ok mem₁ =>
      dsimp only
      rw [hincEv] at hinc
      obtain ⟨envI, hagI, hincStar⟩ := hinc
      have hagSI : AgreeBelow (freshBase F) fr.env envI := fun r hr => (hagS r hr).trans (hagI r hr)
      have hxI : envI[x]? = some xVal := by rw [← hagSI x hxLt, hx]
      have hdec := inl_sharedDecBlocks_exec hr (F' := inlineFunc l F) (fn := fr.fn)
        (decLbl := decLbl) (doneLbl := allocLbl) (tmp := tmp + 1 + 3 * live.length)
        (bound := freshBase F) (x := x) (xVal := xVal) (ctx := ctx) (doneSlot := none)
        (doneBlk := {
          body := #[.assign aBase (.load .w64 .zero (ctxAddr (Int.ofNat (8 * cls))))],
          term := .br .eq .w64 (.v aBase) (.imm 0) ⟨allocLbl + 2, []⟩ ⟨allocLbl + 1, []⟩, cold := true })
        (env0 := envI) (mem := mem₁) (rest := rest)
        hF' hxLt (by have := hcp.tmpGe; omega) hxI (by dsimp only [decLbl, allocLbl, Lir.Label]; omega)
        hshape.b0 rfl hdecBlks
      have hincStar' : Sem.Star (Lir.semStep inl) s₂ 0
          { mem := mem₁, ctx, stack := { fn := fr.fn, label := decLbl, pos := 0, env := envI } :: rest } := by
        simpa [decLbl, sharedLbl, Nat.add_assoc] using hstarS.trans hincStar
      cases hdev : evalDecSite xVal mem₁ with
      | stuck =>
        dsimp only
        rw [hdev] at hdec
        exact .free hs₂ (by simpa using star_reaches hincStar' hdec)
      | ok mem_dec =>
        dsimp only
        rw [hdev] at hdec
        obtain ⟨envD, hdecStar, hagD⟩ := hdec
        exact ⟨envD, s₂, hs₂, hincStar'.trans hdecStar, fun r hr => (hagSI r hr).trans (hagD r hr)⟩
      | free =>
        dsimp only
        rw [hdev] at hdec
        obtain ⟨env1, hag1, hdecStar⟩ := hdec
        have hfrD : ({ fn := fr.fn, label := decLbl + 2, pos := 1, env := env1, dsts := [] } : Lir.Frame) =
            { fr with label := decLbl + 2, pos := 1, env := env1, dsts := [] } := by cases fr; rfl
        exact ⟨env1, s₂, hs₂, by simpa [hfrD] using hincStar'.trans hdecStar,
          fun r hr => (hagSI r hr).trans (hag1 r hr)⟩

/-- Helper: fused dynamic `reset` + `reuse` inlined execution when `live.length > maxInlineResetLive`
(hot unique path OR cold `resetWrapper` fallback followed by branch into `pubLbl` or inline alloc). -/
theorem inl_fusedResetReuse_fallback_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 rest2 : List Lir.Stmt} {s1 s2 : Lir.Stmt}
    {slot x dst : Lir.VReg} {idx1 : Nat} {lay1 : Rt.Rc.CellLayout} {mask : UInt64}
    {idx2 : Nat} {lay2 : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    {xVal : Lir.Word}
    (hltFn : fr.fn < l.sourceCount) (hF : raw.funcs[fr.fn]? = some F)
    (hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = s1 :: s2 :: rest2)
    (hp : classifyPair l s1 s2 = some (.fusedResetReuse slot x dst idx1 lay1 mask idx2 lay2 cls args))
    (hposB1 : rawPos < B.body.size) (hgetB1 : B.body[rawPos] = s1)
    (hposB2 : rawPos + 1 < B.body.size) (hgetB2 : B.body[rawPos + 1] = s2)
    (hx : fr.env[x]? = some xVal) (hxLt : (x : Nat) < freshBase F)
    (hargsLt : argsMax args 0 < freshBase F)
    (hgt : ¬ (liveFields lay1.nobj mask).length ≤ maxInlineResetLive) :
    let inl := inlineProgram l raw
    let hdr2 := Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1
    ChunkPos l F b B (rawPos + 2) (fr.label + 9) (1 + args.length) ∧
    (∃ pubBlk postJ, InlineAllocShape (inlineFunc l F) (fr.label + 3) (fr.label + 9) (tmp + 2) slot dst (.v (tmp + 1)) lay2 cls args pubBlk postJ) ∧
    (inlineFunc l F).blocks[fr.label + 2]? =
      some {
        body := #[.call [tmp + 1] (l.resetWrapper idx1) [.v x, .imm mask]],
        term := .br .tnz .w64 (.v (tmp + 1)) (.imm 1) ⟨fr.label + 3, []⟩ ⟨fr.label + 9, [.v (tmp + 1), .v (tmp + 1)]⟩,
        cold := true } ∧
    (∀ {vals mem'}, evalUniqueCheck xVal mem = .unique →
      Lir.evalArgs fr.env args = some vals →
      writeReuseMem mem xVal hdr2 vals = some mem' →
      ∃ env' s',
        AgreeBelow (freshBase F) ((fr.env.insert slot xVal).insert dst xVal) env' ∧
        Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s' false ∧
        Sem.Star (Lir.semStep inl) s' 0
          { mem := mem', ctx, stack := { fr with label := fr.label + 9, pos := 1 + args.length, env := env', dsts := [] } :: rest }) ∧
    (evalUniqueCheck xVal mem = .shared →
      ∃ callee env' s',
        Lir.enter raw (l.resetWrapper idx1) [xVal, mask] = some callee ∧
        AgreeBelow (freshBase F) fr.env env' ∧
        Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s' false ∧
        Sem.Star (Lir.semStep inl) s' 1
          { mem, ctx, stack := callee :: { fr with label := fr.label + 2, pos := 1, env := env', dsts := [tmp + 1] } :: rest }) := by
  intro inl hdr2
  obtain ⟨hc1, _, _, _, _, _, _, hnd, hns⟩ := classifyPair_eq_fusedResetReuse hp
  obtain ⟨c1, hc1', _, hlay1, hcls1, _, _⟩ := classify_eq_reset hc1
  let pubInit : List Lir.Stmt := Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr2) :: mkFieldStores dst 0 args
  have hpubLen : pubInit.length = 1 + args.length := by
    simp only [pubInit, List.length_cons, mkFieldStores_length]; omega
  have hexp : expandStmts l (newLabel l F) B.term B.cold rest0 fr.label tmp params acc =
      let r := stepPair l B.cold (.fusedResetReuse slot x dst idx1 lay1 mask idx2 lay2 cls args) fr.label tmp params acc
      let t := expandStmts l (newLabel l F) B.term B.cold rest2 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
      (r.1 ++ t.1, t.2) := by
    rw [hrest, expandStmts_cons_pair _ _ _ _ _ _ _ _ _ _ _ hp]
  have cpNext : ChunkAt l F b B (rawPos + 2) (fr.label + 9) (1 + args.length) (tmp + 7) [slot, dst] pubInit.reverse rest2 := {
    bLookup := hcp.bLookup
    tmpGe := by have := hcp.tmpGe; omega
    split := by
      have htake1 : B.body.toList.take (rawPos + 1) = B.body.toList.take rawPos ++ [s1] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB1, hgetB1]; simp
      have htake2 : B.body.toList.take (rawPos + 2) = B.body.toList.take (rawPos + 1) ++ [s2] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB2, hgetB2]; simp
      rw [htake2, htake1, List.append_assoc, List.append_assoc]; simpa [hrest] using hcp.split
    posLe := by omega
    blocksMatch := fun k blk hk => by
      have h := hcp.blocksMatch (9 + k) blk (by
        rw [hexp]; dsimp only [stepPair]; simp only [hgt, ↓reduceIte]
        rw [Nat.add_comm 9 k]; exact hk)
      simpa [Nat.add_assoc] using h
    inPosEq := by rw [List.length_reverse, hpubLen]
    endLbl := by
      have := hcp.endLbl
      rw [hrest, stmtsExtra_cons_pair _ _ _ _ hp] at this
      simp only [pairExtra, hgt, ↓reduceIte] at this
      dsimp only [Lir.Label] at this ⊢; omega }
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  have hb0 : (inlineFunc l F).blocks[fr.label]? = some ({
      params, body := acc.reverse.toArray,
      term := .br .tnz .w64 (.v x) (.imm 1) ⟨fr.label + 2, []⟩ ⟨fr.label + 1, []⟩, cold := B.cold } : Lir.Block) := by
    simpa using hcp.blocksMatch 0 _ (by rw [hexp]; dsimp only [stepPair]; simp only [hgt, ↓reduceIte]; rfl)
  have hb1 : (inlineFunc l F).blocks[fr.label + 1]? = some ({
      body := #[.assign tmp (.load .w32 .zero (cellAddr x 4))],
      term := .br .eq .w32 (.v tmp) (.imm 0) ⟨fr.label + 9, [.v x, .v x]⟩ ⟨fr.label + 2, []⟩, cold := B.cold } : Lir.Block) :=
    hcp.blocksMatch 1 _ (by rw [hexp]; dsimp only [stepPair]; simp only [hgt, ↓reduceIte]; rfl)
  have hb2 : (inlineFunc l F).blocks[fr.label + 2]? = some ({
      body := #[.call [tmp + 1] (l.resetWrapper idx1) [.v x, .imm mask]],
      term := .br .tnz .w64 (.v (tmp + 1)) (.imm 1) ⟨fr.label + 3, []⟩ ⟨fr.label + 9, [.v (tmp + 1), .v (tmp + 1)]⟩,
      cold := true } : Lir.Block) :=
    hcp.blocksMatch 2 _ (by rw [hexp]; dsimp only [stepPair]; simp only [hgt, ↓reduceIte]; rfl)
  have hb3 : (inlineFunc l F).blocks[fr.label + 3]? = some ({
      body := #[.assign (tmp + 2) (.load .w64 .zero (ctxAddr (Int.ofNat (8 * cls))))],
      term := .br .eq .w64 (.v (tmp + 2)) (.imm 0) ⟨fr.label + 5, []⟩ ⟨fr.label + 4, []⟩, cold := true } : Lir.Block) :=
    hcp.blocksMatch 3 _ (by rw [hexp]; dsimp only [stepPair]; simp only [hgt, ↓reduceIte]; rfl)
  have hb4 : (inlineFunc l F).blocks[fr.label + 4]? = some ({
      body := #[.assign (tmp + 3) (.load .w64 .zero (cellAddr (tmp + 2))),
        .store .w64 (ctxAddr (Int.ofNat (8 * cls))) (.v (tmp + 3))],
      term := .jump ⟨fr.label + 9, [.v (tmp + 1), .v (tmp + 2)]⟩, cold := true } : Lir.Block) :=
    hcp.blocksMatch 4 _ (by rw [hexp]; dsimp only [stepPair]; simp only [hgt, ↓reduceIte]; rfl)
  have hb5 : (inlineFunc l F).blocks[fr.label + 5]? = some ({
      body := #[.assign (tmp + 4) (.load .w64 .zero (ctxAddr Rt.bumpOff)),
        .assign (tmp + 5) (.load .w64 .zero (ctxAddr Rt.limitOff))],
      term := .brOvf .addC (tmp + 6) (.v (tmp + 4)) (.imm (UInt64.ofNat (Rt.Rc.classBytes cls)))
        ⟨fr.label + 6, []⟩ ⟨fr.label + 8, []⟩, cold := true } : Lir.Block) :=
    hcp.blocksMatch 5 _ (by rw [hexp]; dsimp only [stepPair]; simp only [hgt, ↓reduceIte]; rfl)
  have hb6 : (inlineFunc l F).blocks[fr.label + 6]? = some ({
      body := #[],
      term := .br .ule .w64 (.v (tmp + 6)) (.v (tmp + 5)) ⟨fr.label + 7, []⟩ ⟨fr.label + 8, []⟩, cold := true } : Lir.Block) :=
    hcp.blocksMatch 6 _ (by rw [hexp]; dsimp only [stepPair]; simp only [hgt, ↓reduceIte]; rfl)
  have hb7 : (inlineFunc l F).blocks[fr.label + 7]? = some ({
      body := #[.store .w64 (ctxAddr Rt.bumpOff) (.v (tmp + 6))],
      term := .jump ⟨fr.label + 9, [.v (tmp + 1), .v (tmp + 4)]⟩, cold := true } : Lir.Block) :=
    hcp.blocksMatch 7 _ (by rw [hexp]; dsimp only [stepPair]; simp only [hgt, ↓reduceIte]; rfl)
  have hb8 : (inlineFunc l F).blocks[fr.label + 8]? = some ({ body := #[], term := .fail .heap, cold := true } : Lir.Block) :=
    hcp.blocksMatch 8 _ (by rw [hexp]; dsimp only [stepPair]; simp only [hgt, ↓reduceIte]; rfl)
  obtain ⟨pubBlk, postJ, hpub0, hpubP, hpubBody0, _, _⟩ :=
    ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold rest2
      (fr.label + 9) (tmp + 7) [slot, dst] pubInit.reverse
  have hpub : (inlineFunc l F).blocks[fr.label + 9]? = some pubBlk := by
    simpa using cpNext.blocksMatch 0 pubBlk hpub0
  have hpubBody : pubBlk.body.toList = [.store .w64 (cellAddr dst) (.imm hdr2)] ++ mkFieldStores dst 0 args ++ postJ := by
    simpa [pubInit, List.reverse_reverse, List.cons_append] using hpubBody0
  have hshape : InlineAllocShape (inlineFunc l F) (fr.label + 3) (fr.label + 9) (tmp + 2) slot dst (.v (tmp + 1)) lay2 cls args pubBlk postJ := {
    pubGt := by dsimp only [Lir.Label]; omega
    pubLookup := hpub
    pubParams := hpubP
    pubBody := hpubBody
    b0 := hb3
    b1 := by simpa [Nat.add_assoc] using hb4
    b2 := by simpa [Nat.add_assoc] using hb5
    b3 := by simpa [Nat.add_assoc] using hb6
    b4 := by simpa [Nat.add_assoc] using hb7
    b5 := by simpa [Nat.add_assoc] using hb8 }
  have hpos0 : fr.pos = acc.reverse.toArray.size := by simp [hcp.inPosEq]
  refine ⟨⟨_, _, _, _, cpNext⟩, ⟨pubBlk, postJ, hshape⟩, hb2, ?_, ?_⟩
  · intro vals mem' huniq hargs hwr
    unfold evalUniqueCheck at huniq
    have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by
      cases ht : Lir.Cond.holds .tnz .w64 xVal 1
      · rfl
      · simp [ht] at huniq
    simp only [htagF, Bool.false_eq_true, ↓reduceIte] at huniq
    cases hlc : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none => simp [hlc] at huniq
    | some cnt =>
      simp only [hlc] at huniq
      have hz : (X86.Width.w32.truncate cnt).toNat = 0 := by
        by_cases h0 : (X86.Width.w32.truncate cnt).toNat = 0
        · exact h0
        · simp [h0] at huniq
      have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = true := by rw [w32_eq_zero]; simp [hz]
      have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term hF' hb0 hpos0]
        simp [Lir.Arg.eval, hx, htagF, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams]
      let env1 := fr.env.insert tmp cnt
      have hx1 : env1[x]? = some xVal := by
        rw [Lir.env_insert_ne _ _ (by dsimp only [Lir.VReg] at hxLt ⊢; have := hcp.tmpGe; omega), hx]
      have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fr with label := fr.label + 1, pos := 0 }) (ρ' := env1) (mem' := mem)
          hF' hb1 (by simp) rfl rfl
          (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell fr.env ctx x xVal 4 hx, hlc, env1])
      let env2 := (env1.insert slot xVal).insert dst xVal
      have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 9, pos := 0, env := env2 } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fr with label := fr.label + 1, pos := 1, env := env1 }) hF' hb1 rfl]
        have hfwd : ¬ (fr.label + 9 ≤ fr.label + 1) := by dsimp only [Lir.Label]; omega
        simp [Lir.Arg.eval, env1, hx1, heq0, Lir.takeEdge, Lir.evalArgs, hpub, hpubP, Lir.bindParams, hfwd, env2]
      have hargs2 : Lir.evalArgs env2 args = some vals := by
        simp only [env2]
        rw [evalArgs_insert_not_mem (argsContainVReg_false hnd),
          evalArgs_insert_not_mem (argsContainVReg_false hns),
          ← (AgreeBelow.refl.insert_ge hcp.tmpGe cnt).evalArgs_eq hargsLt, hargs]
      have hpubBody' : pubBlk.body.toList =
          [] ++ (.store .w64 (cellAddr dst 0) (.imm hdr2) :: mkFieldStores dst 0 args) ++ postJ := by
        simpa [cellAddr] using hpubBody
      have hwrStar := exec_writeReuse (p := inl) (F := inlineFunc l F) (B := pubBlk)
        (fn := fr.fn) (lbl := fr.label + 9) (base := dst) (addr := xVal) (hdr := hdr2)
        (ctx := ctx) (rest := rest) (env := env2) hF' hpub (by simp [env2]) hpubBody' hargs2 (mem := mem)
      rw [hwr] at hwrStar
      have hfrPub : ({ fn := fr.fn, label := fr.label + 9, pos := 0, env := env2, dsts := [] } : Lir.Frame) =
          { fr with label := fr.label + 9, pos := 0, env := env2 } := by
        cases fr; dsimp only at hdsts; subst hdsts; rfl
      refine ⟨env2, _, ((AgreeBelow.refl.insert_ge hcp.tmpGe cnt).insert_same slot xVal).insert_same dst xVal,
        s1, .free s2 (.free s3 (by simpa [hfrPub] using hwrStar))⟩
  · intro hshared
    have hwrapRaw : raw.funcs[l.resetWrapper idx1]? =
        some (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay1 cls) := by
      rw [hlay1]; exact hr.resetWrap idx1 c1 cls hc1' (by rwa [← hlay1])
    have hwrapInl : inl.funcs[l.resetWrapper idx1]? =
        some (mkResetWrapper l.isUniqueProc l.incProc l.decProc lay1 cls) := by
      rw [hlay1]; exact inlineProgram_resetWrap l raw hr hc1' (by rwa [← hlay1])
    let eW : Lir.Env := (({} : Lir.Env).insert 0 xVal).insert 1 mask
    let callee : Lir.Frame := { fn := l.resetWrapper idx1, label := 0, pos := 0, env := eW }
    have hentRaw : Lir.enter raw (l.resetWrapper idx1) [xVal, mask] = some callee := by
      simp [Lir.enter, hwrapRaw, mkResetWrapper, Lir.bindParams, eW, callee]
    have hentInl : Lir.enter inl (l.resetWrapper idx1) [xVal, mask] = some callee := by
      simp [Lir.enter, hwrapInl, mkResetWrapper, Lir.bindParams, eW, callee]
    unfold evalUniqueCheck at hshared
    by_cases htag : Lir.Cond.holds .tnz .w64 xVal 1 = true
    · have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0 } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term hF' hb0 hpos0]
        simp [Lir.Arg.eval, hx, htag, Lir.takeEdge, Lir.evalArgs, hb2, Lir.bindParams]
      have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0 } :: rest } =
          .next { mem, ctx, stack := callee :: { fr with label := fr.label + 2, pos := 1, dsts := [tmp + 1] } :: rest } true := by
        apply Lir.semStep_next.mpr
        exact Lir.step_call (fr := { fr with label := fr.label + 2, pos := 0 }) hF' hb2 (by simp) rfl
          (by simp [Lir.evalArgs, Lir.Arg.eval, hx]) hentInl
      exact ⟨callee, fr.env, _, hentRaw, AgreeBelow.refl, s1, .charge s2 (.refl _)⟩
    · have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by simpa using htag
      simp only [htagF, Bool.false_eq_true, ↓reduceIte] at hshared
      cases hlc : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
      | none => simp [hlc] at hshared
      | some cnt =>
        simp only [hlc] at hshared
        have hnz : (X86.Width.w32.truncate cnt).toNat ≠ 0 := by intro hz; simp [hz] at hshared
        have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = false := by rw [w32_eq_zero]; simp [hnz]
        have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
            .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term hF' hb0 hpos0]
          simp [Lir.Arg.eval, hx, htagF, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams]
        let env1 := fr.env.insert tmp cnt
        have hx1 : env1[x]? = some xVal := by
          rw [Lir.env_insert_ne _ _ (by dsimp only [Lir.VReg] at hxLt ⊢; have := hcp.tmpGe; omega), hx]
        have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } =
            .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fr with label := fr.label + 1, pos := 0 }) (ρ' := env1) (mem' := mem)
            hF' hb1 (by simp) rfl rfl
            (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell fr.env ctx x xVal 4 hx, hlc, env1])
        have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fr with label := fr.label + 1, pos := 1, env := env1 }) hF' hb1 rfl]
          simp [Lir.Arg.eval, env1, heq0, Lir.takeEdge, Lir.evalArgs, hb2, Lir.bindParams]
        have s4 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0, env := env1 } :: rest } =
            .next { mem, ctx, stack := callee :: { fr with label := fr.label + 2, pos := 1, env := env1, dsts := [tmp + 1] } :: rest } true := by
          apply Lir.semStep_next.mpr
          exact Lir.step_call (fr := { fr with label := fr.label + 2, pos := 0, env := env1 }) hF' hb2 (by simp) rfl
            (by simp [Lir.evalArgs, Lir.Arg.eval, hx1]) hentInl
        exact ⟨callee, env1, _, hentRaw, AgreeBelow.refl.insert_ge hcp.tmpGe cnt, s1,
          .free s2 (.free s3 (.charge s4 (.refl _)))⟩

/-- Execute the join block of `fusedResetUReuseU1`: header+field stores + `slot := x`, `dst := x`. -/
theorem exec_fusedResetU1_join {p : Lir.Program} {F' : Lir.Func} {joinBlk : Lir.Block}
    {fn : Lir.FunId} {joinLbl : Lir.Label} {slot x dst : Lir.VReg}
    {lay2 : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg} {postJ : List Lir.Stmt}
    {xVal ctx : Lir.Word} {vals : List Lir.Word} {env : Lir.Env} {mem mem' : X86.Memory}
    {rest : List Lir.Frame}
    (hF' : p.funcs[fn]? = some F') (hjb : F'.blocks[joinLbl]? = some joinBlk)
    (hsx : slot ≠ x) (hx : env[x]? = some xVal)
    (hargs : Lir.evalArgs env args = some vals)
    (hjbBody : joinBlk.body.toList =
      (.store .w64 (cellAddr x 0) (.imm (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1)) ::
        mkFieldStores x 0 args) ++ [.assign slot (.arg (.v x)), .assign dst (.arg (.v x))] ++ postJ)
    (hwr : writeReuseMem mem xVal (Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1) vals = some mem') :
    Sem.Star (Lir.semStep p)
      { mem, ctx, stack := { fn, label := joinLbl, pos := 0, env, dsts := [] } :: rest } 0
      { mem := mem', ctx, stack := { fn, label := joinLbl, pos := 3 + args.length, env := (env.insert slot xVal).insert dst xVal, dsts := [] } :: rest } := by
  let hdr2 := Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1
  have hbodySplit : joinBlk.body.toList = [] ++
      (.store .w64 (cellAddr x 0) (.imm hdr2) :: mkFieldStores x 0 args) ++
      ([.assign slot (.arg (.v x)), .assign dst (.arg (.v x))] ++ postJ) := by
    simpa [List.append_assoc] using hjbBody
  have hwrStar := exec_writeReuse (p := p) (F := F') (B := joinBlk) (fn := fn) (lbl := joinLbl)
    (base := x) (addr := xVal) (hdr := hdr2) (ctx := ctx) (rest := rest)
    hF' hjb hx hbodySplit hargs (mem := mem)
  rw [hwr] at hwrStar
  have hpos1 : 1 + args.length < joinBlk.body.size := by
    have := congrArg List.length hbodySplit
    simp only [Array.length_toList, List.length_append, List.length_cons, mkFieldStores_length] at this
    omega
  have hpos2 : 2 + args.length < joinBlk.body.size := by
    have := congrArg List.length hbodySplit
    simp only [Array.length_toList, List.length_append, List.length_cons, mkFieldStores_length] at this
    omega
  have hget1 : joinBlk.body[1 + args.length] = .assign slot (.arg (.v x)) := by
    have h1 : joinBlk.body.toList[1 + args.length]? = some (.assign slot (.arg (.v x))) := by
      rw [hbodySplit]
      have hl : ((.store .w64 (cellAddr x 0) (.imm hdr2) :: mkFieldStores x 0 args)).length = 1 + args.length := by
        simp [mkFieldStores_length]; omega
      simp only [List.nil_append]
      rw [List.getElem?_append_right (by omega), hl, Nat.sub_self]; rfl
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hpos1, Option.some.injEq] at h1
    exact h1
  have hget2 : joinBlk.body[2 + args.length] = .assign dst (.arg (.v x)) := by
    have h1 : joinBlk.body.toList[2 + args.length]? = some (.assign dst (.arg (.v x))) := by
      rw [hbodySplit]
      have hl : ((.store .w64 (cellAddr x 0) (.imm hdr2) :: mkFieldStores x 0 args)).length = 1 + args.length := by
        simp [mkFieldStores_length]; omega
      simp only [List.nil_append]
      rw [List.getElem?_append_right (by omega), hl]
      have hsub : 2 + args.length - (1 + args.length) = 1 := by omega
      rw [hsub]; rfl
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hpos2, Option.some.injEq] at h1
    exact h1
  let env1 := env.insert slot xVal
  have hx1 : env1[x]? = some xVal := by rw [Lir.env_insert_ne _ _ hsx, hx]
  have sAsn1 : Lir.semStep p
      { mem := mem', ctx, stack := { fn, label := joinLbl, pos := 1 + args.length, env, dsts := [] } :: rest } =
      .next { mem := mem', ctx, stack := { fn, label := joinLbl, pos := 2 + args.length, env := env1, dsts := [] } :: rest } false := by
    apply Lir.semStep_next.mpr
    have h1 := Lir.step_stmt (fr := { fn, label := joinLbl, pos := 1 + args.length, env, dsts := [] })
      (mem := mem') (ctx := ctx) (rest := rest) (ρ' := env1) (mem' := mem')
      hF' hjb hpos1 hget1 rfl (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, hx, env1])
    have hidx : 1 + args.length + 1 = 2 + args.length := by omega
    simpa [hidx] using h1
  have sAsn2 : Lir.semStep p
      { mem := mem', ctx, stack := { fn, label := joinLbl, pos := 2 + args.length, env := env1, dsts := [] } :: rest } =
      .next { mem := mem', ctx, stack := { fn, label := joinLbl, pos := 3 + args.length, env := env1.insert dst xVal, dsts := [] } :: rest } false := by
    apply Lir.semStep_next.mpr
    have h1 := Lir.step_stmt (fr := { fn, label := joinLbl, pos := 2 + args.length, env := env1, dsts := [] })
      (mem := mem') (ctx := ctx) (rest := rest) (ρ' := env1.insert dst xVal) (mem' := mem')
      hF' hjb hpos2 hget2 rfl (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, hx1, env1])
    have hidx : 2 + args.length + 1 = 3 + args.length := by omega
    simpa [hidx] using h1
  have hwrStar' : Sem.Star (Lir.semStep p)
      { mem, ctx, stack := { fn, label := joinLbl, pos := 0, env, dsts := [] } :: rest } 0
      { mem := mem', ctx, stack := { fn, label := joinLbl, pos := 1 + args.length, env, dsts := [] } :: rest } := by
    simpa using hwrStar
  exact hwrStar'.trans (.free sAsn1 (.free sAsn2 (.refl _)))

/-- Helper: fused static `@unique` 1-dead-field `resetU` + `reuseU` inlined execution
(hot immediate dead field skips shell+dec; cold pointer dead field writes shell and calls `decProc`). -/
theorem inl_fusedResetUReuseU1_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 rest2 : List Lir.Stmt} {s1 s2 : Lir.Stmt}
    {slot x dst : Lir.VReg} {lay1 : Rt.Rc.CellLayout} {mask : UInt64} {deadIdx : Nat}
    {lay2 : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg}
    {xVal deadVal : Lir.Word}
    (hltFn : fr.fn < l.sourceCount) (hF : raw.funcs[fr.fn]? = some F)
    (hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = s1 :: s2 :: rest2)
    (hp : classifyPair l s1 s2 = some (.fusedResetUReuseU1 slot x dst lay1 mask deadIdx lay2 cls args))
    (hposB1 : rawPos < B.body.size) (hgetB1 : B.body[rawPos] = s1)
    (hposB2 : rawPos + 1 < B.body.size) (hgetB2 : B.body[rawPos + 1] = s2)
    (hx : fr.env[x]? = some xVal) (hxLt : (x : Nat) < freshBase F)
    (hargsLt : argsMax args 0 < freshBase F)
    (hload : Lir.loadWord mem .w64 .zero (xVal + Lir.dispWord (Int.ofNat (8 * (deadIdx + 1)))) = some deadVal) :
    let inl := inlineProgram l raw
    let hdr1 := Rt.Rc.dynamicHeader lay1.nobj cls lay1.tag 1
    let hdr2 := Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1
    let pFr0 : Lir.Frame := { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 deadVal }
    ChunkPos l F b B (rawPos + 2) (fr.label + 2) (3 + args.length) ∧
    (inlineFunc l F).blocks[fr.label + 1]? =
      some { body := (mkShellStores x hdr1 lay1.nobj ++ [Lir.Stmt.call [] l.decProc [.v tmp]]).toArray,
             term := .jump ⟨fr.label + 2, []⟩, cold := true } ∧
    (∃ jb postJ, (inlineFunc l F).blocks[fr.label + 2]? = some jb ∧ jb.params = [] ∧
      jb.body.toList = (.store .w64 (cellAddr x 0) (.imm hdr2) :: mkFieldStores x 0 args) ++
        [.assign slot (.arg (.v x)), .assign dst (.arg (.v x))] ++ postJ) ∧
    (∀ {vals mem'}, Lir.Cond.holds .tnz .w64 deadVal 1 = true →
      Lir.evalArgs fr.env args = some vals →
      writeReuseMem mem xVal hdr2 vals = some mem' →
      ∃ env' s',
        AgreeBelow (freshBase F) ((fr.env.insert slot xVal).insert dst xVal) env' ∧
        Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s' false ∧
        Sem.Star (Lir.semStep inl) s' 0
          { mem := mem', ctx, stack := { fr with label := fr.label + 2, pos := 3 + args.length, env := env', dsts := [] } :: rest }) ∧
    (∀ {mem_sh}, Lir.Cond.holds .tnz .w64 deadVal 1 = false →
      writeShellMem mem xVal hdr1 lay1.nobj = some mem_sh →
      ∃ env1 s',
        AgreeBelow (freshBase F) fr.env env1 ∧
        Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s' false ∧
        Sem.Star (Lir.semStep inl) s' 1
          { mem := mem_sh, ctx, stack := pFr0 ::
            { fr with label := fr.label + 1, pos := (1 + lay1.nobj) + 1, env := env1, dsts := [] } :: rest }) := by
  intro inl hdr1 hdr2 pFr0
  obtain ⟨_, _, _, _, _, _, _, hsx, _, _, _⟩ := classifyPair_eq_fusedResetUReuseU1 hp
  let fused : List Lir.Stmt :=
    .store .w64 (cellAddr x 0) (.imm hdr2) :: mkFieldStores x 0 args ++
      [.assign slot (.arg (.v x)), .assign dst (.arg (.v x))]
  have hfLen : fused.length = 3 + args.length := by simp [fused, mkFieldStores_length]; omega
  have hexp : expandStmts l (newLabel l F) B.term B.cold rest0 fr.label tmp params acc =
      let r := stepPair l B.cold (.fusedResetUReuseU1 slot x dst lay1 mask deadIdx lay2 cls args) fr.label tmp params acc
      let t := expandStmts l (newLabel l F) B.term B.cold rest2 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
      (r.1 ++ t.1, t.2) := by
    rw [hrest, expandStmts_cons_pair _ _ _ _ _ _ _ _ _ _ _ hp]
  have cpNext : ChunkAt l F b B (rawPos + 2) (fr.label + 2) (3 + args.length) (tmp + 1) [] fused.reverse rest2 := {
    bLookup := hcp.bLookup
    tmpGe := by have := hcp.tmpGe; omega
    split := by
      have htake1 : B.body.toList.take (rawPos + 1) = B.body.toList.take rawPos ++ [s1] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB1, hgetB1]; simp
      have htake2 : B.body.toList.take (rawPos + 2) = B.body.toList.take (rawPos + 1) ++ [s2] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB2, hgetB2]; simp
      rw [htake2, htake1, List.append_assoc, List.append_assoc]; simpa [hrest] using hcp.split
    posLe := by omega
    blocksMatch := fun k blk hk => by
      have h := hcp.blocksMatch (2 + k) blk (by
        rw [hexp]; dsimp only [stepPair]; rw [Nat.add_comm 2 k]; exact hk)
      simpa [Nat.add_assoc] using h
    inPosEq := by rw [List.length_reverse, hfLen]
    endLbl := by
      have := hcp.endLbl
      rw [hrest, stmtsExtra_cons_pair _ _ _ _ hp] at this
      simp only [pairExtra] at this
      dsimp only [Lir.Label] at this ⊢; omega }
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  let loadStmt : Lir.Stmt := .assign tmp (.load .w64 .zero (cellAddr x (Int.ofNat (8 * (deadIdx + 1)))))
  have hb0 : (inlineFunc l F).blocks[fr.label]? = some ({
      params, body := (loadStmt :: acc).reverse.toArray,
      term := .br .tnz .w64 (.v tmp) (.imm 1) ⟨fr.label + 2, []⟩ ⟨fr.label + 1, []⟩, cold := B.cold } : Lir.Block) := by
    have h0 := hcp.blocksMatch 0 _ (by rw [hexp]; rfl)
    rw [Nat.add_zero] at h0
    exact h0
  have hb1 : (inlineFunc l F).blocks[fr.label + 1]? = some ({
      body := (mkShellStores x hdr1 lay1.nobj ++ [Lir.Stmt.call [] l.decProc [.v tmp]]).toArray,
      term := .jump ⟨fr.label + 2, []⟩, cold := true } : Lir.Block) :=
    hcp.blocksMatch 1 _ (by rw [hexp]; rfl)
  obtain ⟨jb, postJ, hj0, hjp, hjbBody0, _, _⟩ :=
    ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold rest2
      (fr.label + 2) (tmp + 1) [] fused.reverse
  have hb2 : (inlineFunc l F).blocks[fr.label + 2]? = some jb := by
    simpa using cpNext.blocksMatch 0 jb hj0
  have hjbBody : jb.body.toList = (.store .w64 (cellAddr x 0) (.imm hdr2) :: mkFieldStores x 0 args) ++
      [.assign slot (.arg (.v x)), .assign dst (.arg (.v x))] ++ postJ := by
    simpa [fused, List.reverse_reverse, List.append_assoc] using hjbBody0
  have hpos0Lt : fr.pos < ((loadStmt :: acc).reverse.toArray).size := by
    simp [hcp.inPosEq]
  have hget0 : ((loadStmt :: acc).reverse.toArray)[fr.pos]'hpos0Lt = loadStmt := by
    have h1 : (loadStmt :: acc).reverse[fr.pos]? = some loadStmt := by
      rw [List.reverse_cons, List.getElem?_append_right (by simp [hcp.inPosEq])]
      simp [hcp.inPosEq]
    have h2 : ((loadStmt :: acc).reverse.toArray)[fr.pos]? = some loadStmt := by
      rw [List.getElem?_toArray]; exact h1
    rw [Array.getElem?_eq_getElem hpos0Lt] at h2
    exact Option.some.inj h2
  let env1 := fr.env.insert tmp deadVal
  have hag1 : AgreeBelow (freshBase F) fr.env env1 := AgreeBelow.refl.insert_ge hcp.tmpGe deadVal
  have hx1 : env1[x]? = some xVal := by rw [← hag1 x hxLt, hx]
  have sLd : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := { fr with pos := fr.pos + 1, env := env1 } :: rest } false := by
    apply Lir.semStep_next.mpr
    exact Lir.step_stmt (fr := fr) (ρ' := env1) (mem' := mem)
      hF' hb0 hpos0Lt hget0 rfl
      (by simp only [loadStmt, cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
        addr_cell fr.env ctx x xVal _ hx, Option.bind_eq_bind, Option.bind_some, hload, env1])
  have hpos0End : fr.pos + 1 = ((loadStmt :: acc).reverse.toArray).size := by simp [hcp.inPosEq]
  refine ⟨⟨_, _, _, _, cpNext⟩, hb1, ⟨jb, postJ, hb2, hjp, hjbBody⟩, ?_, ?_⟩
  · intro vals mem' htag hargs hwr
    have sBr : Lir.semStep inl { mem, ctx, stack := { fr with pos := fr.pos + 1, env := env1 } :: rest } =
        .next { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0, env := env1 } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fr with pos := fr.pos + 1, env := env1 }) hF' hb0 hpos0End]
      have hfwd : ¬ (fr.label + 2 ≤ fr.label) := by dsimp only [Lir.Label]; omega
      simp [Lir.Arg.eval, env1, htag, Lir.takeEdge, Lir.evalArgs, hb2, hjp, Lir.bindParams, hfwd]
    have hargs1 : Lir.evalArgs env1 args = some vals := by
      rw [← hag1.evalArgs_eq hargsLt, hargs]
    have hjoin := exec_fusedResetU1_join (p := inl) (F' := inlineFunc l F) (joinBlk := jb)
      (fn := fr.fn) (joinLbl := fr.label + 2) (slot := slot) (x := x) (dst := dst)
      (lay2 := lay2) (cls := cls) (args := args) (postJ := postJ)
      (xVal := xVal) (ctx := ctx) (vals := vals) (env := env1) (mem := mem) (mem' := mem') (rest := rest)
      hF' hb2 hsx hx1 hargs1 hjbBody hwr
    have hfr2 : ({ fn := fr.fn, label := fr.label + 2, pos := 0, env := env1, dsts := [] } : Lir.Frame) =
        { fr with label := fr.label + 2, pos := 0, env := env1 } := by
      cases fr; dsimp only at hdsts; subst hdsts; rfl
    refine ⟨(env1.insert slot xVal).insert dst xVal, _, (hag1.insert_same slot xVal).insert_same dst xVal,
      sLd, .free sBr (by simpa [hfr2] using hjoin)⟩
  · intro mem_sh htagF hws
    have sBr : Lir.semStep inl { mem, ctx, stack := { fr with pos := fr.pos + 1, env := env1 } :: rest } =
        .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0, env := env1 } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fr with pos := fr.pos + 1, env := env1 }) hF' hb0 hpos0End]
      have hfwd : ¬ (fr.label + 1 ≤ fr.label) := by dsimp only [Lir.Label]; omega
      simp [Lir.Arg.eval, env1, htagF, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams, hfwd]
    let blk1 : Lir.Block :=
      { body := (mkShellStores x hdr1 lay1.nobj ++ [Lir.Stmt.call [] l.decProc [.v tmp]]).toArray,
        term := .jump ⟨fr.label + 2, []⟩, cold := true }
    have hbody1 : blk1.body.toList = [] ++ mkShellStores x hdr1 lay1.nobj ++ [Lir.Stmt.call [] l.decProc [.v tmp]] := by
      simp [blk1]
    have hsh := exec_mkShellStores (p := inl) (F := inlineFunc l F) (B := blk1)
      (fn := fr.fn) (lbl := fr.label + 1) (x := x) (xVal := xVal) (hdr := hdr1)
      (ctx := ctx) (rest := rest) (env := env1) hF' hb1 hx1 hbody1 (mem := mem)
    rw [hws] at hsh
    have hdecInl : inl.funcs[l.decProc]? = some Rt.Rc.Gen.dec := inlineProgram_decProc l raw hr
    have hposCall : 1 + lay1.nobj < blk1.body.size := by
      simp only [blk1, List.size_toArray, List.length_append, mkShellStores_length, List.length_cons,
        List.length_nil]
      omega
    have hgetCall : blk1.body[1 + lay1.nobj]'hposCall = .call [] l.decProc [.v tmp] := by
      have h1 : blk1.body.toList[1 + lay1.nobj]? = some (.call [] l.decProc [.v tmp]) := by
        simp only [blk1]
        rw [List.getElem?_append_right (by rw [mkShellStores_length]; exact Nat.le_refl _), mkShellStores_length, Nat.sub_self]; rfl
      simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hposCall, Option.some.injEq] at h1
      exact h1
    have sCall : Lir.semStep inl
        { mem := mem_sh, ctx, stack := { fn := fr.fn, label := fr.label + 1, pos := 1 + lay1.nobj, env := env1, dsts := [] } :: rest } =
        .next { mem := mem_sh, ctx, stack := pFr0 :: { fr with label := fr.label + 1, pos := (1 + lay1.nobj) + 1, env := env1, dsts := [] } :: rest } true := by
      apply Lir.semStep_next.mpr
      have h1 := Lir.step_call (p := inl) (F := inlineFunc l F) (B := blk1)
        (fr := { fn := fr.fn, label := fr.label + 1, pos := 1 + lay1.nobj, env := env1, dsts := [] })
        (mem := mem_sh) (ctx := ctx) (rest := rest)
        (rs := []) (g := l.decProc) (as := [.v tmp]) (vs := [deadVal]) (callee := pFr0)
        hF' hb1 hposCall hgetCall (by simp [Lir.evalArgs, Lir.Arg.eval, env1])
        (by simp [Lir.enter, hdecInl, Rt.Rc.Gen.dec, Lir.bindParams, pFr0])
      cases fr; exact h1
    have hfr1 : ({ fn := fr.fn, label := fr.label + 1, pos := 0, env := env1, dsts := [] } : Lir.Frame) =
        { fr with label := fr.label + 1, pos := 0, env := env1 } := by
      cases fr; dsimp only at hdsts; subst hdsts; rfl
    have hsh' : Sem.Star (Lir.semStep inl)
        { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0, env := env1 } :: rest } 0
        { mem := mem_sh, ctx, stack := { fn := fr.fn, label := fr.label + 1, pos := 1 + lay1.nobj, env := env1, dsts := [] } :: rest } := by
      simpa [hfr1] using hsh
    exact ⟨env1, _, hag1, sLd, .free sBr (hsh'.trans (.charge sCall (.refl _)))⟩

end IxCC.Cfg.Rc.Inline

