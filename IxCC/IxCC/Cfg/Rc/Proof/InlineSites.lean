import IxCC.Cfg.Rc.Proof.InlineLayout

/-! # Single-site operational equivalence for `Cfg.Rc.Inline`

Proves exact operational equivalence between the raw wrapper+procedure call and
the inlined fast-path block sequence for all three RC site kinds:
1. `inc` (`evalIncSite`, `raw_inc_exec`, `inl_inc_exec`)
2. `dec` (`evalDecSite`, `raw_dec_exec`, `inl_dec_exec`)
3. `alloc` (`evalAllocReserve`, `writeFieldsMem`, `raw_alloc_exec`, `inl_alloc_exec`)

Every proof works over arbitrary memory and register environments without any
heap invariant. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Inline

open IxCC.Cfg.Rc.Native

/-! ## Runtime layout contract on the raw Lir program -/

/-- Exact runtime function lookups in the un-inlined RC Lir program. -/
structure RuntimeFuncs (l : Layout) (p : Lir.Program) : Prop where
  incWrap : p.funcs[l.incWrapper]? = some (incrementWrapper l.incProc)
  decWrap : p.funcs[l.decWrapper]? = some (decrementWrapper l.decProc)
  incProc : p.funcs[l.incProc]? = some Rt.Rc.Procs.inc
  decProc : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec
  allocWrap : ∀ i c, l.ctors[i]? = some c →
    p.funcs[l.allocWrapper i]? = some (allocationWrapper (l.allocProc i) c.arity)
  allocProc : ∀ i c, l.ctors[i]? = some c →
    p.funcs[l.allocProc i]? = some (Rt.Rc.Gen.alloc (Rt.Rc.CellLayout.ofFields c.arity c.tag))
  sourceBound : l.sourceCount ≤ p.funcs.size

theorem inlineProgram_get_lt (l : Layout) (p : Lir.Program) {f : Lir.FunId} (hf : f < l.sourceCount) :
    (inlineProgram l p).funcs[f]? = (p.funcs[f]?).map (inlineFunc l) := by
  simp only [inlineProgram, Array.getElem?_mapIdx]
  cases h : p.funcs[f]? with
  | none => simp
  | some F => simp [hf]

theorem inlineProgram_get_ge (l : Layout) (p : Lir.Program) {f : Lir.FunId} (hf : l.sourceCount ≤ f) :
    (inlineProgram l p).funcs[f]? = p.funcs[f]? := by
  simp only [inlineProgram, Array.getElem?_mapIdx]
  cases h : p.funcs[f]? with
  | none => simp
  | some F => simp [Nat.not_lt.mpr hf]

theorem inlineProgram_decProc (l : Layout) (p : Lir.Program) (hr : RuntimeFuncs l p) :
    (inlineProgram l p).funcs[l.decProc]? = some Rt.Rc.Gen.dec := by
  rw [inlineProgram_get_ge l p (by simp [Layout.decProc, Layout.incProc]; omega)]
  exact hr.decProc

/-! ## Inversion lemmas for `classify` -/

theorem classify_eq_inc {l : Layout} {s : Lir.Stmt} {dst x : Lir.VReg}
    (h : classify l s = some (.inc dst x)) :
    ∃ wLit, s = .call [dst] l.incWrapper [.v x, .imm wLit] := by
  unfold classify at h
  cases s with
  | assign _ _ => cases h
  | limb _ _ _ => cases h
  | store _ _ _ => cases h
  | call rs f as =>
    cases rs with
    | nil => cases h
    | cons d rs' =>
      cases rs' with
      | cons _ _ => cases h
      | nil =>
        by_cases hf1 : (f == l.incWrapper) = true
        · simp only [hf1, ↓reduceIte] at h
          have hfEq : f = l.incWrapper := beq_iff_eq.mp hf1
          cases as with
          | nil => cases h
          | cons a1 as1 =>
            cases a1 with
            | imm _ => cases h
            | v x' =>
              cases as1 with
              | nil => cases h
              | cons a2 as2 =>
                cases a2 with
                | v _ => cases h
                | imm wLit =>
                  cases as2 with
                  | cons _ _ => cases h
                  | nil =>
                    simp only [Option.some.injEq, RcSite.inc.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact ⟨wLit, by rw [hfEq]⟩
        · simp only [hf1, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hf2 : (f == l.decWrapper) = true
          · simp only [hf2, ↓reduceIte] at h
            cases as with
            | cons a as' => cases a <;> cases as' <;> simp at h
            | nil => cases h
          · simp only [hf2, Bool.false_eq_true, ↓reduceIte] at h
            split at h
            · split at h
              · split at h
                · split at h <;> cases h
                · cases h
              · cases h
            · cases h

theorem classify_eq_dec {l : Layout} {s : Lir.Stmt} {dst x : Lir.VReg}
    (h : classify l s = some (.dec dst x)) :
    s = .call [dst] l.decWrapper [.v x] := by
  unfold classify at h
  cases s with
  | assign _ _ => cases h
  | limb _ _ _ => cases h
  | store _ _ _ => cases h
  | call rs f as =>
    cases rs with
    | nil => cases h
    | cons d rs' =>
      cases rs' with
      | cons _ _ => cases h
      | nil =>
        by_cases hf1 : (f == l.incWrapper) = true
        · simp only [hf1, ↓reduceIte] at h
          cases as with
          | cons a1 as1 =>
            cases a1 with
            | imm _ => cases h
            | v _ =>
              cases as1 with
              | cons a2 as2 => cases a2 <;> cases as2 <;> simp at h
              | nil => cases h
          | nil => cases h
        · simp only [hf1, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hf2 : (f == l.decWrapper) = true
          · simp only [hf2, ↓reduceIte] at h
            have hfEq : f = l.decWrapper := beq_iff_eq.mp hf2
            cases as with
            | nil => cases h
            | cons a1 as1 =>
              cases a1 with
              | imm _ => cases h
              | v x' =>
                cases as1 with
                | cons _ _ => cases h
                | nil =>
                  simp only [Option.some.injEq, RcSite.dec.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  rw [hfEq]
          · simp only [hf2, Bool.false_eq_true, ↓reduceIte] at h
            split at h
            · split at h
              · split at h
                · split at h <;> cases h
                · cases h
              · cases h
            · cases h

theorem classify_eq_alloc {l : Layout} {s : Lir.Stmt} {dst : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {as : List Lir.Arg}
    (h : classify l s = some (.alloc dst idx lay cls as)) :
    ∃ c, l.ctors[idx]? = some c ∧
      s = .call [dst] (l.allocWrapper idx) as ∧
      lay = Rt.Rc.CellLayout.ofFields c.arity c.tag ∧
      lay.cls? = some cls ∧
      as.length = c.arity ∧
      lay.ok = true ∧
      argsContainVReg dst as = false := by
  unfold classify at h
  cases s with
  | assign _ _ => cases h
  | limb _ _ _ => cases h
  | store _ _ _ => cases h
  | call rs f as' =>
    cases rs with
    | nil => cases h
    | cons d rs' =>
      cases rs' with
      | cons _ _ => cases h
      | nil =>
        by_cases hf1 : (f == l.incWrapper) = true
        · simp only [hf1, ↓reduceIte] at h
          cases as' with
          | cons a1 as1 =>
            cases a1 with
            | imm _ => cases h
            | v _ =>
              cases as1 with
              | cons a2 as2 => cases a2 <;> cases as2 <;> simp at h
              | nil => cases h
          | nil => cases h
        · simp only [hf1, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hf2 : (f == l.decWrapper) = true
          · simp only [hf2, ↓reduceIte] at h
            cases as' with
            | cons a as1 => cases a <;> cases as1 <;> simp at h
            | nil => cases h
          · simp only [hf2, Bool.false_eq_true, ↓reduceIte] at h
            split at h
            · rename_i hrange
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hrange
              cases hc : l.ctors[f - l.allocWrapper 0]? with
              | none => simp [hc] at h
              | some c =>
                simp only [hc] at h
                cases hcls : (Rt.Rc.CellLayout.ofFields c.arity c.tag).cls? with
                | none => simp [hcls] at h
                | some cls' =>
                  simp only [hcls] at h
                  split at h
                  · rename_i hcond
                    simp only [Option.some.injEq, RcSite.alloc.injEq] at h
                    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
                    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
                    have hfEq : (f : Nat) = l.allocWrapper (f - l.allocWrapper 0) := by
                      dsimp only [Lir.FunId, Layout.allocWrapper] at hrange ⊢; omega
                    exact ⟨c, hc, by rw [← hfEq], rfl, hcls, hcond.1.1, hcond.1.2, hcond.2⟩
                  · cases h
            · cases h

/-! ## 32-bit comparison arithmetic for inline `inc` and `dec` -/

theorem w32_truncate_lt (w : Lir.Word) : (X86.Width.w32.truncate w).toNat < 2 ^ 32 := by
  simp only [X86.Width.truncate, X86.Width.mask, UInt64.toNat_and]
  have h1 : (0xFFFFFFFF : Lir.Word).toNat = 2 ^ 32 - 1 := by decide
  rw [h1, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem w32_signedValue_lt_zero (w : Lir.Word) :
    Lir.Cond.holds .slt .w32 w 0 = decide (2 ^ 31 ≤ (X86.Width.w32.truncate w).toNat) := by
  have hlt := w32_truncate_lt w
  have h0 : X86.Width.w32.signedValue 0 = 0 := by decide
  simp only [Lir.Cond.holds]
  rw [h0]
  simp only [X86.Width.signedValue, X86.Width.bits]
  by_cases hge : (X86.Width.w32.truncate w).toNat < 2 ^ (32 - 1)
  · simp only [hge, ↓reduceIte, Int.ofNat_eq_natCast]
    have h1 : ¬ ((↑(X86.Width.w32.truncate w).toNat : Int) < 0) := by omega
    have h2 : ¬ (2 ^ 31 ≤ (X86.Width.w32.truncate w).toNat) := by omega
    simp only [decide_eq_false h1, decide_eq_false h2]
  · simp only [hge, ↓reduceIte, Int.ofNat_eq_natCast]
    have h1 : ((↑(X86.Width.w32.truncate w).toNat : Int) - (↑(2 ^ 32 : Nat) : Int)) < 0 := by omega
    have h2 : 2 ^ 31 ≤ (X86.Width.w32.truncate w).toNat := by omega
    simp only [decide_eq_true h1, decide_eq_true h2]

theorem w32_eq_maxMinus1 (w : Lir.Word) :
    Lir.Cond.holds .eq .w32 w (UInt64.ofNat (Rt.Rc.maxCount - 1)) =
      decide ((X86.Width.w32.truncate w).toNat = 2 ^ 31 - 1) := by
  have hm : (X86.Width.w32.truncate (UInt64.ofNat (Rt.Rc.maxCount - 1))).toNat = 2 ^ 31 - 1 := by
    decide
  simp only [Lir.Cond.holds]
  by_cases h : (X86.Width.w32.truncate w).toNat = 2 ^ 31 - 1
  · have heq : X86.Width.w32.truncate w = X86.Width.w32.truncate (UInt64.ofNat (Rt.Rc.maxCount - 1)) :=
      UInt64.toNat_inj.mp (by rw [h, hm])
    simp only [heq, beq_self_eq_true, hm, decide_true]
  · have hne : X86.Width.w32.truncate w ≠ X86.Width.w32.truncate (UInt64.ofNat (Rt.Rc.maxCount - 1)) := by
      intro heq; exact h (by rw [heq, hm])
    simp only [beq_eq_false_iff_ne.mpr hne, decide_eq_false h]

theorem w32_ult_maxMinus1 (w : Lir.Word) :
    Lir.Cond.holds .ult .w32 w (UInt64.ofNat (Rt.Rc.maxCount - 1)) =
      decide ((X86.Width.w32.truncate w).toNat < 2 ^ 31 - 1) := by
  have hm : (X86.Width.w32.truncate (UInt64.ofNat (Rt.Rc.maxCount - 1))).toNat = 2 ^ 31 - 1 := by
    decide
  simp only [Lir.Cond.holds, UInt64.lt_iff_toNat_lt, hm]

theorem w32_eq_zero (w : Lir.Word) :
    Lir.Cond.holds .eq .w32 w 0 = decide ((X86.Width.w32.truncate w).toNat = 0) := by
  have h0 : (X86.Width.w32.truncate 0).toNat = 0 := by decide
  simp only [Lir.Cond.holds]
  by_cases h : (X86.Width.w32.truncate w).toNat = 0
  · have heq : X86.Width.w32.truncate w = X86.Width.w32.truncate 0 :=
      UInt64.toNat_inj.mp (by rw [h, h0])
    simp only [heq, beq_self_eq_true, h0, decide_true]
  · have hne : X86.Width.w32.truncate w ≠ X86.Width.w32.truncate 0 := by
      intro heq; exact h (by rw [heq, h0])
    simp only [beq_eq_false_iff_ne.mpr hne, decide_eq_false h]

theorem addr_cell (env : Lir.Env) (ctx : Lir.Word) (x : Lir.VReg) (w : Lir.Word) (off : Int)
    (hx : env[x]? = some w) :
    Lir.Addr.eval env ctx { base := some (.v x), disp := off } = some (w + Lir.dispWord off) := by
  simp [Lir.Addr.eval, hx]

theorem addr_ctx (env : Lir.Env) (ctx : Lir.Word) (off : Int) :
    Lir.Addr.eval env ctx { base := some .ctx, disp := off } = some (ctx + Lir.dispWord off) := by
  simp [Lir.Addr.eval]

theorem evalArgs_length {env : Lir.Env} :
    ∀ {args : List Lir.Arg} {vals : List Lir.Word},
      Lir.evalArgs env args = some vals → vals.length = args.length
  | [], vals, h => by simp [Lir.evalArgs] at h; subst h; rfl
  | a :: args, vals, h => by
    simp only [Lir.evalArgs, List.mapM_cons] at h
    cases ha : a.eval env with
    | none => simp [ha] at h
    | some v =>
      simp only [ha] at h
      cases hr : List.mapM (Lir.Arg.eval env) args with
      | none => simp [hr] at h
      | some vs =>
        simp [hr] at h
        subst h
        simp [evalArgs_length (args := args) (vals := vs) hr]

/-! ## Helper: field stores for `alloc` -/

theorem argsContainVReg_false {dst : Lir.VReg} :
    ∀ {as : List Lir.Arg}, argsContainVReg dst as = false → ∀ a ∈ as, a ≠ .v dst
  | [], _, _, ha => by cases ha
  | .v y :: rest, h, a, ha => by
    simp only [argsContainVReg, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · intro heq; cases heq; exact h.1 rfl
    · exact argsContainVReg_false h.2 a ha
  | .imm _ :: rest, h, a, ha => by
    simp only [argsContainVReg] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · intro heq; cases heq
    · exact argsContainVReg_false h a ha

theorem evalArgs_insert_not_mem {env : Lir.Env} {dst : Lir.VReg} {w : Lir.Word} :
    ∀ {as : List Lir.Arg}, (∀ a ∈ as, a ≠ .v dst) →
      Lir.evalArgs (env.insert dst w) as = Lir.evalArgs env as
  | [], _ => rfl
  | .imm c :: rest, h => by
    have ih : List.mapM (Lir.Arg.eval (env.insert dst w)) rest = List.mapM (Lir.Arg.eval env) rest :=
      evalArgs_insert_not_mem (as := rest) (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [Lir.evalArgs, List.mapM_cons, Lir.Arg.eval, ih]
  | .v y :: rest, h => by
    have hne : dst ≠ y := fun e => h (.v y) (by simp) (by rw [e])
    have ih : List.mapM (Lir.Arg.eval (env.insert dst w)) rest = List.mapM (Lir.Arg.eval env) rest :=
      evalArgs_insert_not_mem (as := rest) (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [Lir.evalArgs, List.mapM_cons, Lir.Arg.eval, Lir.env_insert_ne _ _ hne, ih]

theorem mkFieldStores_length (dst : Lir.VReg) :
    ∀ (j : Nat) (as : List Lir.Arg), (mkFieldStores dst j as).length = as.length
  | _, [] => rfl
  | j, _ :: as => by simp [mkFieldStores, mkFieldStores_length dst (j + 1) as]

theorem bindParams_range_lookup :
    ∀ (n k : Nat) (vs : List Lir.Word) (ρ : Lir.Env) (hlen : vs.length = n),
      ∃ ρ', Lir.bindParams ρ (List.range' k n) vs = some ρ' ∧
        (∀ i < k, ρ'[i]? = ρ[i]?) ∧
        (∀ j, (hj : j < n) → ρ'[k + j]? = some (vs[j]'(by omega)))
  | 0, k, [], ρ, _ => ⟨ρ, rfl, fun _ _ => rfl, fun j hj => by omega⟩
  | 0, _, _ :: _, _, h => by simp at h
  | n + 1, _, [], _, h => by simp at h
  | n + 1, k, v :: vs, ρ, hlen => by
    simp only [List.range'_succ, Lir.bindParams]
    obtain ⟨ρ', hbp, hlt, hge⟩ :=
      bindParams_range_lookup n (k + 1) vs (ρ.insert k v) (by simpa using hlen)
    refine ⟨ρ', hbp, fun i hi => ?_, fun j hj => ?_⟩
    · rw [hlt i (by omega), Lir.env_insert_ne _ _ (by omega)]
    · cases j with
      | zero =>
        rw [Nat.add_zero, hlt k (by omega), Lir.env_insert_self]; rfl
      | succ j =>
        have h1 := hge j (by omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using h1

/-- Executable specification of storing `vals` at `addr + 8 * (j + 1)`, `addr + 8 * (j + 2)`, ... -/
def writeFieldsMem (mem : X86.Memory) (addr : Lir.Word) : Nat → List Lir.Word → Option X86.Memory
  | _, [] => some mem
  | j, v :: vs =>
    match mem.write? .w64 (addr + Lir.dispWord (Int.ofNat (8 * (j + 1)))) v with
    | .ok mem' => writeFieldsMem mem' addr (j + 1) vs
    | .error _ => none

theorem exec_mkFieldStores {p : Lir.Program} {F : Lir.Func} {B : Lir.Block} {fn lbl : Nat}
    {dst : Lir.VReg} {addr ctx : Lir.Word} {rest : List Lir.Frame} {env : Lir.Env}
    (hf : p.funcs[fn]? = some F) (hb : F.blocks[lbl]? = some B)
    (hdst : env[dst]? = some addr) :
    ∀ {pre post : List Lir.Stmt} {j : Nat} {args : List Lir.Arg} {vals : List Lir.Word} {mem : X86.Memory},
      B.body.toList = pre ++ mkFieldStores dst j args ++ post →
      Lir.evalArgs env args = some vals →
      match writeFieldsMem mem addr j vals with
      | some mem' =>
        Sem.Star (Lir.semStep p)
          { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } 0
          { mem := mem', ctx, stack := { fn, label := lbl, pos := pre.length + args.length, env, dsts := [] } :: rest }
      | none =>
        Sem.Reaches (Lir.semStep p)
          { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } 0 .stuck
  | pre, post, j, [], [], mem, _, _ => by
    simp only [writeFieldsMem, List.length_nil, Nat.add_zero]
    exact .refl _
  | _, _, _, [], _ :: _, _, _, hargs => by simp [Lir.evalArgs] at hargs
  | _, _, _, a :: args, [], _, _, hargs => by
    have := evalArgs_length hargs; simp at this
  | pre, post, j, a :: args, v :: vals, mem, hbody, hargs => by
    simp only [Lir.evalArgs, List.mapM_cons] at hargs
    cases ha : a.eval env with
    | none => simp [ha] at hargs
    | some va =>
      simp only [ha] at hargs
      cases hrest : List.mapM (Lir.Arg.eval env) args with
      | none => simp [hrest] at hargs
      | some vs =>
        simp [hrest] at hargs
        obtain ⟨rfl, rfl⟩ := hargs
        have hpos : pre.length < B.body.size := by
          have := congrArg List.length hbody
          simp only [Array.length_toList, mkFieldStores, List.length_append, List.length_cons] at this
          omega
        have hget : B.body[pre.length] = .store .w64 (cellAddr dst (Int.ofNat (8 * (j + 1)))) a := by
          have : B.body.toList[pre.length]? = some (.store .w64 (cellAddr dst (Int.ofNat (8 * (j + 1)))) a) := by
            rw [hbody]; simp [mkFieldStores]
          simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hpos, Option.some.injEq] at this
          exact this
        simp only [writeFieldsMem]
        cases hw : mem.write? .w64 (addr + Lir.dispWord (Int.ofNat (8 * (j + 1)))) va with
        | error e =>
          dsimp only
          apply Sem.Reaches.final
          have hst : Lir.step p { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } = .stuck := by
            unfold Lir.step
            simp only [hf, hb, hpos, ↓reduceDIte, hget, Lir.Stmt.exec, cellAddr,
              addr_cell env ctx dst addr _ hdst, ha, Option.bind_eq_bind, Option.bind_some, hw]
          rw [Lir.semStep, hst]; exact .stuck
        | ok mem₁ =>
          dsimp only
          have hstep : Lir.step p { mem, ctx, stack := { fn, label := lbl, pos := pre.length, env, dsts := [] } :: rest } =
              .next { mem := mem₁, ctx, stack := { fn, label := lbl, pos := pre.length + 1, env, dsts := [] } :: rest } false := by
            exact Lir.step_stmt (fr := { fn, label := lbl, pos := pre.length, env, dsts := [] })
              hf hb hpos hget rfl (by
                simp only [Lir.Stmt.exec, cellAddr, addr_cell env ctx dst addr _ hdst, ha,
                  Option.bind_eq_bind, Option.bind_some, hw])
          have hbody' : B.body.toList = (pre ++ [.store .w64 (cellAddr dst (Int.ofNat (8 * (j + 1)))) a]) ++
              mkFieldStores dst (j + 1) args ++ post := by
            simpa [mkFieldStores, List.append_assoc] using hbody
          have ih := exec_mkFieldStores (ctx := ctx) (rest := rest) hf hb hdst hbody' (by simpa [Lir.evalArgs] using hrest) (mem := mem₁)
          cases hwf : writeFieldsMem mem₁ addr (j + 1) vs with
          | none =>
            rw [hwf] at ih
            exact .free (Lir.semStep_next.mpr hstep) (by simpa using ih)
          | some mem' =>
            rw [hwf] at ih
            have := Sem.Star.free (Lir.semStep_next.mpr hstep) (by simpa using ih)
            simpa [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using this

theorem exec_allocWrapper_stores {p : Lir.Program} {wrap proc : Nat} {fields : Nat}
    {addr ctx : Lir.Word} {rest : List Lir.Frame} {env : Lir.Env}
    (hf : p.funcs[wrap]? = some (allocationWrapper proc fields))
    (haddr : env[fields]? = some addr) :
    ∀ {j : Nat} {vals : List Lir.Word} {mem : X86.Memory},
      j + vals.length = fields →
      (∀ i, (hi : i < vals.length) → env[j + i]? = some vals[i]) →
      match writeFieldsMem mem addr j vals with
      | some mem' =>
        Sem.Star (Lir.semStep p)
          { mem, ctx, stack := { fn := wrap, label := 0, pos := 1 + j, env, dsts := [] } :: rest } 0
          { mem := mem', ctx, stack := { fn := wrap, label := 0, pos := 1 + fields, env, dsts := [] } :: rest }
      | none =>
        Sem.Reaches (Lir.semStep p)
          { mem, ctx, stack := { fn := wrap, label := 0, pos := 1 + j, env, dsts := [] } :: rest } 0 .stuck
  | j, [], mem, hlen, _ => by
    simp only [writeFieldsMem, List.length_nil, Nat.add_zero] at hlen ⊢
    subst hlen; exact .refl _
  | j, v :: vals, mem, hlen, hvals => by
    have hb : (allocationWrapper proc fields).blocks[0]? = some (allocationWrapper proc fields).blocks[0]! := rfl
    have hjlt : j < fields := by simp at hlen; omega
    have hpos : 1 + j < (allocationWrapper proc fields).blocks[0]!.body.size := by
      simp [allocationWrapper]; omega
    have hget : (allocationWrapper proc fields).blocks[0]!.body[1 + j] =
        .store .w64 { base := some (.v fields), disp := Int.ofNat (8 * (j + 1)) } (.v j) := by
      simp [allocationWrapper, Nat.add_comm 1 j]
    have hvj : env[j]? = some v := by
      have := hvals 0 (by simp)
      simpa using this
    simp only [writeFieldsMem]
    cases hw : mem.write? .w64 (addr + Lir.dispWord (Int.ofNat (8 * (j + 1)))) v with
    | error e =>
      dsimp only
      apply Sem.Reaches.final
      have hst : Lir.step p { mem, ctx, stack := { fn := wrap, label := 0, pos := 1 + j, env, dsts := [] } :: rest } = .stuck := by
        unfold Lir.step
        simp only [hf, hb, hpos, ↓reduceDIte, hget, Lir.Stmt.exec,
          addr_cell env ctx fields addr _ haddr, Lir.Arg.eval, hvj, Option.bind_eq_bind, Option.bind_some, hw]
      rw [Lir.semStep, hst]; exact .stuck
    | ok mem₁ =>
      dsimp only
      have hstep : Lir.step p { mem, ctx, stack := { fn := wrap, label := 0, pos := 1 + j, env, dsts := [] } :: rest } =
          .next { mem := mem₁, ctx, stack := { fn := wrap, label := 0, pos := 1 + (j + 1), env, dsts := [] } :: rest } false := by
        have h1 := Lir.step_stmt (p := p) (F := allocationWrapper proc fields) (B := (allocationWrapper proc fields).blocks[0]!)
          (fr := { fn := wrap, label := 0, pos := 1 + j, env, dsts := [] }) (rest := rest) (mem := mem) (ctx := ctx)
          (ρ' := env) (mem' := mem₁)
          hf hb hpos hget rfl (by
            simp only [Lir.Stmt.exec, addr_cell env ctx fields addr _ haddr, Lir.Arg.eval, hvj,
              Option.bind_eq_bind, Option.bind_some, hw])
        simpa [Nat.add_assoc] using h1
      have ih := exec_allocWrapper_stores (p := p) (wrap := wrap) (proc := proc) (fields := fields)
        (ctx := ctx) (rest := rest)
        hf haddr (j := j + 1) (vals := vals) (mem := mem₁) (by simp at hlen; omega)
        (fun i hi => by
          have := hvals (i + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      cases hwf : writeFieldsMem mem₁ addr (j + 1) vals with
      | none =>
        rw [hwf] at ih
        exact .free (Lir.semStep_next.mpr hstep) ih
      | some mem' =>
        rw [hwf] at ih
        exact .free (Lir.semStep_next.mpr hstep) ih

/-! ## Single-site operational outcome descriptors -/

/-- Exact outcome of an `inc` site on `(xVal, mem)`. -/
inductive IncOutcome where
  | ok (mem' : X86.Memory)
  | oom
  | stuck

def evalIncSite (xVal : Lir.Word) (mem : X86.Memory) : IncOutcome :=
  if Lir.Cond.holds .tnz .w64 xVal 1 then .ok mem
  else
    match Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none => .stuck
    | some cnt =>
      if (X86.Width.w32.truncate cnt).toNat < 2 ^ 31 - 1 then
        match mem.write? .w32 (xVal + Lir.dispWord 4) (X86.Width.w32.truncate (cnt + 1)) with
        | .ok mem' => .ok mem'
        | .error _ => .stuck
      else if (X86.Width.w32.truncate cnt).toNat = 2 ^ 31 - 1 then .oom
      else .ok mem

/-- Exact outcome of a `dec` site on `(xVal, mem)`. -/
inductive DecOutcome where
  | ok (mem' : X86.Memory)
  | free
  | stuck

def evalDecSite (xVal : Lir.Word) (mem : X86.Memory) : DecOutcome :=
  if Lir.Cond.holds .tnz .w64 xVal 1 then .ok mem
  else
    match Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none => .stuck
    | some cnt =>
      if (X86.Width.w32.truncate cnt).toNat = 0 then .free
      else if 2 ^ 31 ≤ (X86.Width.w32.truncate cnt).toNat then .ok mem
      else
        match mem.write? .w32 (xVal + Lir.dispWord 4) (X86.Width.w32.truncate (cnt - 1)) with
        | .ok mem' => .ok mem'
        | .error _ => .stuck

/-- Exact outcome of reserving a cell of layout `lay` in class `cls` and writing its header. -/
inductive AllocReserveOutcome where
  | ok (addr : Lir.Word) (mem' : X86.Memory)
  | oom
  | stuck

def evalAllocReserve (lay : Rt.Rc.CellLayout) (cls : Nat) (mem : X86.Memory) (ctx : Lir.Word) :
    AllocReserveOutcome :=
  let headAddr := ctx + Lir.dispWord (Int.ofNat (8 * cls))
  let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
  match Lir.loadWord mem .w64 .zero headAddr with
  | none => .stuck
  | some p0 =>
    if Lir.Cond.holds .eq .w64 p0 0 then
      match Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord Rt.bumpOff) with
      | none => .stuck
      | some b0 =>
        match Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord Rt.limitOff) with
        | none => .stuck
        | some lim =>
          let (b1, ovf) := Lir.Ovf.eval .addC b0 (UInt64.ofNat (Rt.Rc.classBytes cls))
          if ovf then .oom
          else if Lir.Cond.holds .ule .w64 b1 lim then
            match mem.write? .w64 (ctx + Lir.dispWord Rt.bumpOff) b1 with
            | .error _ => .stuck
            | .ok mem₁ =>
              match mem₁.write? .w64 (b0 + Lir.dispWord 0) hdr with
              | .error _ => .stuck
              | .ok mem₂ => .ok b0 mem₂
          else .oom
    else
      match Lir.loadWord mem .w64 .zero (p0 + Lir.dispWord 0) with
      | none => .stuck
      | some p1 =>
        match mem.write? .w64 headAddr p1 with
        | .error _ => .stuck
        | .ok mem₁ =>
          match mem₁.write? .w64 (p0 + Lir.dispWord 0) hdr with
          | .error _ => .stuck
          | .ok mem₂ => .ok p0 mem₂

/-! ## 1. `inc` site execution (raw vs inlined) -/

theorem raw_inc_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {dst x : Lir.VReg} {wLit xVal : Lir.Word}
    (hF : raw.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B)
    (hpos : fr.pos < B.body.size)
    (hstmt : B.body[fr.pos] = .call [dst] l.incWrapper [.v x, .imm wLit])
    (hx : fr.env[x]? = some xVal) :
    match evalIncSite xVal mem with
    | .ok mem' =>
      ∃ s₁, Lir.semStep raw { mem, ctx, stack := fr :: rest } = .next s₁ true ∧
      Sem.Star (Lir.semStep raw) s₁ 1
        { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst 1, dsts := [] } :: rest }
    | .oom =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 2 (.resource .heap)
    | .stuck =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 2 .stuck := by
  let wEnv : Lir.Env := (({} : Lir.Env).insert 0 xVal).insert 1 wLit
  let pEnv : Lir.Env := ({} : Lir.Env).insert 0 xVal
  let caller' : Lir.Frame := { fr with pos := fr.pos + 1, dsts := [dst] }
  let wFr0 : Lir.Frame := { fn := l.incWrapper, label := 0, pos := 0, env := wEnv }
  let wFr1 : Lir.Frame := { fn := l.incWrapper, label := 0, pos := 1, env := wEnv, dsts := [] }
  let pFr0 : Lir.Frame := { fn := l.incProc, label := 0, pos := 0, env := pEnv }
  have hstep1 : Lir.semStep raw { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := wFr0 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (vs := [xVal, wLit]) hF hB hpos hstmt
      (by simp [Lir.evalArgs, Lir.Arg.eval, hx])
      (by simp [Lir.enter, hr.incWrap, incrementWrapper, Lir.bindParams, wEnv, wFr0])
  have hw0 : wEnv[0]? = some xVal := by
    rw [Lir.env_insert_ne _ _ (by decide), Lir.env_insert_self]
  have hstep2 : Lir.semStep raw { mem, ctx, stack := wFr0 :: caller' :: rest } =
      .next { mem, ctx, stack := pFr0 :: wFr1 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (fr := wFr0) (vs := [xVal]) hr.incWrap rfl (by simp [incrementWrapper, wFr0]) rfl
      (by simp [Lir.evalArgs, Lir.Arg.eval, wFr0, hw0])
      (by simp [Lir.enter, hr.incProc, Rt.Rc.Procs.inc, Lir.bindParams, pEnv, pFr0])
  have hret : ∀ (m : X86.Memory) (envP : Lir.Env),
      Sem.Star (Lir.semStep raw)
        { mem := m, ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := envP } :: wFr1 :: caller' :: rest } 0
        { mem := m, ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst 1, dsts := [] } :: rest } := by
    intro m envP
    have s1 : Lir.semStep raw
        { mem := m, ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := envP } :: wFr1 :: caller' :: rest } =
        .next { mem := m, ctx, stack := wFr1 :: caller' :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := l.incProc, label := 5, pos := 0, env := envP }) hr.incProc (by rfl) (by rfl)]
      simp [Rt.Rc.Procs.inc, Lir.evalArgs, Lir.bindParams, wFr1]
    have s2 : Lir.semStep raw { mem := m, ctx, stack := wFr1 :: caller' :: rest } =
        .next { mem := m, ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst 1, dsts := [] } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := wFr1) hr.incWrap rfl (by simp [incrementWrapper, wFr1])]
      simp [incrementWrapper, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams, caller']
    exact .free s1 (.free s2 (.refl _))
  unfold evalIncSite
  by_cases htag : Lir.Cond.holds .tnz .w64 xVal 1 = true
  · simp only [htag, ↓reduceIte]
    refine ⟨_, hstep1, .charge hstep2 ?_⟩
    have s3 : Lir.semStep raw { mem, ctx, stack := pFr0 :: wFr1 :: caller' :: rest } =
        .next { mem, ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := pEnv } :: wFr1 :: caller' :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := pFr0) hr.incProc (by rfl) (by rfl)]
      simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval, pFr0, pEnv, htag,
        Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
    exact .free s3 (hret mem pEnv)
  · have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by simpa using htag
    simp only [htagF, Bool.false_eq_true, ↓reduceIte]
    have s3 : Lir.semStep raw { mem, ctx, stack := pFr0 :: wFr1 :: caller' :: rest } =
        .next { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 0, env := pEnv } :: wFr1 :: caller' :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := pFr0) hr.incProc (by rfl) (by rfl)]
      simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval, pFr0, pEnv, htagF,
        Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
    cases hload : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none =>
      dsimp only
      refine .charge hstep1 (.charge hstep2 (.free s3 (.final ?_)))
      have hst : Lir.step raw { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 0, env := pEnv } :: wFr1 :: caller' :: rest } = .stuck := by
        unfold Lir.step
        simp [hr.incProc, Rt.Rc.Procs.inc, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
          addr_cell pEnv ctx 0 xVal 4 (by simp [pEnv]), hload]
      rw [Lir.semStep, hst]; exact .stuck
    | some cnt =>
      dsimp only
      let pEnv1 := pEnv.insert 1 cnt
      have s4 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 0, env := pEnv } :: wFr1 :: caller' :: rest } =
          .next { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 } :: wFr1 :: caller' :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fn := l.incProc, label := 1, pos := 0, env := pEnv })
          hr.incProc (by rfl) (by simp [Rt.Rc.Procs.inc]) rfl rfl
          (by simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
            addr_cell pEnv ctx 0 xVal 4 (by simp [pEnv]), hload, pEnv1])
      by_cases hlt : (X86.Width.w32.truncate cnt).toNat < 2 ^ 31 - 1
      · simp only [hlt, ↓reduceIte]
        have hslt : Lir.Cond.holds .slt .w32 cnt 0 = false := by
          rw [w32_signedValue_lt_zero]; simp; omega
        have heq : Lir.Cond.holds .eq .w32 cnt (UInt64.ofNat (Rt.Rc.maxCount - 1)) = false := by
          rw [w32_eq_maxMinus1]; simp; omega
        have s5 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 } :: wFr1 :: caller' :: rest } =
            .next { mem, ctx, stack := { fn := l.incProc, label := 2, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 }) hr.incProc (by rfl) (by rfl)]
          simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval, pEnv1, hslt,
            Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        have s6 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 2, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } =
            .next { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fn := l.incProc, label := 2, pos := 0, env := pEnv1 }) hr.incProc (by rfl) (by rfl)]
          simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval, pEnv1, heq,
            Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        let pEnv2 := pEnv1.insert 2 (X86.Width.w32.truncate (cnt + 1))
        have s7 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } =
            .next { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 1, env := pEnv2 } :: wFr1 :: caller' :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fn := l.incProc, label := 3, pos := 0, env := pEnv1 })
            hr.incProc (by rfl) (by simp [Rt.Rc.Procs.inc]) rfl rfl
            (by simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Lir.Stmt.exec, Lir.Rhs.eval, Lir.BinOp.eval,
              Lir.Arg.eval, pEnv1, pEnv2])
        have hpEnv2_0 : pEnv2[0]? = some xVal := by
          rw [Lir.env_insert_ne _ _ (by decide), Lir.env_insert_ne _ _ (by decide), Lir.env_insert_self]
        cases hw : mem.write? .w32 (xVal + Lir.dispWord 4) (X86.Width.w32.truncate (cnt + 1)) with
        | error e =>
          dsimp only
          refine .charge hstep1 (.charge hstep2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 (.final ?_)))))))
          have hst : Lir.step raw { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 1, env := pEnv2 } :: wFr1 :: caller' :: rest } = .stuck := by
            unfold Lir.step
            simp [hr.incProc, Rt.Rc.Procs.inc, Rt.Rc.Procs.cellAddr, Rt.Rc.Procs.v, Lir.Stmt.exec,
              addr_cell pEnv2 ctx 0 xVal 4 hpEnv2_0, Lir.Arg.eval, pEnv2, hw]
          rw [Lir.semStep, hst]; exact .stuck
        | ok mem' =>
          dsimp only
          have s8 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 1, env := pEnv2 } :: wFr1 :: caller' :: rest } =
              .next { mem := mem', ctx, stack := { fn := l.incProc, label := 3, pos := 2, env := pEnv2 } :: wFr1 :: caller' :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fn := l.incProc, label := 3, pos := 1, env := pEnv2 })
              hr.incProc (by rfl) (by simp [Rt.Rc.Procs.inc]) rfl rfl
              (by simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.cellAddr, Rt.Rc.Procs.v, Lir.Stmt.exec,
                addr_cell pEnv2 ctx 0 xVal 4 hpEnv2_0, Lir.Arg.eval, pEnv2, hw])
          have s9 : Lir.semStep raw { mem := mem', ctx, stack := { fn := l.incProc, label := 3, pos := 2, env := pEnv2 } :: wFr1 :: caller' :: rest } =
              .next { mem := mem', ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := pEnv2 } :: wFr1 :: caller' :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.incProc, label := 3, pos := 2, env := pEnv2 }) hr.incProc (by rfl) (by rfl)]
            simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.to, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          exact ⟨_, hstep1, .charge hstep2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 (.free s8 (.free s9 (hret mem' pEnv2))))))))⟩
      · simp only [hlt, ↓reduceIte]
        by_cases heqN : (X86.Width.w32.truncate cnt).toNat = 2 ^ 31 - 1
        · simp only [heqN, ↓reduceIte]
          have hslt : Lir.Cond.holds .slt .w32 cnt 0 = false := by
            rw [w32_signedValue_lt_zero]; simp; omega
          have heq : Lir.Cond.holds .eq .w32 cnt (UInt64.ofNat (Rt.Rc.maxCount - 1)) = true := by
            rw [w32_eq_maxMinus1]; simp [heqN]
          have s5 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 } :: wFr1 :: caller' :: rest } =
              .next { mem, ctx, stack := { fn := l.incProc, label := 2, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 }) hr.incProc (by rfl) (by rfl)]
            simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval, pEnv1, hslt,
              Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          have s6 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 2, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } =
              .next { mem, ctx, stack := { fn := l.incProc, label := 4, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.incProc, label := 2, pos := 0, env := pEnv1 }) hr.incProc (by rfl) (by rfl)]
            simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval, pEnv1, heq,
              Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          refine .charge hstep1 (.charge hstep2 (.free s3 (.free s4 (.free s5 (.free s6 (.final ?_))))))
          have hst : Lir.step raw { mem, ctx, stack := { fn := l.incProc, label := 4, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } = .fail .heap := by
            rw [Lir.step_term (fr := { fn := l.incProc, label := 4, pos := 0, env := pEnv1 }) hr.incProc (by rfl) (by rfl)]; rfl
          rw [Lir.semStep, hst]; exact .fail
        · simp only [heqN, ↓reduceIte]
          have hslt : Lir.Cond.holds .slt .w32 cnt 0 = true := by
            rw [w32_signedValue_lt_zero]; simp; omega
          have s5 : Lir.semStep raw { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 } :: wFr1 :: caller' :: rest } =
              .next { mem, ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.incProc, label := 1, pos := 1, env := pEnv1 }) hr.incProc (by rfl) (by rfl)]
            simp [Rt.Rc.Procs.inc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval, pEnv1, hslt,
              Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          exact ⟨_, hstep1, .charge hstep2 (.free s3 (.free s4 (.free s5 (hret mem pEnv1))))⟩

theorem inl_inc_exec {l : Layout} {raw : Lir.Program}
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 restStmts : List Lir.Stmt} {dst x : Lir.VReg} {wLit xVal : Lir.Word}
    (hltFn : fr.fn < l.sourceCount)
    (hF : raw.funcs[fr.fn]? = some F)
    (hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = .call [dst] l.incWrapper [.v x, .imm wLit] :: restStmts)
    (hposB : rawPos < B.body.size)
    (hgetB : B.body[rawPos] = .call [dst] l.incWrapper [.v x, .imm wLit])
    (hx : fr.env[x]? = some xVal)
    (hxLt : x < freshBase F) :
    let inl := inlineProgram l raw
    ChunkPos l F b B (rawPos + 1) (fr.label + 5) 1 ∧
    match evalIncSite xVal mem with
    | .ok mem' =>
      ∃ env' s₁, Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₁ false ∧
      Sem.Star (Lir.semStep inl) s₁ 0
        { mem := mem', ctx, stack := { fr with label := fr.label + 5, pos := 1, env := env', dsts := [] } :: rest } ∧
      AgreeBelow (freshBase F) (fr.env.insert dst 1) env'
    | .oom =>
      Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 (.resource .heap)
    | .stuck =>
      Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 .stuck := by
  intro inl
  have hc : classify l (.call [dst] l.incWrapper [.v x, .imm wLit]) = some (.inc dst x) := by
    simp [classify]
  have cpNext : ChunkAt l F b B (rawPos + 1) (fr.label + 5) 1 (tmp + 2) [] [.assign dst (.arg (.imm 1))] restStmts := {
    bLookup := hcp.bLookup
    tmpGe := by have := hcp.tmpGe; omega
    split := by
      have htake : B.body.toList.take (rawPos + 1) =
          B.body.toList.take rawPos ++ [.call [dst] l.incWrapper [.v x, .imm wLit]] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB, hgetB]; simp
      rw [htake, List.append_assoc]; simpa [hrest] using hcp.split
    posLe := by omega
    blocksMatch := fun k blk hk => by
      have h := hcp.blocksMatch (5 + k) blk (by
        rw [hrest]; unfold expandStmts; rw [hc]; dsimp only
        rw [Nat.add_comm 5 k]; exact hk)
      simpa [Nat.add_assoc] using h
    inPosEq := rfl
    endLbl := by
      have := hcp.endLbl
      rw [hrest, stmtsExtra_cons, stmtExtra, hc] at this
      simp only [siteExtra] at this
      dsimp only [Lir.Label] at this ⊢; omega }
  refine ⟨⟨_, _, _, _, cpNext⟩, ?_⟩
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  have hb0 : (inlineFunc l F).blocks[fr.label]? = some {
      params, body := acc.reverse.toArray,
      term := .br .tnz .w64 (.v x) (.imm 1) ⟨fr.label + 5, []⟩ ⟨fr.label + 1, []⟩, cold := B.cold } := by
    simpa using hcp.blocksMatch 0 _ (by rw [hrest]; unfold expandStmts; rw [hc]; rfl)
  have hb1 : (inlineFunc l F).blocks[fr.label + 1]? = some {
      body := #[.assign tmp (.load .w32 .zero (cellAddr x 4))],
      term := .br .ult .w32 (.v tmp) (.imm (UInt64.ofNat (Rt.Rc.maxCount - 1)))
        ⟨fr.label + 2, []⟩ ⟨fr.label + 3, []⟩, cold := B.cold } := by
    exact hcp.blocksMatch 1 _ (by rw [hrest]; unfold expandStmts; rw [hc]; rfl)
  have hb2 : (inlineFunc l F).blocks[fr.label + 2]? = some {
      body := #[.assign (tmp + 1) (.bin .add .w32 (.v tmp) (.imm 1)),
        .store .w32 (cellAddr x 4) (.v (tmp + 1))],
      term := .jump ⟨fr.label + 5, []⟩, cold := B.cold } := by
    exact hcp.blocksMatch 2 _ (by rw [hrest]; unfold expandStmts; rw [hc]; rfl)
  have hb3 : (inlineFunc l F).blocks[fr.label + 3]? = some {
      body := #[],
      term := .br .eq .w32 (.v tmp) (.imm (UInt64.ofNat (Rt.Rc.maxCount - 1)))
        ⟨fr.label + 4, []⟩ ⟨fr.label + 5, []⟩, cold := true } := by
    exact hcp.blocksMatch 3 _ (by rw [hrest]; unfold expandStmts; rw [hc]; rfl)
  have hb4 : (inlineFunc l F).blocks[fr.label + 4]? = some {
      body := #[], term := .fail .heap, cold := true } := by
    exact hcp.blocksMatch 4 _ (by rw [hrest]; unfold expandStmts; rw [hc]; rfl)
  obtain ⟨jb, postJ, hj0, hjp, hjbody, _, _⟩ :=
    ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold restStmts
      (fr.label + 5) (tmp + 2) [] [.assign dst (.arg (.imm 1))]
  have hb5 : (inlineFunc l F).blocks[fr.label + 5]? = some jb := by
    simpa using cpNext.blocksMatch 0 jb hj0
  have hjbPos : 0 < jb.body.size := by
    have := congrArg List.length hjbody; simp at this; omega
  have hjbStmt : jb.body[0] = .assign dst (.arg (.imm 1)) := by
    have : jb.body.toList[0]? = some (.assign dst (.arg (.imm 1))) := by rw [hjbody]; simp
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hjbPos, Option.some.injEq] at this
    exact this
  have hpos0 : fr.pos = acc.reverse.toArray.size := by simp [hcp.inPosEq]
  have hjoinStep : ∀ (m : X86.Memory) (envJ : Lir.Env),
      Sem.Star (Lir.semStep inl)
        { mem := m, ctx, stack := { fr with label := fr.label + 5, pos := 0, env := envJ } :: rest } 0
        { mem := m, ctx, stack := { fr with label := fr.label + 5, pos := 1, env := envJ.insert dst 1, dsts := [] } :: rest } := by
    intro m envJ
    have sj : Lir.semStep inl { mem := m, ctx, stack := { fr with label := fr.label + 5, pos := 0, env := envJ } :: rest } =
        .next { mem := m, ctx, stack := { fr with label := fr.label + 5, pos := 1, env := envJ.insert dst 1, dsts := [] } :: rest } false := by
      apply Lir.semStep_next.mpr
      have h1 := Lir.step_stmt (p := inl) (fr := { fr with label := fr.label + 5, pos := 0, env := envJ })
        (rest := rest) (mem := m) (ctx := ctx) (ρ' := envJ.insert dst 1) (mem' := m)
        hF' hb5 hjbPos hjbStmt rfl (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval])
      simpa [hdsts] using h1
    exact .free sj (.refl _)
  have htmpGt : (x : Nat) ≠ tmp := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxLt hcp.tmpGe)
  have htmp1Gt : (x : Nat) ≠ tmp + 1 := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxLt (by have := hcp.tmpGe; omega))
  unfold evalIncSite
  by_cases htag : Lir.Cond.holds .tnz .w64 xVal 1 = true
  · simp only [htag, ↓reduceIte]
    have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
        .next { mem, ctx, stack := { fr with label := fr.label + 5, pos := 0 } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term hF' hb0 hpos0]
      simp [Lir.Arg.eval, hx, htag, Lir.takeEdge, Lir.evalArgs, hb5, hjp, Lir.bindParams]
    exact ⟨fr.env.insert dst 1, _, s1, hjoinStep mem fr.env, AgreeBelow.refl⟩
  · have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by simpa using htag
    simp only [htagF, Bool.false_eq_true, ↓reduceIte]
    have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
        .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term hF' hb0 hpos0]
      simp [Lir.Arg.eval, hx, htagF, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams]
    cases hload : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none =>
      dsimp only
      refine .free s1 (.final ?_)
      have hst : Lir.step inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } = .stuck := by
        unfold Lir.step
        simp [hF', hb1, cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell fr.env ctx x xVal 4 hx, hload]
      rw [Lir.semStep, hst]; exact .stuck
    | some cnt =>
      dsimp only
      let env1 := fr.env.insert tmp cnt
      have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fr with label := fr.label + 1, pos := 0 })
          hF' hb1 (by simp) rfl rfl
          (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell fr.env ctx x xVal 4 hx, hload, env1])
      by_cases hlt : (X86.Width.w32.truncate cnt).toNat < 2 ^ 31 - 1
      · simp only [hlt, ↓reduceIte]
        have hult : Lir.Cond.holds .ult .w32 cnt (UInt64.ofNat (Rt.Rc.maxCount - 1)) = true := by
          rw [w32_ult_maxMinus1]; simp [hlt]
        have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fr with label := fr.label + 1, pos := 1, env := env1 }) hF' hb1 rfl]
          simp [Lir.Arg.eval, env1, hult, Lir.takeEdge, Lir.evalArgs, hb2, Lir.bindParams]
        let env2 := env1.insert (tmp + 1) (X86.Width.w32.truncate (cnt + 1))
        have s4 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fr with label := fr.label + 2, pos := 1, env := env2 } :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fr with label := fr.label + 2, pos := 0, env := env1 })
            hF' hb2 (by simp) rfl rfl
            (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.BinOp.eval, Lir.Arg.eval, env1, env2])
        have hx2 : env2[x]? = some xVal := by
          rw [Lir.env_insert_ne _ _ (Ne.symm htmp1Gt), Lir.env_insert_ne _ _ (Ne.symm htmpGt), hx]
        cases hw : mem.write? .w32 (xVal + Lir.dispWord 4) (X86.Width.w32.truncate (cnt + 1)) with
        | error e =>
          dsimp only
          refine .free s1 (.free s2 (.free s3 (.free s4 (.final ?_))))
          have hst : Lir.step inl { mem, ctx, stack := { fr with label := fr.label + 2, pos := 1, env := env2 } :: rest } = .stuck := by
            unfold Lir.step
            simp [hF', hb2, cellAddr, Lir.Stmt.exec, addr_cell env2 ctx x xVal 4 hx2, Lir.Arg.eval, env2, hw]
          rw [Lir.semStep, hst]; exact .stuck
        | ok mem' =>
          dsimp only
          have s5 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 2, pos := 1, env := env2 } :: rest } =
              .next { mem := mem', ctx, stack := { fr with label := fr.label + 2, pos := 2, env := env2 } :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fr with label := fr.label + 2, pos := 1, env := env2 })
              hF' hb2 (by simp) rfl rfl
              (by simp [cellAddr, Lir.Stmt.exec, addr_cell env2 ctx x xVal 4 hx2, Lir.Arg.eval, env2, hw])
          have s6 : Lir.semStep inl { mem := mem', ctx, stack := { fr with label := fr.label + 2, pos := 2, env := env2 } :: rest } =
              .next { mem := mem', ctx, stack := { fr with label := fr.label + 5, pos := 0, env := env2 } :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fr with label := fr.label + 2, pos := 2, env := env2 }) hF' hb2 rfl]
            simp [Lir.takeEdge, Lir.evalArgs, hb5, hjp, Lir.bindParams]
          refine ⟨env2.insert dst 1, _, s1,
            .free s2 (.free s3 (.free s4 (.free s5 (.free s6 (hjoinStep mem' env2))))), ?_⟩
          exact ((AgreeBelow.refl.insert_ge hcp.tmpGe cnt).insert_ge (by have := hcp.tmpGe; omega) _).insert_same dst 1
      · simp only [hlt, ↓reduceIte]
        have hult : Lir.Cond.holds .ult .w32 cnt (UInt64.ofNat (Rt.Rc.maxCount - 1)) = false := by
          rw [w32_ult_maxMinus1]; simp [hlt]
        have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fr with label := fr.label + 1, pos := 1, env := env1 }) hF' hb1 rfl]
          simp [Lir.Arg.eval, env1, hult, Lir.takeEdge, Lir.evalArgs, hb3, Lir.bindParams]
        by_cases heqN : (X86.Width.w32.truncate cnt).toNat = 2 ^ 31 - 1
        · simp only [heqN, ↓reduceIte]
          have heq : Lir.Cond.holds .eq .w32 cnt (UInt64.ofNat (Rt.Rc.maxCount - 1)) = true := by
            rw [w32_eq_maxMinus1]; simp [heqN]
          have s4 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0, env := env1 } :: rest } =
              .next { mem, ctx, stack := { fr with label := fr.label + 4, pos := 0, env := env1 } :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fr with label := fr.label + 3, pos := 0, env := env1 }) hF' hb3 rfl]
            simp [Lir.Arg.eval, env1, heq, Lir.takeEdge, Lir.evalArgs, hb4, Lir.bindParams]
          refine .free s1 (.free s2 (.free s3 (.free s4 (.final ?_))))
          have hst : Lir.step inl { mem, ctx, stack := { fr with label := fr.label + 4, pos := 0, env := env1 } :: rest } = .fail .heap := by
            rw [Lir.step_term (fr := { fr with label := fr.label + 4, pos := 0, env := env1 }) hF' hb4 rfl]
          rw [Lir.semStep, hst]; exact .fail
        · simp only [heqN, ↓reduceIte]
          have heq : Lir.Cond.holds .eq .w32 cnt (UInt64.ofNat (Rt.Rc.maxCount - 1)) = false := by
            rw [w32_eq_maxMinus1]; simp [heqN]
          have s4 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0, env := env1 } :: rest } =
              .next { mem, ctx, stack := { fr with label := fr.label + 5, pos := 0, env := env1 } :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fr with label := fr.label + 3, pos := 0, env := env1 }) hF' hb3 rfl]
            simp [Lir.Arg.eval, env1, heq, Lir.takeEdge, Lir.evalArgs, hb5, hjp, Lir.bindParams]
          refine ⟨env1.insert dst 1, _, s1,
            .free s2 (.free s3 (.free s4 (hjoinStep mem env1))), ?_⟩
          exact (AgreeBelow.refl.insert_ge hcp.tmpGe cnt).insert_same dst 1

/-! ## 2. `dec` site execution (raw vs inlined) -/

theorem raw_dec_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {dst x : Lir.VReg} {xVal : Lir.Word}
    (hF : raw.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B)
    (hpos : fr.pos < B.body.size)
    (hstmt : B.body[fr.pos] = .call [dst] l.decWrapper [.v x])
    (hx : fr.env[x]? = some xVal) :
    match evalDecSite xVal mem with
    | .ok mem' =>
      ∃ s₁, Lir.semStep raw { mem, ctx, stack := fr :: rest } = .next s₁ true ∧
      Sem.Star (Lir.semStep raw) s₁ 1
        { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst 1, dsts := [] } :: rest }
    | .free =>
      let wEnv : Lir.Env := ({} : Lir.Env).insert 0 xVal
      let caller' : Lir.Frame := { fr with pos := fr.pos + 1, dsts := [dst] }
      let wFr1 : Lir.Frame := { fn := l.decWrapper, label := 0, pos := 1, env := wEnv, dsts := [] }
      let pFr0 : Lir.Frame := { fn := l.decProc, label := 0, pos := 0, env := wEnv, dsts := [] }
      ∃ s₁, Lir.semStep raw { mem, ctx, stack := fr :: rest } = .next s₁ true ∧
      Sem.Star (Lir.semStep raw) s₁ 1
        { mem, ctx, stack := pFr0 :: wFr1 :: caller' :: rest }
    | .stuck =>
      Sem.Reaches (Lir.semStep raw) { mem, ctx, stack := fr :: rest } 2 .stuck := by
  let wEnv : Lir.Env := ({} : Lir.Env).insert 0 xVal
  let caller' : Lir.Frame := { fr with pos := fr.pos + 1, dsts := [dst] }
  let wFr0 : Lir.Frame := { fn := l.decWrapper, label := 0, pos := 0, env := wEnv }
  let wFr1 : Lir.Frame := { fn := l.decWrapper, label := 0, pos := 1, env := wEnv, dsts := [] }
  let pFr0 : Lir.Frame := { fn := l.decProc, label := 0, pos := 0, env := wEnv, dsts := [] }
  have hstep1 : Lir.semStep raw { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := wFr0 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (vs := [xVal]) hF hB hpos hstmt
      (by simp [Lir.evalArgs, Lir.Arg.eval, hx])
      (by simp [Lir.enter, hr.decWrap, decrementWrapper, Lir.bindParams, wEnv, wFr0])
  have hstep2 : Lir.semStep raw { mem, ctx, stack := wFr0 :: caller' :: rest } =
      .next { mem, ctx, stack := pFr0 :: wFr1 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (fr := wFr0) (vs := [xVal]) hr.decWrap rfl (by simp [decrementWrapper, wFr0]) rfl
      (by simp [Lir.evalArgs, Lir.Arg.eval, wFr0, wEnv])
      (by simp [Lir.enter, hr.decProc, Rt.Rc.Gen.dec, Lir.bindParams, wEnv, pFr0])
  let pEnv1 : Lir.Env := (wEnv.insert 1 xVal).insert 2 0
  have hstep3 : Lir.semStep raw { mem, ctx, stack := pFr0 :: wFr1 :: caller' :: rest } =
      .next { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } false := by
    apply Lir.semStep_next.mpr
    rw [Lir.step_term (fr := pFr0) hr.decProc (by rfl) (by rfl)]
    simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
      Lir.takeEdge, Lir.evalArgs, Lir.bindParams, pFr0, wEnv, pEnv1]
  have hret6 : ∀ (m : X86.Memory) (envP : Lir.Env), envP[2]? = some 0 →
      Sem.Star (Lir.semStep raw)
        { mem := m, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := envP.insert 8 0 } :: wFr1 :: caller' :: rest } 0
        { mem := m, ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst 1, dsts := [] } :: rest } := by
    intro m envP _
    have s6 : Lir.semStep raw
        { mem := m, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := envP.insert 8 0 } :: wFr1 :: caller' :: rest } =
        .next { mem := m, ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := envP.insert 8 0 } :: wFr1 :: caller' :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := l.decProc, label := 6, pos := 0, env := envP.insert 8 0 }) hr.decProc (by rfl) (by rfl)]
      simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
        Lir.Cond.holds, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
    have s10 : Lir.semStep raw
        { mem := m, ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := envP.insert 8 0 } :: wFr1 :: caller' :: rest } =
        .next { mem := m, ctx, stack := wFr1 :: caller' :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := l.decProc, label := 10, pos := 0, env := envP.insert 8 0 }) hr.decProc (by rfl) (by rfl)]
      simp [Rt.Rc.Gen.dec, Lir.evalArgs, Lir.bindParams, wFr1]
    have sw : Lir.semStep raw { mem := m, ctx, stack := wFr1 :: caller' :: rest } =
        .next { mem := m, ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst 1, dsts := [] } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := wFr1) hr.decWrap rfl (by simp [decrementWrapper, wFr1])]
      simp [decrementWrapper, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams, caller']
    exact .free s6 (.free s10 (.free sw (.refl _)))
  have hp1_1 : pEnv1[1]? = some xVal := by
    rw [Lir.env_insert_ne _ _ (by decide), Lir.env_insert_self]
  have hp1_2 : pEnv1[2]? = some 0 := by simp [pEnv1]
  unfold evalDecSite
  by_cases htag : Lir.Cond.holds .tnz .w64 xVal 1 = true
  · simp only [htag, ↓reduceIte]
    have s4 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } =
        .next { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := pEnv1.insert 8 0 } :: wFr1 :: caller' :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := l.decProc, label := 1, pos := 0, env := pEnv1 }) hr.decProc (by rfl) (by rfl)]
      simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
        hp1_1, hp1_2, htag, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
    exact ⟨_, hstep1, .charge hstep2 (.free hstep3 (.free s4 (hret6 mem pEnv1 hp1_2)))⟩
  · have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by simpa using htag
    simp only [htagF, Bool.false_eq_true, ↓reduceIte]
    have s4 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } =
        .next { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term (fr := { fn := l.decProc, label := 1, pos := 0, env := pEnv1 }) hr.decProc (by rfl) (by rfl)]
      simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
        hp1_1, htagF, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
    cases hload : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none =>
      dsimp only
      refine .charge hstep1 (.charge hstep2 (.free hstep3 (.free s4 (.final ?_))))
      have hst : Lir.step raw { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } = .stuck := by
        unfold Lir.step
        simp [hr.decProc, Rt.Rc.Gen.dec, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
          addr_cell pEnv1 ctx 1 xVal 4 hp1_1, hload]
      rw [Lir.semStep, hst]; exact .stuck
    | some cnt =>
      dsimp only
      by_cases hzero : (X86.Width.w32.truncate cnt).toNat = 0
      · simp only [hzero, ↓reduceIte]
        exact ⟨_, hstep1, .charge hstep2 (.refl _)⟩
      · simp only [hzero, ↓reduceIte]
        let pEnv2 := pEnv1.insert 3 cnt
        have hp2_1 : pEnv2[1]? = some xVal := by
          rw [Lir.env_insert_ne _ _ (by decide), hp1_1]
        have hp2_2 : pEnv2[2]? = some 0 := by
          rw [Lir.env_insert_ne _ _ (by decide), hp1_2]
        have s5 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := pEnv1 } :: wFr1 :: caller' :: rest } =
            .next { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := pEnv2 } :: wFr1 :: caller' :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fn := l.decProc, label := 2, pos := 0, env := pEnv1 })
            hr.decProc (by rfl) (by simp [Rt.Rc.Gen.dec]) rfl rfl
            (by simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
              addr_cell pEnv1 ctx 1 xVal 4 hp1_1, hload, pEnv2])
        by_cases hneg : 2 ^ 31 ≤ (X86.Width.w32.truncate cnt).toNat
        · simp only [hneg, ↓reduceIte]
          have hslt : Lir.Cond.holds .slt .w32 cnt 0 = true := by
            rw [w32_signedValue_lt_zero]; simp [hneg]
          have s6 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := pEnv2 } :: wFr1 :: caller' :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := pEnv2.insert 8 0 } :: wFr1 :: caller' :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.decProc, label := 2, pos := 1, env := pEnv2 }) hr.decProc (by rfl) (by rfl)]
            simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
              pEnv2, hp2_2, hslt, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          exact ⟨_, hstep1, .charge hstep2 (.free hstep3 (.free s4 (.free s5 (.free s6 (hret6 mem pEnv2 hp2_2)))))⟩
        · simp only [hneg, ↓reduceIte]
          have hslt : Lir.Cond.holds .slt .w32 cnt 0 = false := by
            rw [w32_signedValue_lt_zero]; simp [hneg]
          have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = false := by
            rw [w32_eq_zero]; simp [hzero]
          have s6 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := pEnv2 } :: wFr1 :: caller' :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := pEnv2 } :: wFr1 :: caller' :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.decProc, label := 2, pos := 1, env := pEnv2 }) hr.decProc (by rfl) (by rfl)]
            simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
              pEnv2, hslt, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          have s7 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := pEnv2 } :: wFr1 :: caller' :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 0, env := pEnv2 } :: wFr1 :: caller' :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.decProc, label := 3, pos := 0, env := pEnv2 }) hr.decProc (by rfl) (by rfl)]
            simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
              pEnv2, heq0, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          let pEnv3 := pEnv2.insert 4 (X86.Width.w32.truncate (cnt - 1))
          have hp3_1 : pEnv3[1]? = some xVal := by
            rw [Lir.env_insert_ne _ _ (by decide), hp2_1]
          have hp3_2 : pEnv3[2]? = some 0 := by
            rw [Lir.env_insert_ne _ _ (by decide), hp2_2]
          have s8 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 0, env := pEnv2 } :: wFr1 :: caller' :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 1, env := pEnv3 } :: wFr1 :: caller' :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fn := l.decProc, label := 4, pos := 0, env := pEnv2 })
              hr.decProc (by rfl) (by simp [Rt.Rc.Gen.dec]) rfl rfl
              (by simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Lir.Stmt.exec, Lir.Rhs.eval,
                Lir.BinOp.eval, Lir.Arg.eval, pEnv2, pEnv3])
          cases hw : mem.write? .w32 (xVal + Lir.dispWord 4) (X86.Width.w32.truncate (cnt - 1)) with
          | error e =>
            dsimp only
            refine .charge hstep1 (.charge hstep2 (.free hstep3 (.free s4 (.free s5 (.free s6 (.free s7 (.free s8 (.final ?_))))))))
            have hst : Lir.step raw { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 1, env := pEnv3 } :: wFr1 :: caller' :: rest } = .stuck := by
              unfold Lir.step
              simp [hr.decProc, Rt.Rc.Gen.dec, Rt.Rc.Procs.cellAddr, Rt.Rc.Procs.v, Lir.Stmt.exec,
                addr_cell pEnv3 ctx 1 xVal 4 hp3_1, Lir.Arg.eval, pEnv3, hw]
            rw [Lir.semStep, hst]; exact .stuck
          | ok mem' =>
            dsimp only
            have s9 : Lir.semStep raw { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 1, env := pEnv3 } :: wFr1 :: caller' :: rest } =
                .next { mem := mem', ctx, stack := { fn := l.decProc, label := 4, pos := 2, env := pEnv3 } :: wFr1 :: caller' :: rest } false := by
              apply Lir.semStep_next.mpr
              exact Lir.step_stmt (fr := { fn := l.decProc, label := 4, pos := 1, env := pEnv3 })
                hr.decProc (by rfl) (by simp [Rt.Rc.Gen.dec]) rfl rfl
                (by simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.cellAddr, Rt.Rc.Procs.v, Lir.Stmt.exec,
                  addr_cell pEnv3 ctx 1 xVal 4 hp3_1, Lir.Arg.eval, pEnv3, hw])
            have s10 : Lir.semStep raw { mem := mem', ctx, stack := { fn := l.decProc, label := 4, pos := 2, env := pEnv3 } :: wFr1 :: caller' :: rest } =
                .next { mem := mem', ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := pEnv3.insert 8 0 } :: wFr1 :: caller' :: rest } false := by
              apply Lir.semStep_next.mpr
              rw [Lir.step_term (fr := { fn := l.decProc, label := 4, pos := 2, env := pEnv3 }) hr.decProc (by rfl) (by rfl)]
              simp [Rt.Rc.Gen.dec, Rt.Rc.Procs.v, Rt.Rc.Procs.to, Lir.Arg.eval, hp3_2,
                Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
            exact ⟨_, hstep1, .charge hstep2 (.free hstep3 (.free s4 (.free s5 (.free s6 (.free s7 (.free s8 (.free s9 (.free s10 (hret6 mem' pEnv3 hp3_2)))))))))⟩

theorem inl_dec_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 restStmts : List Lir.Stmt} {dst x : Lir.VReg} {xVal : Lir.Word}
    (hltFn : fr.fn < l.sourceCount)
    (hF : raw.funcs[fr.fn]? = some F)
    (hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = .call [dst] l.decWrapper [.v x] :: restStmts)
    (hposB : rawPos < B.body.size)
    (hgetB : B.body[rawPos] = .call [dst] l.decWrapper [.v x])
    (hx : fr.env[x]? = some xVal)
    (hxLt : x < freshBase F) :
    let inl := inlineProgram l raw
    ChunkPos l F b B (rawPos + 1) (fr.label + 5) 1 ∧
    ((inlineFunc l F).blocks[fr.label + 2]? =
      some { body := #[.call [] l.decProc [.v x]], term := .jump ⟨fr.label + 5, []⟩, cold := B.cold }) ∧
    (∃ jb, (inlineFunc l F).blocks[fr.label + 5]? = some jb ∧
      jb.params = [] ∧ 0 < jb.body.size ∧ jb.body[0]? = some (.assign dst (.arg (.imm 1)))) ∧
    match evalDecSite xVal mem with
    | .ok mem' =>
      ∃ env' s₁, Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₁ false ∧
      Sem.Star (Lir.semStep inl) s₁ 0
        { mem := mem', ctx, stack := { fr with label := fr.label + 5, pos := 1, env := env', dsts := [] } :: rest } ∧
      AgreeBelow (freshBase F) (fr.env.insert dst 1) env'
    | .free =>
      let pFr0 : Lir.Frame := { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal, dsts := [] }
      ∃ env' s₁, Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₁ false ∧
      Sem.Star (Lir.semStep inl) s₁ 1
        { mem, ctx, stack := pFr0 :: { fr with label := fr.label + 2, pos := 1, env := env', dsts := [] } :: rest } ∧
      AgreeBelow (freshBase F) fr.env env'
    | .stuck =>
      Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 .stuck := by
  intro inl
  have hc : classify l (.call [dst] l.decWrapper [.v x]) = some (.dec dst x) := by
    have hne : l.decWrapper ≠ l.incWrapper := by simp [Layout.decWrapper, Layout.incWrapper]
    simp [classify, hne]
  have cpNext : ChunkAt l F b B (rawPos + 1) (fr.label + 5) 1 (tmp + 2) [] [.assign dst (.arg (.imm 1))] restStmts := {
    bLookup := hcp.bLookup
    tmpGe := by have := hcp.tmpGe; omega
    split := by
      have htake : B.body.toList.take (rawPos + 1) =
          B.body.toList.take rawPos ++ [.call [dst] l.decWrapper [.v x]] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB, hgetB]; simp
      rw [htake, List.append_assoc]; simpa [hrest] using hcp.split
    posLe := by omega
    blocksMatch := fun k blk hk => by
      have h := hcp.blocksMatch (5 + k) blk (by
        rw [hrest]; unfold expandStmts; rw [hc]; dsimp only
        rw [Nat.add_comm 5 k]; exact hk)
      simpa [Nat.add_assoc] using h
    inPosEq := rfl
    endLbl := by
      have := hcp.endLbl
      rw [hrest, stmtsExtra_cons, stmtExtra, hc] at this
      simp only [siteExtra] at this
      dsimp only [Lir.Label] at this ⊢; omega }
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  have hb0 : (inlineFunc l F).blocks[fr.label]? = some {
      params, body := acc.reverse.toArray,
      term := .br .tnz .w64 (.v x) (.imm 1) ⟨fr.label + 5, []⟩ ⟨fr.label + 1, []⟩, cold := B.cold } := by
    simpa using hcp.blocksMatch 0 _ (by rw [hrest]; unfold expandStmts; rw [hc]; rfl)
  have hb1 : (inlineFunc l F).blocks[fr.label + 1]? = some {
      body := #[.assign tmp (.load .w32 .zero (cellAddr x 4))],
      term := .br .eq .w32 (.v tmp) (.imm 0) ⟨fr.label + 2, []⟩ ⟨fr.label + 3, []⟩, cold := B.cold } := by
    exact hcp.blocksMatch 1 _ (by rw [hrest]; unfold expandStmts; rw [hc]; rfl)
  have hb2 : (inlineFunc l F).blocks[fr.label + 2]? = some {
      body := #[.call [] l.decProc [.v x]],
      term := .jump ⟨fr.label + 5, []⟩, cold := B.cold } := by
    exact hcp.blocksMatch 2 _ (by rw [hrest]; unfold expandStmts; rw [hc]; rfl)
  have hb3 : (inlineFunc l F).blocks[fr.label + 3]? = some {
      body := #[],
      term := .br .slt .w32 (.v tmp) (.imm 0) ⟨fr.label + 5, []⟩ ⟨fr.label + 4, []⟩, cold := B.cold } := by
    exact hcp.blocksMatch 3 _ (by rw [hrest]; unfold expandStmts; rw [hc]; rfl)
  have hb4 : (inlineFunc l F).blocks[fr.label + 4]? = some {
      body := #[.assign (tmp + 1) (.bin .sub .w32 (.v tmp) (.imm 1)),
        .store .w32 (cellAddr x 4) (.v (tmp + 1))],
      term := .jump ⟨fr.label + 5, []⟩, cold := B.cold } := by
    exact hcp.blocksMatch 4 _ (by rw [hrest]; unfold expandStmts; rw [hc]; rfl)
  obtain ⟨jb, postJ, hj0, hjp, hjbody, _, _⟩ :=
    ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold restStmts
      (fr.label + 5) (tmp + 2) [] [.assign dst (.arg (.imm 1))]
  have hb5 : (inlineFunc l F).blocks[fr.label + 5]? = some jb := by
    simpa using cpNext.blocksMatch 0 jb hj0
  have hjbPos : 0 < jb.body.size := by
    have := congrArg List.length hjbody; simp at this; omega
  have hjbStmt : jb.body[0] = .assign dst (.arg (.imm 1)) := by
    have : jb.body.toList[0]? = some (.assign dst (.arg (.imm 1))) := by rw [hjbody]; simp
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hjbPos, Option.some.injEq] at this
    exact this
  refine ⟨⟨_, _, _, _, cpNext⟩, hb2, ⟨jb, hb5, hjp, hjbPos, by rw [Array.getElem?_eq_getElem hjbPos, hjbStmt]⟩, ?_⟩
  have hpos0 : fr.pos = acc.reverse.toArray.size := by simp [hcp.inPosEq]
  have hjoinStep : ∀ (m : X86.Memory) (envJ : Lir.Env),
      Sem.Star (Lir.semStep inl)
        { mem := m, ctx, stack := { fr with label := fr.label + 5, pos := 0, env := envJ } :: rest } 0
        { mem := m, ctx, stack := { fr with label := fr.label + 5, pos := 1, env := envJ.insert dst 1, dsts := [] } :: rest } := by
    intro m envJ
    have sj : Lir.semStep inl { mem := m, ctx, stack := { fr with label := fr.label + 5, pos := 0, env := envJ } :: rest } =
        .next { mem := m, ctx, stack := { fr with label := fr.label + 5, pos := 1, env := envJ.insert dst 1, dsts := [] } :: rest } false := by
      apply Lir.semStep_next.mpr
      have h1 := Lir.step_stmt (p := inl) (fr := { fr with label := fr.label + 5, pos := 0, env := envJ })
        (rest := rest) (mem := m) (ctx := ctx) (ρ' := envJ.insert dst 1) (mem' := m)
        hF' hb5 hjbPos hjbStmt rfl (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval])
      simpa [hdsts] using h1
    exact .free sj (.refl _)
  have htmpGt : (x : Nat) ≠ tmp := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxLt hcp.tmpGe)
  have htmp1Gt : (x : Nat) ≠ tmp + 1 := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxLt (by have := hcp.tmpGe; omega))
  unfold evalDecSite
  by_cases htag : Lir.Cond.holds .tnz .w64 xVal 1 = true
  · simp only [htag, ↓reduceIte]
    have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
        .next { mem, ctx, stack := { fr with label := fr.label + 5, pos := 0 } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term hF' hb0 hpos0]
      simp [Lir.Arg.eval, hx, htag, Lir.takeEdge, Lir.evalArgs, hb5, hjp, Lir.bindParams]
    exact ⟨fr.env.insert dst 1, _, s1, hjoinStep mem fr.env, AgreeBelow.refl⟩
  · have htagF : Lir.Cond.holds .tnz .w64 xVal 1 = false := by simpa using htag
    simp only [htagF, Bool.false_eq_true, ↓reduceIte]
    have s1 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
        .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } false := by
      apply Lir.semStep_next.mpr
      rw [Lir.step_term hF' hb0 hpos0]
      simp [Lir.Arg.eval, hx, htagF, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams]
    cases hload : Lir.loadWord mem .w32 .zero (xVal + Lir.dispWord 4) with
    | none =>
      dsimp only
      refine .free s1 (.final ?_)
      have hst : Lir.step inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } = .stuck := by
        unfold Lir.step
        simp [hF', hb1, cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell fr.env ctx x xVal 4 hx, hload]
      rw [Lir.semStep, hst]; exact .stuck
    | some cnt =>
      dsimp only
      let env1 := fr.env.insert tmp cnt
      have hx1 : env1[x]? = some xVal := by rw [Lir.env_insert_ne _ _ (Ne.symm htmpGt), hx]
      have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0 } :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fr with label := fr.label + 1, pos := 0 })
          hF' hb1 (by simp) rfl rfl
          (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell fr.env ctx x xVal 4 hx, hload, env1])
      by_cases hzero : (X86.Width.w32.truncate cnt).toNat = 0
      · simp only [hzero, ↓reduceIte]
        have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = true := by rw [w32_eq_zero]; simp [hzero]
        have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fr with label := fr.label + 1, pos := 1, env := env1 }) hF' hb1 rfl]
          simp [Lir.Arg.eval, env1, heq0, Lir.takeEdge, Lir.evalArgs, hb2, Lir.bindParams]
        have s4 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fn := l.decProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 xVal, dsts := [] } ::
              { fr with label := fr.label + 2, pos := 1, env := env1, dsts := [] } :: rest } true := by
          apply Lir.semStep_next.mpr
          exact Lir.step_call (fr := { fr with label := fr.label + 2, pos := 0, env := env1 })
            (vs := [xVal]) hF' hb2 (by simp) rfl
            (by simp [Lir.evalArgs, Lir.Arg.eval, hx1])
            (by simp [Lir.enter, inl, inlineProgram_decProc l raw hr, Rt.Rc.Gen.dec, Lir.bindParams])
        exact ⟨env1, _, s1, .free s2 (.free s3 (.charge s4 (.refl _))), AgreeBelow.refl.insert_ge hcp.tmpGe cnt⟩
      · simp only [hzero, ↓reduceIte]
        have heq0 : Lir.Cond.holds .eq .w32 cnt 0 = false := by rw [w32_eq_zero]; simp [hzero]
        have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } =
            .next { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fr with label := fr.label + 1, pos := 1, env := env1 }) hF' hb1 rfl]
          simp [Lir.Arg.eval, env1, heq0, Lir.takeEdge, Lir.evalArgs, hb3, Lir.bindParams]
        by_cases hneg : 2 ^ 31 ≤ (X86.Width.w32.truncate cnt).toNat
        · simp only [hneg, ↓reduceIte]
          have hslt : Lir.Cond.holds .slt .w32 cnt 0 = true := by rw [w32_signedValue_lt_zero]; simp [hneg]
          have s4 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0, env := env1 } :: rest } =
              .next { mem, ctx, stack := { fr with label := fr.label + 5, pos := 0, env := env1 } :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fr with label := fr.label + 3, pos := 0, env := env1 }) hF' hb3 rfl]
            simp [Lir.Arg.eval, env1, hslt, Lir.takeEdge, Lir.evalArgs, hb5, hjp, Lir.bindParams]
          exact ⟨env1.insert dst 1, _, s1, .free s2 (.free s3 (.free s4 (hjoinStep mem env1))),
            (AgreeBelow.refl.insert_ge hcp.tmpGe cnt).insert_same dst 1⟩
        · simp only [hneg, ↓reduceIte]
          have hslt : Lir.Cond.holds .slt .w32 cnt 0 = false := by rw [w32_signedValue_lt_zero]; simp [hneg]
          have s4 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0, env := env1 } :: rest } =
              .next { mem, ctx, stack := { fr with label := fr.label + 4, pos := 0, env := env1 } :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fr with label := fr.label + 3, pos := 0, env := env1 }) hF' hb3 rfl]
            simp [Lir.Arg.eval, env1, hslt, Lir.takeEdge, Lir.evalArgs, hb4, Lir.bindParams]
          let env2 := env1.insert (tmp + 1) (X86.Width.w32.truncate (cnt - 1))
          have hx2 : env2[x]? = some xVal := by rw [Lir.env_insert_ne _ _ (Ne.symm htmp1Gt), hx1]
          have s5 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 4, pos := 0, env := env1 } :: rest } =
              .next { mem, ctx, stack := { fr with label := fr.label + 4, pos := 1, env := env2 } :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fr with label := fr.label + 4, pos := 0, env := env1 })
              hF' hb4 (by simp) rfl rfl
              (by simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.BinOp.eval, Lir.Arg.eval, env1, env2])
          cases hw : mem.write? .w32 (xVal + Lir.dispWord 4) (X86.Width.w32.truncate (cnt - 1)) with
          | error e =>
            dsimp only
            refine .free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.final ?_)))))
            have hst : Lir.step inl { mem, ctx, stack := { fr with label := fr.label + 4, pos := 1, env := env2 } :: rest } = .stuck := by
              unfold Lir.step
              simp [hF', hb4, cellAddr, Lir.Stmt.exec, addr_cell env2 ctx x xVal 4 hx2, Lir.Arg.eval, env2, hw]
            rw [Lir.semStep, hst]; exact .stuck
          | ok mem' =>
            dsimp only
            have s6 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 4, pos := 1, env := env2 } :: rest } =
                .next { mem := mem', ctx, stack := { fr with label := fr.label + 4, pos := 2, env := env2 } :: rest } false := by
              apply Lir.semStep_next.mpr
              exact Lir.step_stmt (fr := { fr with label := fr.label + 4, pos := 1, env := env2 })
                hF' hb4 (by simp) rfl rfl
                (by simp [cellAddr, Lir.Stmt.exec, addr_cell env2 ctx x xVal 4 hx2, Lir.Arg.eval, env2, hw])
            have s7 : Lir.semStep inl { mem := mem', ctx, stack := { fr with label := fr.label + 4, pos := 2, env := env2 } :: rest } =
                .next { mem := mem', ctx, stack := { fr with label := fr.label + 5, pos := 0, env := env2 } :: rest } false := by
              apply Lir.semStep_next.mpr
              rw [Lir.step_term (fr := { fr with label := fr.label + 4, pos := 2, env := env2 }) hF' hb4 rfl]
              simp [Lir.takeEdge, Lir.evalArgs, hb5, hjp, Lir.bindParams]
            refine ⟨env2.insert dst 1, _, s1,
              .free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 (hjoinStep mem' env2)))))), ?_⟩
            exact ((AgreeBelow.refl.insert_ge hcp.tmpGe cnt).insert_ge (by have := hcp.tmpGe; omega) _).insert_same dst 1

/-! ## 3. `alloc` site execution (raw vs inlined) -/

theorem raw_alloc_exec {l : Layout} {raw : Lir.Program} (hr : RuntimeFuncs l raw)
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {dst : Lir.VReg} {idx : Nat} {c : Lam.CtorInfo}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg} {vals : List Lir.Word}
    (hF : raw.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B)
    (hpos : fr.pos < B.body.size)
    (hc : l.ctors[idx]? = some c)
    (hlay : lay = Rt.Rc.CellLayout.ofFields c.arity c.tag)
    (hcls : lay.cls? = some cls) (hok : lay.ok = true)
    (hlen : args.length = c.arity)
    (hstmt : B.body[fr.pos] = .call [dst] (l.allocWrapper idx) args)
    (hargs : Lir.evalArgs fr.env args = some vals) :
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
  have hvlen : vals.length = c.arity := by
    have := evalArgs_length hargs
    omega
  obtain ⟨wEnv, hwBind, _, hwLookup⟩ := bindParams_range_lookup c.arity 0 vals {} hvlen
  have hrange : List.range c.arity = List.range' 0 c.arity := List.range_eq_range'
  rw [← hrange] at hwBind
  have hwrapF := hr.allocWrap idx c hc
  have hprocF : raw.funcs[l.allocProc idx]? = some (Rt.Rc.Gen.allocFunc lay cls) := by
    have := hr.allocProc idx c hc
    rw [← hlay, Rt.Rc.Gen.alloc_eq hok hcls] at this
    exact this
  let caller' : Lir.Frame := { fr with pos := fr.pos + 1, dsts := [dst] }
  let wFr0 : Lir.Frame := { fn := l.allocWrapper idx, label := 0, pos := 0, env := wEnv }
  let wFr1 : Lir.Frame := { fn := l.allocWrapper idx, label := 0, pos := 1, env := wEnv, dsts := [c.arity] }
  let pFr0 : Lir.Frame := { fn := l.allocProc idx, label := 0, pos := 0, env := {} }
  have hstep1 : Lir.semStep raw { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := wFr0 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call hF hB hpos hstmt hargs
      (by simp [Lir.enter, hwrapF, allocationWrapper, hwBind, wFr0])
  have hstep2 : Lir.semStep raw { mem, ctx, stack := wFr0 :: caller' :: rest } =
      .next { mem, ctx, stack := pFr0 :: wFr1 :: caller' :: rest } true := by
    apply Lir.semStep_next.mpr
    exact Lir.step_call (fr := wFr0) (rs := [c.arity]) (g := l.allocProc idx) (as := []) (vs := [])
      hwrapF rfl (by simp [allocationWrapper, wFr0]) (by simp [allocationWrapper, wFr0])
      (by simp [Lir.evalArgs])
      (by simp [Lir.enter, hprocF, Rt.Rc.Gen.allocFunc, Lir.bindParams, pFr0])
  let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
  have hfinish : ∀ (addr : Lir.Word) (mem₁ : X86.Memory) (envP : Lir.Env),
      match mem₁.write? .w64 (addr + Lir.dispWord 0) hdr with
      | .error _ =>
        Sem.Reaches (Lir.semStep raw)
          { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := envP.insert 5 addr } :: wFr1 :: caller' :: rest } 0 .stuck
      | .ok mem₂ =>
        match writeFieldsMem mem₂ addr 0 vals with
        | some mem' =>
          Sem.Star (Lir.semStep raw)
            { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := envP.insert 5 addr } :: wFr1 :: caller' :: rest } 0
            { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst addr, dsts := [] } :: rest }
        | none =>
          Sem.Reaches (Lir.semStep raw)
            { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := envP.insert 5 addr } :: wFr1 :: caller' :: rest } 0 .stuck := by
    intro addr mem₁ envP
    cases hwH : mem₁.write? .w64 (addr + Lir.dispWord 0) hdr with
    | error _ =>
      dsimp only
      apply Sem.Reaches.final
      have hst : Lir.step raw { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := envP.insert 5 addr } :: wFr1 :: caller' :: rest } = .stuck := by
        unfold Lir.step
        simp [hprocF, Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec,
          addr_cell (envP.insert 5 addr) ctx 5 addr 0 (by simp), Lir.Arg.eval, hdr, hwH]
      rw [Lir.semStep, hst]; exact .stuck
    | ok mem₂ =>
      dsimp only
      have s5_0 : Lir.semStep raw
          { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := envP.insert 5 addr } :: wFr1 :: caller' :: rest } =
          .next { mem := mem₂, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 1, env := envP.insert 5 addr } :: wFr1 :: caller' :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fn := l.allocProc idx, label := 5, pos := 0, env := envP.insert 5 addr })
          hprocF (by rfl) (by simp [Rt.Rc.Gen.allocFunc]) rfl rfl
          (by simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec,
            addr_cell (envP.insert 5 addr) ctx 5 addr 0 (by simp), Lir.Arg.eval, hdr, hwH])
      have s5_1 : Lir.semStep raw
          { mem := mem₂, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 1, env := envP.insert 5 addr } :: wFr1 :: caller' :: rest } =
          .next { mem := mem₂, ctx, stack := { fn := l.allocWrapper idx, label := 0, pos := 1, env := wEnv.insert c.arity addr, dsts := [] } :: caller' :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 5, pos := 1, env := envP.insert 5 addr }) hprocF (by rfl) (by rfl)]
        simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams, wFr1]
      have hstores := exec_allocWrapper_stores (p := raw) (wrap := l.allocWrapper idx)
        (proc := l.allocProc idx) (fields := c.arity) (addr := addr) (ctx := ctx)
        (rest := caller' :: rest) (env := wEnv.insert c.arity addr)
        hwrapF (by simp) (j := 0) (vals := vals) (mem := mem₂) (by omega)
        (fun i hi => by
          rw [Nat.zero_add, Lir.env_insert_ne _ _ (by omega)]
          simpa using hwLookup i (by omega))
      cases hwf : writeFieldsMem mem₂ addr 0 vals with
      | none =>
        rw [hwf] at hstores
        exact .free s5_0 (.free s5_1 hstores)
      | some mem' =>
        rw [hwf] at hstores
        have sRet : Lir.semStep raw
            { mem := mem', ctx, stack := { fn := l.allocWrapper idx, label := 0, pos := 1 + c.arity, env := wEnv.insert c.arity addr, dsts := [] } :: caller' :: rest } =
            .next { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := fr.env.insert dst addr, dsts := [] } :: rest } false := by
          apply Lir.semStep_next.mpr
          rw [Lir.step_term (fr := { fn := l.allocWrapper idx, label := 0, pos := 1 + c.arity, env := wEnv.insert c.arity addr, dsts := [] })
            hwrapF rfl (by simp [allocationWrapper]; omega)]
          simp [allocationWrapper, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams, caller']
        exact .free s5_0 (.free s5_1 (hstores.trans (.free sRet (.refl _))))
  unfold evalAllocReserve
  dsimp only
  cases hload0 : Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord (Int.ofNat (8 * cls))) with
  | none =>
    dsimp only
    refine .charge hstep1 (.charge hstep2 (.final ?_))
    have hst : Lir.step raw { mem, ctx, stack := pFr0 :: wFr1 :: caller' :: rest } = .stuck := by
      unfold Lir.step
      have h0 : (Rt.Rc.Gen.allocFunc lay cls).blocks[0]? = some (Rt.Rc.Gen.allocFunc lay cls).blocks[0]! := rfl
      have hlt0 : 0 < (Rt.Rc.Gen.allocFunc lay cls).blocks[0]!.body.size := by simp [Rt.Rc.Gen.allocFunc]
      have hget0 : (Rt.Rc.Gen.allocFunc lay cls).blocks[0]!.body[0] =
          .assign 0 (.load .w64 .zero (Rt.Rc.Procs.ctx (Int.ofNat (8 * cls)))) := rfl
      simp only [hprocF, pFr0, h0, hlt0, ↓reduceDIte, hget0,
        Lir.Stmt.exec, Lir.Rhs.eval, Rt.Rc.Procs.ctx, addr_ctx, Option.bind_eq_bind, Option.bind_some,
        Option.bind_none, hload0]
    rw [Lir.semStep, hst]; exact .stuck
  | some p0 =>
    dsimp only
    let e0 : Lir.Env := ({} : Lir.Env).insert 0 p0
    have s0 : Lir.semStep raw { mem, ctx, stack := pFr0 :: wFr1 :: caller' :: rest } =
        .next { mem, ctx, stack := { fn := l.allocProc idx, label := 0, pos := 1, env := e0 } :: wFr1 :: caller' :: rest } false := by
      apply Lir.semStep_next.mpr
      have hlt0 : 0 < (Rt.Rc.Gen.allocFunc lay cls).blocks[0]!.body.size := by simp [Rt.Rc.Gen.allocFunc]
      have hget0 : (Rt.Rc.Gen.allocFunc lay cls).blocks[0]!.body[0]'hlt0 =
          .assign 0 (.load .w64 .zero (Rt.Rc.Procs.ctx (Int.ofNat (8 * cls)))) := rfl
      exact Lir.step_stmt (fr := pFr0) (B := (Rt.Rc.Gen.allocFunc lay cls).blocks[0]!)
        hprocF rfl hlt0 hget0 rfl
        (by simp only [Rt.Rc.Procs.ctx, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx,
          Option.bind_eq_bind, Option.bind_some, hload0, pFr0, e0])
    by_cases hp0 : Lir.Cond.holds .eq .w64 p0 0 = true
    · simp only [hp0, ↓reduceIte]
      have s1 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 0, pos := 1, env := e0 } :: wFr1 :: caller' :: rest } =
          .next { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 0, env := e0 } :: wFr1 :: caller' :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 0, pos := 1, env := e0 }) hprocF (by rfl) (by rfl)]
        simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
          e0, hp0, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
      cases hlb : Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord Rt.bumpOff) with
      | none =>
        dsimp only
        refine .charge hstep1 (.charge hstep2 (.free s0 (.free s1 (.final ?_))))
        have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 0, env := e0 } :: wFr1 :: caller' :: rest } = .stuck := by
          unfold Lir.step
          simp [hprocF, Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hlb]
        rw [Lir.semStep, hst]; exact .stuck
      | some b0 =>
        dsimp only
        let e2 := e0.insert 2 b0
        have s2 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 0, env := e0 } :: wFr1 :: caller' :: rest } =
            .next { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 1, env := e2 } :: wFr1 :: caller' :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fn := l.allocProc idx, label := 2, pos := 0, env := e0 })
            hprocF (by rfl) (by simp [Rt.Rc.Gen.allocFunc]) rfl rfl
            (by simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hlb, e2])
        cases hll : Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord Rt.limitOff) with
        | none =>
          dsimp only
          refine .charge hstep1 (.charge hstep2 (.free s0 (.free s1 (.free s2 (.final ?_)))))
          have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 1, env := e2 } :: wFr1 :: caller' :: rest } = .stuck := by
            unfold Lir.step
            simp [hprocF, Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hll]
          rw [Lir.semStep, hst]; exact .stuck
        | some lim =>
          dsimp only
          let e3 := e2.insert 3 lim
          have he3_2 : e3[2]? = some b0 := by rw [Lir.env_insert_ne _ _ (by decide)]; simp [e2]
          have s3 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 1, env := e2 } :: wFr1 :: caller' :: rest } =
              .next { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 2, env := e3 } :: wFr1 :: caller' :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fn := l.allocProc idx, label := 2, pos := 1, env := e2 })
              hprocF (by rfl) (by simp [Rt.Rc.Gen.allocFunc]) rfl rfl
              (by simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hll, e3])
          cases hovf : Lir.Ovf.eval .addC b0 (UInt64.ofNat (Rt.Rc.classBytes cls)) with
          | mk b1 ovf =>
            dsimp only
            let e4 := e3.insert 4 b1
            cases ovf with
            | true =>
              simp only [↓reduceIte]
              have s4 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 2, env := e3 } :: wFr1 :: caller' :: rest } =
                  .next { mem, ctx, stack := { fn := l.allocProc idx, label := 6, pos := 0, env := e4 } :: wFr1 :: caller' :: rest } false := by
                apply Lir.semStep_next.mpr
                rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 2, pos := 2, env := e3 }) hprocF (by rfl) (by rfl)]
                simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
                  he3_2, hovf, Lir.takeEdge, Lir.evalArgs, Lir.bindParams, e4]
              refine .charge hstep1 (.charge hstep2 (.free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.final ?_)))))))
              have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 6, pos := 0, env := e4 } :: wFr1 :: caller' :: rest } = .fail .heap := by
                rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 6, pos := 0, env := e4 }) hprocF (by rfl) (by rfl)]; rfl
              rw [Lir.semStep, hst]; exact .fail
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              have s4 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 2, env := e3 } :: wFr1 :: caller' :: rest } =
                  .next { mem, ctx, stack := { fn := l.allocProc idx, label := 3, pos := 0, env := e4 } :: wFr1 :: caller' :: rest } false := by
                apply Lir.semStep_next.mpr
                rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 2, pos := 2, env := e3 }) hprocF (by rfl) (by rfl)]
                simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
                  he3_2, hovf, Lir.takeEdge, Lir.evalArgs, Lir.bindParams, e4]
              have he4_3 : e4[3]? = some lim := by rw [Lir.env_insert_ne _ _ (by decide)]; simp [e3]
              have he4_2 : e4[2]? = some b0 := by rw [Lir.env_insert_ne _ _ (by decide), he3_2]
              by_cases hule : Lir.Cond.holds .ule .w64 b1 lim = true
              · simp only [hule, ↓reduceIte]
                have s5 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 3, pos := 0, env := e4 } :: wFr1 :: caller' :: rest } =
                    .next { mem, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 0, env := e4 } :: wFr1 :: caller' :: rest } false := by
                  apply Lir.semStep_next.mpr
                  rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 3, pos := 0, env := e4 }) hprocF (by rfl) (by rfl)]
                  simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.to, Lir.Arg.eval,
                    e4, he4_3, hule, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
                cases hwb : mem.write? .w64 (ctx + Lir.dispWord Rt.bumpOff) b1 with
                | error _ =>
                  dsimp only
                  refine .charge hstep1 (.charge hstep2 (.free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.final ?_))))))))
                  have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 0, env := e4 } :: wFr1 :: caller' :: rest } = .stuck := by
                    unfold Lir.step
                    simp [hprocF, Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Rt.Rc.Procs.v, Lir.Stmt.exec,
                      addr_ctx, Lir.Arg.eval, e4, hwb]
                  rw [Lir.semStep, hst]; exact .stuck
                | ok mem₁ =>
                  dsimp only
                  have s6 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 0, env := e4 } :: wFr1 :: caller' :: rest } =
                      .next { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 1, env := e4 } :: wFr1 :: caller' :: rest } false := by
                    apply Lir.semStep_next.mpr
                    exact Lir.step_stmt (fr := { fn := l.allocProc idx, label := 4, pos := 0, env := e4 })
                      hprocF (by rfl) (by simp [Rt.Rc.Gen.allocFunc]) rfl rfl
                      (by simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.ctx, Rt.Rc.Procs.v, Lir.Stmt.exec,
                        addr_ctx, Lir.Arg.eval, e4, hwb])
                  have s7 : Lir.semStep raw { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 1, env := e4 } :: wFr1 :: caller' :: rest } =
                      .next { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := e4.insert 5 b0 } :: wFr1 :: caller' :: rest } false := by
                    apply Lir.semStep_next.mpr
                    rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 4, pos := 1, env := e4 }) hprocF (by rfl) (by rfl)]
                    simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.to, Lir.Arg.eval,
                      he4_2, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
                  have hf := hfinish b0 mem₁ e4
                  cases hwH : mem₁.write? .w64 (b0 + Lir.dispWord 0) hdr with
                  | error _ =>
                    dsimp only; rw [hwH] at hf; dsimp only at hf
                    exact .charge hstep1 (.charge hstep2 (.free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 hf)))))))))
                  | ok mem₂ =>
                    dsimp only; rw [hwH] at hf; dsimp only at hf
                    cases hwf : writeFieldsMem mem₂ b0 0 vals with
                    | none =>
                      dsimp only; rw [hwf] at hf
                      exact .charge hstep1 (.charge hstep2 (.free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 hf)))))))))
                    | some mem' =>
                      dsimp only; rw [hwf] at hf
                      exact ⟨_, hstep1, .charge hstep2 (.free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 hf))))))))⟩
              · have huleF : Lir.Cond.holds .ule .w64 b1 lim = false := by simpa using hule
                simp only [huleF, Bool.false_eq_true, ↓reduceIte]
                have s5 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 3, pos := 0, env := e4 } :: wFr1 :: caller' :: rest } =
                    .next { mem, ctx, stack := { fn := l.allocProc idx, label := 6, pos := 0, env := e4 } :: wFr1 :: caller' :: rest } false := by
                  apply Lir.semStep_next.mpr
                  rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 3, pos := 0, env := e4 }) hprocF (by rfl) (by rfl)]
                  simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.to, Lir.Arg.eval,
                    e4, he4_3, huleF, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
                refine .charge hstep1 (.charge hstep2 (.free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.final ?_))))))))
                have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 6, pos := 0, env := e4 } :: wFr1 :: caller' :: rest } = .fail .heap := by
                  rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 6, pos := 0, env := e4 }) hprocF (by rfl) (by rfl)]; rfl
                rw [Lir.semStep, hst]; exact .fail
    · have hp0F : Lir.Cond.holds .eq .w64 p0 0 = false := by simpa using hp0
      simp only [hp0F, Bool.false_eq_true, ↓reduceIte]
      have s1 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 0, pos := 1, env := e0 } :: wFr1 :: caller' :: rest } =
          .next { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 0, env := e0 } :: wFr1 :: caller' :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 0, pos := 1, env := e0 }) hprocF (by rfl) (by rfl)]
        simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.i, Rt.Rc.Procs.to, Lir.Arg.eval,
          e0, hp0F, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
      cases hlp1 : Lir.loadWord mem .w64 .zero (p0 + Lir.dispWord 0) with
      | none =>
        dsimp only
        refine .charge hstep1 (.charge hstep2 (.free s0 (.free s1 (.final ?_))))
        have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 0, env := e0 } :: wFr1 :: caller' :: rest } = .stuck := by
          unfold Lir.step
          simp [hprocF, Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
            addr_cell e0 ctx 0 p0 0 (by simp [e0]), hlp1]
        rw [Lir.semStep, hst]; exact .stuck
      | some p1 =>
        dsimp only
        let e1 := e0.insert 1 p1
        have he1_0 : e1[0]? = some p0 := by rw [Lir.env_insert_ne _ _ (by decide)]; simp [e0]
        have s2 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 0, env := e0 } :: wFr1 :: caller' :: rest } =
            .next { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 1, env := e1 } :: wFr1 :: caller' :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fn := l.allocProc idx, label := 1, pos := 0, env := e0 })
            hprocF (by rfl) (by simp [Rt.Rc.Gen.allocFunc]) rfl rfl
            (by simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
              addr_cell e0 ctx 0 p0 0 (by simp [e0]), hlp1, e1])
        cases hwh : mem.write? .w64 (ctx + Lir.dispWord (Int.ofNat (8 * cls))) p1 with
        | error _ =>
          dsimp only
          refine .charge hstep1 (.charge hstep2 (.free s0 (.free s1 (.free s2 (.final ?_)))))
          have hst : Lir.step raw { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 1, env := e1 } :: wFr1 :: caller' :: rest } = .stuck := by
            unfold Lir.step
            have h1 : (Rt.Rc.Gen.allocFunc lay cls).blocks[1]? = some (Rt.Rc.Gen.allocFunc lay cls).blocks[1]! := rfl
            have hlt1 : 1 < (Rt.Rc.Gen.allocFunc lay cls).blocks[1]!.body.size := by simp [Rt.Rc.Gen.allocFunc]
            have hget1 : (Rt.Rc.Gen.allocFunc lay cls).blocks[1]!.body[1] =
                .store .w64 (Rt.Rc.Procs.ctx (Int.ofNat (8 * cls))) (Rt.Rc.Procs.v 1) := rfl
            simp only [hprocF, h1, hlt1, ↓reduceDIte, hget1, Lir.Stmt.exec, Rt.Rc.Procs.ctx,
              Rt.Rc.Procs.v, addr_ctx, Lir.Arg.eval, Option.bind_eq_bind, Option.bind_some,
              e1, Lir.env_insert_self, hwh]
          rw [Lir.semStep, hst]; exact .stuck
        | ok mem₁ =>
          dsimp only
          have s3 : Lir.semStep raw { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 1, env := e1 } :: wFr1 :: caller' :: rest } =
              .next { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 2, env := e1 } :: wFr1 :: caller' :: rest } false := by
            apply Lir.semStep_next.mpr
            have hlt1 : 1 < (Rt.Rc.Gen.allocFunc lay cls).blocks[1]!.body.size := by simp [Rt.Rc.Gen.allocFunc]
            have hget1 : (Rt.Rc.Gen.allocFunc lay cls).blocks[1]!.body[1]'hlt1 =
                .store .w64 (Rt.Rc.Procs.ctx (Int.ofNat (8 * cls))) (Rt.Rc.Procs.v 1) := rfl
            exact Lir.step_stmt (fr := { fn := l.allocProc idx, label := 1, pos := 1, env := e1 })
              (B := (Rt.Rc.Gen.allocFunc lay cls).blocks[1]!)
              hprocF rfl hlt1 hget1 rfl
              (by simp only [Rt.Rc.Procs.ctx, Rt.Rc.Procs.v, Lir.Stmt.exec,
                addr_ctx, Lir.Arg.eval, Option.bind_eq_bind, Option.bind_some, e1, Lir.env_insert_self, hwh])
          have s4 : Lir.semStep raw { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 2, env := e1 } :: wFr1 :: caller' :: rest } =
              .next { mem := mem₁, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := e1.insert 5 p0 } :: wFr1 :: caller' :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fn := l.allocProc idx, label := 1, pos := 2, env := e1 }) hprocF (by rfl) (by rfl)]
            simp [Rt.Rc.Gen.allocFunc, Rt.Rc.Procs.v, Rt.Rc.Procs.to, Lir.Arg.eval,
              he1_0, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
          have hf := hfinish p0 mem₁ e1
          cases hwH : mem₁.write? .w64 (p0 + Lir.dispWord 0) hdr with
          | error _ =>
            dsimp only; rw [hwH] at hf; dsimp only at hf
            exact .charge hstep1 (.charge hstep2 (.free s0 (.free s1 (.free s2 (.free s3 (.free s4 hf))))))
          | ok mem₂ =>
            dsimp only; rw [hwH] at hf; dsimp only at hf
            cases hwf : writeFieldsMem mem₂ p0 0 vals with
            | none =>
              dsimp only; rw [hwf] at hf
              exact .charge hstep1 (.charge hstep2 (.free s0 (.free s1 (.free s2 (.free s3 (.free s4 hf))))))
            | some mem' =>
              dsimp only; rw [hwf] at hf
              exact ⟨_, hstep1, .charge hstep2 (.free s0 (.free s1 (.free s2 (.free s3 (.free s4 hf)))))⟩

theorem inl_alloc_exec {l : Layout} {raw : Lir.Program}
    {F : Lir.Func} {B : Lir.Block} {fr : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Lir.Word} {b rawPos tmp : Nat} {params : List Lir.VReg}
    {acc rest0 restStmts : List Lir.Stmt} {dst : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat} {args : List Lir.Arg} {vals : List Lir.Word}
    (hltFn : fr.fn < l.sourceCount)
    (hF : raw.funcs[fr.fn]? = some F)
    (hdsts : fr.dsts = [])
    (hcp : ChunkAt l F b B rawPos fr.label fr.pos tmp params acc rest0)
    (hrest : rest0 = .call [dst] (l.allocWrapper idx) args :: restStmts)
    (hclsSite : classify l (.call [dst] (l.allocWrapper idx) args) = some (.alloc dst idx lay cls args))
    (hposB : rawPos < B.body.size)
    (hgetB : B.body[rawPos] = .call [dst] (l.allocWrapper idx) args)
    (hargs : Lir.evalArgs fr.env args = some vals)
    (hargsLt : argsMax args 0 < freshBase F) :
    let inl := inlineProgram l raw
    ChunkPos l F b B (rawPos + 1) (fr.label + 6) (1 + args.length) ∧
    match evalAllocReserve lay cls mem ctx with
    | .ok addr mem₂ =>
      match writeFieldsMem mem₂ addr 0 vals with
      | some mem' =>
        ∃ env' s₁, Lir.semStep inl { mem, ctx, stack := fr :: rest } = .next s₁ false ∧
        Sem.Star (Lir.semStep inl) s₁ 0
          { mem := mem', ctx, stack := { fr with label := fr.label + 6, pos := 1 + args.length, env := env', dsts := [] } :: rest } ∧
        AgreeBelow (freshBase F) (fr.env.insert dst addr) env'
      | none =>
        Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 .stuck
    | .oom =>
      Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 (.resource .heap)
    | .stuck =>
      Sem.Reaches (Lir.semStep inl) { mem, ctx, stack := fr :: rest } 0 .stuck := by
  intro inl
  obtain ⟨c, _, _, _, _, _, _, hnoDst⟩ := classify_eq_alloc hclsSite
  let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
  let pubInit : List Lir.Stmt :=
    Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr) :: mkFieldStores dst 0 args
  have hpubLen : pubInit.reverse.length = 1 + args.length := by
    simp [pubInit, mkFieldStores_length]; omega
  have cpNext : ChunkAt l F b B (rawPos + 1) (fr.label + 6) (1 + args.length) (tmp + 5) [dst]
      pubInit.reverse restStmts := {
    bLookup := hcp.bLookup
    tmpGe := by have := hcp.tmpGe; omega
    split := by
      have htake : B.body.toList.take (rawPos + 1) =
          B.body.toList.take rawPos ++ [.call [dst] (l.allocWrapper idx) args] := by
        rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hposB, hgetB]; simp
      rw [htake, List.append_assoc]; simpa [hrest] using hcp.split
    posLe := by omega
    blocksMatch := fun k blk hk => by
      have h := hcp.blocksMatch (6 + k) blk (by
        rw [hrest]; unfold expandStmts; rw [hclsSite]; dsimp only
        rw [Nat.add_comm 6 k]; exact hk)
      simpa [Nat.add_assoc] using h
    inPosEq := by omega
    endLbl := by
      have := hcp.endLbl
      rw [hrest, stmtsExtra_cons, stmtExtra, hclsSite] at this
      simp only [siteExtra] at this
      dsimp only [Lir.Label] at this ⊢; omega }
  refine ⟨⟨_, _, _, _, cpNext⟩, ?_⟩
  have hF' : inl.funcs[fr.fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_lt l raw hltFn, hF]; rfl
  let headOff := Int.ofNat (8 * cls)
  let bytes := UInt64.ofNat (Rt.Rc.classBytes cls)
  have hb0 : (inlineFunc l F).blocks[fr.label]? = some {
      params,
      body := (Lir.Stmt.assign tmp (.load .w64 .zero (ctxAddr headOff)) :: acc).reverse.toArray,
      term := .br .eq .w64 (.v tmp) (.imm 0) ⟨fr.label + 2, []⟩ ⟨fr.label + 1, []⟩,
      cold := B.cold } := by
    have h0 := hcp.blocksMatch 0 {
        params,
        body := (Lir.Stmt.assign tmp (.load .w64 .zero (ctxAddr headOff)) :: acc).reverse.toArray,
        term := .br .eq .w64 (.v tmp) (.imm 0) ⟨fr.label + 2, []⟩ ⟨fr.label + 1, []⟩,
        cold := B.cold } (by rw [hrest]; unfold expandStmts; rw [hclsSite]; rfl)
    simpa using h0
  have hb1 : (inlineFunc l F).blocks[fr.label + 1]? = some {
      body := #[.assign (tmp + 1) (.load .w64 .zero (cellAddr tmp)),
        .store .w64 (ctxAddr headOff) (.v (tmp + 1))],
      term := .jump ⟨fr.label + 6, [.v tmp]⟩, cold := B.cold } := by
    exact hcp.blocksMatch 1 _ (by rw [hrest]; unfold expandStmts; rw [hclsSite]; rfl)
  have hb2 : (inlineFunc l F).blocks[fr.label + 2]? = some {
      body := #[.assign (tmp + 2) (.load .w64 .zero (ctxAddr Rt.bumpOff)),
        .assign (tmp + 3) (.load .w64 .zero (ctxAddr Rt.limitOff))],
      term := .brOvf .addC (tmp + 4) (.v (tmp + 2)) (.imm bytes) ⟨fr.label + 3, []⟩ ⟨fr.label + 5, []⟩,
      cold := B.cold } := by
    exact hcp.blocksMatch 2 _ (by rw [hrest]; unfold expandStmts; rw [hclsSite]; rfl)
  have hb3 : (inlineFunc l F).blocks[fr.label + 3]? = some {
      body := #[],
      term := .br .ule .w64 (.v (tmp + 4)) (.v (tmp + 3)) ⟨fr.label + 4, []⟩ ⟨fr.label + 5, []⟩,
      cold := B.cold } := by
    exact hcp.blocksMatch 3 _ (by rw [hrest]; unfold expandStmts; rw [hclsSite]; rfl)
  have hb4 : (inlineFunc l F).blocks[fr.label + 4]? = some {
      body := #[.store .w64 (ctxAddr Rt.bumpOff) (.v (tmp + 4))],
      term := .jump ⟨fr.label + 6, [.v (tmp + 2)]⟩, cold := B.cold } := by
    exact hcp.blocksMatch 4 _ (by rw [hrest]; unfold expandStmts; rw [hclsSite]; rfl)
  have hb5 : (inlineFunc l F).blocks[fr.label + 5]? = some {
      body := #[], term := .fail .heap, cold := true } := by
    exact hcp.blocksMatch 5 _ (by rw [hrest]; unfold expandStmts; rw [hclsSite]; rfl)
  obtain ⟨jb, postJ, hj0, hjp, hjbody, _, _⟩ :=
    ChunkPos.firstBlock_of_expandStmts l (newLabel l F) B.term B.cold restStmts
      (fr.label + 6) (tmp + 5) [dst] pubInit.reverse
  have hb6 : (inlineFunc l F).blocks[fr.label + 6]? = some jb := by
    simpa using cpNext.blocksMatch 0 jb hj0
  have hjbody' : jb.body.toList = [.store .w64 (cellAddr dst) (.imm hdr)] ++ mkFieldStores dst 0 args ++ postJ := by
    simpa [pubInit, List.reverse_reverse, List.append_assoc] using hjbody
  have hjbPos0 : 0 < jb.body.size := by
    have := congrArg List.length hjbody'
    simp only [Array.length_toList, List.length_append, List.length_cons] at this
    omega
  have hjbStmt0 : jb.body[0] = .store .w64 (cellAddr dst) (.imm hdr) := by
    have : jb.body.toList[0]? = some (.store .w64 (cellAddr dst) (.imm hdr)) := by rw [hjbody']; simp
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hjbPos0, Option.some.injEq] at this
    exact this
  have hpos0Lt : fr.pos < (Lir.Stmt.assign tmp (.load .w64 .zero (ctxAddr headOff)) :: acc).reverse.toArray.size := by
    simp [hcp.inPosEq]
  have hget0 : (Lir.Stmt.assign tmp (.load .w64 .zero (ctxAddr headOff)) :: acc).reverse.toArray[fr.pos] =
      .assign tmp (.load .w64 .zero (ctxAddr headOff)) := by
    have : (Lir.Stmt.assign tmp (.load .w64 .zero (ctxAddr headOff)) :: acc).reverse.toArray[fr.pos]? =
        some (.assign tmp (.load .w64 .zero (ctxAddr headOff))) := by
      rw [← Array.getElem?_toList, List.toList_toArray, List.reverse_cons, hcp.inPosEq,
        List.getElem?_append_right (by simp), List.length_reverse]
      simp
    rwa [Array.getElem?_eq_getElem hpos0Lt, Option.some.injEq] at this
  have hpos0End : fr.pos + 1 = (Lir.Stmt.assign tmp (.load .w64 .zero (ctxAddr headOff)) :: acc).reverse.toArray.size := by
    simp [hcp.inPosEq]
  have hpubRun : ∀ (addr : Lir.Word) (mem₁ : X86.Memory) (envP : Lir.Env),
      AgreeBelow (freshBase F) fr.env envP →
      match mem₁.write? .w64 (addr + Lir.dispWord 0) hdr with
      | .error _ =>
        Sem.Reaches (Lir.semStep inl)
          { mem := mem₁, ctx, stack := { fr with label := fr.label + 6, pos := 0, env := envP.insert dst addr, dsts := [] } :: rest } 0 .stuck
      | .ok mem₂ =>
        match writeFieldsMem mem₂ addr 0 vals with
        | some mem' =>
          Sem.Star (Lir.semStep inl)
            { mem := mem₁, ctx, stack := { fr with label := fr.label + 6, pos := 0, env := envP.insert dst addr, dsts := [] } :: rest } 0
            { mem := mem', ctx, stack := { fr with label := fr.label + 6, pos := 1 + args.length, env := envP.insert dst addr, dsts := [] } :: rest }
        | none =>
          Sem.Reaches (Lir.semStep inl)
            { mem := mem₁, ctx, stack := { fr with label := fr.label + 6, pos := 0, env := envP.insert dst addr, dsts := [] } :: rest } 0 .stuck := by
    intro addr mem₁ envP hagP
    have hargsP : Lir.evalArgs (envP.insert dst addr) args = some vals := by
      rw [evalArgs_insert_not_mem (argsContainVReg_false hnoDst), ← hagP.evalArgs_eq hargsLt, hargs]
    cases hwH : mem₁.write? .w64 (addr + Lir.dispWord 0) hdr with
    | error _ =>
      dsimp only
      apply Sem.Reaches.final
      have hst : Lir.step inl { mem := mem₁, ctx, stack := { fr with label := fr.label + 6, pos := 0, env := envP.insert dst addr, dsts := [] } :: rest } = .stuck := by
        unfold Lir.step
        simp [hF', hb6, hjbPos0, hjbStmt0, cellAddr, Lir.Stmt.exec,
          addr_cell (envP.insert dst addr) ctx dst addr 0 (by simp), Lir.Arg.eval, hwH]
      rw [Lir.semStep, hst]; exact .stuck
    | ok mem₂ =>
      dsimp only
      have sH : Lir.semStep inl
          { mem := mem₁, ctx, stack := { fr with label := fr.label + 6, pos := 0, env := envP.insert dst addr, dsts := [] } :: rest } =
          .next { mem := mem₂, ctx, stack := { fr with label := fr.label + 6, pos := 1, env := envP.insert dst addr, dsts := [] } :: rest } false := by
        apply Lir.semStep_next.mpr
        exact Lir.step_stmt (fr := { fr with label := fr.label + 6, pos := 0, env := envP.insert dst addr, dsts := [] })
          hF' hb6 hjbPos0 hjbStmt0 rfl
          (by simp [cellAddr, Lir.Stmt.exec, addr_cell (envP.insert dst addr) ctx dst addr 0 (by simp), Lir.Arg.eval, hwH])
      have hst := exec_mkFieldStores (p := inl) (F := inlineFunc l F) (B := jb)
        (fn := fr.fn) (lbl := fr.label + 6) (dst := dst) (addr := addr) (ctx := ctx)
        (rest := rest) (env := envP.insert dst addr)
        hF' hb6 (by simp) (pre := [.store .w64 (cellAddr dst) (.imm hdr)]) (post := postJ)
        (j := 0) (args := args) (vals := vals) (mem := mem₂) hjbody' hargsP
      cases hwf : writeFieldsMem mem₂ addr 0 vals with
      | none =>
        rw [hwf] at hst
        exact .free sH (by simpa using hst)
      | some mem' =>
        rw [hwf] at hst
        exact .free sH (by simpa using hst)
  unfold evalAllocReserve
  dsimp only
  cases hload0 : Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord headOff) with
  | none =>
    dsimp only
    apply Sem.Reaches.final
    have hst : Lir.step inl { mem, ctx, stack := fr :: rest } = .stuck := by
      unfold Lir.step
      simp only [hF', hb0, hpos0Lt, ↓reduceDIte, hget0]
      simp only [ctxAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, Option.bind_eq_bind,
        Option.bind_some, Option.bind_none, hload0]
    rw [Lir.semStep, hst]; exact .stuck
  | some p0 =>
    dsimp only
    let env0 := fr.env.insert tmp p0
    have hag0 : AgreeBelow (freshBase F) fr.env env0 := AgreeBelow.refl.insert_ge hcp.tmpGe p0
    have s0 : Lir.semStep inl { mem, ctx, stack := fr :: rest } =
        .next { mem, ctx, stack := { fr with pos := fr.pos + 1, env := env0 } :: rest } false := by
      apply Lir.semStep_next.mpr
      exact Lir.step_stmt hF' hb0 hpos0Lt hget0 rfl
        (by simp [ctxAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hload0, env0])
    by_cases hp0 : Lir.Cond.holds .eq .w64 p0 0 = true
    · simp only [hp0, ↓reduceIte]
      have s1 : Lir.semStep inl { mem, ctx, stack := { fr with pos := fr.pos + 1, env := env0 } :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0, env := env0 } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fr with pos := fr.pos + 1, env := env0 }) hF' hb0 hpos0End]
        simp [Lir.Arg.eval, env0, hp0, Lir.takeEdge, Lir.evalArgs, hb2, Lir.bindParams]
      cases hlb : Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord Rt.bumpOff) with
      | none =>
        dsimp only
        refine .free s0 (.free s1 (.final ?_))
        have hst : Lir.step inl { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0, env := env0 } :: rest } = .stuck := by
          unfold Lir.step
          simp [hF', hb2, ctxAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hlb]
        rw [Lir.semStep, hst]; exact .stuck
      | some b0 =>
        dsimp only
        let env2 := env0.insert (tmp + 2) b0
        have hag2 : AgreeBelow (freshBase F) fr.env env2 := hag0.insert_ge (by have := hcp.tmpGe; omega) b0
        have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 2, pos := 0, env := env0 } :: rest } =
            .next { mem, ctx, stack := { fr with label := fr.label + 2, pos := 1, env := env2 } :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fr with label := fr.label + 2, pos := 0, env := env0 })
            hF' hb2 (by simp) rfl rfl
            (by simp [ctxAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hlb, env2])
        cases hll : Lir.loadWord mem .w64 .zero (ctx + Lir.dispWord Rt.limitOff) with
        | none =>
          dsimp only
          refine .free s0 (.free s1 (.free s2 (.final ?_)))
          have hst : Lir.step inl { mem, ctx, stack := { fr with label := fr.label + 2, pos := 1, env := env2 } :: rest } = .stuck := by
            unfold Lir.step
            simp [hF', hb2, ctxAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hll]
          rw [Lir.semStep, hst]; exact .stuck
        | some lim =>
          dsimp only
          let env3 := env2.insert (tmp + 3) lim
          have hag3 : AgreeBelow (freshBase F) fr.env env3 := hag2.insert_ge (by have := hcp.tmpGe; omega) lim
          have he3_2 : env3[tmp + 2]? = some b0 := by rw [Lir.env_insert_ne _ _ (by omega)]; simp [env2]
          have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 2, pos := 1, env := env2 } :: rest } =
              .next { mem, ctx, stack := { fr with label := fr.label + 2, pos := 2, env := env3 } :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fr with label := fr.label + 2, pos := 1, env := env2 })
              hF' hb2 (by simp) rfl rfl
              (by simp [ctxAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_ctx, hll, env3])
          cases hovf : Lir.Ovf.eval .addC b0 bytes with
          | mk b1 ovf =>
            dsimp only
            let env4 := env3.insert (tmp + 4) b1
            have hag4 : AgreeBelow (freshBase F) fr.env env4 := hag3.insert_ge (by have := hcp.tmpGe; omega) b1
            cases ovf with
            | true =>
              simp only [↓reduceIte]
              have s4 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 2, pos := 2, env := env3 } :: rest } =
                  .next { mem, ctx, stack := { fr with label := fr.label + 5, pos := 0, env := env4 } :: rest } false := by
                apply Lir.semStep_next.mpr
                rw [Lir.step_term (fr := { fr with label := fr.label + 2, pos := 2, env := env3 }) hF' hb2 rfl]
                simp [Lir.Arg.eval, he3_2, hovf, Lir.takeEdge, Lir.evalArgs, hb5, Lir.bindParams, env4]
              refine .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.final ?_)))))
              have hst : Lir.step inl { mem, ctx, stack := { fr with label := fr.label + 5, pos := 0, env := env4 } :: rest } = .fail .heap := by
                rw [Lir.step_term (fr := { fr with label := fr.label + 5, pos := 0, env := env4 }) hF' hb5 rfl]
              rw [Lir.semStep, hst]; exact .fail
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              have s4 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 2, pos := 2, env := env3 } :: rest } =
                  .next { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0, env := env4 } :: rest } false := by
                apply Lir.semStep_next.mpr
                rw [Lir.step_term (fr := { fr with label := fr.label + 2, pos := 2, env := env3 }) hF' hb2 rfl]
                simp [Lir.Arg.eval, he3_2, hovf, Lir.takeEdge, Lir.evalArgs, hb3, Lir.bindParams, env4]
              have he4_3 : env4[tmp + 3]? = some lim := by rw [Lir.env_insert_ne _ _ (by omega)]; simp [env3]
              have he4_2 : env4[tmp + 2]? = some b0 := by rw [Lir.env_insert_ne _ _ (by omega), he3_2]
              by_cases hule : Lir.Cond.holds .ule .w64 b1 lim = true
              · simp only [hule, ↓reduceIte]
                have s5 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0, env := env4 } :: rest } =
                    .next { mem, ctx, stack := { fr with label := fr.label + 4, pos := 0, env := env4 } :: rest } false := by
                  apply Lir.semStep_next.mpr
                  rw [Lir.step_term (fr := { fr with label := fr.label + 3, pos := 0, env := env4 }) hF' hb3 rfl]
                  simp [Lir.Arg.eval, env4, he4_3, hule, Lir.takeEdge, Lir.evalArgs, hb4, Lir.bindParams]
                cases hwb : mem.write? .w64 (ctx + Lir.dispWord Rt.bumpOff) b1 with
                | error _ =>
                  dsimp only
                  refine .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.final ?_))))))
                  have hst : Lir.step inl { mem, ctx, stack := { fr with label := fr.label + 4, pos := 0, env := env4 } :: rest } = .stuck := by
                    unfold Lir.step
                    simp [hF', hb4, ctxAddr, Lir.Stmt.exec, addr_ctx, Lir.Arg.eval, env4, hwb]
                  rw [Lir.semStep, hst]; exact .stuck
                | ok mem₁ =>
                  dsimp only
                  have s6 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 4, pos := 0, env := env4 } :: rest } =
                      .next { mem := mem₁, ctx, stack := { fr with label := fr.label + 4, pos := 1, env := env4 } :: rest } false := by
                    apply Lir.semStep_next.mpr
                    exact Lir.step_stmt (fr := { fr with label := fr.label + 4, pos := 0, env := env4 })
                      hF' hb4 (by simp) rfl rfl
                      (by simp [ctxAddr, Lir.Stmt.exec, addr_ctx, Lir.Arg.eval, env4, hwb])
                  have s7 : Lir.semStep inl { mem := mem₁, ctx, stack := { fr with label := fr.label + 4, pos := 1, env := env4 } :: rest } =
                      .next { mem := mem₁, ctx, stack := { fr with label := fr.label + 6, pos := 0, env := env4.insert dst b0, dsts := [] } :: rest } false := by
                    apply Lir.semStep_next.mpr
                    rw [Lir.step_term (fr := { fr with label := fr.label + 4, pos := 1, env := env4 }) hF' hb4 rfl]
                    simp [Lir.Arg.eval, he4_2, Lir.takeEdge, Lir.evalArgs, hb6, hjp, Lir.bindParams, hdsts]
                  have hp := hpubRun b0 mem₁ env4 hag4
                  cases hwH : mem₁.write? .w64 (b0 + Lir.dispWord 0) hdr with
                  | error _ =>
                    dsimp only; rw [hwH] at hp; dsimp only at hp
                    exact .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 hp)))))))
                  | ok mem₂ =>
                    dsimp only; rw [hwH] at hp; dsimp only at hp
                    cases hwf : writeFieldsMem mem₂ b0 0 vals with
                    | none =>
                      dsimp only; rw [hwf] at hp
                      exact .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 hp)))))))
                    | some mem' =>
                      dsimp only; rw [hwf] at hp
                      exact ⟨env4.insert dst b0, _, s0,
                        .free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.free s6 (.free s7 hp)))))),
                        hag4.insert_same dst b0⟩
              · have huleF : Lir.Cond.holds .ule .w64 b1 lim = false := by simpa using hule
                simp only [huleF, Bool.false_eq_true, ↓reduceIte]
                have s5 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 3, pos := 0, env := env4 } :: rest } =
                    .next { mem, ctx, stack := { fr with label := fr.label + 5, pos := 0, env := env4 } :: rest } false := by
                  apply Lir.semStep_next.mpr
                  rw [Lir.step_term (fr := { fr with label := fr.label + 3, pos := 0, env := env4 }) hF' hb3 rfl]
                  simp [Lir.Arg.eval, env4, he4_3, huleF, Lir.takeEdge, Lir.evalArgs, hb5, Lir.bindParams]
                refine .free s0 (.free s1 (.free s2 (.free s3 (.free s4 (.free s5 (.final ?_))))))
                have hst : Lir.step inl { mem, ctx, stack := { fr with label := fr.label + 5, pos := 0, env := env4 } :: rest } = .fail .heap := by
                  rw [Lir.step_term (fr := { fr with label := fr.label + 5, pos := 0, env := env4 }) hF' hb5 rfl]
                rw [Lir.semStep, hst]; exact .fail
    · have hp0F : Lir.Cond.holds .eq .w64 p0 0 = false := by simpa using hp0
      simp only [hp0F, Bool.false_eq_true, ↓reduceIte]
      have s1 : Lir.semStep inl { mem, ctx, stack := { fr with pos := fr.pos + 1, env := env0 } :: rest } =
          .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0, env := env0 } :: rest } false := by
        apply Lir.semStep_next.mpr
        rw [Lir.step_term (fr := { fr with pos := fr.pos + 1, env := env0 }) hF' hb0 hpos0End]
        simp [Lir.Arg.eval, env0, hp0F, Lir.takeEdge, Lir.evalArgs, hb1, Lir.bindParams]
      cases hlp1 : Lir.loadWord mem .w64 .zero (p0 + Lir.dispWord 0) with
      | none =>
        dsimp only
        refine .free s0 (.free s1 (.final ?_))
        have hst : Lir.step inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0, env := env0 } :: rest } = .stuck := by
          unfold Lir.step
          simp [hF', hb1, cellAddr, Lir.Stmt.exec, Lir.Rhs.eval,
            addr_cell env0 ctx tmp p0 0 (by simp [env0]), hlp1]
        rw [Lir.semStep, hst]; exact .stuck
      | some p1 =>
        dsimp only
        let env1 := env0.insert (tmp + 1) p1
        have hag1 : AgreeBelow (freshBase F) fr.env env1 := hag0.insert_ge (by have := hcp.tmpGe; omega) p1
        have he1_0 : env1[tmp]? = some p0 := by rw [Lir.env_insert_ne _ _ (by omega)]; simp [env0]
        have s2 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 0, env := env0 } :: rest } =
            .next { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } false := by
          apply Lir.semStep_next.mpr
          exact Lir.step_stmt (fr := { fr with label := fr.label + 1, pos := 0, env := env0 })
            hF' hb1 (by simp) rfl rfl
            (by simp [cellAddr, Lir.Stmt.exec, Lir.Rhs.eval, addr_cell env0 ctx tmp p0 0 (by simp [env0]), hlp1, env1])
        cases hwh : mem.write? .w64 (ctx + Lir.dispWord headOff) p1 with
        | error _ =>
          dsimp only
          refine .free s0 (.free s1 (.free s2 (.final ?_)))
          have hst : Lir.step inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } = .stuck := by
            unfold Lir.step
            simp [hF', hb1, ctxAddr, Lir.Stmt.exec, addr_ctx, Lir.Arg.eval, env1, hwh]
          rw [Lir.semStep, hst]; exact .stuck
        | ok mem₁ =>
          dsimp only
          have s3 : Lir.semStep inl { mem, ctx, stack := { fr with label := fr.label + 1, pos := 1, env := env1 } :: rest } =
              .next { mem := mem₁, ctx, stack := { fr with label := fr.label + 1, pos := 2, env := env1 } :: rest } false := by
            apply Lir.semStep_next.mpr
            exact Lir.step_stmt (fr := { fr with label := fr.label + 1, pos := 1, env := env1 })
              hF' hb1 (by simp) rfl rfl
              (by simp [ctxAddr, Lir.Stmt.exec, addr_ctx, Lir.Arg.eval, env1, hwh])
          have s4 : Lir.semStep inl { mem := mem₁, ctx, stack := { fr with label := fr.label + 1, pos := 2, env := env1 } :: rest } =
              .next { mem := mem₁, ctx, stack := { fr with label := fr.label + 6, pos := 0, env := env1.insert dst p0, dsts := [] } :: rest } false := by
            apply Lir.semStep_next.mpr
            rw [Lir.step_term (fr := { fr with label := fr.label + 1, pos := 2, env := env1 }) hF' hb1 rfl]
            simp [Lir.Arg.eval, he1_0, Lir.takeEdge, Lir.evalArgs, hb6, hjp, Lir.bindParams, hdsts]
          have hp := hpubRun p0 mem₁ env1 hag1
          cases hwH : mem₁.write? .w64 (p0 + Lir.dispWord 0) hdr with
          | error _ =>
            dsimp only; rw [hwH] at hp; dsimp only at hp
            exact .free s0 (.free s1 (.free s2 (.free s3 (.free s4 hp))))
          | ok mem₂ =>
            dsimp only; rw [hwH] at hp; dsimp only at hp
            cases hwf : writeFieldsMem mem₂ p0 0 vals with
            | none =>
              dsimp only; rw [hwf] at hp
              exact .free s0 (.free s1 (.free s2 (.free s3 (.free s4 hp))))
            | some mem' =>
              dsimp only; rw [hwf] at hp
              exact ⟨env1.insert dst p0, _, s0,
                .free s1 (.free s2 (.free s3 (.free s4 hp))),
                hag1.insert_same dst p0⟩

end IxCC.Cfg.Rc.Inline
