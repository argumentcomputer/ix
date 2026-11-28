import IxCC.Rt.Proof.Check

/-!
# The immortal bump allocation

`alloc_sim`: `Rt.lower`'s allocation of a constructor with fields loads the
bump pointer into `x`, computes the end of the cell, compares it with the
limit (`fail heap` above it), then stores the new bump pointer, the header
halves and the fields; the memory it leaves is `allocStores`, which keeps
the heap invariant with the new cell placed at the old bump pointer
(`alloc_mem`). A field-less constructor is its immediate.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

/-- An action that throws ends every run with an error. -/
macro "throw_absurd" " at " h:ident : tactic =>
  `(tactic| simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.bind] at $h:ident)

/-! ## The field stores -/

/-- The stores of the fields `las`, from field `k`. -/
def fieldStmts (x : Nat) (las : List Lir.Arg) (k : Nat) : List Lir.Stmt :=
  (las.zipIdx k).map fun (a, i) => .store .w64 (mem x (fieldOffset i)) a

theorem fieldStmts_cons (x : Nat) (a : Lir.Arg) (las : List Lir.Arg) (k : Nat) :
    fieldStmts x (a :: las) k = .store .w64 (mem x (fieldOffset k)) a :: fieldStmts x las (k + 1) := rfl

theorem forM_stores_run (x : Nat) :
    ∀ (las : List Lir.Arg) (k : Nat) (st : St),
      ((las.zipIdx k).forM fun (p : Lir.Arg × Nat) => emit (.store .w64 (mem x (fieldOffset p.2)) p.1)).run st =
        .ok ((), { st with acc := (fieldStmts x las k).reverse ++ st.acc })
  | [], k, st => rfl
  | a :: las, k, st => by
    have hstep : (((a, k) :: las.zipIdx (k + 1)).forM fun (p : Lir.Arg × Nat) =>
        emit (.store .w64 (mem x (fieldOffset p.2)) p.1)).run st =
        ((las.zipIdx (k + 1)).forM fun (p : Lir.Arg × Nat) => emit (.store .w64 (mem x (fieldOffset p.2)) p.1)).run
          { st with acc := .store .w64 (mem x (fieldOffset k)) a :: st.acc } := rfl
    rw [List.zipIdx_cons, hstep, forM_stores_run x las (k + 1)]
    simp [fieldStmts_cons]

theorem fieldStmts_noCall (x : Nat) (las : List Lir.Arg) (k : Nat) : ∀ s ∈ fieldStmts x las k, s.isCall = false := by
  intro s hs
  simp only [fieldStmts, List.mem_map] at hs
  obtain ⟨_, -, rfl⟩ := hs
  rfl

/-! ## The run of an allocation -/

theorem stbind_run {α β : Type} (x : M α) (f : α → M β) (s : St) :
    (StateT.bind x f).run s = Except.bind (x.run s) (fun p => (f p.1).run p.2) := rfl

theorem freshReg_run (st : St) : freshReg.run st = .ok (st.fresh, { st with fresh := st.fresh + 1 }) := rfl

/-- What an allocation the lowering accepts emits. -/
theorem alloc_run {f : Fir.FunId} {T : Tables} {x : Nat} {c : Fir.CtorInfo} {las : List Lir.Arg} {st st' : St}
    (h : (Lower.alloc f T x c las).run st = .ok ((), st')) :
    isNatKey T c.key = false ∧ las.length = c.arity ∧ Fir.CtorInfo.ofKey T.ctors c.key = some c ∧
      (∀ a ∈ las, a ≠ .v x) ∧ c.tag ≤ maxTag ∧
      ((c.fieldless = true ∧ st' = { st with
          acc := [.assign x (.arg (.imm (ctor0Word c.tag)))].reverse ++ st.acc, fresh := st.fresh }) ∨
       (c.fieldless = false ∧ c.arity ≤ maxFields ∧
        st' = CheckSt st .heap
          [.assign x (.load .w64 .zero (ctxAt bumpOff)), .assign st.fresh (.addr (mem x (cellBytes c.arity))),
            .assign (st.fresh + 1) (.load .w64 .zero (ctxAt limitOff))]
          ([.store .w64 (ctxAt bumpOff) (.v st.fresh),
            .store .w32 (mem x 0) (.imm (UInt64.ofNat (headerLow c.arity 0 c.tag))),
            .store .w32 (mem x 4) (.imm (UInt64.ofNat immortalRc))] ++ fieldStmts x las 0)
          (.br .ugt (.v st.fresh) (.v (st.fresh + 1)) (loc st.next) (loc (st.next + 1))) (st.fresh + 1 + 1))) := by
  have h1 : isNatKey T c.key = false := by
    cases h' : isNatKey T c.key
    · rfl
    · simp only [Lower.alloc, h', ↓reduceIte, StateT.run] at h; throw_absurd at h
  have h2 : (c.nscalar != 0) = false := by
    cases h' : (c.nscalar != 0)
    · rfl
    · simp only [Lower.alloc, h1, h', Bool.false_eq_true, ↓reduceIte, StateT.run] at h; throw_absurd at h
  have h3 : (las.length != c.arity) = false := by
    cases h' : (las.length != c.arity)
    · rfl
    · simp only [Lower.alloc, h1, h2, h', Bool.false_eq_true, ↓reduceIte, StateT.run] at h; throw_absurd at h
  have h4 : (Fir.CtorInfo.ofKey T.ctors c.key != some c) = false := by
    cases h' : (Fir.CtorInfo.ofKey T.ctors c.key != some c)
    · rfl
    · simp only [Lower.alloc, h1, h2, h3, h', Bool.false_eq_true, ↓reduceIte, StateT.run] at h; throw_absurd at h
  have h5 : (las.any fun a => a == .v x) = false := by
    cases h' : (las.any fun a => a == .v x)
    · rfl
    · simp only [Lower.alloc, h1, h2, h3, h4, h', Bool.false_eq_true, ↓reduceIte, StateT.run] at h; throw_absurd at h
  have h6 : ¬ c.tag > maxTag := by
    intro h'
    simp only [Lower.alloc, h1, h2, h3, h4, h5, h', Bool.false_eq_true, ↓reduceIte, StateT.run] at h; throw_absurd at h
  refine ⟨h1, by simpa using h3, by simpa using h4, fun a ha e => ?_, by omega, ?_⟩
  · subst e
    have := List.any_eq_false.1 h5 _ ha
    simp at this
  cases hfl : c.fieldless with
  | true =>
    simp only [Lower.alloc, h1, h2, h3, h4, h5, h6, hfl, Bool.false_eq_true, ↓reduceIte] at h
    have := (assign_run st x (.arg (.imm (ctor0Word c.tag)))).symm.trans h
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at this
    exact .inl ⟨rfl, this.symm⟩
  | false =>
    have h7 : ¬ c.arity > maxFields := by
      intro h'
      simp only [Lower.alloc, h1, h2, h3, h4, h5, h6, hfl, h', Bool.false_eq_true, ↓reduceIte, StateT.run] at h
      throw_absurd at h
    let ss1 : List Lir.Stmt := [.assign x (.load .w64 .zero (ctxAt bumpOff)),
      .assign st.fresh (.addr (mem x (cellBytes c.arity))), .assign (st.fresh + 1) (.load .w64 .zero (ctxAt limitOff))]
    let ss2 : List Lir.Stmt := [.store .w64 (ctxAt bumpOff) (.v st.fresh),
      .store .w32 (mem x 0) (.imm (UInt64.ofNat (headerLow c.arity 0 c.tag))),
      .store .w32 (mem x 4) (.imm (UInt64.ofNat immortalRc))]
    let t : PTerm := .br .ugt (.v st.fresh) (.v (st.fresh + 1)) (loc st.next) (loc (st.next + 1))
    have key : (Lower.alloc f T x c las).run st =
        ((las.zipIdx 0).forM fun (p : Lir.Arg × Nat) => emit (.store .w64 (mem x (fieldOffset p.2)) p.1)).run
          (CheckSt st .heap ss1 ss2 t (st.fresh + 1 + 1)) := by
      simp only [Lower.alloc, h1, h2, h3, h4, h5, h6, hfl, h7, Bool.false_eq_true, ↓reduceIte]
      rfl
    rw [key, forM_stores_run] at h
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    refine .inr ⟨rfl, by omega, ?_⟩
    rw [← h]
    simp [CheckSt, ss1, ss2, t]

/-! ## Addresses -/

theorem execList_append (ρ : Lir.Env) (m : X86.Memory) (ctx : Word) :
    ∀ (xs ys : List Lir.Stmt), Lir.execList ρ m ctx (xs ++ ys) =
      (Lir.execList ρ m ctx xs).bind fun p => Lir.execList p.1 p.2 ctx ys
  | [], ys => rfl
  | s :: xs, ys => by
    simp only [List.cons_append, Lir.execList]
    split
    · exact execList_append _ _ ctx xs ys
    · rfl

theorem ctx_disp_neg (ctx : Word) {k : Nat} (hk : k ≤ 64) :
    ctx + 0 + Lir.dispWord (-(k : Int)) = ctx - UInt64.ofNat k := by
  rw [Lir.dispWord_neg (by omega)]
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat']
  have := ctx.toNat_lt_size
  simp only [UInt64.size] at this
  have h0 : (UInt64.toNat 0) = 0 := rfl
  rw [h0]
  omega

theorem eval_bumpOff (ρ : Lir.Env) (ctx : Word) : Lir.Addr.eval ρ ctx (ctxAt bumpOff) = some (ctx - 40) := by
  simp only [Lir.Addr.eval, ctxAt, bumpOff, Option.bind_eq_bind, Option.bind_some, Lir.option_pure]
  exact congrArg some (ctx_disp_neg ctx (k := 40) (by omega))

theorem eval_limitOff (ρ : Lir.Env) (ctx : Word) : Lir.Addr.eval ρ ctx (ctxAt limitOff) = some (ctx - 32) := by
  simp only [Lir.Addr.eval, ctxAt, limitOff, Option.bind_eq_bind, Option.bind_some, Lir.option_pure]
  exact congrArg some (ctx_disp_neg ctx (k := 32) (by omega))

theorem eval_mem {ρ : Lir.Env} {ctx : Word} {x : Nat} {a : Word} (hx : ρ[x]? = some a) (d : Nat) :
    Lir.Addr.eval ρ ctx (mem x (d : Int)) = some (a + UInt64.ofNat d) := by
  simp only [Lir.Addr.eval, mem, Option.bind_eq_bind, Option.bind_some, Lir.option_pure, hx]
  rw [Lir.dispWord_ofNat]
  simp

theorem fieldOffset_nat (i : Nat) : fieldOffset i = ((8 + 8 * i : Nat) : Int) := by
  simp [fieldOffset]

theorem load_word {ρ : Lir.Env} {ctx a v : Word} {m : X86.Memory} {addr : Lir.Addr}
    (ha : Lir.Addr.eval ρ ctx addr = some a) (hw : WordAt m a v) :
    Lir.Rhs.eval ρ m ctx (.load .w64 .zero addr) = some v := by
  simp only [Lir.Rhs.eval, ha, Option.bind_eq_bind, Option.bind_some, Lir.loadWord, hw.read64]

/-- The field stores write `storeFields`. -/
theorem exec_fieldStmts {x : Nat} {a : Word} {ctx : Word} :
    ∀ (las : List Lir.Arg) (ws : List Word) (k : Nat) (ρ : Lir.Env) (m : X86.Memory), ρ[x]? = some a →
      Lir.evalArgs ρ las = some ws →
      (∀ i < las.length, ∀ j < 8, m.writable (a + UInt64.ofNat (8 + 8 * (k + i)) + UInt64.ofNat j) = true) →
      Lir.execList ρ m ctx (fieldStmts x las k) = some (ρ, storeFields m a k ws)
  | [], ws, k, ρ, m, _, hws, _ => by
    simp only [Lir.evalArgs_nil, Option.some.injEq] at hws
    subst hws
    rfl
  | la :: las, ws, k, ρ, m, hx, hws, hwr => by
    simp only [Lir.evalArgs_cons, Option.bind_eq_bind] at hws
    cases hla : la.eval ρ with
    | none => simp [hla] at hws
    | some w =>
      cases hlas : Lir.evalArgs ρ las with
      | none => simp [hla, hlas] at hws
      | some ws' =>
        simp [hla, hlas] at hws
        subst hws
        simp only [fieldStmts_cons, Lir.execList, Lir.Stmt.exec, fieldOffset_nat, eval_mem hx, hla,
          Option.bind_eq_bind, Option.bind_some]
        rw [write?_ok (fun j hj => by simpa using hwr 0 (by simp) j (by simpa [X86.Width.bytes] using hj))]
        simp only [storeFields]
        exact exec_fieldStmts las ws' (k + 1) ρ _ hx hlas (fun i hi j hj => by
          simpa [X86.Memory.write, Nat.add_assoc, Nat.add_comm 1] using hwr (i + 1) (by simp; omega) j hj)

/-- Lowered operands that read neither `x` nor registers from the supply up
evaluate the same in registers that agree below the supply away from
`x`. -/
theorem evalArgs_agree {sup x : Nat} {ρ ρ' : Lir.Env} (hag : ∀ y, y < sup → y ≠ x → ρ'[y]? = ρ[y]?) :
    ∀ {las : List Lir.Arg}, (∀ la ∈ las, ArgReads sup la) → (∀ la ∈ las, la ≠ .v x) →
      Lir.evalArgs ρ' las = Lir.evalArgs ρ las
  | [], _, _ => rfl
  | la :: las, hr, hn => by
    simp only [Lir.evalArgs_cons]
    rw [evalArgs_agree hag (fun l h => hr l (by simp [h])) (fun l h => hn l (by simp [h]))]
    congr 1
    cases la with
    | imm _ => rfl
    | v y =>
      have hy := hr (.v y) (by simp) y rfl
      have hyx : y ≠ x := fun e => hn (.v y) (by simp) (by rw [e])
      exact hag y hy hyx

/-- An allocation's Cfg meaning. -/
theorem evalRhs_alloc {T : Own.Tables} {ρ : Own.Env} {H H' : Own.Heap} {c : Fir.CtorInfo} {as : List Fir.Arg}
    {κ : Own.Kind} {v : Own.RVal} (h : Own.evalRhs .immortal T ρ H (.alloc c as κ) = .ok (v, H')) :
    ∃ vs, Own.evalArgs ρ as = some vs ∧ vs.length = c.arity ∧
      ((c.fieldless = true ∧ v = .ctor0 c ∧ H' = H) ∨
       (c.fieldless = false ∧ v = .loc H.cells.size ∧
        H' = { cells := H.cells.push (.live 1 .static { ctor := c, fields := vs }) })) := by
  simp only [Own.evalRhs] at h
  cases hv : Own.evalArgs ρ as with
  | none => simp [hv] at h
  | some vs =>
    simp only [hv] at h
    split at h
    · rename_i hlen
      refine ⟨vs, rfl, hlen, ?_⟩
      cases hfl : c.fieldless with
      | true =>
        simp only [hfl, ↓reduceIte, Sem.Result.ok.injEq, Prod.mk.injEq] at h
        exact .inl ⟨rfl, h.1.symm, h.2.symm⟩
      | false =>
        simp only [hfl, Bool.false_eq_true, ↓reduceIte, Own.Heap.alloc, Own.AllocPol.mode, Sem.Result.ok.injEq,
          Prod.mk.injEq] at h
        exact .inr ⟨rfl, h.1.symm, h.2.symm⟩
    · simp at h

theorem add_ofNat_zero (a : Word) : a + UInt64.ofNat 0 = a := by simp

theorem ofNat_four : (UInt64.ofNat 4 : Word) = 4 := rfl

/-- The allocation's stores leave `allocStores`. -/
theorem exec_allocStores {ρl : Lir.Env} {ctx bump e lo hi : Word} {m : X86.Memory} {x f0 : Nat}
    {las : List Lir.Arg} {ws : List Word} (hx : ρl[x]? = some bump) (he : ρl[f0]? = some e)
    (hlas : Lir.evalArgs ρl las = some ws) (hw40 : ∀ j < 8, m.writable (ctx - 40 + UInt64.ofNat j) = true)
    (hfree : ∀ k, bump.toNat ≤ k → k < bump.toNat + 8 + 8 * ws.length → m.writable (UInt64.ofNat k) = true)
    (hb : bump.toNat + 8 + 8 * ws.length < 2 ^ 63) :
    Lir.execList ρl m ctx ([.store .w64 (ctxAt bumpOff) (.v f0), .store .w32 (mem x 0) (.imm lo),
      .store .w32 (mem x 4) (.imm hi)] ++ fieldStmts x las 0) = some (ρl, allocStores m ctx bump e lo hi ws) := by
  have hlen : las.length = ws.length := by
    clear hfree hb hw40
    induction las generalizing ws with
    | nil => simp at hlas; subst hlas; rfl
    | cons la las ih =>
      simp only [Lir.evalArgs_cons, Option.bind_eq_bind] at hlas
      cases hla : la.eval ρl with
      | none => simp [hla] at hlas
      | some w =>
        cases hl : Lir.evalArgs ρl las with
        | none => simp [hla, hl] at hlas
        | some ws' => simp [hla, hl] at hlas; subst hlas; simp [ih hl]
  have hw : ∀ (mm : X86.Memory), mm.writable = m.writable → ∀ (k : Nat), bump.toNat ≤ k →
      k < bump.toNat + 8 + 8 * ws.length → mm.writable (UInt64.ofNat k) = true :=
    fun mm hmm k hk hk' => by rw [hmm]; exact hfree k hk hk'
  have hofs : ∀ (j : Nat), j < 8 + 8 * ws.length → bump + UInt64.ofNat j = UInt64.ofNat (bump.toNat + j) := by
    intro j hj
    apply UInt64.toNat_inj.mp
    rw [addr_toNat (by omega), UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  rw [execList_append]
  simp only [Lir.execList, Lir.Stmt.exec, eval_bumpOff, Option.bind_eq_bind, Option.bind_some, Lir.Arg.eval_v,
    Lir.Arg.eval_imm, he]
  rw [write?_ok (fun j hj => hw40 j (by simpa [X86.Width.bytes] using hj))]
  simp only [show (0 : Int) = ((0 : Nat) : Int) from rfl, show (4 : Int) = ((4 : Nat) : Int) from rfl,
    eval_mem hx, add_ofNat_zero, Option.bind_some]
  rw [write?_ok (fun j hj => by
    have hj' : j < 4 := by simpa [X86.Width.bytes] using hj
    rw [hofs j (by omega)]
    exact hw _ (by simp [X86.Memory.write]) _ (by omega) (by omega))]
  simp only [eval_mem hx, Option.bind_some]
  rw [write?_ok (fun j hj => by
    have hj' : j < 4 := by simpa [X86.Width.bytes] using hj
    rw [show bump + UInt64.ofNat 4 + UInt64.ofNat j = bump + UInt64.ofNat (4 + j) by
      rw [UInt64.add_assoc, ← UInt64.ofNat_add], hofs (4 + j) (by omega)]
    exact hw _ (by simp [X86.Memory.write]) _ (by omega) (by omega))]
  simp only [Option.bind_some]
  rw [exec_fieldStmts las ws 0 ρl _ hx hlas (fun i hi j hj => by
    rw [show bump + UInt64.ofNat (8 + 8 * (0 + i)) + UInt64.ofNat j = bump + UInt64.ofNat (8 + 8 * i + j) by
      rw [UInt64.add_assoc, ← UInt64.ofNat_add, Nat.zero_add], hofs (8 + 8 * i + j) (by omega)]
    exact hw _ (by simp [X86.Memory.write]) _ (by omega) (by omega))]
  rfl

/-- **The immortal bump allocation simulates Cfg's `alloc`**. -/
theorem alloc_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {c : Fir.CtorInfo} {las : List Lir.Arg}
    {as : List Fir.Arg} {κ : Own.Kind}
    (hrun : (Lower.alloc f T x c las).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st) (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some las))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x (.alloc c as κ) := by
  obtain ⟨hnat, hlen, hkey, hnx, htag, hcase⟩ := alloc_run hrun
  have hok : CtorOk T c := ⟨hkey, hnat, htag⟩
  rcases hcase with ⟨hfl, rfl⟩ | ⟨hfl, hmax, rfl⟩
  · apply straight_sim hF hH hC ho (by simp [Lir.Stmt.isCall])
    intro P H ρ ρl mem v H' hρ hr
    obtain ⟨vs, hvs, hvlen, ⟨-, rfl, rfl⟩ | ⟨hfl', -⟩⟩ := evalRhs_alloc hr
    · refine ⟨rfl, ρl.insert x (ctor0Word c.tag), by simp only [lir_eval], ?_⟩
      exact hρ.insert hx ⟨rfl, hok, hfl⟩
    · rw [hfl] at hfl'; cases hfl'
  · simp only [CheckSt, List.length_reverse]
    refine check_br_sim hF hH hC hl ho (by simp [Lir.Stmt.isCall])
      (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil]; rintro s (((rfl | rfl | rfl | h)) | h) <;> first | rfl | exact absurd h (by simp) | exact fieldStmts_noCall _ _ _ s h) ?_
    intro P H ρ ρl mem v H' hheap hρ hr
    obtain ⟨vs, hvs, hvlen, ⟨hfl', -⟩ | ⟨-, rfl, rfl⟩⟩ := evalRhs_alloc hr
    · rw [hfl] at hfl'; cases hfl'
    obtain ⟨bump, limit, hA⟩ := hheap
    obtain ⟨ws, hws, hrel, hreads⟩ := operands_rel hρ hops hlive hvs
    have hwlen := hrel.length_eq
    let e := bump + UInt64.ofNat (cellBytes c.arity)
    let ρl₁ := ((ρl.insert x bump).insert st.fresh e).insert (st.fresh + 1) limit
    have hx1 : Lir.execList ρl mem ctx
        [.assign x (.load .w64 .zero (ctxAt bumpOff)), .assign st.fresh (.addr (Lower.mem x (cellBytes c.arity))),
          .assign (st.fresh + 1) (.load .w64 .zero (ctxAt limitOff))] = some (ρl₁, mem) := by
      simp only [Lir.execList, Lir.Stmt.exec, Lir.Rhs.eval, eval_bumpOff, eval_limitOff, Option.bind_eq_bind,
        Option.bind_some, Lir.loadWord, hA.bumpWord.read64, hA.limitWord.read64,
        eval_mem (Lir.env_insert_self ρl x bump) (cellBytes c.arity)]
      rfl
    have hfx : ρl₁[x]? = some bump := by
      simp only [ρl₁]
      rw [Lir.env_insert_ne _ _ (Nat.ne_of_gt (by omega)), Lir.env_insert_ne _ _ (Nat.ne_of_gt (by omega))]
      exact Lir.env_insert_self _ _ _
    refine ⟨ρl₁, mem, e, limit, hx1, by simp only [Lir.Arg.eval_v, ρl₁]; rw [Lir.env_insert_ne _ _ (Nat.succ_ne_self st.fresh), Lir.env_insert_self], by simp [ρl₁], fun hgt => ?_⟩
    -- the cell fits below the limit
    simp only [Lir.holds_ugt, decide_eq_false_iff_not] at hgt
    have hctx := hA.ctxLo
    have hlim := hA.limitLt
    have hbl := hA.bumpLe
    have hst := hA.start
    have harity : c.arity ≤ 254 := by have := hmax; unfold maxFields at this; omega
    have he : e.toNat = bump.toNat + cellBytes c.arity := by
      simp only [e]
      rw [addr_toNat (by unfold cellBytes; omega)]
    have hfit : bump.toNat + cellSize vs.length ≤ limit.toNat := by
      rw [UInt64.lt_iff_toNat_lt, he] at hgt
      simp only [cellSize, hvlen]
      unfold cellBytes at hgt
      omega
    have hA' := alloc_mem hA hok hfl hvlen (by omega) hrel hfit
    have hcs : cellSize vs.length = cellBytes c.arity := by simp [cellSize, cellBytes, hvlen]
    rw [hcs, hvlen] at hA'
    refine ⟨ρl₁, _, P ++ [bump], ?_, ⟨_, _, hA'⟩, ⟨[bump], rfl⟩, ?_⟩
    · -- the stores
      have hlas : Lir.evalArgs ρl₁ las = some ws := by
        rw [evalArgs_agree (sup := sup) (x := x) (ρ := ρl) (fun y hy hyx => by
          simp only [ρl₁]
          rw [Lir.env_insert_ne _ _ (Nat.ne_of_gt (by omega)), Lir.env_insert_ne _ _ (Nat.ne_of_gt (by omega)),
            Lir.env_insert_ne _ _ (Ne.symm hyx)]) hreads hnx]
        exact hws
      exact exec_allocStores hfx (by simp only [ρl₁]; rw [Lir.env_insert_ne _ _ (Nat.succ_ne_self st.fresh), Lir.env_insert_self]) hlas hA.bumpWritable
        (fun k hk hk' => (hA.free k hk (by rw [← hwlen, hvlen] at hk'; simp only [cellSize, hvlen] at hfit; omega)).2)
        (by simp only [cellSize, hvlen] at hfit; rw [← hwlen, hvlen]; omega)
    · refine (((hρ.mono ⟨[bump], rfl⟩).insert hx ?_).temp hsup _).temp (by omega) _
      show (P ++ [bump])[H.cells.size]? = some bump
      rw [List.getElem?_append_right (by rw [hA.len]; exact Nat.le_refl _), hA.len]
      simp

end IxCC.Rt.Proof
