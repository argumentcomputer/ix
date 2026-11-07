import IxCC.Rt.Proof.CxInit

/-! Scratch strengthening of the existing cx_init proof retaining exact final
memory. The original public theorem and runtime procedure are unchanged. -/
set_option autoImplicit false
namespace IxCC.Rt.Rc.Procs.Init
open IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Procs IxCC.Lir
open IxCC.X86 (Memory)

def initMemory (mem : Memory) (ctx size budget : Word) : Memory :=
  zeros ((((mem.write .w64 (ctx-48) budget).write .w64 (ctx-40) (bumpOf (ctx-64))).write
    .w64 (ctx-32) (ctx-64+size)).write .w64 (ctx-24) (ctx-64)) ctx
    (reservedOffs ++ headClasses.map headOffset)

theorem cxInit_cases_exact {q : Program} {g : FunId} (hq : q.funcs[g]? = some cxInit) (hmain : q.main = g)
    (size budget ctx : Word) (mem : Memory) :
    ((∀ k, eval q k [size, budget] mem ctx = .resource .heap) ∧ ¬ RegionOk ctx size) ∨
      (RegionOk ctx size ∧ (LirRegion mem ctx size → ∃ left mem',
        (∀ k, eval q k [size, budget] mem ctx = .ok ([left], mem')) ∧ InitPost ctx budget mem mem' ∧ mem' = initMemory mem ctx size budget)) := by
  let ρ₀ : Env := (({} : Env).insert 0 size).insert 1 budget
  have hinit : State.initial q [size, budget] mem ctx = some (atState mem ctx g 0 0 ρ₀ []) := by
    simp [State.initial, enter, hmain, hq, cxInit_params, bindParams, ρ₀]
  have hB := base_toNat ctx
  have hctx := word_lt ctx
  have hS := word_lt size
  -- block 0: the base and its misalignment
  let ρ₁ : Env := (ρ₀.insert 2 (ctx - 64)).insert 3 ((ctx - 64) &&& UInt64.ofNat 7)
  have hbase : ctx + 0 + dispWord (-(ctxOffset : Int)) = ctx - 64 := ctx_disp_neg ctx (k := ctxOffset) (by decide)
  have hx0 : execList ρ₀ mem ctx [.assign 2 (.addr { base := some .ctx, disp := -(ctxOffset : Int) }),
      .assign 3 (.bin .and .w64 (.v 2) (.imm (UInt64.ofNat 7)))] = some (ρ₁, mem) := by
    rw [execList_cons_of (exec_assign (v := ctx - 64) (by simp only [lir_eval]; rw [hbase])),
      execList_cons_of (exec_assign (v := (ctx - 64) &&& UInt64.ofNat 7) (by simp only [lir_eval, env_insert_self]))]
    rfl
  have hstar0 := stmts_at (p := q) (rest := []) (pre := []) (post := []) hq cxInit_b0 (by rfl)
    (by simp [Stmt.isCall]) hx0
  by_cases h7n : (ctx - 64) &&& UInt64.ofNat 7 ≠ 0
  · -- misaligned
    left
    have hs := br_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 2) (ρ := ρ₁)
      (e := ⟨1, []⟩) (va := (ctx - 64) &&& UInt64.ofNat 7) (vb := 0) (vals := []) (ρ' := ρ₁)
      hq cxInit_b0 rfl rfl (by simp [ρ₁]) rfl (by rw [holds_ne, decide_eq_true h7n]; rfl) rfl cxInit_b1 rfl
    refine ⟨eval_fail_of hinit (hstar0.trans (star_of_step hs)) rfl (fail_at hq cxInit_b1 rfl rfl), ?_⟩
    rintro ⟨h8, -, -⟩
    apply h7n
    apply UInt64.toNat_inj.mp
    rw [and7_toNat, h8]
    rfl
  have h7 : (ctx - 64) &&& UInt64.ofNat 7 = 0 := Decidable.of_not_not h7n
  have hs0 := br_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 2) (ρ := ρ₁)
    (e := ⟨2, []⟩) (va := (ctx - 64) &&& UInt64.ofNat 7) (vb := 0) (vals := []) (ρ' := ρ₁)
    hq cxInit_b0 rfl rfl (by simp [ρ₁]) rfl (by rw [holds_ne, h7]; rfl) rfl cxInit_b2 rfl
  have hstar1 := hstar0.trans (star_of_step hs0)
  -- block 2: at least `minRegion` bytes
  have hv0 : (Arg.v 0).eval ρ₁ = some size := by
    simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁, ρ₀]
  have hmin' : (UInt64.ofNat minRegion : Word).toNat = 4096 := rfl
  by_cases hmin : size < UInt64.ofNat minRegion
  · left
    have hs := br_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 0) (ρ := ρ₁)
      (e := ⟨3, []⟩) (va := size) (vb := UInt64.ofNat minRegion) (vals := []) (ρ' := ρ₁)
      hq cxInit_b2 rfl rfl hv0 rfl (by rw [holds_ult, decide_eq_true hmin]; rfl) rfl cxInit_b3 rfl
    refine ⟨eval_fail_of hinit (hstar1.trans (star_of_step hs)) rfl (fail_at hq cxInit_b3 rfl rfl), ?_⟩
    rintro ⟨-, hm, -⟩
    rw [UInt64.lt_iff_toNat_lt, hmin'] at hmin
    exact absurd hm (Nat.not_le.2 hmin)
  have hs2 := br_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 0) (ρ := ρ₁)
    (e := ⟨4, []⟩) (va := size) (vb := UInt64.ofNat minRegion) (vals := []) (ρ' := ρ₁)
    hq cxInit_b2 rfl rfl hv0 rfl (by rw [holds_ult, decide_eq_false hmin]; rfl) rfl cxInit_b4 rfl
  have hstar2 := hstar1.trans (star_of_step hs2)
  -- block 4: the limit, without a carry
  have hv2 : (Arg.v 2).eval ρ₁ = some (ctx - 64) := by
    simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁, ρ₀]
  let ρ₄ : Env := ρ₁.insert 4 (ctx - 64 + size)
  by_cases hcar : ctx - 64 + size < ctx - 64
  · left
    have hs := brOvf_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 0) (ρ := ρ₁) (o := .addC)
      (x := 4) (e := ⟨6, []⟩) (va := ctx - 64) (vb := size) (vals := []) (ρ' := ρ₄)
      hq cxInit_b4 rfl rfl hv2 hv0 (by simp [Ovf.eval, hcar]) rfl cxInit_b6 rfl
    refine ⟨eval_fail_of hinit (hstar2.trans (star_of_step hs)) rfl (fail_at hq cxInit_b6 rfl rfl), ?_⟩
    rintro ⟨-, -, hlt⟩
    rw [UInt64.lt_iff_toNat_lt, add_word_toNat] at hcar
    omega
  have hs4 := brOvf_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 0) (ρ := ρ₁) (o := .addC)
    (x := 4) (e := ⟨5, []⟩) (va := ctx - 64) (vb := size) (vals := []) (ρ' := ρ₄)
    hq cxInit_b4 rfl rfl hv2 hv0 (by simp [Ovf.eval, hcar]) rfl cxInit_b5 rfl
  have hstar4 := hstar2.trans (star_of_step hs4)
  -- block 5: below `2^63`
  have hv4 : (Arg.v 4).eval ρ₄ = some (ctx - 64 + size) := by
    simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₄]
  by_cases hneg : 2 ^ 63 ≤ (ctx - 64 + size).toNat
  · left
    have hs := br_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 0) (ρ := ρ₄)
      (e := ⟨7, []⟩) (va := ctx - 64 + size) (vb := 0) (vals := []) (ρ' := ρ₄)
      hq cxInit_b5 rfl rfl hv4 rfl (by rw [holds_slt_zero, decide_eq_true hneg]; rfl) rfl cxInit_b7 rfl
    refine ⟨eval_fail_of hinit (hstar4.trans (star_of_step hs)) rfl (fail_at hq cxInit_b7 rfl rfl), ?_⟩
    rintro ⟨-, -, hlt⟩
    rw [add_word_toNat] at hneg
    omega
  have hs5 := br_at (p := q) (mem := mem) (ctx := ctx) (rest := []) (pos := 0) (ρ := ρ₄)
    (e := ⟨8, []⟩) (va := ctx - 64 + size) (vb := 0) (vals := []) (ρ' := ρ₄)
    hq cxInit_b5 rfl rfl hv4 rfl (by rw [holds_slt_zero, decide_eq_false hneg]; rfl) rfl cxInit_b8 rfl
  have hstar5 := hstar4.trans (star_of_step hs5)
  -- the region passes the checks
  rw [UInt64.lt_iff_toNat_lt, add_word_toNat] at hcar
  rw [UInt64.lt_iff_toNat_lt, hmin'] at hmin
  rw [add_word_toNat] at hneg
  have h7' : (ctx - 64).toNat % 8 = 0 := by rw [← and7_toNat, h7]; rfl
  have hc64 : 64 ≤ ctx.toNat := by omega
  have hBc : (ctx - 64).toNat = ctx.toNat - 64 := by omega
  have hlim : (ctx - 64 + size).toNat = (ctx - 64).toNat + size.toNat := by rw [add_word_toNat]; omega
  right
  refine ⟨⟨h7', by rw [show minRegion = 4096 from rfl]; omega, by omega⟩, fun hreg => ?_⟩
  -- block 8
  have hW : ∀ (a : Word) (i : Nat), ctx.toNat - 48 ≤ a.toNat + i → a.toNat + i < ctx.toNat - 64 + size.toNat →
      mem.readable (a + UInt64.ofNat i) = true ∧ mem.writable (a + UInt64.ofNat i) = true :=
    fun a i h1 h2 => lirRegion_at hreg (by omega) (by omega) (by omega)
  have h48 : (ctx - 48).toNat = ctx.toNat - 48 := ctx_sub_toNat (k := 48) hc64 (by omega)
  have h40 : (ctx - 40).toNat = ctx.toNat - 40 := ctx40_toNat hc64
  have h32 : (ctx - 32).toNat = ctx.toNat - 32 := ctx32_toNat hc64
  have h24 : (ctx - 24).toNat = ctx.toNat - 24 := ctx_sub_toNat (k := 24) hc64 (by omega)
  have hbump := bumpOf_toNat (base := ctx - 64) (by omega)
  let bump := bumpOf (ctx - 64)
  let limit := ctx - 64 + size
  let ρ₅ : Env := (ρ₄.insert 5 (blockEnd (ctx - 64))).insert 6 bump
  let ρ₈ : Env := ρ₅.insert 7 (limit - bump)
  let m₁ := mem.write .w64 (ctx - 48) budget
  let m₂ := m₁.write .w64 (ctx - 40) bump
  let m₃ := m₂.write .w64 (ctx - 32) limit
  let m₄ := m₃.write .w64 (ctx - 24) (ctx - 64)
  let ds := reservedOffs ++ headClasses.map headOffset
  have hp₄ : m₄.readable = mem.readable ∧ m₄.writable = mem.writable := by
    simp [m₄, m₃, m₂, m₁, Memory.write]
  have e5 : (Stmt.assign 5
      (.addr { base := some (.v 2), disp := ((ctxBlockBytes + objectAlign - 1 : Nat) : Int) })).exec
        ρ₄ mem ctx = some (ρ₄.insert 5 (blockEnd (ctx - 64)), mem) :=
    exec_assign (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₄, ρ₁, ρ₀]; rfl)
  have e6 : (Stmt.assign 6 (.bin .and .w64 (.v 5) (.imm (0 - UInt64.ofNat objectAlign)))).exec
      (ρ₄.insert 5 (blockEnd (ctx - 64))) mem ctx = some (ρ₅, mem) :=
    exec_assign (by simp only [lir_eval, env_insert_self]; rfl)
  have eB : (Stmt.store .w64 { base := some .ctx, disp := stackBudgetOff } (.v 1)).exec ρ₅ mem ctx =
      some (ρ₅, m₁) :=
    exec_store (ctx_disp_neg ctx (k := 48) (by omega))
      (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₅, ρ₄, ρ₁, ρ₀])
      (fun i hi => (hW _ i (by omega) (by omega)).2)
  have eP : (Stmt.store .w64 { base := some .ctx, disp := bumpOff } (.v 6)).exec ρ₅ m₁ ctx =
      some (ρ₅, m₂) :=
    exec_store (ctx_disp_neg ctx (k := 40) (by omega))
      (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₅])
      (fun i hi => by simpa [m₁, Memory.write] using (hW (ctx - 40) i (by omega) (by omega)).2)
  have eL : (Stmt.store .w64 { base := some .ctx, disp := limitOff } (.v 4)).exec ρ₅ m₂ ctx =
      some (ρ₅, m₃) :=
    exec_store (ctx_disp_neg ctx (k := 32) (by omega))
      (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₅, ρ₄]; rfl)
      (fun i hi => by simpa [m₂, m₁, Memory.write] using (hW (ctx - 32) i (by omega) (by omega)).2)
  have eR : (Stmt.store .w64 { base := some .ctx, disp := regionBaseOff } (.v 2)).exec ρ₅ m₃ ctx =
      some (ρ₅, m₄) :=
    exec_store (ctx_disp_neg ctx (k := 24) (by omega))
      (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₅, ρ₄, ρ₁, ρ₀])
      (fun i hi => by simpa [m₃, m₂, m₁, Memory.write] using (hW (ctx - 24) i (by omega) (by omega)).2)
  have hfit : ctx.toNat + 576 < 2 ^ 64 := by omega
  have hwz : ∀ d ∈ ds, ∀ i < 8, m₄.writable (ctx + 0 + dispWord d + UInt64.ofNat i) = true := by
    intro d hd i hi
    obtain ⟨h1, h2⟩ := zeroAddr hc64 hfit hd
    rw [hp₄.2]
    exact (hW _ i (by omega) (by omega)).2
  have e7 : (Stmt.assign 7 (.bin .sub .w64 (.v 4) (.v 6))).exec ρ₅ (zeros m₄ ctx ds) ctx =
      some (ρ₈, zeros m₄ ctx ds) :=
    exec_assign (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₅, ρ₄]; rfl)
  have hx8 : execList ρ₄ mem ctx body8 = some (ρ₈, zeros m₄ ctx ds) := by
    simp only [body8, List.cons_append, List.nil_append]
    rw [execList_cons_of e5, execList_cons_of e6, execList_cons_of eB, execList_cons_of eP, execList_cons_of eL,
      execList_cons_of eR, execList_append, execList_zeros _ _ hwz, Option.bind_some, execList_cons_of e7]
    rfl
  have hstar8 := stmts_at (p := q) (rest := []) (pre := []) (post := []) hq cxInit_b8 (by simp)
    body8_noCall hx8
  have hdone : step q (atState (zeros m₄ ctx ds) ctx g 8 (([] : List Stmt).length + body8.length) ρ₈ []) =
      .done [limit - bump] (zeros m₄ ctx ds) :=
    step_ret_done (fr := { fn := g, label := 8, pos := ([] : List Stmt).length + body8.length, env := ρ₈ }) hq cxInit_b8
      (by simp) rfl (by simp [ρ₈])
  refine ⟨limit - bump, zeros m₄ ctx ds, eval_done_of hinit (hstar5.trans hstar8) rfl hdone, ?_⟩
  refine ⟨?_, rfl⟩
  -- the words the context block holds
  have hR : ∀ (a : Word) (i : Nat), ctx.toNat - 48 ≤ a.toNat + i → a.toNat + i < ctx.toNat - 64 + size.toNat →
      mem.readable (a + UInt64.ofNat i) = true := fun a i h1 h2 => (hW a i h1 h2).1
  have w8 : 8 = X86.Width.bytes .w64 := rfl
  have wB₁ : WordAt m₁ (ctx - 48) budget := wordAt_write64 fun i hi => hR _ i (by omega) (by omega)
  have wB₂ : WordAt m₂ (ctx - 48) budget := wB₁.write_disjoint (by rw [← w8]; omega) (by omega) (.inl (by omega))
  have wP₂ : WordAt m₂ (ctx - 40) bump :=
    wordAt_write64 fun i hi => by simpa [m₁, Memory.write] using hR (ctx - 40) i (by omega) (by omega)
  have wB₃ : WordAt m₃ (ctx - 48) budget := wB₂.write_disjoint (by rw [← w8]; omega) (by omega) (.inl (by omega))
  have wP₃ : WordAt m₃ (ctx - 40) bump := wP₂.write_disjoint (by rw [← w8]; omega) (by omega) (.inl (by omega))
  have wL₃ : WordAt m₃ (ctx - 32) limit :=
    wordAt_write64 fun i hi => by simpa [m₂, m₁, Memory.write] using hR (ctx - 32) i (by omega) (by omega)
  have wB₄ : WordAt m₄ (ctx - 48) budget := wB₃.write_disjoint (by rw [← w8]; omega) (by omega) (.inl (by omega))
  have wP₄ : WordAt m₄ (ctx - 40) bump := wP₃.write_disjoint (by rw [← w8]; omega) (by omega) (.inl (by omega))
  have wL₄ : WordAt m₄ (ctx - 32) limit := wL₃.write_disjoint (by rw [← w8]; omega) (by omega) (.inl (by omega))
  have hkeep : ∀ (b v : Word), b.toNat + 8 ≤ ctx.toNat - 16 → WordAt m₄ b v → WordAt (zeros m₄ ctx ds) b v :=
    fun b v hb hw => zeros_keep (by omega) _ ds hw fun d hd => by
      obtain ⟨h1, h2⟩ := zeroAddr hc64 hfit hd
      exact ⟨by omega, .inl (by omega)⟩
  have hp' : (zeros m₄ ctx ds).readable = mem.readable ∧ (zeros m₄ ctx ds).writable = mem.writable := by
    rw [zeros_readable, zeros_writable]; exact hp₄
  refine ⟨fun T => ⟨bump, limit, ?_⟩, hkeep _ _ (by omega) wB₄, hp'.1, hp'.2⟩
  exact {
    len := rfl
    ctxLo := hc64
    bumpWord := hkeep _ _ (by omega) wP₄
    bumpWritable := fun i hi => by rw [hp'.2]; exact (hW (ctx - 40) i (by omega) (by omega)).2
    limitWord := hkeep _ _ (by omega) wL₄
    start := by show ctx.toNat + 576 ≤ (bumpOf (ctx - 64)).toNat; omega
    bumpLe := by show (bumpOf (ctx - 64)).toNat ≤ (ctx - 64 + size).toNat; omega
    limitLt := by show (ctx - 64 + size).toNat < 2 ^ 63; omega
    bumpAligned := by show (bumpOf (ctx - 64)).toNat % 8 = 0; omega
    free := fun k hk hk' => by
      rw [hp'.1, hp'.2]
      exact hreg k (by show (ctx - 64).toNat + 16 ≤ k; change (bumpOf (ctx - 64)).toNat ≤ k at hk; omega)
        (by change k < (ctx - 64 + size).toNat at hk'; omega)
    cells := fun ℓ h => absurd h (Nat.not_lt_zero ℓ)
    ordered := fun ℓ ℓ' a a' rc b _ hP => by simp at hP }


end IxCC.Rt.Rc.Procs.Init
