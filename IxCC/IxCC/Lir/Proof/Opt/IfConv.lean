import IxCC.Lir.Opt.IfConv
import IxCC.Lir.Proof.Opt.Inline
import IxCC.Lir.Proof.Steps
import IxCC.Lir.Proof.Eval
import IxCC.Src.Proof.NatMap
import IxCC.Sem.Forward
import IxCC.Sem.Simulation

/-!
# Direct soundness proof for diamond if-conversion (`Lir.Opt.IfConv`)

Proves `ifConvDiamondSite_sim : Sem.Sim Eq id` and
`ifConvDiamondSiteChecked_sim` / `ifConvDiamondSiteChecked_wellFormed` directly
via `Sem.Forward` using a Lazy-Arm-Sync simulation relation:
- Outside the converted diamond, `q` steps in lockstep with `p` (with all
  registers `< off` outside `armTDefs ∪ armFDefs` preserved identically).
- When `p` enters `armT` or `armF` from block `b`, `q` stays parked at
  `(b, blk.body.size)` until either:
  - `p` hits an arm `brOvf` overflow edge (in which case `q` speculatively runs
    both arms, evaluates `predReg ≠ 0`, and reaches `.fail res`, discharging
    the `Sem.Fails` disjunct directly), or
  - `p` jumps to `join` (in which case `q` speculatively runs both arms +
    `select`s + predicated `predReg = 0` check and lands at `join` with
    identical parameter bindings in `0` charges).
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Label FunId Width Ext Base Addr Arg Cond BinOp Ovf LimbOp
  Rhs Stmt Edge Term Block Func Program Word Env Frame State Step semStep
  semStep_next semStep_fail semStep_trap semStep_done evalArgs bindParams execList
  enter takeEdge step step_stmt step_call step_term step_jump step_br step_brOvf
  step_ret_done step_ret_caller step_tail step_fail step_trap star_stmts
  fails_of_star star_of_step eval eval_mono runs_eval atState
  env_insert_self env_insert_ne env_insert_get env_empty)

/-! ## Helper lemmas for `loopMapReg`, `isHoistableStmt`, and `emitOvfLimb` -/

theorem loopMapReg_zero (defs : Src.NatSet) (off : VReg) (x : VReg) :
    loopMapReg defs off 0 x = x := by
  simp [loopMapReg]

theorem loopMapReg_not_mem {defs : Src.NatSet} {off c : Nat} {x : VReg}
    (h : defs.contains x = false) : loopMapReg defs off c x = x := by
  simp [loopMapReg, h]

theorem loopMapReg_mem_pos {defs : Src.NatSet} {off c : Nat} {x : VReg}
    (hc : 0 < c) (h : defs.contains x = true) : loopMapReg defs off c x = c * off + x := by
  have hne : (c == 0) = false := beq_false_of_ne (by omega)
  simp [loopMapReg, hne, h]

theorem loopMapReg_ge_of_mem {defs : Src.NatSet} {off c : Nat} {x : VReg}
    (hc : 0 < c) (h : defs.contains x = true) : c * off ≤ (loopMapReg defs off c x : Nat) := by
  rw [loopMapReg_mem_pos hc h]; omega

theorem loopMapReg_lt_of_mem {defs : Src.NatSet} {off c : Nat} {x : VReg}
    (hc : 0 < c) (h : defs.contains x = true) (hx : x < off) :
    (loopMapReg defs off c x : Nat) < (c + 1) * off := by
  rw [loopMapReg_mem_pos hc h, Nat.add_mul, Nat.one_mul]
  exact Nat.add_lt_add_left hx (c * off)

/-- Pure hoistable statements always succeed without modifying memory whenever their used
registers are defined in `ρ`, and only write to `s.defs`. -/
theorem isHoistableStmt_exec {s : Stmt} (hh : isHoistableStmt s = true)
    {ρ : Env} {mem : X86.Memory} {ctx : Word}
    (hdef : ∀ x ∈ s.uses, ρ[x]?.isSome = true) :
    s.isCall = false ∧
    ∃ ρ', s.exec ρ mem ctx = some (ρ', mem) ∧
      (∀ d ∈ s.defs, ρ'[d]?.isSome = true) ∧
      (∀ z, z ∉ s.defs → ρ'[z]? = ρ[z]?) := by
  have harg : ∀ a : Arg, (∀ x ∈ a.uses, ρ[x]?.isSome = true) → ∃ v, a.eval ρ = some v := by
    intro a ha
    cases a with
    | imm w => exact ⟨w, rfl⟩
    | v x =>
        have hx := ha x (by simp [Arg.uses, Arg.vreg?])
        cases hg : ρ[x]? with
        | none => simp [hg] at hx
        | some v => exact ⟨v, hg⟩
  have haddr : ∀ m : Addr, (∀ x ∈ m.uses, ρ[x]?.isSome = true) → ∃ v, m.eval ρ ctx = some v := by
    intro ⟨mb, mi, disp⟩ hm
    cases mb with
    | none =>
        cases mi with
        | none => exact ⟨Lir.dispWord disp, by simp [Addr.eval]⟩
        | some p =>
            rcases p with ⟨ix, sc⟩
            have hx := hm ix (by simp [Addr.uses])
            cases hg : ρ[ix]? with
            | none => simp [hg] at hx
            | some vi => exact ⟨vi * sc.word + Lir.dispWord disp, by simp [Addr.eval, hg]⟩
    | some b =>
        cases b with
        | ctx =>
            cases mi with
            | none => exact ⟨ctx + Lir.dispWord disp, by simp [Addr.eval]⟩
            | some p =>
                rcases p with ⟨ix, sc⟩
                have hx := hm ix (by simp [Addr.uses])
                cases hg : ρ[ix]? with
                | none => simp [hg] at hx
                | some vi => exact ⟨ctx + vi * sc.word + Lir.dispWord disp, by simp [Addr.eval, hg]⟩
        | v bx =>
            have hbx := hm bx (by simp [Addr.uses, Base.uses])
            cases hgb : ρ[bx]? with
            | none => simp [hgb] at hbx
            | some vb =>
                cases mi with
                | none => exact ⟨vb + Lir.dispWord disp, by simp [Addr.eval, hgb]⟩
                | some p =>
                    rcases p with ⟨ix, sc⟩
                    have hx := hm ix (by simp [Addr.uses])
                    cases hg : ρ[ix]? with
                    | none => simp [hg] at hx
                    | some vi => exact ⟨vb + vi * sc.word + Lir.dispWord disp, by simp [Addr.eval, hgb, hg]⟩
  cases s with
  | store _ _ _ | call _ _ _ => simp [isHoistableStmt] at hh
  | assign x r =>
      refine ⟨rfl, ?_⟩
      have hr : ∃ v, r.eval ρ mem ctx = some v := by
        cases r with
        | arg a => exact harg a hdef
        | addr m => exact haddr m hdef
        | load _ _ _ => simp [isHoistableStmt] at hh
        | select c w a b t f =>
            obtain ⟨va, ha⟩ := harg a (fun u hu => hdef u (by simp [Stmt.uses, Rhs.uses, hu]))
            obtain ⟨vb, hb⟩ := harg b (fun u hu => hdef u (by simp [Stmt.uses, Rhs.uses, hu]))
            obtain ⟨vt, ht⟩ := harg t (fun u hu => hdef u (by simp [Stmt.uses, Rhs.uses, hu]))
            obtain ⟨vf, hf⟩ := harg f (fun u hu => hdef u (by simp [Stmt.uses, Rhs.uses, hu]))
            exact ⟨if c.holds w va vb then vt else vf, by simp [Rhs.eval, ha, hb, ht, hf]⟩
        | test c w a b =>
            obtain ⟨va, ha⟩ := harg a (fun u hu => hdef u (by simp [Stmt.uses, Rhs.uses, hu]))
            obtain ⟨vb, hb⟩ := harg b (fun u hu => hdef u (by simp [Stmt.uses, Rhs.uses, hu]))
            exact ⟨if c.holds w va vb then 1 else 0, by simp [Rhs.eval, ha, hb]⟩
        | bsr64 a =>
            cases a with
            | v _ => simp [isHoistableStmt] at hh
            | imm k =>
                have hnz : (k == 0) = false := by simpa [isHoistableStmt, bne] using hh
                have hne : k ≠ 0 := by intro h0; subst h0; simp at hnz
                exact ⟨UInt64.ofNat k.toNat.log2, by simp [Rhs.eval, hne]⟩
        | bin o w a b =>
            obtain ⟨va, ha⟩ := harg a (fun u hu => hdef u (by simp [Stmt.uses, Rhs.uses, hu]))
            obtain ⟨vb, hb⟩ := harg b (fun u hu => hdef u (by simp [Stmt.uses, Rhs.uses, hu]))
            simp only [isHoistableStmt, Bool.or_eq_true] at hh
            rcases hh with htot | hnz
            · cases o <;> simp [binOpIsTotal] at htot <;>
                exact ⟨_, by simp only [Rhs.eval, ha, hb, Option.bind_eq_bind, Option.bind_some, BinOp.eval]; rfl⟩
            · cases b with
              | v _ => cases hnz
              | imm k =>
                  simp only [Arg.eval, Option.some.injEq] at hb; subst hb
                  have hne : (w.truncate k == 0) = false := by simpa [bne] using hnz
                  cases o <;>
                    exact ⟨_, by
                      simp only [Rhs.eval, ha, Option.bind_eq_bind, Option.bind_some]
                      simp only [Arg.eval, Option.bind_some, BinOp.eval, hne, Bool.false_eq_true, ↓reduceIte]; rfl⟩
      obtain ⟨v, hv⟩ := hr
      refine ⟨ρ.insert x v, by simp [Stmt.exec, hv], ?_, ?_⟩
      · intro d hd; simp only [Stmt.defs, List.mem_singleton] at hd; subst hd; simp
      · intro z hz; simp only [Stmt.defs, List.mem_singleton] at hz; exact env_insert_ne _ _ (Ne.symm hz)
  | limb r1 r2 op =>
      refine ⟨rfl, ?_⟩
      have hop : ∃ v1 v2, op.eval ρ = some (v1, v2) := by
        cases op with
        | divWide64 _ _ _ => simp [isHoistableStmt] at hh
        | mulWide64 a b =>
            obtain ⟨va, ha⟩ := harg a (fun u hu => hdef u (by simp [Stmt.uses, LimbOp.uses, hu]))
            obtain ⟨vb, hb⟩ := harg b (fun u hu => hdef u (by simp [Stmt.uses, LimbOp.uses, hu]))
            exact ⟨_, _, by simp only [LimbOp.eval, ha, hb, Option.bind_eq_bind, Option.bind_some]; rfl⟩
        | addCarry64 a b c =>
            obtain ⟨va, ha⟩ := harg a (fun u hu => hdef u (by simp [Stmt.uses, LimbOp.uses, hu]))
            obtain ⟨vb, hb⟩ := harg b (fun u hu => hdef u (by simp [Stmt.uses, LimbOp.uses, hu]))
            obtain ⟨vc, hc⟩ := harg c (fun u hu => hdef u (by simp [Stmt.uses, LimbOp.uses, hu]))
            exact ⟨_, _, by simp only [LimbOp.eval, ha, hb, hc, Option.bind_eq_bind, Option.bind_some]; rfl⟩
        | subBorrow64 a b c =>
            obtain ⟨va, ha⟩ := harg a (fun u hu => hdef u (by simp [Stmt.uses, LimbOp.uses, hu]))
            obtain ⟨vb, hb⟩ := harg b (fun u hu => hdef u (by simp [Stmt.uses, LimbOp.uses, hu]))
            obtain ⟨vc, hc⟩ := harg c (fun u hu => hdef u (by simp [Stmt.uses, LimbOp.uses, hu]))
            exact ⟨_, _, by simp only [LimbOp.eval, ha, hb, hc, Option.bind_eq_bind, Option.bind_some]; rfl⟩
      obtain ⟨v1, v2, hv⟩ := hop
      refine ⟨(ρ.insert r1 v1).insert r2 v2, by simp [Stmt.exec, hv], ?_, ?_⟩
      · intro d hd
        simp only [Stmt.defs, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · rw [env_insert_get]; split <;> simp
        · simp
      · intro z hz
        simp only [Stmt.defs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        rw [env_insert_ne _ _ (Ne.symm hz.2), env_insert_ne _ _ (Ne.symm hz.1)]

/-- `emitOvfLimb` computes exact `(o.eval va vb).1` into `x` and a word `fv` into `flag`
such that `fv ≠ 0 ↔ (o.eval va vb).2 = true`. -/
theorem emitOvfLimb_exec {o : Ovf} {x flag : VReg} {a b : Arg} {ρ : Env} {mem : X86.Memory}
    {ctx : Word} {va vb : Word} (ha : a.eval ρ = some va) (hb : b.eval ρ = some vb) :
    ∃ fv : Word,
      (emitOvfLimb o x flag a b).exec ρ mem ctx =
        some (((ρ.insert x (o.eval va vb).1).insert flag fv), mem) ∧
      (fv ≠ 0 ↔ (o.eval va vb).2 = true) := by
  cases o with
  | addC =>
      refine ⟨if 2 ^ 64 ≤ va.toNat + vb.toNat + 0 then 1 else 0, ?_, ?_⟩
      · have h0 : UInt64.ofNat 0 = 0 := rfl
        have hc0 : (Arg.imm 0).eval ρ = some 0 := rfl
        simp only [emitOvfLimb, Stmt.exec, LimbOp.eval, ha, hb, hc0, Option.bind_eq_bind,
          Option.bind_some, beq_self_eq_true, ↓reduceIte, h0, UInt64.add_zero, Ovf.eval]
      · have hva : va.toNat < 2 ^ 64 := va.toNat_lt_size
        have hvb : vb.toNat < 2 ^ 64 := vb.toNat_lt_size
        simp only [Ovf.eval, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.add_zero]
        by_cases h : 2 ^ 64 ≤ va.toNat + vb.toNat
        · have hmod : (va.toNat + vb.toNat) % 2 ^ 64 = va.toNat + vb.toNat - 2 ^ 64 := by omega
          simp only [h, ↓reduceIte, hmod]
          exact ⟨fun _ => by omega, fun _ => by decide⟩
        · have hmod : (va.toNat + vb.toNat) % 2 ^ 64 = va.toNat + vb.toNat := Nat.mod_eq_of_lt (by omega)
          simp only [h, ↓reduceIte, hmod]
          exact ⟨fun hc => absurd rfl hc, fun hlt => by omega⟩
  | subB =>
      refine ⟨if va.toNat < vb.toNat + 0 then 1 else 0, ?_, ?_⟩
      · have h0 : UInt64.ofNat 0 = 0 := rfl
        have hc0 : (Arg.imm 0).eval ρ = some 0 := rfl
        simp only [emitOvfLimb, Stmt.exec, LimbOp.eval, ha, hb, hc0, Option.bind_eq_bind,
          Option.bind_some, beq_self_eq_true, ↓reduceIte, h0, UInt64.sub_zero, Ovf.eval]
      · simp only [Ovf.eval, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, Nat.add_zero]
        by_cases h : va.toNat < vb.toNat <;> simp [h]
  | mulOvf =>
      refine ⟨UInt64.ofNat ((va.toNat * vb.toNat) / 2 ^ 64), ?_, ?_⟩
      · simp only [emitOvfLimb, Stmt.exec, LimbOp.eval, ha, hb, Option.bind_eq_bind,
          Option.bind_some, Ovf.eval]
      · have hhi_lt : (va.toNat * vb.toNat) / 2 ^ 64 < 2 ^ 64 := by
          rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 64)]
          exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right vb.toNat (Nat.le_of_lt va.toNat_lt_size))
            (Nat.mul_lt_mul_of_pos_left vb.toNat_lt_size (by decide))
        simp only [Ovf.eval, decide_eq_true_eq]
        constructor
        · intro hne
          have hnat : (UInt64.ofNat ((va.toNat * vb.toNat) / 2 ^ 64)).toNat ≠ 0 := fun h0 =>
            hne (UInt64.toNat_inj.mp h0)
          rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hhi_lt] at hnat
          by_cases hge : 2 ^ 64 ≤ va.toNat * vb.toNat
          · exact hge
          · have hdiv0 : (va.toNat * vb.toNat) / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
            exact absurd hdiv0 hnat
        · intro hge h0
          have hnat := congrArg UInt64.toNat h0
          rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hhi_lt] at hnat
          have : 1 ≤ (va.toNat * vb.toNat) / 2 ^ 64 := Nat.div_pos hge (by decide)
          change (va.toNat * vb.toNat) / 2 ^ 64 = 0 at hnat
          omega

theorem emitOvfLimb_isCall (o : Ovf) (x flag : VReg) (a b : Arg) :
    (emitOvfLimb o x flag a b).isCall = false := by
  cases o <;> rfl

theorem loopMapStmt_isHoistable {defs : Src.NatSet} {off k : Nat} {s : Stmt}
    (hh : isHoistableStmt s = true) :
    isHoistableStmt (loopMapStmt defs off k s) = true := by
  cases s with
  | assign x r =>
      cases r with
      | arg _ | addr _ | select _ _ _ _ _ _ | test _ _ _ _ => rfl
      | load _ _ _ => simp [isHoistableStmt] at hh
      | bsr64 a =>
          cases a with
          | v _ => simp [isHoistableStmt] at hh
          | imm _ => exact hh
      | bin o w a b =>
          cases b with
          | v _ => simpa [loopMapStmt, loopMapRhs, loopMapArg, isHoistableStmt] using hh
          | imm _ => simpa [loopMapStmt, loopMapRhs, loopMapArg, isHoistableStmt] using hh
  | limb r1 r2 op =>
      cases op <;> simp [loopMapStmt, loopMapLimb, isHoistableStmt] at hh ⊢
  | store _ _ _ | call _ _ _ => simp [isHoistableStmt] at hh

theorem loopMapArg_uses {defs : Src.NatSet} {off k : Nat} {a : Arg} :
    (loopMapArg defs off k a).uses = a.uses.map (loopMapReg defs off k) := by
  cases a <;> rfl

theorem loopMapStmt_uses {defs : Src.NatSet} {off k : Nat} {s : Stmt} :
    (loopMapStmt defs off k s).uses = s.uses.map (loopMapReg defs off k) := by
  cases s with
  | assign x r =>
      cases r with
      | arg a => simp [loopMapStmt, loopMapRhs, Stmt.uses, Rhs.uses, loopMapArg_uses]
      | bin o w a b => simp [loopMapStmt, loopMapRhs, Stmt.uses, Rhs.uses, loopMapArg_uses]
      | select c w a b t f => simp [loopMapStmt, loopMapRhs, Stmt.uses, Rhs.uses, loopMapArg_uses]
      | test c w a b => simp [loopMapStmt, loopMapRhs, Stmt.uses, Rhs.uses, loopMapArg_uses]
      | bsr64 a => simp [loopMapStmt, loopMapRhs, Stmt.uses, Rhs.uses, loopMapArg_uses]
      | load w e m | addr m =>
          rcases m with ⟨mb, mi, disp⟩
          cases mb with
          | none =>
              cases mi <;> simp [loopMapStmt, loopMapRhs, loopMapAddr, Stmt.uses, Rhs.uses, Addr.uses]
          | some b => cases b with
            | ctx =>
                cases mi <;> simp [loopMapStmt, loopMapRhs, loopMapAddr, loopMapBase, Stmt.uses, Rhs.uses, Addr.uses, Base.uses]
            | v r =>
                cases mi <;> simp [loopMapStmt, loopMapRhs, loopMapAddr, loopMapBase, Stmt.uses, Rhs.uses, Addr.uses, Base.uses]
  | limb r1 r2 op =>
      cases op <;> simp [loopMapStmt, loopMapLimb, Stmt.uses, LimbOp.uses, loopMapArg_uses]
  | store w m a =>
      rcases m with ⟨mb, mi, disp⟩
      cases mb with
      | none =>
          cases mi <;> simp [loopMapStmt, loopMapAddr, Stmt.uses, Addr.uses, loopMapArg_uses]
      | some b => cases b with
        | ctx =>
            cases mi <;> simp [loopMapStmt, loopMapAddr, loopMapBase, Stmt.uses, Addr.uses, Base.uses, loopMapArg_uses]
        | v r =>
            cases mi <;> simp [loopMapStmt, loopMapAddr, loopMapBase, Stmt.uses, Addr.uses, Base.uses, loopMapArg_uses]
  | call rs f as =>
      simp only [loopMapStmt, Stmt.uses, Lir.argsUses]
      induction as with
      | nil => rfl
      | cons a rest ih => simp only [List.map_cons, List.flatMap_cons, List.map_append, loopMapArg_uses, ih]

theorem loopMapStmt_defs {defs : Src.NatSet} {off k : Nat} {s : Stmt} :
    (loopMapStmt defs off k s).defs = s.defs.map (loopMapReg defs off k) := by
  cases s <;> simp [loopMapStmt, Stmt.defs]

/-! ## Speculative execution of `loopMapStmt` and `emitSpeculativeArm` -/

/-- Exact evaluation agreement between `s` in `ρ₁` and `loopMapStmt defs off k s` in `ρ₂`. -/
theorem loopMapArg_eval {defs : Src.NatSet} {off k : Nat} {ρ₁ ρ₂ : Env} {a : Arg} {v : Word}
    (hagree : ∀ x ∈ a.uses, ∀ vx, ρ₁[x]? = some vx → ρ₂[loopMapReg defs off k x]? = some vx)
    (ha : a.eval ρ₁ = some v) :
    (loopMapArg defs off k a).eval ρ₂ = some v := by
  cases a with
  | imm w => exact ha
  | v x => exact hagree x (by simp [Arg.uses, Arg.vreg?]) v ha

theorem loopMapAddr_eval {defs : Src.NatSet} {off k : Nat} {ρ₁ ρ₂ : Env} {ctx : Word} {m : Addr} {va : Word}
    (hagree : ∀ x ∈ m.uses, ∀ vx, ρ₁[x]? = some vx → ρ₂[loopMapReg defs off k x]? = some vx)
    (hm : m.eval ρ₁ ctx = some va) :
    (loopMapAddr defs off k m).eval ρ₂ ctx = some va := by
  rcases m with ⟨mb, mi, disp⟩
  cases mb with
  | none =>
      cases mi with
      | none => exact hm
      | some p =>
          rcases p with ⟨ix, sc⟩
          simp only [Addr.eval, Option.bind_eq_bind, Option.bind_some, Option.map_eq_map,
            Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hm
          obtain ⟨_, ⟨vx, hvx, rfl⟩, rfl⟩ := hm
          have hvx2 := hagree ix (by simp [Addr.uses]) vx hvx
          simp [loopMapAddr, Addr.eval, hvx2]
  | some b =>
      cases b with
      | ctx =>
          cases mi with
          | none => exact hm
          | some p =>
              rcases p with ⟨ix, sc⟩
              simp only [Addr.eval, Option.bind_eq_bind, Option.bind_some, Option.map_eq_map,
                Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hm
              obtain ⟨_, ⟨vx, hvx, rfl⟩, rfl⟩ := hm
              have hvx2 := hagree ix (by simp [Addr.uses]) vx hvx
              simp [loopMapAddr, loopMapBase, Addr.eval, hvx2]
      | v bx =>
          cases mi with
          | none =>
              simp only [Addr.eval, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at hm
              obtain ⟨vb, hvb, rfl⟩ := hm
              have hvb2 := hagree bx (by simp [Addr.uses, Base.uses]) vb hvb
              simp [loopMapAddr, loopMapBase, Addr.eval, hvb2]
          | some p =>
              rcases p with ⟨ix, sc⟩
              simp only [Addr.eval, Option.bind_eq_bind, Option.map_eq_map,
                Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hm
              obtain ⟨vb, hvb, _, ⟨vx, hvx, rfl⟩, rfl⟩ := hm
              have hvb2 := hagree bx (by simp [Addr.uses, Base.uses]) vb hvb
              have hvx2 := hagree ix (by simp [Addr.uses]) vx hvx
              simp [loopMapAddr, loopMapBase, Addr.eval, hvb2, hvx2]

theorem loopMapStmt_exec_agree {defs : Src.NatSet} {off k : Nat} {ρ₁ ρ₂ ρ₁' : Env}
    {mem mem' : X86.Memory} {ctx : Word} {s : Stmt}
    (hk : 0 < k)
    (hdefs : ∀ d ∈ s.defs, defs.contains d = true)
    (hdefsLt : ∀ d ∈ s.defs, d < off)
    (hagree : ∀ x ∈ s.uses, ∀ vx, ρ₁[x]? = some vx → ρ₂[loopMapReg defs off k x]? = some vx)
    (hnc : s.isCall = false)
    (hx : s.exec ρ₁ mem ctx = some (ρ₁', mem')) :
    ∃ ρ₂', (loopMapStmt defs off k s).exec ρ₂ mem ctx = some (ρ₂', mem') ∧
      (∀ d ∈ s.defs, ∀ v, ρ₁'[d]? = some v → ρ₂'[k * off + d]? = some v) ∧
      (∀ z, (∀ d ∈ s.defs, z ≠ k * off + d) → ρ₂'[z]? = ρ₂[z]?) ∧
      (∀ x, x ∉ s.defs → ρ₁'[x]? = ρ₁[x]?) := by
  cases s with
  | call _ _ _ => simp [Stmt.isCall] at hnc
  | store w m a =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
      obtain ⟨va, hm, vv, ha, hw⟩ := hx
      cases hwr : mem.write? w va vv with
      | error _ => rw [hwr] at hw; cases hw
      | ok m2 =>
          rw [hwr] at hw; simp only [Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have hm2 := loopMapAddr_eval (fun x hx => hagree x (by simp [Stmt.uses, hx])) hm
          have ha2 := loopMapArg_eval (fun x hx => hagree x (by simp [Stmt.uses, hx])) ha
          exact ⟨ρ₂, by simp [loopMapStmt, Stmt.exec, hm2, ha2, hwr],
            (fun _ h => by cases h), (fun _ _ => rfl), (fun _ _ => rfl)⟩
  | assign x r =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hx
      obtain ⟨v, hv, rfl, rfl⟩ := hx
      have hv2 : (loopMapRhs defs off k r).eval ρ₂ mem ctx = some v := by
        cases r with
        | arg a => exact loopMapArg_eval hagree hv
        | addr m => exact loopMapAddr_eval hagree hv
        | load w e m =>
            simp only [loopMapRhs, Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv ⊢
            obtain ⟨va, hm, hld⟩ := hv
            exact ⟨va, loopMapAddr_eval hagree hm, hld⟩
        | bin o w a b =>
            simp only [loopMapRhs, Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv ⊢
            obtain ⟨va, ha, vb, hb, ho⟩ := hv
            exact ⟨va, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, Rhs.uses, hu])) ha,
              vb, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, Rhs.uses, hu])) hb, ho⟩
        | select c w a b t f =>
            simp only [loopMapRhs, Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv ⊢
            obtain ⟨va, ha, vb, hb, vt, ht, vf, hf, rfl⟩ := hv
            exact ⟨va, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, Rhs.uses, hu])) ha,
              vb, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, Rhs.uses, hu])) hb,
              vt, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, Rhs.uses, hu])) ht,
              vf, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, Rhs.uses, hu])) hf, rfl⟩
        | test c w a b =>
            simp only [loopMapRhs, Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv ⊢
            obtain ⟨va, ha, vb, hb, rfl⟩ := hv
            exact ⟨va, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, Rhs.uses, hu])) ha,
              vb, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, Rhs.uses, hu])) hb, rfl⟩
        | bsr64 a =>
            simp only [loopMapRhs, Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv ⊢
            obtain ⟨va, ha, hres⟩ := hv
            exact ⟨va, loopMapArg_eval hagree ha, hres⟩
      have hmx : loopMapReg defs off k x = k * off + x :=
        loopMapReg_mem_pos hk (hdefs x (by simp [Stmt.defs]))
      refine ⟨ρ₂.insert (k * off + x) v, by simp [loopMapStmt, Stmt.exec, hv2, hmx], ?_, ?_, ?_⟩
      · intro d hd val hval
        simp only [Stmt.defs, List.mem_singleton] at hd; subst hd
        rw [env_insert_self] at hval; cases hval; exact env_insert_self _ _ _
      · intro z hz
        exact env_insert_ne _ _ (Ne.symm (hz x (by simp [Stmt.defs])))
      · intro u hu
        simp only [Stmt.defs, List.mem_singleton] at hu
        exact env_insert_ne _ _ (Ne.symm hu)
  | limb r1 r2 op =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hx
      obtain ⟨⟨v1, v2⟩, hop, rfl, rfl⟩ := hx
      have hop2 : (loopMapLimb defs off k op).eval ρ₂ = some (v1, v2) := by
        cases op with
        | mulWide64 a b =>
            simp only [loopMapLimb, LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hop ⊢
            obtain ⟨va, ha, vb, hb, he⟩ := hop
            exact ⟨va, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, LimbOp.uses, hu])) ha,
              vb, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, LimbOp.uses, hu])) hb, he⟩
        | divWide64 hi lo d =>
            simp only [loopMapLimb, LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hop ⊢
            obtain ⟨vhi, hhi, vlo, hlo, vd, hd, hres⟩ := hop
            exact ⟨vhi, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, LimbOp.uses, hu])) hhi,
              vlo, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, LimbOp.uses, hu])) hlo,
              vd, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, LimbOp.uses, hu])) hd, hres⟩
        | addCarry64 a b c =>
            simp only [loopMapLimb, LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hop ⊢
            obtain ⟨va, ha, vb, hb, vc, hc, he⟩ := hop
            exact ⟨va, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, LimbOp.uses, hu])) ha,
              vb, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, LimbOp.uses, hu])) hb,
              vc, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, LimbOp.uses, hu])) hc, he⟩
        | subBorrow64 a b c =>
            simp only [loopMapLimb, LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hop ⊢
            obtain ⟨va, ha, vb, hb, vc, hc, he⟩ := hop
            exact ⟨va, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, LimbOp.uses, hu])) ha,
              vb, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, LimbOp.uses, hu])) hb,
              vc, loopMapArg_eval (fun u hu => hagree u (by simp [Stmt.uses, LimbOp.uses, hu])) hc, he⟩
      have hm1 : loopMapReg defs off k r1 = k * off + r1 :=
        loopMapReg_mem_pos hk (hdefs r1 (by simp [Stmt.defs]))
      have hm2 : loopMapReg defs off k r2 = k * off + r2 :=
        loopMapReg_mem_pos hk (hdefs r2 (by simp [Stmt.defs]))
      refine ⟨(ρ₂.insert (k * off + r1) v1).insert (k * off + r2) v2,
        by simp [loopMapStmt, Stmt.exec, hop2, hm1, hm2], ?_, ?_, ?_⟩
      · intro d hd val hval
        simp only [Stmt.defs, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · by_cases heq : d = r2
          · subst heq; rw [env_insert_self] at hval ⊢; exact hval
          · rw [env_insert_ne _ _ (Ne.symm heq), env_insert_self] at hval
            rw [env_insert_ne _ _ (fun h => heq (Nat.add_left_cancel h).symm), env_insert_self]; exact hval
        · rw [env_insert_self] at hval ⊢; exact hval
      · intro z hz
        rw [env_insert_ne _ _ (Ne.symm (hz r2 (by simp [Stmt.defs]))),
            env_insert_ne _ _ (Ne.symm (hz r1 (by simp [Stmt.defs])))]
      · intro u hu
        simp only [Stmt.defs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
        rw [env_insert_ne _ _ (Ne.symm hu.2), env_insert_ne _ _ (Ne.symm hu.1)]

/-- Helper: `foldl insert` on `NatSet` containment characterization. -/
theorem natSet_foldl_insert_contains :
    ∀ (xs : List VReg) (s : Src.NatSet) (y : VReg),
      (xs.foldl (fun a x => a.insert x) s).contains y = true ↔ y ∈ xs ∨ s.contains y = true
  | [], s, y => by simp
  | x :: rest, s, y => by
      simp only [List.foldl_cons, List.mem_cons]
      rw [natSet_foldl_insert_contains rest (s.insert x) y]
      have hins : (s.insert x).contains y = true ↔ y = x ∨ s.contains y = true := by
        simp only [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert]
        by_cases h : y = x <;> simp [h]
      rw [hins]
      constructor
      · rintro (hr | hx | hs)
        · exact .inl (.inr hr)
        · exact .inl (.inl hx)
        · exact .inr hs
      · rintro ((hx | hr) | hs)
        · exact .inr (.inl hx)
        · exact .inl hr
        · exact .inr (.inr hs)

private theorem execList_append_ifconv {ρ ρ₁ ρ₂ : Env} {mem mem₁ mem₂ : X86.Memory} {ctx : Word} :
    ∀ {xs ys : List Stmt},
      execList ρ mem ctx xs = some (ρ₁, mem₁) →
      execList ρ₁ mem₁ ctx ys = some (ρ₂, mem₂) →
      execList ρ mem ctx (xs ++ ys) = some (ρ₂, mem₂)
  | [], _, h1, h2 => by simp only [execList, Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1; exact h2
  | s :: xs, ys, h1, h2 => by
      simp only [execList] at h1
      split at h1
      · rename_i ρ' mem' hs
        simp only [List.cons_append, execList, hs]
        exact execList_append_ifconv h1 h2
      · cases h1

/-- Total pure execution of a shifted statement list from `checkStmtsAvail`. -/
theorem exec_shifted_pure_stmts {defs : Src.NatSet} {off k : Nat} (hk : 0 < k) :
    ∀ {ss : List Stmt} {av0 av1 : Src.NatSet} {ρ₂ : Env} {mem : X86.Memory} {ctx : Word},
      ss.all isHoistableStmt = true →
      checkStmtsAvail defs av0 ss = some av1 →
      (∀ s ∈ ss, ∀ d ∈ s.defs, defs.contains d = true ∧ d < off) →
      (∀ s ∈ ss, ∀ x ∈ s.uses, defs.contains x = false → ρ₂[x]?.isSome = true) →
      (∀ x, av0.contains x = true → ρ₂[loopMapReg defs off k x]?.isSome = true) →
      (∀ s ∈ ss, (loopMapStmt defs off k s).isCall = false) ∧
      ∃ ρ₂', execList ρ₂ mem ctx (ss.map (loopMapStmt defs off k)) = some (ρ₂', mem) ∧
        (∀ x, av1.contains x = true → ρ₂'[loopMapReg defs off k x]?.isSome = true) ∧
        (∀ z, z < k * off ∨ (k + 1) * off ≤ z → ρ₂'[z]? = ρ₂[z]?)
  | [], av0, av1, ρ₂, _, _, _, hck, _, _, hav0 => by
      simp only [checkStmtsAvail, Option.some.injEq] at hck; subst hck
      exact ⟨(fun _ h => by cases h), ρ₂, rfl, hav0, fun _ _ => rfl⟩
  | s :: rest, av0, av1, ρ₂, mem, ctx, hhoist, hck, hdefs, houter, hav0 => by
      simp only [List.all_cons, Bool.and_eq_true] at hhoist
      simp only [checkStmtsAvail] at hck
      split at hck
      · rename_i huses
        simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at huses
        have hs_hoist : isHoistableStmt (loopMapStmt defs off k s) = true :=
          loopMapStmt_isHoistable hhoist.1
        have hs_def : ∀ y ∈ (loopMapStmt defs off k s).uses, ρ₂[y]?.isSome = true := by
          intro y hy
          rw [loopMapStmt_uses, List.mem_map] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          rcases huses x hx with hnot | hav
          · rw [loopMapReg_not_mem hnot]
            exact houter s (by simp) x hx hnot
          · exact hav0 x hav
        obtain ⟨hnc_s, ρ₂1, hx1, hdef1, hother1⟩ :=
          isHoistableStmt_exec (mem := mem) (ctx := ctx) hs_hoist hs_def
        have hpres1 : ∀ z, z < k * off ∨ (k + 1) * off ≤ z → ρ₂1[z]? = ρ₂[z]? := by
          intro z hz
          apply hother1 z
          rw [loopMapStmt_defs, List.mem_map]
          rintro ⟨d, hd, rfl⟩
          obtain ⟨hdm, hdlt⟩ := hdefs s (by simp) d hd
          have hge := loopMapReg_ge_of_mem (off := off) hk hdm
          have hlt := loopMapReg_lt_of_mem (off := off) hk hdm hdlt
          rcases hz with h1 | h2
          · exact Nat.not_lt.2 hge h1
          · exact Nat.not_lt.2 h2 hlt
        have hav1_ok : ∀ x, (s.defs.foldl (fun a d => a.insert d) av0).contains x = true →
            ρ₂1[loopMapReg defs off k x]?.isSome = true := by
          intro x hx
          rw [natSet_foldl_insert_contains] at hx
          rcases hx with hxd | hx0
          · exact hdef1 _ (by rw [loopMapStmt_defs]; exact List.mem_map.2 ⟨x, hxd, rfl⟩)
          · by_cases hmem : loopMapReg defs off k x ∈ (loopMapStmt defs off k s).defs
            · exact hdef1 _ hmem
            · rw [hother1 _ hmem]; exact hav0 x hx0
        have houter_rest : ∀ s' ∈ rest, ∀ x ∈ s'.uses, defs.contains x = false → ρ₂1[x]?.isSome = true := by
          intro s' hs' x hx hnot
          by_cases hmem : x ∈ (loopMapStmt defs off k s).defs
          · exact hdef1 x hmem
          · rw [hother1 x hmem]; exact houter s' (by simp [hs']) x hx hnot
        obtain ⟨hnc_r, ρ₂', hxr, hav_end, hpres_r⟩ :=
          exec_shifted_pure_stmts (mem := mem) (ctx := ctx) hk hhoist.2 hck
            (fun s' hs' => hdefs s' (by simp [hs']))
            houter_rest hav1_ok
        refine ⟨fun s' hs' => ?_, ρ₂', by simp [execList, hx1, hxr], hav_end, fun z hz => by
          rw [hpres_r z hz, hpres1 z hz]⟩
        simp only [List.mem_cons] at hs'
        rcases hs' with rfl | hs'
        · exact hnc_s
        · exact hnc_r s' hs'
      · cases hck

/-- Speculative execution of `emitSpeculativeArm` ALWAYS succeeds without modifying memory,
leaves all registers outside `[k * off, (k + 1) * off) ∪ [flagBase, frOut)` untouched,
evaluates `flagArg` to `some _`, and defines all `armDefs` registers (reached at end of arm). -/
theorem emitSpeculativeArm_total {arm : DiamondArm} {armDefs : Src.NatSet} {off k flagBase : Nat}
    (hk : 0 < k) (hfb : (k + 1) * off ≤ flagBase)
    (hpure : checkArmPure arm armDefs = true)
    (hregs : ∀ st ∈ arm.steps,
      (∀ s ∈ st.body, ∀ d ∈ s.defs, armDefs.contains d = true ∧ d < off) ∧
      (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) → armDefs.contains x = true ∧ x < off))
    (houter : ∀ st ∈ arm.steps,
      (∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → x < off) ∧
      (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
        ∀ u ∈ oa.uses ++ ob.uses, armDefs.contains u = false → u < off))
    {ρ₂ : Env} {mem : X86.Memory} {ctx : Word}
    (hdefOuter : ∀ st ∈ arm.steps,
      (∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → ρ₂[x]?.isSome = true) ∧
      (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
        ∀ u ∈ oa.uses ++ ob.uses, armDefs.contains u = false → ρ₂[u]?.isSome = true)) :
    let (stmts, flagArg, frOut) := emitSpeculativeArm armDefs off k arm flagBase
    flagBase ≤ frOut ∧
    (∀ s ∈ stmts, s.isCall = false) ∧
    (∀ x ∈ flagArg.uses, flagBase ≤ x ∧ x < frOut) ∧
    ∃ (ρ₂' : Env) (avEnd : Src.NatSet),
      execList ρ₂ mem ctx stmts = some (ρ₂', mem) ∧
      (∀ x, avEnd.contains x = true → ρ₂'[loopMapReg armDefs off k x]?.isSome = true) ∧
      (∀ a ∈ arm.joinArgs, ∀ x ∈ a.uses, armDefs.contains x = true → avEnd.contains x = true) ∧
      (∃ fv, flagArg.eval ρ₂' = some fv) ∧
      (∀ z, (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ frOut ≤ z) → ρ₂'[z]? = ρ₂[z]?) := by
  have hfold : ∀ (steps : List ArmStep) (acc : List Stmt) (curFlag : Arg) (nextReg : Nat)
      (av : Src.NatSet) (ρCur : Env),
      flagBase ≤ nextReg →
      (∀ s ∈ acc, s.isCall = false) →
      (∀ (x : Nat), x ∈ curFlag.uses → flagBase ≤ x ∧ x < nextReg) →
      (∃ fv, curFlag.eval ρCur = some fv) →
      execList ρ₂ mem ctx acc = some (ρCur, mem) →
      (∀ x, av.contains x = true → ρCur[loopMapReg armDefs off k x]?.isSome = true) →
      (∀ z, (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ nextReg ≤ z) → ρCur[z]? = ρ₂[z]?) →
      checkArmPure.go arm armDefs av steps = true →
      (∀ st ∈ steps,
        (∀ s ∈ st.body, ∀ d ∈ s.defs, armDefs.contains d = true ∧ d < off) ∧
        (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) → armDefs.contains x = true ∧ x < off)) →
      (∀ st ∈ steps,
        (∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → x < off) ∧
        (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
          ∀ u ∈ oa.uses ++ ob.uses, armDefs.contains u = false → u < off)) →
      (∀ st ∈ steps,
        (∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → ρ₂[x]?.isSome = true) ∧
        (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
          ∀ u ∈ oa.uses ++ ob.uses, armDefs.contains u = false → ρ₂[u]?.isSome = true)) →
      let (stmts, flagArg, frOut) :=
        steps.foldl (init := (acc, curFlag, nextReg)) fun (acc, curFlag, nextReg) st =>
          let bodyShifted := st.body.map (loopMapStmt armDefs off k)
          match st.ovf? with
          | none => (acc ++ bodyShifted, curFlag, nextReg)
          | some (o, x, oa, ob, _) =>
              let x' := loopMapReg armDefs off k x
              let oa' := loopMapArg armDefs off k oa
              let ob' := loopMapArg armDefs off k ob
              let fReg := nextReg
              let limbSt := emitOvfLimb o x' fReg oa' ob'
              match curFlag with
              | .imm 0 => (acc ++ bodyShifted ++ [limbSt], .v fReg, nextReg + 1)
              | _ =>
                  let orReg := nextReg + 1
                  let orSt := Stmt.assign orReg (.bin .or .w64 curFlag (.v fReg))
                  (acc ++ bodyShifted ++ [limbSt, orSt], .v orReg, nextReg + 2)
      flagBase ≤ frOut ∧
      (∀ s ∈ stmts, s.isCall = false) ∧
      (∀ x ∈ flagArg.uses, flagBase ≤ x ∧ x < frOut) ∧
      ∃ (ρ₂' : Env) (avEnd : Src.NatSet),
        execList ρ₂ mem ctx stmts = some (ρ₂', mem) ∧
        (∀ x, avEnd.contains x = true → ρ₂'[loopMapReg armDefs off k x]?.isSome = true) ∧
        (∀ a ∈ arm.joinArgs, ∀ x ∈ a.uses, armDefs.contains x = true → avEnd.contains x = true) ∧
        (∃ fv, flagArg.eval ρ₂' = some fv) ∧
        (∀ z, (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ frOut ≤ z) → ρ₂'[z]? = ρ₂[z]?) := by
    intro steps
    induction steps with
    | nil =>
        intro acc curFlag nextReg av ρCur hle hnc hfu hfev hex hav hpres hp _ _ _
        simp only [List.foldl_nil]
        refine ⟨hle, hnc, hfu, ρCur, av, hex, hav, ?_, hfev, hpres⟩
        intro a ha x hx hdm
        simp only [checkArmPure.go, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hp
        rcases hp a ha x hx with hnot | hav'
        · rw [hdm] at hnot; cases hnot
        · exact hav'
    | cons st rest ih =>
        intro acc curFlag nextReg av ρCur hle hnc hfu hfev hex hav hpres hp hrg hou hdo
        simp only [List.foldl_cons]
        simp only [checkArmPure.go] at hp
        split at hp
        · cases hp
        · rename_i hhoist
          have hhoist' : st.body.all isHoistableStmt = true := by simpa using hhoist
          cases hck : checkStmtsAvail armDefs av st.body with
          | none => rw [hck] at hp; cases hp
          | some av1 =>
              rw [hck] at hp; dsimp only at hp
              have hdo_st := hdo st (by simp)
              have hou_st := hou st (by simp)
              have hrg_st := hrg st (by simp)
              have houterCur : ∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → ρCur[x]?.isSome = true := by
                intro s hs x hx hnot
                have hxlt := hou_st.1 s hs x hx hnot
                rw [hpres x (.inl (Nat.lt_of_lt_of_le hxlt (Nat.le_mul_of_pos_left off hk)))]
                exact hdo_st.1 s hs x hx hnot
              obtain ⟨hnc_b, ρ1, hxb, hav1, hpres_b⟩ :=
                exec_shifted_pure_stmts (mem := mem) (ctx := ctx) hk hhoist' hck hrg_st.1 houterCur hav
              have hex1 : execList ρ₂ mem ctx (acc ++ st.body.map (loopMapStmt armDefs off k)) = some (ρ1, mem) :=
                execList_append_ifconv hex hxb
              have hpres1 : ∀ z, (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ nextReg ≤ z) → ρ1[z]? = ρ₂[z]? := by
                intro z hz
                have hz' : z < k * off ∨ (k + 1) * off ≤ z := by
                  rcases hz with h1 | ⟨h2, _⟩ | h3
                  · exact .inl h1
                  · exact .inr h2
                  · exact .inr (by omega)
                rw [hpres_b z hz', hpres z hz]
              have hfev1 : ∃ fv, curFlag.eval ρ1 = some fv := by
                obtain ⟨fv, hfv⟩ := hfev
                refine ⟨fv, ?_⟩
                cases curFlag with
                | imm w => exact hfv
                | v r =>
                    have hr := hfu r (by simp [Arg.uses, Arg.vreg?])
                    rw [Arg.eval, hpres_b r (.inr (Nat.le_trans hfb hr.1))]; exact hfv
              cases hov : st.ovf? with
              | none =>
                  rw [hov] at hp; dsimp only at hp
                  exact ih (acc ++ st.body.map (loopMapStmt armDefs off k)) curFlag nextReg av1 ρ1
                    hle
                    (fun s hs => by
                      simp only [List.mem_append] at hs
                      rcases hs with h1 | h2
                      · exact hnc s h1
                      · rw [List.mem_map] at h2; obtain ⟨s0, hs0, rfl⟩ := h2; exact hnc_b s0 hs0)
                    hfu hfev1 hex1 hav1 hpres1 hp
                    (fun s' hs' => hrg s' (by simp [hs']))
                    (fun s' hs' => hou s' (by simp [hs']))
                    (fun s' hs' => hdo s' (by simp [hs']))
              | some ovfTuple =>
                  rcases ovfTuple with ⟨o, x, oa, ob, res⟩
                  rw [hov] at hp; dsimp only at hp
                  split at hp
                  · rename_i hou_ovf
                    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hou_ovf
                    obtain ⟨hxm, hxlt⟩ := hrg_st.2 o x oa ob res hov
                    have hevalArg : ∀ (a : Arg), (∀ u ∈ a.uses, u ∈ oa.uses ++ ob.uses) →
                        ∃ v, (loopMapArg armDefs off k a).eval ρ1 = some v := by
                      intro a ha
                      cases a with
                      | imm w => exact ⟨w, rfl⟩
                      | v u =>
                          have hu := ha u (by simp [Arg.uses, Arg.vreg?])
                          rcases hou_ovf u hu with hnot | havu
                          · rw [loopMapArg, loopMapReg_not_mem hnot]
                            have hult := hou_st.2 o x oa ob res hov u hu hnot
                            have hdefu := hdo_st.2 o x oa ob res hov u hu hnot
                            have h1 : ρ1[u]? = ρ₂[u]? := hpres1 u (.inl (Nat.lt_of_lt_of_le hult (Nat.le_mul_of_pos_left off hk)))
                            rw [Arg.eval, h1]
                            cases hg : ρ₂[u]? with
                            | none => simp [hg] at hdefu
                            | some v => exact ⟨v, rfl⟩
                          · have hd := hav1 u havu
                            rw [loopMapArg, Arg.eval]
                            cases hg : ρ1[loopMapReg armDefs off k u]? with
                            | none => simp [hg] at hd
                            | some v => exact ⟨v, rfl⟩
                    obtain ⟨voa, hoa⟩ := hevalArg oa (fun u hu => List.mem_append_left _ hu)
                    obtain ⟨vob, hob⟩ := hevalArg ob (fun u hu => List.mem_append_right _ hu)
                    obtain ⟨fv, hlimb, _⟩ := emitOvfLimb_exec (o := o) (x := loopMapReg armDefs off k x)
                      (flag := nextReg) (mem := mem) (ctx := ctx) hoa hob
                    have hx_ge := loopMapReg_ge_of_mem (off := off) hk hxm
                    have hx_lt : Nat.succ (loopMapReg armDefs off k x) ≤ (k + 1) * off := loopMapReg_lt_of_mem hk hxm hxlt
                    let ρL := (ρ1.insert (loopMapReg armDefs off k x) (o.eval voa vob).1).insert nextReg fv
                    have hexL : execList ρ₂ mem ctx
                        (acc ++ st.body.map (loopMapStmt armDefs off k) ++
                          [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                            (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob)]) = some (ρL, mem) :=
                      execList_append_ifconv hex1 (by simp [execList, hlimb, ρL])
                    have havL : ∀ u, (av1.insert x).contains u = true →
                        ρL[loopMapReg armDefs off k u]?.isSome = true := by
                      intro u hu
                      rw [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert] at hu
                      by_cases hux : u = x
                      · subst hux
                        rw [env_insert_ne _ _ (by omega), env_insert_self]; rfl
                      · simp only [hux, ↓reduceIte] at hu
                        by_cases hmu : loopMapReg armDefs off k u = nextReg
                        · rw [hmu, env_insert_self]; rfl
                        · rw [env_insert_ne _ _ (Ne.symm hmu)]
                          by_cases hmx : loopMapReg armDefs off k u = loopMapReg armDefs off k x
                          · rw [hmx, env_insert_self]; rfl
                          · rw [env_insert_ne _ _ (Ne.symm hmx)]
                            exact hav1 u hu
                    have hpresL : ∀ (z : Nat), (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ nextReg + 1 ≤ z) →
                        ρL[z]? = ρ₂[z]? := by
                      intro z hz
                      have hneF : nextReg ≠ z := by omega
                      have hneX : loopMapReg armDefs off k x ≠ z := by
                        intro heq
                        have h0 : k * off ≤ z := heq ▸ hx_ge
                        have h1 : Nat.succ z ≤ (k + 1) * off := heq ▸ hx_lt
                        omega
                      rw [env_insert_ne _ _ hneF, env_insert_ne _ _ hneX]
                      exact hpres1 z (by rcases hz with h1 | h2 | h3; exact .inl h1; exact .inr (.inl h2); exact .inr (.inr (by omega)))
                    -- Split on `curFlag == .imm 0`
                    have hcase_other : ∀ (hnot0 : curFlag ≠ .imm 0),
                        let orReg := nextReg + 1
                        let orSt := Stmt.assign orReg (.bin .or .w64 curFlag (.v nextReg))
                        let (stmts, flagArg, frOut) :=
                          rest.foldl (init := (acc ++ st.body.map (loopMapStmt armDefs off k) ++
                            [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                              (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob), orSt],
                            Arg.v orReg, nextReg + 2)) fun (acc, curFlag, nextReg) st =>
                              let bodyShifted := st.body.map (loopMapStmt armDefs off k)
                              match st.ovf? with
                              | none => (acc ++ bodyShifted, curFlag, nextReg)
                              | some (o, x, oa, ob, _) =>
                                  let x' := loopMapReg armDefs off k x
                                  let oa' := loopMapArg armDefs off k oa
                                  let ob' := loopMapArg armDefs off k ob
                                  let fReg := nextReg
                                  let limbSt := emitOvfLimb o x' fReg oa' ob'
                                  match curFlag with
                                  | Arg.imm 0 => (acc ++ bodyShifted ++ [limbSt], Arg.v fReg, nextReg + 1)
                                  | _ =>
                                      let orReg := nextReg + 1
                                      let orSt := Stmt.assign orReg (.bin .or .w64 curFlag (.v fReg))
                                      (acc ++ bodyShifted ++ [limbSt, orSt], Arg.v orReg, nextReg + 2)
                        flagBase ≤ frOut ∧
                        (∀ s ∈ stmts, s.isCall = false) ∧
                        (∀ x ∈ flagArg.uses, flagBase ≤ x ∧ x < frOut) ∧
                        ∃ (ρ₂' : Env) (avEnd : Src.NatSet),
                          execList ρ₂ mem ctx stmts = some (ρ₂', mem) ∧
                          (∀ x, avEnd.contains x = true → ρ₂'[loopMapReg armDefs off k x]?.isSome = true) ∧
                          (∀ a ∈ arm.joinArgs, ∀ x ∈ a.uses, armDefs.contains x = true → avEnd.contains x = true) ∧
                          (∃ fv, flagArg.eval ρ₂' = some fv) ∧
                          (∀ z, (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ frOut ≤ z) → ρ₂'[z]? = ρ₂[z]?) := by
                      intro _
                      obtain ⟨cfv, hcfv⟩ := hfev1
                      have hcfvL : curFlag.eval ρL = some cfv := by
                        cases curFlag with
                        | imm w => exact hcfv
                        | v r =>
                            have hr := hfu r (by simp [Arg.uses, Arg.vreg?])
                            rw [Arg.eval, env_insert_ne _ _ (by omega), env_insert_ne _ _ (by omega)]
                            exact hcfv
                      let ρO := ρL.insert (nextReg + 1) (cfv ||| fv)
                      have hor_exec : (Stmt.assign (nextReg + 1) (.bin .or .w64 curFlag (.v nextReg))).exec ρL mem ctx =
                          some (ρO, mem) := by
                        rw [Stmt.exec, Rhs.eval, hcfvL]
                        simp [Arg.eval, BinOp.eval, trunc64, ρO, ρL]
                      have hexO : execList ρ₂ mem ctx
                          (acc ++ st.body.map (loopMapStmt armDefs off k) ++
                            [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                              (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob),
                             Stmt.assign (nextReg + 1) (.bin .or .w64 curFlag (.v nextReg))]) = some (ρO, mem) := by
                        rw [show [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                              (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob),
                              Stmt.assign (nextReg + 1) (.bin .or .w64 curFlag (.v nextReg))] =
                            [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                              (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob)] ++
                            [Stmt.assign (nextReg + 1) (.bin .or .w64 curFlag (.v nextReg))] from rfl,
                            ← List.append_assoc]
                        exact execList_append_ifconv hexL (by simp [execList, hor_exec])
                      apply ih _ (.v (nextReg + 1)) (nextReg + 2) (av1.insert x) ρO (by omega)
                        (fun s hs => by
                          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
                          rcases hs with (h1 | h2) | (rfl | rfl)
                          · exact hnc s h1
                          · rw [List.mem_map] at h2; obtain ⟨s0, hs0, rfl⟩ := h2; exact hnc_b s0 hs0
                          · exact emitOvfLimb_isCall ..
                          · rfl)
                        (fun u hu => by simp only [Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hu; subst hu; omega)
                        ⟨cfv ||| fv, by simp [Arg.eval, ρO]⟩
                        hexO
                        (fun u hu => by
                          by_cases h1 : loopMapReg armDefs off k u = nextReg + 1
                          · rw [h1, env_insert_self]; rfl
                          · rw [env_insert_ne _ _ (Ne.symm h1)]; exact havL u hu)
                        (fun z hz => by
                          rw [env_insert_ne _ _ (by omega)]
                          exact hpresL z (by rcases hz with h1 | h2 | h3; exact .inl h1; exact .inr (.inl h2); exact .inr (.inr (by omega))))
                        hp
                        (fun s' hs' => hrg s' (by simp [hs']))
                        (fun s' hs' => hou s' (by simp [hs']))
                        (fun s' hs' => hdo s' (by simp [hs']))
                    cases curFlag with
                    | imm w =>
                        by_cases hw0 : w = 0
                        · subst hw0
                          exact ih _ (.v nextReg) (nextReg + 1) (av1.insert x) ρL (by omega)
                            (fun s hs => by
                              simp only [List.mem_append, List.mem_singleton] at hs
                              rcases hs with (h1 | h2) | rfl
                              · exact hnc s h1
                              · rw [List.mem_map] at h2; obtain ⟨s0, hs0, rfl⟩ := h2; exact hnc_b s0 hs0
                              · exact emitOvfLimb_isCall ..)
                            (fun u hu => by simp only [Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hu; subst hu; omega)
                            ⟨fv, by simp [Arg.eval, ρL]⟩
                            hexL havL hpresL hp
                            (fun s' hs' => hrg s' (by simp [hs']))
                            (fun s' hs' => hou s' (by simp [hs']))
                            (fun s' hs' => hdo s' (by simp [hs']))
                        · have hnot0 : Arg.imm w ≠ .imm 0 := fun h => hw0 (Arg.imm.inj h)
                          dsimp only
                          split
                          · simp_all
                          · exact hcase_other hnot0
                    | v r =>
                        exact hcase_other (by intro h; cases h)
                  · cases hp
  exact hfold arm.steps [] (.imm 0) flagBase .leaf ρ₂ (Nat.le_refl _) (fun _ h => by cases h)
    (fun _ h => by cases h) ⟨0, rfl⟩ rfl (fun _ h => by simp [Src.NatMap.contains, Src.NatMap.get?] at h)
    (fun _ _ => rfl) hpure hregs houter hdefOuter

/-! ## Concrete correspondence between `arm` execution and `emitSpeculativeArm` -/

private theorem or_ne_zero_of_left_ne_zero {a b : Word} (ha : a ≠ 0) : a ||| b ≠ 0 := by
  intro h0
  apply ha
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun z : Word => z.toBitVec.getLsbD i) h0
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_zero, BitVec.getLsbD_or, BitVec.getLsbD_zero,
    Bool.or_eq_false_iff] at hb
  simp [hb.1]

/-- Pure statement list agreement: `execList` on `ss` matches `execList` on shifted `ss`,
preserving outer agreement and tracking `av` shifted agreement. -/
private theorem exec_shifted_stmts_agree {armDefs otherDefs : Src.NatSet} {off k : Nat} (hk : 0 < k)
    {mem : X86.Memory} {ctx : Word} :
    ∀ {ss : List Stmt} {av0 av1 : Src.NatSet} {ρ₁ ρ₁' ρ₂Cur : Env},
      ss.all isHoistableStmt = true →
      checkStmtsAvail armDefs av0 ss = some av1 →
      (∀ x, av0.contains x = true → armDefs.contains x = true ∧ x < off) →
      (∀ s ∈ ss, ∀ d ∈ s.defs, armDefs.contains d = true ∧ d < off) →
      (∀ s ∈ ss, ∀ x ∈ s.uses, armDefs.contains x = false → x < off ∧ otherDefs.contains x = false) →
      (∀ x v, x < off → armDefs.contains x = false → otherDefs.contains x = false → ρ₁[x]? = some v → ρ₂Cur[x]? = some v) →
      (∀ x v, av0.contains x = true → ρ₁[x]? = some v → ρ₂Cur[loopMapReg armDefs off k x]? = some v) →
      execList ρ₁ mem ctx ss = some (ρ₁', mem) →
      (∀ x, av1.contains x = true → armDefs.contains x = true ∧ x < off) ∧
      ∃ ρ₂', execList ρ₂Cur mem ctx (ss.map (loopMapStmt armDefs off k)) = some (ρ₂', mem) ∧
        (∀ x v, x < off → armDefs.contains x = false → otherDefs.contains x = false → ρ₁'[x]? = some v → ρ₂'[x]? = some v) ∧
        (∀ x v, av1.contains x = true → ρ₁'[x]? = some v → ρ₂'[loopMapReg armDefs off k x]? = some v) ∧
        (∀ z, z < k * off ∨ (k + 1) * off ≤ z → ρ₂'[z]? = ρ₂Cur[z]?)
  | [], av0, av1, ρ₁, ρ₁', ρ₂Cur, _, hck, havSub, _, _, hout, hav, hx => by
      simp only [checkStmtsAvail, Option.some.injEq] at hck; subst hck
      simp only [execList, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, _⟩ := hx
      exact ⟨havSub, ρ₂Cur, rfl, hout, hav, fun _ _ => rfl⟩
  | s :: rest, av0, av1, ρ₁, ρ₁', ρ₂Cur, hhoist, hck, havSub, hds, hou, hout, hav, hx => by
      simp only [List.all_cons, Bool.and_eq_true] at hhoist
      simp only [checkStmtsAvail] at hck
      split at hck
      · rename_i huses
        simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at huses
        simp only [execList] at hx
        split at hx
        · rename_i ρ₁1 mem1 hxs
          have hnc : s.isCall = false := by
            cases s <;> simp [Stmt.isCall, isHoistableStmt] at hhoist ⊢
          have hmem1 : mem1 = mem := by
            cases s with
            | assign _ _ =>
                simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff,
                  Option.some.injEq, Prod.mk.injEq] at hxs
                obtain ⟨_, _, _, rfl⟩ := hxs; rfl
            | limb _ _ _ =>
                simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff,
                  Option.some.injEq, Prod.mk.injEq] at hxs
                obtain ⟨_, _, _, rfl⟩ := hxs; rfl
            | store _ _ _ | call _ _ _ => simp [isHoistableStmt] at hhoist
          subst hmem1
          have harg_ag : ∀ x ∈ s.uses, ∀ vx, ρ₁[x]? = some vx → ρ₂Cur[loopMapReg armDefs off k x]? = some vx := by
            intro x hx_u vx hvx
            rcases huses x hx_u with hnot | havx
            · rw [loopMapReg_not_mem hnot]
              obtain ⟨hxlt, hxno⟩ := hou s (by simp) x hx_u hnot
              exact hout x vx hxlt hnot hxno hvx
            · exact hav x vx havx hvx
          obtain ⟨ρ₂1, hx2, hd2, hother2, hother1⟩ :=
            loopMapStmt_exec_agree hk
              (fun d hd => (hds s (by simp) d hd).1)
              (fun d hd => (hds s (by simp) d hd).2)
              harg_ag hnc hxs
          have hpres1 : ∀ z, z < k * off ∨ (k + 1) * off ≤ z → ρ₂1[z]? = ρ₂Cur[z]? := by
            intro z hz
            apply hother2 z
            intro d hd
            have hdlt := (hds s (by simp) d hd).2
            have hlt : k * off + d < (k + 1) * off := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left hdlt _
            rcases hz with h1 | h2
            · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _))
            · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt h2)
          have havSub1 : ∀ x, (s.defs.foldl (fun a d => a.insert d) av0).contains x = true →
              armDefs.contains x = true ∧ x < off := by
            intro x hx_av
            rw [natSet_foldl_insert_contains] at hx_av
            rcases hx_av with hxd | hx0
            · exact hds s (by simp) x hxd
            · exact havSub x hx0
          have hout1 : ∀ x v, x < off → armDefs.contains x = false → otherDefs.contains x = false → ρ₁1[x]? = some v → ρ₂1[x]? = some v := by
            intro x v hxlt hnot hno hv
            have hnotd : x ∉ s.defs := fun hmem => by
              have := (hds s (by simp) x hmem).1; rw [hnot] at this; cases this
            rw [hother1 x hnotd] at hv
            rw [hpres1 x (.inl (by have : off ≤ k * off := Nat.le_mul_of_pos_left off hk; omega))]
            exact hout x v hxlt hnot hno hv
          have hav1 : ∀ x v, (s.defs.foldl (fun a d => a.insert d) av0).contains x = true →
              ρ₁1[x]? = some v → ρ₂1[loopMapReg armDefs off k x]? = some v := by
            intro x v hx_av hv
            by_cases hxd : x ∈ s.defs
            · rw [loopMapReg_mem_pos hk (hds s (by simp) x hxd).1]
              exact hd2 x hxd v hv
            · rw [natSet_foldl_insert_contains] at hx_av
              rcases hx_av with hxd' | hx0
              · exact absurd hxd' hxd
              · rw [hother1 x hxd] at hv
                obtain ⟨hxm, _⟩ := havSub x hx0
                rw [loopMapReg_mem_pos hk hxm]
                rw [hother2 (k * off + x) (fun d hd heq => hxd (by have : x = d := Nat.add_left_cancel heq; subst this; exact hd))]
                rw [← loopMapReg_mem_pos hk hxm]
                exact hav x v hx0 hv
          obtain ⟨havSubEnd, ρ₂', hxr, hout', hav', hpres_r⟩ :=
            exec_shifted_stmts_agree hk hhoist.2 hck havSub1
              (fun s' hs' => hds s' (by simp [hs']))
              (fun s' hs' => hou s' (by simp [hs']))
              hout1 hav1 hx
          exact ⟨havSubEnd, ρ₂', by simp [execList, hx2, hxr], hout', hav',
            fun z hz => by rw [hpres_r z hz, hpres1 z hz]⟩
        · cases hx
      · cases hck

/-- Once `curFlag` is already nonzero during `emitSpeculativeArm`, the remaining fold keeps
`flagArg` nonzero. -/
private theorem emitSpeculativeArm_flag_stays_nonzero {arm : DiamondArm} {armDefs : Src.NatSet}
    {off k flagBase : Nat} (hk : 0 < k) (hfb : (k + 1) * off ≤ flagBase)
    {mem : X86.Memory} {ctx : Word} :
    ∀ (steps : List ArmStep) (acc : List Stmt) (curFlag : Arg) (nextReg : Nat)
      (av : Src.NatSet) (ρ₂ ρCur : Env),
      flagBase ≤ nextReg →
      (∀ (x : Nat), x ∈ curFlag.uses → flagBase ≤ x ∧ x < nextReg) →
      (∃ fv, curFlag.eval ρCur = some fv ∧ fv ≠ 0) →
      execList ρ₂ mem ctx acc = some (ρCur, mem) →
      (∀ x, av.contains x = true → ρCur[loopMapReg armDefs off k x]?.isSome = true) →
      (∀ z, (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ nextReg ≤ z) → ρCur[z]? = ρ₂[z]?) →
      checkArmPure.go arm armDefs av steps = true →
      (∀ st ∈ steps,
        (∀ s ∈ st.body, ∀ d ∈ s.defs, armDefs.contains d = true ∧ d < off) ∧
        (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) → armDefs.contains x = true ∧ x < off)) →
      (∀ st ∈ steps,
        (∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → x < off) ∧
        (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
          ∀ u ∈ oa.uses ++ ob.uses, armDefs.contains u = false → u < off)) →
      (∀ st ∈ steps,
        (∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → ρ₂[x]?.isSome = true) ∧
        (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
          ∀ u ∈ oa.uses ++ ob.uses, armDefs.contains u = false → ρ₂[u]?.isSome = true)) →
      let (stmts, flagArg, _) :=
        steps.foldl (init := (acc, curFlag, nextReg)) fun (acc, curFlag, nextReg) st =>
          let bodyShifted := st.body.map (loopMapStmt armDefs off k)
          match st.ovf? with
          | none => (acc ++ bodyShifted, curFlag, nextReg)
          | some (o, x, oa, ob, _) =>
              let x' := loopMapReg armDefs off k x
              let oa' := loopMapArg armDefs off k oa
              let ob' := loopMapArg armDefs off k ob
              let fReg := nextReg
              let limbSt := emitOvfLimb o x' fReg oa' ob'
              match curFlag with
              | .imm 0 => (acc ++ bodyShifted ++ [limbSt], .v fReg, nextReg + 1)
              | _ =>
                  let orReg := nextReg + 1
                  let orSt := Stmt.assign orReg (.bin .or .w64 curFlag (.v fReg))
                  (acc ++ bodyShifted ++ [limbSt, orSt], .v orReg, nextReg + 2)
      ∃ ρ₂' fv, execList ρ₂ mem ctx stmts = some (ρ₂', mem) ∧ flagArg.eval ρ₂' = some fv ∧ fv ≠ 0 := by
  intro steps
  induction steps with
  | nil =>
      intro acc curFlag nextReg av ρ₂ ρCur _ _ ⟨fv, hfv, hne⟩ hex _ _ _ _ _ _
      exact ⟨ρCur, fv, hex, hfv, hne⟩
  | cons st rest ih =>
      intro acc curFlag nextReg av ρ₂ ρCur hle hfu ⟨cfv, hcfv, hcfv_ne⟩ hex hav hpres hp hrg hou hdo
      simp only [List.foldl_cons]
      simp only [checkArmPure.go] at hp
      split at hp
      · cases hp
      · rename_i hhoist
        have hhoist' : st.body.all isHoistableStmt = true := by simpa using hhoist
        cases hck : checkStmtsAvail armDefs av st.body with
        | none => rw [hck] at hp; cases hp
        | some av1 =>
            rw [hck] at hp
            have hdo_st := hdo st (by simp); have hou_st := hou st (by simp); have hrg_st := hrg st (by simp)
            have houterCur : ∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → ρCur[x]?.isSome = true := by
              intro s hs x hx hnot
              have hxlt := hou_st.1 s hs x hx hnot
              rw [hpres x (.inl (Nat.lt_of_lt_of_le hxlt (Nat.le_mul_of_pos_left off hk)))]
              exact hdo_st.1 s hs x hx hnot
            obtain ⟨_, ρ1, hxb, hav1, hpres_b⟩ :=
              exec_shifted_pure_stmts (mem := mem) (ctx := ctx) hk hhoist' hck hrg_st.1 houterCur hav
            have hex1 := execList_append_ifconv hex hxb
            have hpres1 : ∀ z, (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ nextReg ≤ z) → ρ1[z]? = ρ₂[z]? := by
              intro z hz
              rw [hpres_b z (by rcases hz with h1 | ⟨h2, _⟩ | h3; exact .inl h1; exact .inr h2; exact .inr (Nat.le_trans hfb (Nat.le_trans hle h3))), hpres z hz]
            have hcfv1 : curFlag.eval ρ1 = some cfv := by
              cases curFlag with
              | imm _ => exact hcfv
              | v r =>
                  have hr := hfu r (by simp [Arg.uses, Arg.vreg?])
                  rw [Arg.eval, hpres_b r (.inr (by omega))]; exact hcfv
            cases hov : st.ovf? with
            | none =>
                rw [hov] at hp
                exact ih _ curFlag nextReg av1 ρ₂ ρ1 hle hfu ⟨cfv, hcfv1, hcfv_ne⟩ hex1 hav1 hpres1 hp
                  (fun s' hs' => hrg s' (by simp [hs']))
                  (fun s' hs' => hou s' (by simp [hs']))
                  (fun s' hs' => hdo s' (by simp [hs']))
            | some ovfTuple =>
                rcases ovfTuple with ⟨o, x, oa, ob, res⟩
                rw [hov] at hp; dsimp only at hp
                split at hp
                · rename_i hou_ovf
                  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hou_ovf
                  obtain ⟨hxm, hxlt⟩ := hrg_st.2 o x oa ob res hov
                  have hevalArg : ∀ (a : Arg), (∀ u ∈ a.uses, u ∈ oa.uses ++ ob.uses) →
                      ∃ v, (loopMapArg armDefs off k a).eval ρ1 = some v := by
                    intro a ha
                    cases a with
                    | imm w => exact ⟨w, rfl⟩
                    | v u =>
                        have hu := ha u (by simp [Arg.uses, Arg.vreg?])
                        rcases hou_ovf u hu with hnot | havu
                        · rw [loopMapArg, loopMapReg_not_mem hnot]
                          have hult := hou_st.2 o x oa ob res hov u hu hnot
                          have hdefu := hdo_st.2 o x oa ob res hov u hu hnot
                          have h1 : ρ1[u]? = ρ₂[u]? := hpres1 u (.inl (Nat.lt_of_lt_of_le hult (Nat.le_mul_of_pos_left off hk)))
                          rw [Arg.eval, h1]
                          cases hg : ρ₂[u]? with | none => simp [hg] at hdefu | some v => exact ⟨v, rfl⟩
                        · have hd := hav1 u havu
                          rw [loopMapArg, Arg.eval]
                          cases hg : ρ1[loopMapReg armDefs off k u]? with | none => simp [hg] at hd | some v => exact ⟨v, rfl⟩
                  obtain ⟨voa, hoa⟩ := hevalArg oa (fun u hu => List.mem_append_left _ hu)
                  obtain ⟨vob, hob⟩ := hevalArg ob (fun u hu => List.mem_append_right _ hu)
                  obtain ⟨fv, hlimb, _⟩ := emitOvfLimb_exec (o := o) (x := loopMapReg armDefs off k x)
                    (flag := nextReg) (mem := mem) (ctx := ctx) hoa hob
                  have hx_ge := loopMapReg_ge_of_mem (off := off) hk hxm
                  have hx_lt : Nat.succ (loopMapReg armDefs off k x) ≤ (k + 1) * off := loopMapReg_lt_of_mem hk hxm hxlt
                  let ρL := (ρ1.insert (loopMapReg armDefs off k x) (o.eval voa vob).1).insert nextReg fv
                  have hexL : execList ρ₂ mem ctx
                      (acc ++ st.body.map (loopMapStmt armDefs off k) ++
                        [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                          (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob)]) = some (ρL, mem) :=
                    execList_append_ifconv hex1 (by simp [execList, hlimb, ρL])
                  have hnot0 : curFlag ≠ .imm 0 := by
                    intro heq; rw [heq] at hcfv; simp only [Arg.eval, Option.some.injEq] at hcfv
                    exact hcfv_ne hcfv.symm
                  have hcfvL : curFlag.eval ρL = some cfv := by
                    cases curFlag with
                    | imm _ => exact hcfv1
                    | v r =>
                        have hr := hfu r (by simp [Arg.uses, Arg.vreg?])
                        rw [Arg.eval, env_insert_ne _ _ (by omega), env_insert_ne _ _ (by omega)]
                        exact hcfv1
                  let ρO := ρL.insert (nextReg + 1) (cfv ||| fv)
                  have hor_exec : (Stmt.assign (nextReg + 1) (.bin .or .w64 curFlag (.v nextReg))).exec ρL mem ctx = some (ρO, mem) := by
                    rw [Stmt.exec, Rhs.eval, hcfvL]
                    simp [Arg.eval, BinOp.eval, trunc64, ρO, ρL]
                  have hexO : execList ρ₂ mem ctx
                      (acc ++ st.body.map (loopMapStmt armDefs off k) ++
                        [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                          (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob),
                         Stmt.assign (nextReg + 1) (.bin .or .w64 curFlag (.v nextReg))]) = some (ρO, mem) := by
                    rw [show [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                          (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob),
                          Stmt.assign (nextReg + 1) (.bin .or .w64 curFlag (.v nextReg))] =
                        [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                          (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob)] ++
                        [Stmt.assign (nextReg + 1) (.bin .or .w64 curFlag (.v nextReg))] from rfl,
                        ← List.append_assoc]
                    exact execList_append_ifconv hexL (by simp [execList, hor_exec])
                  have havL : ∀ u, (av1.insert x).contains u = true → ρO[loopMapReg armDefs off k u]?.isSome = true := by
                    intro u hu
                    by_cases h1 : loopMapReg armDefs off k u = nextReg + 1
                    · rw [h1, env_insert_self]; rfl
                    · rw [env_insert_ne _ _ (Ne.symm h1)]
                      rw [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert] at hu
                      by_cases hux : u = x
                      · subst hux; rw [env_insert_ne _ _ (by omega), env_insert_self]; rfl
                      · simp only [hux, ↓reduceIte] at hu
                        by_cases h2 : loopMapReg armDefs off k u = nextReg
                        · rw [h2, env_insert_self]; rfl
                        · rw [env_insert_ne _ _ (Ne.symm h2)]
                          by_cases h3 : loopMapReg armDefs off k u = loopMapReg armDefs off k x
                          · rw [h3, env_insert_self]; rfl
                          · rw [env_insert_ne _ _ (Ne.symm h3)]; exact hav1 u hu
                  have hpresO : ∀ z, (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ nextReg + 2 ≤ z) → ρO[z]? = ρ₂[z]? := by
                    intro z hz
                    rw [env_insert_ne _ _ (by omega), env_insert_ne _ _ (by omega), env_insert_ne _ _ (by omega)]
                    exact hpres1 z (by rcases hz with h1 | h2 | h3; exact .inl h1; exact .inr (.inl h2); exact .inr (.inr (by omega)))
                  dsimp only
                  split
                  · exact absurd rfl hnot0
                  · exact ih _ (.v (nextReg + 1)) (nextReg + 2) (av1.insert x) ρ₂ ρO (by omega)
                      (fun u hu => by simp only [Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hu; subst hu; omega)
                      ⟨cfv ||| fv, by simp [Arg.eval, ρO], or_ne_zero_of_left_ne_zero hcfv_ne⟩
                      hexO havL hpresO hp
                      (fun s' hs' => hrg s' (by simp [hs']))
                      (fun s' hs' => hou s' (by simp [hs']))
                      (fun s' hs' => hdo s' (by simp [hs']))
                · cases hp

/-- Concrete step-by-step execution of a diamond arm's `ArmStep` chain: returns
`some (.inl r)` on the first overflowing `brOvf` step with resource `r`, or
`some (.inr ρEnd)` if all steps complete without overflowing. -/
private def runArmConcrete (mem : X86.Memory) (ctx : Word) :
    List ArmStep → Env → Option (Sem.Resource ⊕ Env)
  | [], ρ => some (.inr ρ)
  | st :: rest, ρ => do
      let (ρ1, _) ← execList ρ mem ctx st.body
      match st.ovf? with
      | none => runArmConcrete mem ctx rest ρ1
      | some (o, x, oa, ob, r) =>
          let va ← oa.eval ρ1
          let vb ← ob.eval ρ1
          if (o.eval va vb).2 then some (.inl r)
          else runArmConcrete mem ctx rest (ρ1.insert x (o.eval va vb).1)

/-- Concrete correspondence: when `runArmConcrete` produces `res` from `ρ₁₀`,
`emitSpeculativeArm` computes `flagArg = 0` + exact shifted `joinArgs` on `.inr ρ₁End`,
and `flagArg ≠ 0` on `.inl r`. -/
theorem emitSpeculativeArm_matches_concrete {arm : DiamondArm} {armDefs otherDefs : Src.NatSet}
    {off k flagBase : Nat} (hk : 0 < k) (hfb : (k + 1) * off ≤ flagBase)
    (hpure : checkArmPure arm armDefs = true)
    (hregs : ∀ st ∈ arm.steps,
      (∀ s ∈ st.body, ∀ d ∈ s.defs, armDefs.contains d = true ∧ d < off) ∧
      (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) → armDefs.contains x = true ∧ x < off))
    (houter : ∀ st ∈ arm.steps,
      (∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → x < off ∧ otherDefs.contains x = false) ∧
      (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
        ∀ u ∈ oa.uses ++ ob.uses, armDefs.contains u = false → u < off ∧ otherDefs.contains u = false))
    {ρ₁₀ ρ₂ : Env} {mem : X86.Memory} {ctx : Word} {res : Sum Sem.Resource Env}
    (hagreeOuter : ∀ x v, x < off → armDefs.contains x = false → otherDefs.contains x = false → ρ₁₀[x]? = some v → ρ₂[x]? = some v)
    (hdefOuter : ∀ st ∈ arm.steps,
      (∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → ρ₂[x]?.isSome = true) ∧
      (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
        ∀ u ∈ oa.uses ++ ob.uses, armDefs.contains u = false → ρ₂[u]?.isSome = true))
    (hjoinOuterLt : ∀ a ∈ arm.joinArgs, ∀ x ∈ a.uses, armDefs.contains x = false → x < off ∧ otherDefs.contains x = false)
    (hrun : runArmConcrete mem ctx arm.steps ρ₁₀ = some res) :
    let (stmts, flagArg, _) := emitSpeculativeArm armDefs off k arm flagBase
    ∃ ρ₂',
      execList ρ₂ mem ctx stmts = some (ρ₂', mem) ∧
      match res with
      | .inl _ => ∃ fv, flagArg.eval ρ₂' = some fv ∧ fv ≠ 0
      | .inr ρ₁End =>
          flagArg.eval ρ₂' = some 0 ∧
          ∀ a ∈ arm.joinArgs, ∀ v, a.eval ρ₁End = some v →
            (loopMapArg armDefs off k a).eval ρ₂' = some v := by
  have hfold : ∀ (steps : List ArmStep) (acc : List Stmt) (curFlag : Arg) (nextReg : Nat)
      (av : Src.NatSet) (ρ₁Cur ρ₂Cur : Env),
      flagBase ≤ nextReg →
      (∀ (x : Nat), x ∈ curFlag.uses → flagBase ≤ x ∧ x < nextReg) →
      curFlag.eval ρ₂Cur = some 0 →
      execList ρ₂ mem ctx acc = some (ρ₂Cur, mem) →
      (∀ x, av.contains x = true → armDefs.contains x = true ∧ x < off) →
      (∀ x v, x < off → armDefs.contains x = false → otherDefs.contains x = false → ρ₁Cur[x]? = some v → ρ₂Cur[x]? = some v) →
      (∀ x v, av.contains x = true → ρ₁Cur[x]? = some v → ρ₂Cur[loopMapReg armDefs off k x]? = some v) →
      (∀ x, av.contains x = true → ρ₂Cur[loopMapReg armDefs off k x]?.isSome = true) →
      (∀ z, (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ nextReg ≤ z) → ρ₂Cur[z]? = ρ₂[z]?) →
      checkArmPure.go arm armDefs av steps = true →
      (∀ st ∈ steps,
        (∀ s ∈ st.body, ∀ d ∈ s.defs, armDefs.contains d = true ∧ d < off) ∧
        (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) → armDefs.contains x = true ∧ x < off)) →
      (∀ st ∈ steps,
        (∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → x < off ∧ otherDefs.contains x = false) ∧
        (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
          ∀ u ∈ oa.uses ++ ob.uses, armDefs.contains u = false → u < off ∧ otherDefs.contains u = false)) →
      (∀ st ∈ steps,
        (∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → ρ₂[x]?.isSome = true) ∧
        (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
          ∀ u ∈ oa.uses ++ ob.uses, armDefs.contains u = false → ρ₂[u]?.isSome = true)) →
      runArmConcrete mem ctx steps ρ₁Cur = some res →
      let (stmts, flagArg, _) :=
        steps.foldl (init := (acc, curFlag, nextReg)) fun (acc, curFlag, nextReg) st =>
          let bodyShifted := st.body.map (loopMapStmt armDefs off k)
          match st.ovf? with
          | none => (acc ++ bodyShifted, curFlag, nextReg)
          | some (o, x, oa, ob, _) =>
              let x' := loopMapReg armDefs off k x
              let oa' := loopMapArg armDefs off k oa
              let ob' := loopMapArg armDefs off k ob
              let fReg := nextReg
              let limbSt := emitOvfLimb o x' fReg oa' ob'
              match curFlag with
              | .imm 0 => (acc ++ bodyShifted ++ [limbSt], .v fReg, nextReg + 1)
              | _ =>
                  let orReg := nextReg + 1
                  let orSt := Stmt.assign orReg (.bin .or .w64 curFlag (.v fReg))
                  (acc ++ bodyShifted ++ [limbSt, orSt], .v orReg, nextReg + 2)
      ∃ ρ₂',
        execList ρ₂ mem ctx stmts = some (ρ₂', mem) ∧
        match res with
        | .inl _ => ∃ fv, flagArg.eval ρ₂' = some fv ∧ fv ≠ 0
        | .inr ρ₁End =>
            flagArg.eval ρ₂' = some 0 ∧
            ∀ a ∈ arm.joinArgs, ∀ v, a.eval ρ₁End = some v →
              (loopMapArg armDefs off k a).eval ρ₂' = some v := by
    intro steps
    induction steps with
    | nil =>
        intro acc curFlag nextReg av ρ₁Cur ρ₂Cur _ _ hcf0 hex _ hout hav _ _ hp _ _ _ hr
        simp only [List.foldl_nil]
        simp only [runArmConcrete, Option.some.injEq] at hr; subst hr
        refine ⟨ρ₂Cur, hex, hcf0, ?_⟩
        intro a ha v hv
        simp only [checkArmPure.go, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hp
        apply loopMapArg_eval _ hv
        intro x hx vx hvx
        rcases hp a ha x hx with hnot | havx
        · rw [loopMapReg_not_mem hnot]
          obtain ⟨hxlt, hxno⟩ := hjoinOuterLt a ha x hx hnot
          exact hout x vx hxlt hnot hxno hvx
        · exact hav x vx havx hvx
    | cons st rest ih =>
        intro acc curFlag nextReg av ρ₁Cur ρ₂Cur hle hfu hcf0 hex havSub hout hav havDef hpres hp hrg hou hdo hr
        simp only [List.foldl_cons]
        simp only [checkArmPure.go] at hp
        split at hp
        · cases hp
        · rename_i hhoist
          have hhoist' : st.body.all isHoistableStmt = true := by simpa using hhoist
          cases hck : checkStmtsAvail armDefs av st.body with
          | none => rw [hck] at hp; cases hp
          | some av1 =>
              rw [hck] at hp
              simp only [runArmConcrete, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
              obtain ⟨⟨ρ₁1, mem1⟩, hxb1, hr_rest⟩ := hr
              have hmem1 : mem1 = mem := by
                have hpure_mem : ∀ (ss : List Stmt) (ρa ρb : Env) (ma mb : X86.Memory),
                    ss.all isHoistableStmt = true → execList ρa ma ctx ss = some (ρb, mb) → mb = ma := by
                  intro ss
                  induction ss with
                  | nil => intro _ _ _ _ _ hx; simp [execList] at hx; exact hx.2.symm
                  | cons s0 rs ih0 =>
                      intro ρa ρb ma mb hh hx
                      simp only [List.all_cons, Bool.and_eq_true] at hh
                      simp only [execList] at hx
                      split at hx
                      · rename_i ρm mm hs0
                        have hmm : mm = ma := by
                          cases s0 with
                          | assign _ _ => simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hs0; obtain ⟨_, _, _, rfl⟩ := hs0; rfl
                          | limb _ _ _ => simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hs0; obtain ⟨_, _, _, rfl⟩ := hs0; rfl
                          | store _ _ _ | call _ _ _ => simp [isHoistableStmt] at hh
                        subst hmm; exact ih0 _ _ _ _ hh.2 hx
                      · cases hx
                exact hpure_mem st.body ρ₁Cur ρ₁1 mem mem1 hhoist' hxb1
              subst mem1
              have hrg_st := hrg st (by simp); have hou_st := hou st (by simp); have hdo_st := hdo st (by simp)
              obtain ⟨havSub1, ρ₂1, hxb2, hout1, hav1, hpres_b⟩ :=
                exec_shifted_stmts_agree hk hhoist' hck havSub hrg_st.1 hou_st.1 hout hav hxb1
              have hex1 := execList_append_ifconv hex hxb2
              have hpres1 : ∀ z, (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ nextReg ≤ z) → ρ₂1[z]? = ρ₂[z]? := by
                intro z hz
                rw [hpres_b z (by rcases hz with h1 | ⟨h2, _⟩ | h3; exact .inl h1; exact .inr h2; exact .inr (Nat.le_trans hfb (Nat.le_trans hle h3))), hpres z hz]
              have hcf01 : curFlag.eval ρ₂1 = some 0 := by
                cases curFlag with
                | imm _ => exact hcf0
                | v r =>
                    have hr_ := hfu r (by simp [Arg.uses, Arg.vreg?])
                    rw [Arg.eval, hpres_b r (.inr (Nat.le_trans hfb hr_.1))]; exact hcf0
              have havDef1 : ∀ u, av1.contains u = true → ρ₂1[loopMapReg armDefs off k u]?.isSome = true := by
                have houterCur : ∀ s ∈ st.body, ∀ x ∈ s.uses, armDefs.contains x = false → ρ₂Cur[x]?.isSome = true := by
                  intro s hs x hx hnot
                  have hxlt := (hou_st.1 s hs x hx hnot).1
                  rw [hpres x (.inl (Nat.lt_of_lt_of_le hxlt (Nat.le_mul_of_pos_left off hk)))]
                  exact hdo_st.1 s hs x hx hnot
                obtain ⟨_, ρ₂1', hxb2', havDef1', _⟩ := exec_shifted_pure_stmts (mem := mem) (ctx := ctx) hk hhoist' hck hrg_st.1 houterCur havDef
                rw [hxb2] at hxb2'; cases hxb2'; exact havDef1'
              cases hov : st.ovf? with
              | none =>
                  rw [hov] at hp hr_rest
                  exact ih _ curFlag nextReg av1 ρ₁1 ρ₂1 hle hfu hcf01 hex1 havSub1 hout1 hav1 havDef1 hpres1 hp
                    (fun s' hs' => hrg s' (by simp [hs']))
                    (fun s' hs' => hou s' (by simp [hs']))
                    (fun s' hs' => hdo s' (by simp [hs']))
                    hr_rest
              | some ovfTuple =>
                  rcases ovfTuple with ⟨o, x, oa, ob, rFail⟩
                  rw [hov] at hp hr_rest; dsimp only at hp hr_rest
                  split at hp
                  · rename_i hou_ovf
                    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hou_ovf
                    simp only [Option.bind_eq_some_iff] at hr_rest
                    obtain ⟨voa, hoa1, vob, hob1, hr_ovf⟩ := hr_rest
                    obtain ⟨hxm, hxlt⟩ := hrg_st.2 o x oa ob rFail hov
                    have hoa2 : (loopMapArg armDefs off k oa).eval ρ₂1 = some voa := by
                      apply loopMapArg_eval _ hoa1
                      intro u hu vu hvu
                      rcases hou_ovf u (List.mem_append_left _ hu) with hnot | havu
                      · rw [loopMapReg_not_mem hnot]
                        obtain ⟨hult, huno⟩ := hou_st.2 o x oa ob rFail hov u (List.mem_append_left _ hu) hnot
                        exact hout1 u vu hult hnot huno hvu
                      · exact hav1 u vu havu hvu
                    have hob2 : (loopMapArg armDefs off k ob).eval ρ₂1 = some vob := by
                      apply loopMapArg_eval _ hob1
                      intro u hu vu hvu
                      rcases hou_ovf u (List.mem_append_right _ hu) with hnot | havu
                      · rw [loopMapReg_not_mem hnot]
                        obtain ⟨hult, huno⟩ := hou_st.2 o x oa ob rFail hov u (List.mem_append_right _ hu) hnot
                        exact hout1 u vu hult hnot huno hvu
                      · exact hav1 u vu havu hvu
                    obtain ⟨fv, hlimb, hfv_iff⟩ := emitOvfLimb_exec (o := o) (x := loopMapReg armDefs off k x)
                      (flag := nextReg) (mem := mem) (ctx := ctx) hoa2 hob2
                    have hx_ge := loopMapReg_ge_of_mem (off := off) hk hxm
                    have hx_lt : Nat.succ (loopMapReg armDefs off k x) ≤ (k + 1) * off := loopMapReg_lt_of_mem hk hxm hxlt
                    let ρL := (ρ₂1.insert (loopMapReg armDefs off k x) (o.eval voa vob).1).insert nextReg fv
                    have hexL : execList ρ₂ mem ctx
                        (acc ++ st.body.map (loopMapStmt armDefs off k) ++
                          [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                            (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob)]) = some (ρL, mem) :=
                      execList_append_ifconv hex1 (by simp [execList, hlimb, ρL])
                    have havSubL : ∀ u, (av1.insert x).contains u = true → armDefs.contains u = true ∧ u < off := by
                      intro u hu
                      rw [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert] at hu
                      by_cases hux : u = x
                      · subst hux; exact ⟨hxm, hxlt⟩
                      · simp only [hux, ↓reduceIte] at hu; exact havSub1 u hu
                    have hpresL : ∀ z, (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ nextReg + 1 ≤ z) → ρL[z]? = ρ₂[z]? := by
                      intro z hz
                      rw [env_insert_ne _ _ (by omega), env_insert_ne _ _ (by omega)]
                      exact hpres1 z (by rcases hz with h1 | h2 | h3; exact .inl h1; exact .inr (.inl h2); exact .inr (.inr (by omega)))
                    have havDefL : ∀ u, (av1.insert x).contains u = true → ρL[loopMapReg armDefs off k u]?.isSome = true := by
                      intro u hu
                      rw [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert] at hu
                      by_cases hux : u = x
                      · subst hux; rw [env_insert_ne _ _ (by omega), env_insert_self]; rfl
                      · simp only [hux, ↓reduceIte] at hu
                        by_cases h1 : loopMapReg armDefs off k u = nextReg
                        · rw [h1, env_insert_self]; rfl
                        · rw [env_insert_ne _ _ (Ne.symm h1)]
                          by_cases h2 : loopMapReg armDefs off k u = loopMapReg armDefs off k x
                          · rw [h2, env_insert_self]; rfl
                          · rw [env_insert_ne _ _ (Ne.symm h2)]; exact havDef1 u hu
                    have hcf0L : curFlag.eval ρL = some 0 := by
                      cases curFlag with
                      | imm _ => exact hcf01
                      | v r =>
                          have hr_ := hfu r (by simp [Arg.uses, Arg.vreg?])
                          rw [Arg.eval, env_insert_ne _ _ (by omega), env_insert_ne _ _ (by omega)]; exact hcf01
                    let ρO := ρL.insert (nextReg + 1) (0 ||| fv)
                    have hor_exec : (Stmt.assign (nextReg + 1) (.bin .or .w64 curFlag (.v nextReg))).exec ρL mem ctx = some (ρO, mem) := by
                      rw [Stmt.exec, Rhs.eval, hcf0L]
                      simp [Arg.eval, BinOp.eval, trunc64, ρO, ρL]
                    have hexO : execList ρ₂ mem ctx
                        (acc ++ st.body.map (loopMapStmt armDefs off k) ++
                          [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                            (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob),
                           Stmt.assign (nextReg + 1) (.bin .or .w64 curFlag (.v nextReg))]) = some (ρO, mem) := by
                      rw [show [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                            (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob),
                            Stmt.assign (nextReg + 1) (.bin .or .w64 curFlag (.v nextReg))] =
                          [emitOvfLimb o (loopMapReg armDefs off k x) nextReg
                            (loopMapArg armDefs off k oa) (loopMapArg armDefs off k ob)] ++
                          [Stmt.assign (nextReg + 1) (.bin .or .w64 curFlag (.v nextReg))] from rfl,
                          ← List.append_assoc]
                      exact execList_append_ifconv hexL (by simp [execList, hor_exec])
                    have hpresO : ∀ z, (z < k * off ∨ ((k + 1) * off ≤ z ∧ z < flagBase) ∨ nextReg + 2 ≤ z) → ρO[z]? = ρ₂[z]? := by
                      intro z hz
                      rw [env_insert_ne _ _ (by omega)]
                      exact hpresL z (by rcases hz with h1 | h2 | h3; exact .inl h1; exact .inr (.inl h2); exact .inr (.inr (by omega)))
                    have havDefO : ∀ u, (av1.insert x).contains u = true → ρO[loopMapReg armDefs off k u]?.isSome = true := by
                      intro u hu
                      by_cases h1 : loopMapReg armDefs off k u = nextReg + 1
                      · rw [h1, env_insert_self]; rfl
                      · rw [env_insert_ne _ _ (Ne.symm h1)]; exact havDefL u hu
                    -- Branch on concrete overflow `(o.eval voa vob).2`!
                    cases hovf : (o.eval voa vob).2 with
                    | true =>
                        rw [hovf] at hr_ovf; simp only [↓reduceIte, Option.some.injEq] at hr_ovf
                        subst hr_ovf
                        have hfv_ne : fv ≠ 0 := hfv_iff.2 hovf
                        have h0or : (0 ||| fv) ≠ 0 := by simpa [UInt64.zero_or] using hfv_ne
                        dsimp only
                        split
                        · obtain ⟨ρ₂', fv', hx', hfv', hne'⟩ :=
                            emitSpeculativeArm_flag_stays_nonzero hk hfb rest _ (.v nextReg) (nextReg + 1)
                              (av1.insert x) ρ₂ ρL (by omega)
                              (fun u hu => by simp only [Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hu; subst hu; omega)
                              ⟨fv, by simp [Arg.eval, ρL], hfv_ne⟩
                              hexL havDefL hpresL hp
                              (fun s' hs' => hrg s' (by simp [hs']))
                              (fun s' hs' => ⟨fun s hsb x hx hn => (hou s' (by simp [hs'])).1 s hsb x hx hn |>.1,
                                fun o x oa ob r hov u hu hn => (hou s' (by simp [hs'])).2 o x oa ob r hov u hu hn |>.1⟩)
                              (fun s' hs' => hdo s' (by simp [hs']))
                          exact ⟨ρ₂', hx', fv', hfv', hne'⟩
                        · obtain ⟨ρ₂', fv', hx', hfv', hne'⟩ :=
                            emitSpeculativeArm_flag_stays_nonzero hk hfb rest _ (.v (nextReg + 1)) (nextReg + 2)
                              (av1.insert x) ρ₂ ρO (by omega)
                              (fun u hu => by simp only [Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hu; subst hu; omega)
                              ⟨0 ||| fv, by simp [Arg.eval, ρO], h0or⟩
                              hexO havDefO hpresO hp
                              (fun s' hs' => hrg s' (by simp [hs']))
                              (fun s' hs' => ⟨fun s hsb x hx hn => (hou s' (by simp [hs'])).1 s hsb x hx hn |>.1,
                                fun o x oa ob r hov u hu hn => (hou s' (by simp [hs'])).2 o x oa ob r hov u hu hn |>.1⟩)
                              (fun s' hs' => hdo s' (by simp [hs']))
                          exact ⟨ρ₂', hx', fv', hfv', hne'⟩
                    | false =>
                        rw [hovf] at hr_ovf; simp only [Bool.false_eq_true, ↓reduceIte] at hr_ovf
                        have hfv0 : fv = 0 := by
                          by_cases h0 : fv = 0
                          · exact h0
                          · exact absurd (hfv_iff.1 h0) (by rw [hovf]; decide)
                        have houtL : ∀ (u : Nat) v, u < off → armDefs.contains u = false → otherDefs.contains u = false →
                            (ρ₁1.insert x (o.eval voa vob).1)[u]? = some v → ρL[u]? = some v := by
                          intro u v hult hnot hno hv
                          have hne_ux : u ≠ x := fun heq => by subst heq; rw [hnot] at hxm; cases hxm
                          rw [env_insert_ne _ _ (Ne.symm hne_ux)] at hv
                          have h1 : off ≤ k * off := Nat.le_mul_of_pos_left off hk
                          have h2 : k * off ≤ (k + 1) * off := Nat.mul_le_mul_right off (Nat.le_succ k)
                          rw [env_insert_ne _ _ (by omega), env_insert_ne _ _ (by omega)]
                          exact hout1 u v hult hnot hno hv
                        have havL : ∀ u v, (av1.insert x).contains u = true →
                            (ρ₁1.insert x (o.eval voa vob).1)[u]? = some v → ρL[loopMapReg armDefs off k u]? = some v := by
                          intro u v hu hv
                          rw [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert] at hu
                          by_cases hux : u = x
                          · subst hux
                            rw [env_insert_self] at hv; cases hv
                            rw [env_insert_ne _ _ (by omega), env_insert_self]
                          · simp only [hux, ↓reduceIte] at hu
                            rw [env_insert_ne _ _ (Ne.symm hux)] at hv
                            obtain ⟨hum, hult⟩ := havSub1 u hu
                            have hmu_lt : Nat.succ (loopMapReg armDefs off k u) ≤ (k + 1) * off := loopMapReg_lt_of_mem hk hum hult
                            have hne_mx : loopMapReg armDefs off k u ≠ loopMapReg armDefs off k x := by
                              rw [loopMapReg_mem_pos hk hum, loopMapReg_mem_pos hk hxm]
                              intro heq; exact hux (Nat.add_left_cancel heq)
                            rw [env_insert_ne _ _ (by omega), env_insert_ne _ _ (Ne.symm hne_mx)]
                            exact hav1 u v hu hv
                        dsimp only
                        split
                        · exact ih _ (.v nextReg) (nextReg + 1) (av1.insert x) (ρ₁1.insert x (o.eval voa vob).1) ρL
                            (by omega)
                            (fun u hu => by simp only [Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hu; subst hu; omega)
                            (by simp [Arg.eval, ρL, hfv0])
                            hexL havSubL houtL havL havDefL hpresL hp
                            (fun s' hs' => hrg s' (by simp [hs']))
                            (fun s' hs' => hou s' (by simp [hs']))
                            (fun s' hs' => hdo s' (by simp [hs']))
                            hr_ovf
                        · exact ih _ (.v (nextReg + 1)) (nextReg + 2) (av1.insert x) (ρ₁1.insert x (o.eval voa vob).1) ρO
                            (by omega)
                            (fun u hu => by simp only [Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hu; subst hu; omega)
                            (by simp [Arg.eval, ρO, hfv0])
                            hexO havSubL
                            (fun u v hult hnot hno hv => by
                              have huN : (u : Nat) < off := hult
                              have h1 : off ≤ k * off := Nat.le_mul_of_pos_left off hk
                              have h2 : k * off ≤ (k + 1) * off := Nat.mul_le_mul_right off (Nat.le_succ k)
                              rw [env_insert_ne _ _ (by omega)]
                              exact houtL u v hult hnot hno hv)
                            (fun u v hu hv => by
                              obtain ⟨hum, hult⟩ := havSubL u hu
                              have hmu_lt : Nat.succ (loopMapReg armDefs off k u) ≤ (k + 1) * off := loopMapReg_lt_of_mem hk hum hult
                              rw [env_insert_ne _ _ (by omega)]
                              exact havL u v hu hv)
                            havDefO hpresO hp
                            (fun s' hs' => hrg s' (by simp [hs']))
                            (fun s' hs' => hou s' (by simp [hs']))
                            (fun s' hs' => hdo s' (by simp [hs']))
                            hr_ovf
                  · cases hp
  exact hfold arm.steps [] (.imm 0) flagBase .leaf ρ₁₀ ρ₂ (Nat.le_refl _) (fun _ h => by cases h)
    rfl rfl (fun _ h => by simp [Src.NatMap.contains, Src.NatMap.get?] at h)
    hagreeOuter (fun _ _ h => by simp [Src.NatMap.contains, Src.NatMap.get?] at h)
    (fun _ h => by simp [Src.NatMap.contains, Src.NatMap.get?] at h)
    (fun _ _ => rfl) hpure hregs houter hdefOuter hrun

/-! ## Select-list execution helper -/

private theorem exec_selStmts {c : Cond} {w : Width} {a bArg : Arg} {va vb : Word} {condVal : Bool}
    {mem : X86.Memory} {ctx : Word} {frStart : VReg}
    (hcond : c.holds w va vb = condVal)
    (haLt : ∀ u ∈ a.uses, u < frStart) (hbLt : ∀ u ∈ bArg.uses, u < frStart) :
    ∀ (pairs : List (Arg × Arg)) (ss : List Stmt) (outRev : List Arg) (fr : VReg) (ρ0 ρCur : Env)
      (prevVals : List Word),
      frStart ≤ fr →
      a.eval ρCur = some va → bArg.eval ρCur = some vb →
      execList ρ0 mem ctx ss = some (ρCur, mem) →
      (∀ s ∈ ss, s.isCall = false) →
      (∀ z, z < frStart → ρCur[z]? = ρ0[z]?) →
      (∀ r ∈ outRev, ∀ u ∈ r.uses, u < fr) →
      evalArgs ρCur outRev.reverse = some prevVals →
      (∀ p ∈ pairs, (∀ u ∈ p.1.uses, u < frStart) ∧ (∀ u ∈ p.2.uses, u < frStart) ∧
        (p.1 ≠ p.2 → (∃ vt, p.1.eval ρ0 = some vt) ∧ (∃ vf, p.2.eval ρ0 = some vf))) →
      ∀ (tailVals : List Word),
      evalArgs ρ0 (pairs.map fun p => if condVal then p.1 else p.2) = some tailVals →
      let (ssEnd, outEnd, frEnd) :=
        pairs.foldl (init := (ss, outRev, fr)) fun (ss, out, fr) (at_, af_) =>
          if at_ == af_ then (ss, at_ :: out, fr)
          else (ss ++ [Stmt.assign fr (.select c w a bArg at_ af_)], Arg.v fr :: out, fr + 1)
      frStart ≤ frEnd ∧
      (∀ s ∈ ssEnd, s.isCall = false) ∧
      ∃ ρEnd, execList ρ0 mem ctx ssEnd = some (ρEnd, mem) ∧
        evalArgs ρEnd outEnd.reverse = some (prevVals ++ tailVals) ∧
        (∀ z, z < frStart → ρEnd[z]? = ρ0[z]?) := by
  intro pairs
  induction pairs with
  | nil =>
      intro ss outRev fr ρ0 ρCur prevVals hle _ _ hex hnc hpres _ hev _ tailVals htv
      simp only [List.map_nil, evalArgs_nil, Option.some.injEq] at htv; subst htv
      simp only [List.foldl_nil, List.append_nil]
      exact ⟨hle, hnc, ρCur, hex, hev, hpres⟩
  | cons p rest ih =>
      rcases p with ⟨at_, af_⟩
      intro ss outRev fr ρ0 ρCur prevVals hle haCur hbCur hex hnc hpres houtLt hev hps tailVals htv
      simp only [List.foldl_cons]
      simp only [List.map_cons, evalArgs_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htv
      obtain ⟨vChosen, hvChosen, restVals, hrestVals, rfl⟩ := htv
      obtain ⟨hatLt, hafLt, hdiff⟩ := hps (at_, af_) (by simp)
      have hevAt : ∀ v, at_.eval ρ0 = some v → at_.eval ρCur = some v := fun v hv => by
        cases at_ with
        | imm _ => exact hv
        | v u => rw [Arg.eval, hpres u (hatLt u (by simp [Arg.uses, Arg.vreg?]))]; exact hv
      have hevAf : ∀ v, af_.eval ρ0 = some v → af_.eval ρCur = some v := fun v hv => by
        cases af_ with
        | imm _ => exact hv
        | v u => rw [Arg.eval, hpres u (hafLt u (by simp [Arg.uses, Arg.vreg?]))]; exact hv
      have hevArgsAppend : ∀ (ρ : Env) (xs : List Arg) (x : Arg) (vs : List Word) (vx : Word),
          evalArgs ρ xs = some vs → x.eval ρ = some vx →
          evalArgs ρ (xs ++ [x]) = some (vs ++ [vx]) := by
        intro ρ xs
        induction xs with
        | nil =>
            intro x vs vx h1 h2
            simp only [evalArgs_nil, Option.some.injEq] at h1; subst h1
            simp [evalArgs_cons, evalArgs_nil, h2]
        | cons y ys ihy =>
            intro x vs vx h1 h2
            simp only [evalArgs_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h1
            obtain ⟨vy, hvy, vys, hvys, rfl⟩ := h1
            simp [evalArgs_cons, hvy, ihy x vys vx hvys h2]
      by_cases hsame : (at_ == af_) = true
      · have hsame' : at_ = af_ := by simpa using hsame
        simp only [hsame, ↓reduceIte]
        rw [← hsame', ite_self] at hvChosen
        have hvAtCur := hevAt vChosen hvChosen
        have hev' : evalArgs ρCur (at_ :: outRev).reverse = some (prevVals ++ [vChosen]) := by
          rw [List.reverse_cons]; exact hevArgsAppend ρCur outRev.reverse at_ prevVals vChosen hev hvAtCur
        have hres := ih ss (at_ :: outRev) fr ρ0 ρCur (prevVals ++ [vChosen]) hle haCur hbCur hex hnc hpres
          (fun r hr u hu => by
            simp only [List.mem_cons] at hr
            rcases hr with rfl | hr
            · exact Nat.lt_of_lt_of_le (hatLt u hu) hle
            · exact houtLt r hr u hu)
          hev' (fun p' hp' => hps p' (by simp [hp'])) restVals hrestVals
        simpa [List.append_assoc] using hres
      · have hne : at_ ≠ af_ := by simpa using hsame
        simp only [hsame, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨⟨vt, hvt0⟩, ⟨vf, hvf0⟩⟩ := hdiff hne
        have hvSel : (if condVal then vt else vf) = vChosen := by
          cases condVal <;> simp only [↓reduceIte, Bool.false_eq_true] at hvChosen ⊢
          · rw [hvf0] at hvChosen; exact Option.some.inj hvChosen
          · rw [hvt0] at hvChosen; exact Option.some.inj hvChosen
        let selSt := Stmt.assign fr (.select c w a bArg at_ af_)
        let ρ1 := ρCur.insert fr vChosen
        have hsel_exec : selSt.exec ρCur mem ctx = some (ρ1, mem) := by
          simp only [selSt, Stmt.exec, Rhs.eval, Option.bind_eq_bind, haCur, hbCur,
            hevAt vt hvt0, hevAf vf hvf0, Option.bind_some, hcond, hvSel, ρ1]
        have hex1 : execList ρ0 mem ctx (ss ++ [selSt]) = some (ρ1, mem) :=
          execList_append_ifconv hex (by simp [execList, hsel_exec])
        have hpres1 : ∀ z, z < frStart → ρ1[z]? = ρ0[z]? := fun z hz => by
          rw [env_insert_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le hz hle))]; exact hpres z hz
        have ha1 : a.eval ρ1 = some va := by
          cases a with
          | imm _ => exact haCur
          | v u => rw [Arg.eval, env_insert_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le (haLt u (by simp [Arg.uses, Arg.vreg?])) hle))]; exact haCur
        have hb1 : bArg.eval ρ1 = some vb := by
          cases bArg with
          | imm _ => exact hbCur
          | v u => rw [Arg.eval, env_insert_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le (hbLt u (by simp [Arg.uses, Arg.vreg?])) hle))]; exact hbCur
        have hevOld1 : evalArgs ρ1 outRev.reverse = some prevVals := by
          have hagree : ∀ xs : List Arg, (∀ r ∈ xs, ∀ u ∈ r.uses, u < fr) → evalArgs ρ1 xs = evalArgs ρCur xs := by
            intro xs
            induction xs with
            | nil => intro _; rfl
            | cons x0 xs0 ihx =>
                intro hlt
                have hx0 : x0.eval ρ1 = x0.eval ρCur := by
                  cases x0 with
                  | imm _ => rfl
                  | v u => rw [Arg.eval, Arg.eval, env_insert_ne _ _ (Nat.ne_of_gt (hlt (.v u) (by simp) u (by simp [Arg.uses, Arg.vreg?])))]
                simp [evalArgs_cons, hx0, ihx (fun r hr => hlt r (by simp [hr]))]
          rw [hagree outRev.reverse (fun r hr => houtLt r (by simpa using hr)), hev]
        have hev1 : evalArgs ρ1 (Arg.v fr :: outRev).reverse = some (prevVals ++ [vChosen]) := by
          rw [List.reverse_cons]
          exact hevArgsAppend ρ1 outRev.reverse (.v fr) prevVals vChosen hevOld1 (by simp [Arg.eval, ρ1])
        have hres := ih (ss ++ [selSt]) (.v fr :: outRev) (fr + 1) ρ0 ρ1 (prevVals ++ [vChosen])
          (Nat.le_succ_of_le hle) ha1 hb1 hex1
          (fun s hs => by simp only [List.mem_append, List.mem_singleton] at hs; rcases hs with h1 | rfl; exact hnc s h1; rfl)
          hpres1
          (fun r hr u hu => by
            simp only [List.mem_cons] at hr
            rcases hr with rfl | hr
            · simp only [Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hu; subst hu; exact Nat.lt_succ_self _
            · exact Nat.lt_succ_of_lt (houtLt r hr u hu))
          hev1 (fun p' hp' => hps p' (by simp [hp'])) restVals hrestVals
        simpa [List.append_assoc] using hres

/-! ## `buildIfConvFunc` block lookup lemmas -/

/-- Label remapping induced by `buildIfConvFunc` (identity for Shape 1, `+1` above `b` for Shape 2). -/
def ifConvRemap (b : Label) (hasGuard : Bool) (l : Label) : Label :=
  if hasGuard && decide (b + 1 ≤ l) then l + 1 else l

theorem ifConvRemap_le_iff (b : Label) (hasGuard : Bool) (l₁ l₂ : Label) :
    ifConvRemap b hasGuard l₁ ≤ ifConvRemap b hasGuard l₂ ↔ l₁ ≤ l₂ := by
  unfold ifConvRemap
  cases hasGuard with
  | false => simp
  | true =>
      simp only [Bool.true_and, decide_eq_true_eq]
      by_cases h1 : b + 1 ≤ l₁ <;> by_cases h2 : b + 1 ≤ l₂ <;> simp only [h1, h2, ↓reduceIte]
      · exact ⟨Nat.le_of_add_le_add_right, fun h => Nat.add_le_add_right h 1⟩
      · exact ⟨fun h => absurd (Nat.le_trans h1 (Nat.le_trans (Nat.le_add_right _ _) h)) h2,
          fun h => absurd (Nat.le_trans h1 h) h2⟩
      · have hlt : l₁ < l₂ := Nat.lt_of_lt_of_le (Nat.lt_of_not_ge h1) h2
        exact ⟨fun _ => Nat.le_of_lt hlt, fun _ => Nat.le_trans (Nat.le_of_lt hlt) (Nat.le_add_right _ _)⟩

private theorem ifConvRemap_zero (b : Label) (hasGuard : Bool) :
    ifConvRemap b hasGuard 0 = 0 := by
  unfold ifConvRemap; simp

private theorem ifConvRemap_b (b : Label) (hasGuard : Bool) :
    ifConvRemap b hasGuard b = b := by
  unfold ifConvRemap; simp

/-- Soundness specification extracted from `ifConvDiamondOk F b armT armF off = true`. -/
private structure IfConvData (p q : Program) (fi : FunId) (b : Label) where
  F : Func
  G : Func
  blk : Block
  c : Cond
  w : Width
  a : Arg
  bArg : Arg
  eT : Edge
  eF : Edge
  armT : DiamondArm
  armF : DiamondArm
  off : VReg
  hF : p.funcs[fi]? = some F
  hG : q.funcs[fi]? = some G
  hGEq : G = buildIfConvFunc F b armT armF off
  hOtherF : ∀ g, g ≠ fi → q.funcs[g]? = p.funcs[g]?
  hMain : q.main = p.main
  hb : F.blocks[b]? = some blk
  hTerm : blk.term = .br c w a bArg eT eF
  hOk : ifConvDiamondOk F b armT armF off = true

/-! ## Lazy-Arm-Sync simulation relation (`IfConvFrameRel`, `IfConvStateRel`) -/

private def OuterRegOk (off : VReg) (armTDefs armFDefs : Src.NatSet) (x : VReg) : Prop :=
  x < off ∧ armTDefs.contains x = false ∧ armFDefs.contains x = false

private def EnvAgreeOuter (off : VReg) (armTDefs armFDefs : Src.NatSet) (ρ₁ ρ₂ : Env) : Prop :=
  ∀ x v, OuterRegOk off armTDefs armFDefs x → ρ₁[x]? = some v → ρ₂[x]? = some v

private theorem envAgreeOuter_refl (off : VReg) (tDefs fDefs : Src.NatSet) (ρ : Env) :
    EnvAgreeOuter off tDefs fDefs ρ ρ := fun _ _ _ h => h

private theorem envAgreeOuter_insert {off : VReg} {tDefs fDefs : Src.NatSet} {ρ₁ ρ₂ : Env}
    (h : EnvAgreeOuter off tDefs fDefs ρ₁ ρ₂) (x : VReg) (v : Word) :
    EnvAgreeOuter off tDefs fDefs (ρ₁.insert x v) (ρ₂.insert x v) := by
  intro u val hu h1
  rw [env_insert_get] at h1 ⊢
  by_cases hux : x = u
  · simp only [hux, ↓reduceIte] at h1 ⊢; exact h1
  · simp only [hux, ↓reduceIte] at h1 ⊢; exact h u val hu h1

private theorem bindParams_agreeOuter {off : VReg} {tDefs fDefs : Src.NatSet} :
    ∀ {xs : List VReg} {vs : List Word} {ρ₁ ρ₂ ρ₁' : Env},
      EnvAgreeOuter off tDefs fDefs ρ₁ ρ₂ →
      bindParams ρ₁ xs vs = some ρ₁' →
      ∃ ρ₂', bindParams ρ₂ xs vs = some ρ₂' ∧ EnvAgreeOuter off tDefs fDefs ρ₁' ρ₂' ∧
        ∀ x ∈ xs, ρ₁'[x]?.isSome = true
  | [], [], ρ₁, ρ₂, ρ₁', h, hb => by
      simp only [bindParams, Option.some.injEq] at hb; subst hb
      exact ⟨ρ₂, rfl, h, fun _ hm => by cases hm⟩
  | x :: xs, v :: vs, ρ₁, ρ₂, ρ₁', h, hb => by
      simp only [bindParams] at hb ⊢
      obtain ⟨ρ₂', hb2, hag, hmem⟩ := bindParams_agreeOuter (envAgreeOuter_insert h x v) hb
      refine ⟨ρ₂', hb2, hag, ?_⟩
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · by_cases htail : y ∈ xs
        · exact hmem y htail
        · have hnot : ∀ (ρa ρb : Env) (ps : List VReg) (ws : List Word),
              bindParams ρa ps ws = some ρb → y ∉ ps → ρb[y]? = ρa[y]? := by
            intro ρa ρb ps
            induction ps generalizing ρa with
            | nil => intro ws hb0 _; cases ws with | nil => simp [bindParams] at hb0; subst hb0; rfl | cons _ _ => cases hb0
            | cons p0 ps0 ihp =>
                intro ws hb0 hny
                cases ws with
                | nil => cases hb0
                | cons w0 ws0 =>
                    simp only [List.mem_cons, not_or] at hny
                    simp only [bindParams] at hb0
                    rw [ihp _ ws0 hb0 hny.2, env_insert_ne _ _ (Ne.symm hny.1)]
          rw [hnot _ _ xs vs hb htail, env_insert_self]; rfl
      · exact hmem y hy
  | [], _ :: _, _, _, _, _, hb | _ :: _, [], _, _, _, _, hb => by cases hb

/-- Normal-mode frame correspondence (outside `armT`/`armF`, including inside `b` before its terminator). -/
private structure NormalIfConvFrame {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b) (isTop : Bool) (fr₁ fr₂ : Frame) : Prop where
  fnEq : fr₂.fn = fr₁.fn
  dstsEq : fr₂.dsts = fr₁.dsts
  bodyEq :
    if fr₁.fn = fi then
      let hasG := (d.armT.failRes?.orElse fun _ => d.armF.failRes?).isSome
      let tLbls := Src.NatSet.ofList d.armT.labels
      let fLbls := Src.NatSet.ofList d.armF.labels
      fr₂.label = ifConvRemap b hasG fr₁.label ∧
      fr₂.pos = fr₁.pos ∧
      tLbls.contains fr₁.label = false ∧
      fLbls.contains fr₁.label = false ∧
      EnvAgreeOuter d.off d.armT.defs d.armF.defs fr₁.env fr₂.env ∧
      (∀ x ∈ d.F.params, fr₁.env[x]?.isSome = true) ∧
      (fr₁.label = b →
        fr₁.pos ≤ d.blk.body.size ∧
        (∀ x ∈ d.blk.params, fr₁.env[x]?.isSome = true) ∧
        (∀ i, i < (if isTop then fr₁.pos else fr₁.pos - 1) →
          ∀ st, d.blk.body[i]? = some st → ∀ x ∈ st.uses ++ st.defs, fr₁.env[x]?.isSome = true) ∧
        (isTop = false → fr₁.pos > 0 →
          ∀ st, d.blk.body[fr₁.pos - 1]? = some st →
            (∀ x ∈ st.uses, fr₁.env[x]?.isSome = true) ∧ st.defs = fr₁.dsts))
    else
      fr₂.label = fr₁.label ∧ fr₂.pos = fr₁.pos ∧ fr₂.env = fr₁.env

/-- Parked-arm frame correspondence while `fr₁` is stepping through the taken diamond arm
`arm` (`armT` if `condVal = true`, `armF` if `condVal = false`) and `fr₂` stays parked at
`(b, d.blk.body.size)` ready to speculatively execute both arms + `select`s. -/
private structure InArmFrame {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b) (mem : X86.Memory) (ctx : Word) (fr₁ fr₂ : Frame) : Type where
  fn1 : fr₁.fn = fi
  fn2 : fr₂.fn = fi
  dstsEq : fr₂.dsts = fr₁.dsts
  lbl2 : fr₂.label = b
  pos2 : fr₂.pos = d.blk.body.size
  condVal : Bool
  ρ₁₀ : Env
  va : Word
  vb : Word
  ha : d.a.eval ρ₁₀ = some va
  hb : d.bArg.eval ρ₁₀ = some vb
  hcond : d.c.holds d.w va vb = condVal
  hAgree0 : EnvAgreeOuter d.off d.armT.defs d.armF.defs ρ₁₀ fr₂.env
  hFParams : ∀ x ∈ d.F.params, ρ₁₀[x]?.isSome = true
  hBParams : ∀ x ∈ d.blk.params, ρ₁₀[x]?.isSome = true
  hBBody : ∀ i, i < d.blk.body.size → ∀ st, d.blk.body[i]? = some st →
    ∀ x ∈ st.uses ++ st.defs, ρ₁₀[x]?.isSome = true
  preSteps : List ArmStep
  curStep : ArmStep
  remSteps : List ArmStep
  hStepsEq : (if condVal then d.armT else d.armF).steps = preSteps ++ curStep :: remSteps
  hLbl1 : fr₁.label = curStep.label
  hPosLe : fr₁.pos ≤ curStep.body.length
  ρStepEntry : Env
  hPreRun : runArmConcrete mem ctx preSteps ρ₁₀ = some (.inr ρStepEntry)
  hCurRun : execList ρStepEntry mem ctx (curStep.body.take fr₁.pos) = some (fr₁.env, mem)

/-- Top frame relation: either normal mode or parked inside the converted diamond arm. -/
private inductive IfConvTopRel {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b) (mem : X86.Memory) (ctx : Word) (fr₁ fr₂ : Frame) : Prop where
  | normal : NormalIfConvFrame d true fr₁ fr₂ → IfConvTopRel d mem ctx fr₁ fr₂
  | inArm : InArmFrame d mem ctx fr₁ fr₂ → IfConvTopRel d mem ctx fr₁ fr₂

private inductive ListForall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : ListForall2 R [] []
  | cons {a b as bs} : R a b → ListForall2 R as bs → ListForall2 R (a :: as) (b :: bs)

/-- Whole-state simulation relation for `ifConvDiamondSite`. -/
private inductive IfConvStackRel {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b) (mem : X86.Memory) (ctx : Word) : List Frame → List Frame → Prop where
  | nil : IfConvStackRel d mem ctx [] []
  | cons {fr₁ fr₂ rest₁ rest₂} :
      IfConvTopRel d mem ctx fr₁ fr₂ →
      ListForall2 (NormalIfConvFrame d false) rest₁ rest₂ →
      IfConvStackRel d mem ctx (fr₁ :: rest₁) (fr₂ :: rest₂)

private def IfConvStateRel {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b) (s₁ s₂ : State) : Prop :=
  s₂.mem = s₁.mem ∧ s₂.ctx = s₁.ctx ∧ IfConvStackRel d s₁.mem s₁.ctx s₁.stack s₂.stack

/-! ## Unpacking `IfConvData` & `buildIfConvFunc` block lookup lemmas -/

private theorem natSet_ofList_contains (xs : List Nat) (x : Nat) :
    (Src.NatSet.ofList xs).contains x = decide (x ∈ xs) := by
  have hgo : ∀ (ys : List Nat) (acc : Src.NatSet),
      ((ys.map (·, ())).foldl (fun m (p : Nat × Unit) => Src.NatMap.insert m p.1 p.2) acc).contains x =
        (acc.contains x || decide (x ∈ ys)) := by
    intro ys
    induction ys with
    | nil => intro acc; simp
    | cons y rest ih =>
        intro acc
        simp only [List.map_cons, List.foldl_cons, List.mem_cons]
        rw [ih (Src.NatMap.insert acc y ())]
        simp only [Src.NatMap.contains, Src.NatMap.get?_insert]
        by_cases hxy : x = y
        · subst hxy; simp
        · simp [hxy]
  have h0 := hgo xs .leaf
  have hleaf : (Src.NatMap.leaf : Src.NatSet).contains x = false := rfl
  rw [hleaf, Bool.false_or] at h0
  exact h0

private theorem env_isSome_insert {ρ : Env} {x y : VReg} {v : Word}
    (h : ρ[x]?.isSome = true) : (ρ.insert y v)[x]?.isSome = true := by
  rw [env_insert_get]; split
  · rfl
  · exact h

private theorem bindParams_preserves_isSome {ρ ρ' : Env} :
    ∀ {xs : List VReg} {vs : List Word},
      bindParams ρ xs vs = some ρ' →
      ∀ (u : VReg), ρ[u]?.isSome = true → ρ'[u]?.isSome = true
  | [], [], hb, u, hu => by simp [bindParams] at hb; subst hb; exact hu
  | x :: xs, v :: vs, hb, u, hu =>
      bindParams_preserves_isSome (ρ := ρ.insert x v) hb u (env_isSome_insert (y := x) (v := v) hu)
  | [], _ :: _, hb, _, _ | _ :: _, [], hb, _, _ => by simp [bindParams] at hb

private theorem stmt_exec_preserves_isSome {ρ ρ' : Env} {mem mem' : X86.Memory} {ctx : Word}
    {s : Stmt} (hx : s.exec ρ mem ctx = some (ρ', mem')) :
    ∀ (u : VReg), ρ[u]?.isSome = true → ρ'[u]?.isSome = true := by
  intro u hu
  cases s with
  | assign x r =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨v, _, rfl, _⟩ := hx; exact env_isSome_insert hu
  | limb r1 r2 op =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨⟨v1, v2⟩, _, rfl, _⟩ := hx; exact env_isSome_insert (env_isSome_insert hu)
  | store _ _ _ =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
      obtain ⟨_, _, _, _, hw⟩ := hx
      cases h : mem.write? _ _ _ with
      | error _ => rw [h] at hw; cases hw
      | ok _ => rw [h] at hw; simp only [Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, _⟩ := hw; exact hu
  | call _ _ _ => simp [Stmt.exec] at hx

private theorem arg_eval_isSome {ρ : Env} {a : Arg} {v : Word} (ha : a.eval ρ = some v) :
    ∀ x ∈ a.uses, ρ[x]?.isSome = true := by
  intro x hx
  cases a with
  | imm _ => simp [Arg.uses, Arg.vreg?] at hx
  | v u =>
      simp only [Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hx
      subst hx; simp [Arg.eval] at ha; simp [ha]

private theorem evalArgs_isSome {ρ : Env} :
    ∀ {as : List Arg} {vs : List Word},
      evalArgs ρ as = some vs → ∀ a ∈ as, ∀ x ∈ a.uses, ρ[x]?.isSome = true
  | [], _, _, _, ha => by cases ha
  | a :: rest, vs, h, a0, ha0 => by
      simp only [evalArgs_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨v, hv, vs', hvs', rfl⟩ := h
      simp only [List.mem_cons] at ha0
      rcases ha0 with rfl | hmem
      · exact arg_eval_isSome hv
      · exact evalArgs_isSome hvs' a0 hmem

private theorem addr_eval_isSome {ρ : Env} {ctx : Word} {m : Addr} {v : Word} (hm : m.eval ρ ctx = some v) :
    ∀ x ∈ m.uses, ρ[x]?.isSome = true := by
  rcases m with ⟨base, idx, disp⟩
  intro x hx
  simp only [Addr.uses, List.mem_append] at hx
  cases base with
  | none =>
      rcases hx with h1 | h2
      · simp at h1
      · cases idx with
        | none => simp at h2
        | some p =>
            rcases p with ⟨ix, s⟩
            simp only [List.mem_singleton] at h2; subst h2
            simp only [Addr.eval, Option.bind_eq_bind, Option.bind_some, Option.map_eq_map,
              Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
            obtain ⟨_, ⟨vx, hvx, _⟩, _⟩ := hm; simp [hvx]
  | some b0 =>
      cases b0 with
      | ctx =>
          rcases hx with h1 | h2
          · simp [Base.uses] at h1
          · cases idx with
            | none => simp at h2
            | some p =>
                rcases p with ⟨ix, s⟩
                simp only [List.mem_singleton] at h2; subst h2
                simp only [Addr.eval, Option.bind_eq_bind, Option.bind_some, Option.map_eq_map,
                  Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
                obtain ⟨_, ⟨vx, hvx, _⟩, _⟩ := hm; simp [hvx]
      | v bx =>
          rcases hx with h1 | h2
          · simp only [Base.uses, List.mem_singleton] at h1; subst h1
            simp only [Addr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hm
            obtain ⟨vb, hvb, _⟩ := hm; simp [hvb]
          · cases idx with
            | none => simp at h2
            | some p =>
                rcases p with ⟨ix, s⟩
                simp only [List.mem_singleton] at h2; subst h2
                simp only [Addr.eval, Option.bind_eq_bind, Option.map_eq_map,
                  Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
                obtain ⟨_, _, _, ⟨vx, hvx, _⟩, _⟩ := hm; simp [hvx]

private theorem stmt_exec_uses_defs_isSome {ρ ρ' : Env} {mem mem' : X86.Memory} {ctx : Word}
    {s : Stmt} (hx : s.exec ρ mem ctx = some (ρ', mem')) :
    ∀ x ∈ s.uses ++ s.defs, ρ'[x]?.isSome = true := by
  have hpres := stmt_exec_preserves_isSome hx
  intro x hxmem
  cases s with
  | assign r rhs =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨v, hv, rfl, rfl⟩ := hx
      simp only [Stmt.uses, Stmt.defs, List.mem_append, List.mem_singleton] at hxmem
      rcases hxmem with hu | rfl
      · apply env_isSome_insert
        cases rhs with
        | arg a => exact arg_eval_isSome hv x hu
        | bin _ _ a b =>
            simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
            obtain ⟨_, ha, _, hb, _⟩ := hv
            simp only [Rhs.uses, List.mem_append] at hu
            rcases hu with h1 | h2
            · exact arg_eval_isSome ha x h1
            · exact arg_eval_isSome hb x h2
        | load _ _ m =>
            simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
            obtain ⟨_, hm, _⟩ := hv; exact addr_eval_isSome hm x hu
        | addr m => exact addr_eval_isSome hv x hu
        | select _ _ a b t f =>
            simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
            obtain ⟨_, ha, _, hb, _, ht, _, hf, _⟩ := hv
            simp only [Rhs.uses, List.mem_append] at hu
            rcases hu with ((h1 | h2) | h3) | h4
            · exact arg_eval_isSome ha x h1
            · exact arg_eval_isSome hb x h2
            · exact arg_eval_isSome ht x h3
            · exact arg_eval_isSome hf x h4
        | test _ _ a b =>
            simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
            obtain ⟨_, ha, _, hb, _⟩ := hv
            simp only [Rhs.uses, List.mem_append] at hu
            rcases hu with h1 | h2
            · exact arg_eval_isSome ha x h1
            · exact arg_eval_isSome hb x h2
        | bsr64 a =>
            simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
            obtain ⟨_, ha, _⟩ := hv; exact arg_eval_isSome ha x hu
      · simp
  | limb r1 r2 op =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨⟨v1, v2⟩, hv, rfl, rfl⟩ := hx
      simp only [Stmt.uses, Stmt.defs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hxmem
      rcases hxmem with hu | (rfl | rfl)
      · apply env_isSome_insert; apply env_isSome_insert
        cases op with
        | mulWide64 a b =>
            simp only [LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
            obtain ⟨_, ha, _, hb, _⟩ := hv
            simp only [LimbOp.uses, List.mem_append] at hu
            rcases hu with h1 | h2
            · exact arg_eval_isSome ha x h1
            · exact arg_eval_isSome hb x h2
        | divWide64 hi lo d | addCarry64 hi lo d | subBorrow64 hi lo d =>
            simp only [LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
            obtain ⟨_, h1, _, h2, _, h3, _⟩ := hv
            simp only [LimbOp.uses, List.mem_append] at hu
            rcases hu with (ha | hb) | hc
            · exact arg_eval_isSome h1 x ha
            · exact arg_eval_isSome h2 x hb
            · exact arg_eval_isSome h3 x hc
      · exact env_isSome_insert (by simp)
      · simp
  | store w m a =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
      obtain ⟨_, hm, _, ha, hw⟩ := hx
      cases h : mem.write? w _ _ with
      | error _ => rw [h] at hw; cases hw
      | ok _ =>
          rw [h] at hw; simp only [Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          simp only [Stmt.uses, Stmt.defs, List.append_nil, List.mem_append] at hxmem
          rcases hxmem with h1 | h2
          · exact addr_eval_isSome hm x h1
          · exact arg_eval_isSome ha x h2
  | call _ _ _ => simp [Stmt.exec] at hx

/-- Execute a contiguous sublist of non-call statements inside `G.blocks[b]` in 0 clock charges. -/
private theorem execList_star_steps {q : Program} {fi : FunId} {b : Label} {G : Func} {blk' : Block}
    {ctx : Word} {dsts : List VReg} {rest : List Frame}
    (hG : q.funcs[fi]? = some G) (hb : G.blocks[b]? = some blk') :
    ∀ (pre ss post : List Stmt) (ρ ρ' : Env) (mem mem' : X86.Memory),
      blk'.body.toList = pre ++ ss ++ post →
      (∀ s ∈ ss, s.isCall = false) →
      execList ρ mem ctx ss = some (ρ', mem') →
      Sem.Star (semStep q)
        { mem, ctx, stack := { fn := fi, label := b, pos := pre.length, env := ρ, dsts } :: rest }
        0
        { mem := mem', ctx, stack := { fn := fi, label := b, pos := pre.length + ss.length, env := ρ', dsts } :: rest }
  | pre, [], post, ρ, ρ', mem, mem', _, _, hex => by
      simp only [execList, Option.some.injEq, Prod.mk.injEq] at hex
      obtain ⟨rfl, rfl⟩ := hex
      simpa using (Sem.Star.refl (step := semStep q)
        { mem := mem, ctx := ctx, stack := { fn := fi, label := b, pos := pre.length, env := ρ, dsts } :: rest })
  | pre, s :: restS, post, ρ, ρ', mem, mem', hbody, hnc, hex => by
      simp only [execList] at hex
      split at hex
      · rename_i ρ1 mem1 hxs
        have hnc_s : s.isCall = false := hnc s (by simp)
        have hlt : pre.length < blk'.body.size := by
          have := congrArg List.length hbody
          simp only [Array.length_toList, List.length_append, List.length_cons] at this
          omega
        have hget : blk'.body[pre.length]'hlt = s := by
          have h1 : blk'.body.toList[pre.length]? = some s := by
            rw [hbody, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
            rfl
          rw [Array.getElem?_toList, Array.getElem?_eq_getElem hlt] at h1
          exact Option.some.inj h1
        have hst1 : step q { mem, ctx, stack := { fn := fi, label := b, pos := pre.length, env := ρ, dsts } :: rest } =
            .next { mem := mem1, ctx, stack := { fn := fi, label := b, pos := pre.length + 1, env := ρ1, dsts } :: rest } false := by
          exact step_stmt (p := q) (F := G) (B := blk')
            (fr := { fn := fi, label := b, pos := pre.length, env := ρ, dsts })
            (rest := rest) (mem := mem) (ctx := ctx) hG hb hlt hget hnc_s hxs
        have hbody' : blk'.body.toList = (pre ++ [s]) ++ restS ++ post := by
          simpa [List.append_assoc] using hbody
        have hstar2 := execList_star_steps (dsts := dsts) (rest := rest) hG hb (pre ++ [s]) restS post ρ1 ρ' mem1 mem' hbody'
          (fun s' hs' => hnc s' (by simp [hs'])) hex
        simp only [List.length_append, List.length_singleton] at hstar2
        have hlen : pre.length + 1 + restS.length = pre.length + (s :: restS).length := by
          simp only [List.length_cons]; omega
        rw [hlen] at hstar2
        have hcomb := (star_of_step hst1).trans hstar2
        simpa using hcomb
      · cases hex

/-! ## `verifyArmMatches` & `runArmConcrete` correspondence lemmas -/

private theorem verifyArmMatches_step_at {F : Func} {b join : Label} {commonRes? : Option Sem.Resource}
    {arm : DiamondArm} :
    ∀ {start : Label} {pre rem : List ArmStep} {cur : ArmStep},
      b < start →
      verifyArmMatches.go F b join commonRes? arm start (pre ++ cur :: rem) = true →
      b < cur.label ∧
      (∃ curBlk, F.blocks[cur.label]? = some curBlk ∧ curBlk.params = [] ∧
        curBlk.body.toList = cur.body ∧
        (match rem with
         | [] =>
             (join ≤ b ∨ cur.label < join) ∧
             cur.ovf? = none ∧
             curBlk.term = .jump { target := join, args := arm.joinArgs }
         | next :: _ =>
             cur.label < next.label ∧
             ∃ o x oa ob res ovfEdge,
               cur.ovf? = some (o, x, oa, ob, res) ∧
               commonRes? = some res ∧
               curBlk.term = .brOvf o x oa ob { target := next.label, args := [] } ovfEdge ∧
               failEdgeResource? F ovfEdge = some res))
  | start, [], [], cur, hlt, hv => by
      simp only [List.nil_append, verifyArmMatches.go, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq, Bool.or_eq_true] at hv
      obtain ⟨⟨⟨rfl, hjb⟩, hov⟩, hblk⟩ := hv
      cases hB : F.blocks[cur.label]? with
      | none => rw [hB] at hblk; cases hblk
      | some curBlk =>
          rw [hB] at hblk
          simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hblk
          exact ⟨hlt, curBlk, rfl, hblk.1.1, hblk.1.2, hjb, Option.isNone_iff_eq_none.mp hov, hblk.2⟩
  | start, [], next :: rest, cur, hlt, hv => by
      simp only [List.nil_append, verifyArmMatches.go, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hv
      obtain ⟨⟨rfl, hcn⟩, hrest⟩ := hv
      cases hov : cur.ovf? with
      | none => rw [hov] at hrest; cases hrest
      | some tup =>
          rcases tup with ⟨o, x, oa, ob, res⟩
          rw [hov] at hrest
          cases hB : F.blocks[cur.label]? with
          | none => rw [hB] at hrest; cases hrest
          | some curBlk =>
              rw [hB] at hrest
              simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hrest
              obtain ⟨⟨⟨hresC, hpar⟩, hbody⟩, hterm⟩ := hrest
              have hcr : commonRes? = some res := by
                cases commonRes? with
                | none => cases hresC
                | some r0 => simp only [beq_iff_eq] at hresC; subst hresC; rfl
              cases ht : curBlk.term with
              | brOvf o' x' oa' ob' okEdge ovfEdge =>
                  rw [ht] at hterm
                  simp only [Bool.and_eq_true, beq_iff_eq] at hterm
                  obtain ⟨⟨⟨⟨⟨⟨ho, hx⟩, hoa⟩, hob⟩, hok⟩, hfail⟩, _⟩ := hterm
                  rw [ho, hx, hoa, hob, hok] at ht
                  exact ⟨hlt, curBlk, rfl, hpar, hbody, hcn, o, x, oa, ob, res, ovfEdge, rfl, hcr, ht, hfail⟩
              | jump _ | br _ _ _ _ _ _ | ret _ | tail _ _ | fail _ | trap => rw [ht] at hterm; cases hterm
  | start, st :: pre', rem, cur, hlt, hv => by
      have hcons : (st :: pre') ++ cur :: rem = st :: (pre' ++ cur :: rem) := rfl
      rw [hcons] at hv
      cases hnext : pre' ++ cur :: rem with
      | nil => cases pre' <;> cases hnext
      | cons nxt tail =>
          rw [hnext] at hv
          simp only [verifyArmMatches.go, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
          obtain ⟨⟨rfl, hltN⟩, hrest⟩ := hv
          cases hov : st.ovf? with
          | none => rw [hov] at hrest; cases hrest
          | some tup =>
              rcases tup with ⟨o, x, oa, ob, res⟩
              rw [hov] at hrest
              cases hB : F.blocks[st.label]? with
              | none => rw [hB] at hrest; cases hrest
              | some stBlk =>
                  rw [hB] at hrest
                  simp only [Bool.and_eq_true] at hrest
                  obtain ⟨_, hterm⟩ := hrest
                  cases ht : stBlk.term with
                  | brOvf o' x' oa' ob' okEdge ovfEdge =>
                      rw [ht] at hterm
                      simp only [Bool.and_eq_true] at hterm
                      have hgo := hterm.2
                      rw [← hnext] at hgo
                      exact verifyArmMatches_step_at (Nat.lt_trans hlt hltN) hgo
                  | jump _ | br _ _ _ _ _ _ | ret _ | tail _ _ | fail _ | trap => rw [ht] at hterm; cases hterm

private theorem verifyArmMatches_nonempty {F : Func} {b start join : Label}
    {commonRes? : Option Sem.Resource} {arm : DiamondArm}
    (hv : verifyArmMatches F b start join commonRes? arm = true) :
    ∃ first tail, arm.steps = first :: tail ∧ first.label = start := by
  unfold verifyArmMatches at hv
  simp only [Bool.and_eq_true, beq_iff_eq] at hv
  cases hs : arm.steps with
  | nil => rw [hs] at hv; simp [verifyArmMatches.go] at hv
  | cons first tail =>
      rw [hs] at hv
      cases tail with
      | nil =>
          simp only [verifyArmMatches.go, Bool.and_eq_true, beq_iff_eq] at hv
          exact ⟨first, [], rfl, hv.2.1.1.1⟩
      | cons nxt rest =>
          simp only [verifyArmMatches.go, Bool.and_eq_true, beq_iff_eq] at hv
          exact ⟨first, nxt :: rest, rfl, hv.2.1.1⟩

private theorem verifyArmMatches_labels_gt {F : Func} {b start join : Label}
    {commonRes? : Option Sem.Resource} {arm : DiamondArm}
    (hlt : b < start) (hv : verifyArmMatches F b start join commonRes? arm = true) :
    ∀ l ∈ arm.labels, b < l := by
  unfold verifyArmMatches at hv
  simp only [Bool.and_eq_true] at hv
  intro l hl
  simp only [DiamondArm.labels, List.mem_map] at hl
  obtain ⟨cur, hmem, rfl⟩ := hl
  obtain ⟨pre, rem, heq⟩ := List.append_of_mem hmem
  rw [heq] at hv
  exact (verifyArmMatches_step_at hlt hv.2).1

private theorem runArmConcrete_append {mem : X86.Memory} {ctx : Word} :
    ∀ {pre rem : List ArmStep} {ρ₀ ρMid : Env} {res : Sem.Resource ⊕ Env},
      runArmConcrete mem ctx pre ρ₀ = some (.inr ρMid) →
      runArmConcrete mem ctx rem ρMid = some res →
      runArmConcrete mem ctx (pre ++ rem) ρ₀ = some res
  | [], rem, ρ₀, ρMid, res, hpre, hrem => by
      simp only [runArmConcrete, Option.some.injEq, Sum.inr.injEq] at hpre
      subst hpre; exact hrem
  | st :: pre', rem, ρ₀, ρMid, res, hpre, hrem => by
      simp only [List.cons_append, runArmConcrete] at hpre ⊢
      cases hx : execList ρ₀ mem ctx st.body with
      | none => rw [hx] at hpre; cases hpre
      | some p1 =>
          rcases p1 with ⟨ρ1, mem1⟩
          rw [hx] at hpre
          simp only [Option.bind_eq_bind, Option.bind_some] at hpre ⊢
          cases hov : st.ovf? with
          | none =>
              rw [hov] at hpre; dsimp only at hpre ⊢
              exact runArmConcrete_append hpre hrem
          | some tup =>
              rcases tup with ⟨o, x, oa, ob, r⟩
              rw [hov] at hpre; dsimp only at hpre ⊢
              cases hoa : oa.eval ρ1 with
              | none => rw [hoa] at hpre; cases hpre
              | some va =>
                  rw [hoa] at hpre
                  simp only [Option.bind_some] at hpre ⊢
                  cases hob : ob.eval ρ1 with
                  | none => rw [hob] at hpre; cases hpre
                  | some vb =>
                      rw [hob] at hpre
                      simp only [Option.bind_some] at hpre ⊢
                      cases hcond : (o.eval va vb).2 <;> simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hpre ⊢
                      · exact runArmConcrete_append hpre hrem
                      · cases hpre

/-! ## `IfConvData` block lookup and helper lemmas -/

private theorem ifConv_outer_eval_arg {off : VReg} {tDefs fDefs : Src.NatSet} {ρ₁ ρ₂ : Env}
    (hag : EnvAgreeOuter off tDefs fDefs ρ₁ ρ₂) {a : Arg} {v : Word}
    (hok : ∀ x ∈ a.uses, OuterRegOk off tDefs fDefs x)
    (ha : a.eval ρ₁ = some v) : a.eval ρ₂ = some v := by
  cases a with
  | imm _ => exact ha
  | v x => exact hag x v (hok x (by simp [Arg.uses, Arg.vreg?])) ha

private theorem ifConv_outer_evalArgs {off : VReg} {tDefs fDefs : Src.NatSet} {ρ₁ ρ₂ : Env}
    (hag : EnvAgreeOuter off tDefs fDefs ρ₁ ρ₂) :
    ∀ {as : List Arg} {vs : List Word},
      (∀ a ∈ as, ∀ x ∈ a.uses, OuterRegOk off tDefs fDefs x) →
      evalArgs ρ₁ as = some vs → evalArgs ρ₂ as = some vs
  | [], vs, _, h => by simp only [evalArgs_nil, Option.some.injEq] at h; subst h; rfl
  | a :: rest, vs, hok, h => by
      simp only [evalArgs_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨v, hv, vs', hvs', rfl⟩ := h
      simp [evalArgs_cons, ifConv_outer_eval_arg hag (hok a (by simp)) hv,
        ifConv_outer_evalArgs hag (fun a' ha' => hok a' (by simp [ha'])) hvs']

private theorem ifConv_outer_eval_addr {off : VReg} {tDefs fDefs : Src.NatSet} {ρ₁ ρ₂ : Env} {ctx : Word}
    (hag : EnvAgreeOuter off tDefs fDefs ρ₁ ρ₂) {m : Addr} {v : Word}
    (hok : ∀ x ∈ m.uses, OuterRegOk off tDefs fDefs x)
    (hm : m.eval ρ₁ ctx = some v) : m.eval ρ₂ ctx = some v := by
  rcases m with ⟨base, idx, disp⟩
  cases base with
  | none =>
      cases idx with
      | none => exact hm
      | some p =>
          rcases p with ⟨x, s⟩
          simp only [Addr.eval, Option.bind_eq_bind, Option.bind_some, Option.map_eq_map,
            Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hm
          obtain ⟨_, ⟨vx, hvx, rfl⟩, rfl⟩ := hm
          simp [Addr.eval, hag x vx (hok x (by simp [Addr.uses])) hvx]
  | some b0 =>
      cases b0 with
      | ctx =>
          cases idx with
          | none => exact hm
          | some p =>
              rcases p with ⟨x, s⟩
              simp only [Addr.eval, Option.bind_eq_bind, Option.bind_some, Option.map_eq_map,
                Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hm
              obtain ⟨_, ⟨vx, hvx, rfl⟩, rfl⟩ := hm
              simp [Addr.eval, hag x vx (hok x (by simp [Addr.uses])) hvx]
      | v bx =>
          have hbx_ok := hok bx (by simp [Addr.uses, Base.uses])
          cases idx with
          | none =>
              simp only [Addr.eval, Option.bind_eq_bind, Option.bind_some,
                Option.bind_eq_some_iff, Option.some.injEq] at hm
              obtain ⟨vb, hvb, rfl⟩ := hm
              simp [Addr.eval, hag bx vb hbx_ok hvb]
          | some p =>
              rcases p with ⟨x, s⟩
              simp only [Addr.eval, Option.bind_eq_bind, Option.map_eq_map,
                Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hm
              obtain ⟨vb, hvb, _, ⟨vx, hvx, rfl⟩, rfl⟩ := hm
              simp [Addr.eval, hag bx vb hbx_ok hvb, hag x vx (hok x (by simp [Addr.uses])) hvx]

private theorem ifConv_outer_exec_stmt {off : VReg} {tDefs fDefs : Src.NatSet}
    {ρ₁ ρ₂ ρ₁' : Env} {mem mem' : X86.Memory} {ctx : Word}
    (hag : EnvAgreeOuter off tDefs fDefs ρ₁ ρ₂) {s : Stmt}
    (hok : ∀ x ∈ s.uses, OuterRegOk off tDefs fDefs x)
    (hx : s.exec ρ₁ mem ctx = some (ρ₁', mem')) :
    ∃ ρ₂', s.exec ρ₂ mem ctx = some (ρ₂', mem') ∧ EnvAgreeOuter off tDefs fDefs ρ₁' ρ₂' := by
  cases s with
  | assign x r =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨v, hv, rfl, rfl⟩ := hx
      have hv2 : r.eval ρ₂ mem ctx = some v := by
        cases r with
        | arg a => exact ifConv_outer_eval_arg hag hok hv
        | bin o w a b =>
            simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
            obtain ⟨va, ha, vb, hb, ho⟩ := hv
            simp only [Rhs.eval, Option.bind_eq_bind,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, Rhs.uses, hu])) ha,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, Rhs.uses, hu])) hb,
              Option.bind_some]; exact ho
        | load w e m =>
            simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
            obtain ⟨va, ha, hl⟩ := hv
            simp only [Rhs.eval, Option.bind_eq_bind, ifConv_outer_eval_addr hag hok ha, Option.bind_some]; exact hl
        | addr m => exact ifConv_outer_eval_addr hag hok hv
        | select c w a b t f =>
            simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
            obtain ⟨va, ha, vb, hb, vt, ht, vf, hf, rfl⟩ := hv
            simp only [Rhs.eval, Option.bind_eq_bind,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, Rhs.uses, hu])) ha,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, Rhs.uses, hu])) hb,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, Rhs.uses, hu])) ht,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, Rhs.uses, hu])) hf,
              Option.bind_some]
        | test c w a b =>
            simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
            obtain ⟨va, ha, vb, hb, rfl⟩ := hv
            simp only [Rhs.eval, Option.bind_eq_bind,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, Rhs.uses, hu])) ha,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, Rhs.uses, hu])) hb,
              Option.bind_some]
        | bsr64 a =>
            simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
            obtain ⟨va, ha, hb⟩ := hv
            simp only [Rhs.eval, Option.bind_eq_bind, ifConv_outer_eval_arg hag hok ha, Option.bind_some]; exact hb
      exact ⟨ρ₂.insert x v, by simp [Stmt.exec, hv2], envAgreeOuter_insert hag x v⟩
  | limb r1 r2 op =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨⟨v1, v2⟩, hv, rfl, rfl⟩ := hx
      have hv2 : op.eval ρ₂ = some (v1, v2) := by
        cases op with
        | mulWide64 a b =>
            simp only [LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
            obtain ⟨va, ha, vb, hb, ho⟩ := hv
            simp only [LimbOp.eval, Option.bind_eq_bind,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, LimbOp.uses, hu])) ha,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, LimbOp.uses, hu])) hb,
              Option.bind_some]; exact ho
        | divWide64 hi lo d | addCarry64 hi lo d | subBorrow64 hi lo d =>
            simp only [LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
            obtain ⟨v1', h1, v2', h2, v3', h3, ho⟩ := hv
            simp only [LimbOp.eval, Option.bind_eq_bind,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, LimbOp.uses, hu])) h1,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, LimbOp.uses, hu])) h2,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, LimbOp.uses, hu])) h3,
              Option.bind_some]; exact ho
      exact ⟨(ρ₂.insert r1 v1).insert r2 v2, by simp [Stmt.exec, hv2],
        envAgreeOuter_insert (envAgreeOuter_insert hag r1 v1) r2 v2⟩
  | store w m a =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
      obtain ⟨addr, haddr, val, hval, hwr⟩ := hx
      cases hw : mem.write? w addr val with
      | error _ => rw [hw] at hwr; cases hwr
      | ok mem'' =>
          rw [hw] at hwr; simp only [Option.some.injEq, Prod.mk.injEq] at hwr
          obtain ⟨rfl, rfl⟩ := hwr
          exact ⟨ρ₂, by
            simp [Stmt.exec,
              ifConv_outer_eval_addr hag (fun u hu => hok u (by simp [Stmt.uses, hu])) haddr,
              ifConv_outer_eval_arg hag (fun u hu => hok u (by simp [Stmt.uses, hu])) hval, hw], hag⟩
  | call _ _ _ => simp [Stmt.exec] at hx

/-- Helper: `Term.setEdges` preserves terminator structure, replacing only edges. -/
private theorem setEdges_remap_jump (e : Edge) (f : Label → Label) :
    (Term.jump e).setEdges ((Term.jump e).edges.map fun e => { e with target := f e.target }) =
      Term.jump { e with target := f e.target } := rfl

private theorem setEdges_remap_br (c : Cond) (w : Width) (a b : Arg) (t e : Edge) (f : Label → Label) :
    (Term.br c w a b t e).setEdges ((Term.br c w a b t e).edges.map fun e => { e with target := f e.target }) =
      Term.br c w a b { t with target := f t.target } { e with target := f e.target } := rfl

private theorem setEdges_remap_brOvf (o : Ovf) (x : VReg) (a b : Arg) (ok ovf : Edge) (f : Label → Label) :
    (Term.brOvf o x a b ok ovf).setEdges
        ((Term.brOvf o x a b ok ovf).edges.map fun e => { e with target := f e.target }) =
      Term.brOvf o x a b { ok with target := f ok.target } { ovf with target := f ovf.target } := rfl

private theorem setEdges_remap_ret (as : List Arg) (f : Label → Label) :
    (Term.ret as).setEdges ((Term.ret as).edges.map fun e => { e with target := f e.target }) =
      Term.ret as := rfl

private theorem setEdges_remap_tail (g : FunId) (as : List Arg) (f : Label → Label) :
    (Term.tail g as).setEdges ((Term.tail g as).edges.map fun e => { e with target := f e.target }) =
      Term.tail g as := rfl

private theorem setEdges_remap_fail (r : Sem.Resource) (f : Label → Label) :
    (Term.fail r).setEdges ((Term.fail r).edges.map fun e => { e with target := f e.target }) =
      Term.fail r := rfl

private theorem setEdges_remap_trap (f : Label → Label) :
    Term.trap.setEdges (Term.trap.edges.map fun e => { e with target := f e.target }) =
      Term.trap := rfl

private structure IfConvUnpacked {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b) where
  bLt : b < d.F.blocks.size
  b0Empty : b = 0 → d.blk.params = []
  bLtT : b < d.eT.target
  bLtF : b < d.eF.target
  joinLt : d.armT.join < d.F.blocks.size
  eTArgs : d.eT.args = []
  eFArgs : d.eF.args = []
  joinEq : d.armT.join = d.armF.join
  argsLenEq : d.armT.joinArgs.length = d.armF.joinArgs.length
  bNotT : (Src.NatSet.ofList d.armT.labels).contains b = false
  bNotF : (Src.NatSet.ofList d.armF.labels).contains b = false
  joinNotT : (Src.NatSet.ofList d.armT.labels).contains d.armT.join = false
  joinNotF : (Src.NatSet.ofList d.armF.labels).contains d.armT.join = false
  regsLt : funcRegsLt d.F d.off = true
  verT : verifyArmMatches d.F b d.eT.target d.armT.join (d.armT.failRes?.orElse fun _ => d.armF.failRes?) d.armT = true
  verF : verifyArmMatches d.F b d.eF.target d.armT.join (d.armT.failRes?.orElse fun _ => d.armF.failRes?) d.armF = true
  pureT : checkArmPure d.armT d.armT.defs = true
  pureF : checkArmPure d.armF d.armF.defs = true
  guarDisjoint : ∀ x ∈ d.F.params ++ d.blk.params ++ d.blk.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ d.a.uses ++ d.bArg.uses,
    OuterRegOk d.off d.armT.defs d.armF.defs x
  outerT : ∀ st ∈ d.armT.steps,
    (∀ s ∈ st.body, ∀ x ∈ s.uses, d.armT.defs.contains x = false →
      x ∈ d.F.params ++ d.blk.params ++ d.blk.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ d.a.uses ++ d.bArg.uses) ∧
    (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
      ∀ u ∈ oa.uses ++ ob.uses, d.armT.defs.contains u = false →
        u ∈ d.F.params ++ d.blk.params ++ d.blk.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ d.a.uses ++ d.bArg.uses)
  outerF : ∀ st ∈ d.armF.steps,
    (∀ s ∈ st.body, ∀ x ∈ s.uses, d.armF.defs.contains x = false →
      x ∈ d.F.params ++ d.blk.params ++ d.blk.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ d.a.uses ++ d.bArg.uses) ∧
    (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
      ∀ u ∈ oa.uses ++ ob.uses, d.armF.defs.contains u = false →
        u ∈ d.F.params ++ d.blk.params ++ d.blk.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ d.a.uses ++ d.bArg.uses)
  diffJoin : ∀ p0 ∈ d.armT.joinArgs.zip d.armF.joinArgs,
    loopMapArg d.armT.defs d.off 1 p0.1 ≠ loopMapArg d.armF.defs d.off 2 p0.2 →
    (∀ x ∈ p0.1.uses, d.armT.defs.contains x = true ∨
      x ∈ d.F.params ++ d.blk.params ++ d.blk.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ d.a.uses ++ d.bArg.uses) ∧
    (∀ x ∈ p0.2.uses, d.armF.defs.contains x = true ∨
      x ∈ d.F.params ++ d.blk.params ++ d.blk.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ d.a.uses ++ d.bArg.uses)
  outsideNoEnter : ∀ u uBlk, d.F.blocks[u]? = some uBlk → u ≠ b →
    (Src.NatSet.ofList d.armT.labels).contains u = false →
    (Src.NatSet.ofList d.armF.labels).contains u = false →
    ∀ e ∈ uBlk.term.edges,
      (Src.NatSet.ofList d.armT.labels).contains e.target = false ∧
      (Src.NatSet.ofList d.armF.labels).contains e.target = false
  outsideUses : ∀ u uBlk, d.F.blocks[u]? = some uBlk →
    (Src.NatSet.ofList d.armT.labels).contains u = false →
    (Src.NatSet.ofList d.armF.labels).contains u = false →
    ∀ x ∈ uBlk.body.toList.flatMap (·.uses) ++ uBlk.term.uses ++ uBlk.term.edgeUses,
      OuterRegOk d.off d.armT.defs d.armF.defs x

private theorem listLt_mem {off : VReg} {xs : List VReg} (h : listLt off xs = true)
    {x : VReg} (hx : x ∈ xs) : x < off := by
  simp only [listLt, List.all_eq_true, decide_eq_true_eq] at h
  exact h x hx

private theorem ifConv_unpack {p q : Program} {fi : FunId} {b : Label} (d : IfConvData p q fi b) :
    IfConvUnpacked d := by
  have hbLt : b < d.F.blocks.size := (Array.getElem?_eq_some_iff.1 d.hb).1
  have hok := d.hOk
  unfold ifConvDiamondOk at hok
  rw [d.hb] at hok
  dsimp only at hok
  rw [d.hTerm] at hok
  dsimp only at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq,
    List.isEmpty_iff, beq_iff_eq, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb0, hbT⟩, hbF⟩, hjLt⟩, heT⟩, heF⟩, hjEq⟩, haLen⟩, _⟩, ⟨⟨⟨⟨hbNT, hbNF⟩, hjNT⟩, hjNF⟩, _⟩⟩,
    hgd⟩, hregs⟩, hverT⟩, hverF⟩, hpureT⟩, hpureF⟩, houtT⟩, houtF⟩, hdiff⟩, hall⟩ := hok
  have hmemG : ∀ x, (Src.NatSet.ofList (d.F.params ++ d.blk.params ++
      d.blk.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ d.a.uses ++ d.bArg.uses)).contains x = true ↔
      x ∈ d.F.params ++ d.blk.params ++ d.blk.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ d.a.uses ++ d.bArg.uses := by
    intro x; rw [natSet_ofList_contains]; simp
  refine ⟨hbLt, fun hb0' => hb0.elim (fun hne => absurd hb0' hne) id,
    hbT, hbF, hjLt, heT, heF, hjEq, haLen, hbNT, hbNF, hjNT, hjNF, hregs, hverT, hverF, hpureT, hpureF,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hgd
    obtain ⟨hnt, hnf⟩ := hgd x hx
    have hlt : x < d.off := by
      simp only [funcRegsLt, Bool.and_eq_true, List.all_eq_true] at hregs
      have hbr : blockRegsLt d.off d.blk = true :=
        hregs.2 d.blk (Array.mem_toList_iff.2 (Array.mem_of_getElem? d.hb))
      simp only [blockRegsLt, Bool.and_eq_true, List.all_eq_true] at hbr
      simp only [List.mem_append, List.mem_flatMap] at hx
      rcases hx with (((hfp | hbp) | ⟨s, hs, hxs⟩) | ha) | hb
      · exact listLt_mem hregs.1 hfp
      · exact listLt_mem hbr.1.1.1.1 hbp
      · rcases hxs with hu | hd
        · exact listLt_mem (hbr.1.1.1.2 s hs).1 hu
        · exact listLt_mem (hbr.1.1.1.2 s hs).2 hd
      · have hu := hbr.1.1.2; rw [d.hTerm] at hu; exact listLt_mem hu (by simp [Term.uses, ha])
      · have hu := hbr.1.1.2; rw [d.hTerm] at hu; exact listLt_mem hu (by simp [Term.uses, hb])
    exact ⟨hlt, hnt, hnf⟩
  · intro st hst
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true] at houtT
    obtain ⟨h1, h2⟩ := houtT st hst
    refine ⟨fun s hs x hx hnot => ?_, fun o x oa ob r hov u hu hnot => ?_⟩
    · rcases h1 s hs x hx with h | h
      · rw [hnot] at h; cases h
      · exact (hmemG x).1 h
    · rw [hov] at h2; dsimp only at h2
      simp only [List.all_eq_true, Bool.or_eq_true] at h2
      rcases h2 u hu with h | h
      · rw [hnot] at h; cases h
      · exact (hmemG u).1 h
  · intro st hst
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true] at houtF
    obtain ⟨h1, h2⟩ := houtF st hst
    refine ⟨fun s hs x hx hnot => ?_, fun o x oa ob r hov u hu hnot => ?_⟩
    · rcases h1 s hs x hx with h | h
      · rw [hnot] at h; cases h
      · exact (hmemG x).1 h
    · rw [hov] at h2; dsimp only at h2
      simp only [List.all_eq_true, Bool.or_eq_true] at h2
      rcases h2 u hu with h | h
      · rw [hnot] at h; cases h
      · exact (hmemG u).1 h
  · intro p0 hp0 hne
    simp only [List.all_eq_true] at hdiff
    have hp := hdiff p0 hp0
    simp only [hne, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp
    exact ⟨fun x hx => by rcases hp.1 x hx with h | h; exact .inl h; exact .inr ((hmemG x).1 h),
           fun x hx => by rcases hp.2 x hx with h | h; exact .inl h; exact .inr ((hmemG x).1 h)⟩
  · intro u uBlk hu hne huNT huNF e he
    have huLt : u < d.F.blocks.size := (Array.getElem?_eq_some_iff.1 hu).1
    simp only [List.all_eq_true, List.mem_range] at hall
    have hbu := hall u huLt
    rw [hu] at hbu
    simp only [Bool.and_eq_true] at hbu
    have hno := hbu.1.1
    simp only [hne, ↓reduceIte, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at hno
    obtain ⟨h1, h2⟩ := hno e he
    exact ⟨h1.elim (fun h => by rw [huNT] at h; cases h) id,
           h2.elim (fun h => by rw [huNF] at h; cases h) id⟩
  · intro u uBlk hu huNT huNF x hx
    have huLt : u < d.F.blocks.size := (Array.getElem?_eq_some_iff.1 hu).1
    simp only [List.all_eq_true, List.mem_range] at hall
    have hbu := hall u huLt
    rw [hu] at hbu
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, Bool.not_eq_true'] at hbu
    have hnotT : d.armT.defs.contains x = false := by
      rcases hbu.1.2 with h | h
      · rw [huNT] at h; cases h
      · exact h x hx
    have hnotF : d.armF.defs.contains x = false := by
      rcases hbu.2 with h | h
      · rw [huNF] at h; cases h
      · exact h x hx
    have hregLt : x < d.off := by
      have hbr : blockRegsLt d.off uBlk = true := by
        simp only [funcRegsLt, Bool.and_eq_true, List.all_eq_true] at hregs
        exact hregs.2 uBlk (Array.mem_toList_iff.2 (Array.mem_of_getElem? hu))
      simp only [blockRegsLt, Bool.and_eq_true, List.all_eq_true] at hbr
      simp only [List.mem_append, List.mem_flatMap] at hx
      rcases hx with (⟨s, hs, hxs⟩ | hxt) | hxe
      · exact listLt_mem (hbr.1.1.1.2 s hs).1 hxs
      · exact listLt_mem hbr.1.1.2 hxt
      · exact listLt_mem hbr.2 hxe
    exact ⟨hregLt, hnotT, hnotF⟩

private theorem array_getElem!_of_getElem? {α : Type} [Inhabited α] {a : Array α} {i : Nat} {v : α}
    (h : a[i]? = some v) : a[i]! = v := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.1 h
  simp [hlt]

private theorem ifConv_G_params {p q : Program} {fi : FunId} {b : Label} (d : IfConvData p q fi b) :
    d.G.params = d.F.params := by
  rw [d.hGEq]; unfold buildIfConvFunc
  have hget : d.F.blocks[b]! = d.blk := array_getElem!_of_getElem? d.hb
  rw [hget]; dsimp only; rw [d.hTerm]
  dsimp only
  cases d.armT.failRes?.orElse fun _ => d.armF.failRes? <;> rfl

/-- Block lookup for `G` at `u ≠ b` (for both Shape 1 and Shape 2). -/
private theorem ifConv_G_blocks_other {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b) {u : Label} {uBlk : Block}
    (hu : d.F.blocks[u]? = some uBlk) (hne : u ≠ b) :
    let hasG := (d.armT.failRes?.orElse fun _ => d.armF.failRes?).isSome
    d.G.blocks[ifConvRemap b hasG u]? =
      some { uBlk with term := uBlk.term.setEdges (uBlk.term.edges.map fun e => { e with target := ifConvRemap b hasG e.target }) } := by
  have hbLt : b < d.F.blocks.size := (Array.getElem?_eq_some_iff.1 d.hb).1
  have huLt : u < d.F.blocks.size := (Array.getElem?_eq_some_iff.1 hu).1
  have hgetB : d.F.blocks[b]! = d.blk := array_getElem!_of_getElem? d.hb
  have hgetU : d.F.blocks[u]! = uBlk := array_getElem!_of_getElem? hu
  rw [d.hGEq]; unfold buildIfConvFunc; rw [hgetB]; dsimp only; rw [d.hTerm]; dsimp only
  cases hres : d.armT.failRes?.orElse fun _ => d.armF.failRes? with
  | none =>
      have hid : ∀ l, ifConvRemap b false l = l := fun l => by simp [ifConvRemap]
      simp only [Option.isSome_none, hid]
      have hterm_id : uBlk.term.setEdges (uBlk.term.edges.map fun e => { e with target := e.target }) = uBlk.term := by
        cases uBlk.term <;> rfl
      rw [hterm_id]
      simp [Array.set!_eq_setIfInBounds, Ne.symm hne, hu]
  | some res =>
      simp only [Option.isSome_some]
      rw [List.getElem?_toArray]
      have hrm : ∀ l, (if l < b + 1 then l else l + 1) = ifConvRemap b true l := fun l => by
        unfold ifConvRemap
        by_cases h : b + 1 ≤ l
        · have hnl : ¬ l < b + 1 := Nat.not_lt.2 h
          simp [h, hnl]
        · have hlt' : l < b + 1 := Nat.lt_of_not_ge h
          simp [h, hlt']
      simp only [hrm, List.append_assoc]
      by_cases hlt : u < b
      · have hru : ifConvRemap b true u = u := by
          unfold ifConvRemap; simp [Nat.not_le.2 (Nat.lt_succ_of_lt hlt)]
        rw [hru, List.getElem?_append_left (by simp [hlt]), List.getElem?_map,
          List.getElem?_range hlt, Option.map_some, hgetU]
      · have hgt : b < u := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
        have hru : ifConvRemap b true u = u + 1 := by
          unfold ifConvRemap; simp [Nat.succ_le_of_lt hgt]
        let uN : Nat := u
        let bN : Nat := b
        have hgtN : bN < uN := hgt
        have huLtN : uN < d.F.blocks.size := huLt
        rw [hru, List.getElem?_append_right (by simp; exact Nat.le_trans (Nat.le_of_lt hgt) (Nat.le_succ _))]
        simp only [List.length_map, List.length_range]
        rw [show u + 1 - b = (u - (b + 1)) + 1 + 1 by change uN + 1 - bN = (uN - (bN + 1)) + 1 + 1; omega]
        rw [List.cons_append, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_succ]
        rw [List.getElem?_append_left (by simp only [List.length_map, List.length_range]; change uN - (bN + 1) < d.F.blocks.size - (bN + 1); omega),
          List.getElem?_map,
          List.getElem?_range (by change uN - (bN + 1) < d.F.blocks.size - (bN + 1); omega), Option.map_some]
        rw [show b + 1 + (u - (b + 1)) = u by change bN + 1 + (uN - (bN + 1)) = uN; omega, hgetU]

/-- Block lookup for `G` at `b` in Shape 1 (`commonRes? = none`). -/
private theorem ifConv_G_blocks_b_shape1 {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b)
    (hnone : (d.armT.failRes?.orElse fun _ => d.armF.failRes?) = none) :
    let (stmtsT, _, fr1) := emitSpeculativeArm d.armT.defs d.off 1 d.armT (3 * d.off)
    let (stmtsF, _, fr2) := emitSpeculativeArm d.armF.defs d.off 2 d.armF fr1
    let argsT := d.armT.joinArgs.map (loopMapArg d.armT.defs d.off 1)
    let argsF := d.armF.joinArgs.map (loopMapArg d.armF.defs d.off 2)
    let (selStmts, selArgsRev, _) :=
      (argsT.zip argsF).foldl (init := ([], [], fr2)) fun (ss, out, fr) (at_, af_) =>
        if at_ == af_ then (ss, at_ :: out, fr)
        else (ss ++ [Stmt.assign fr (.select d.c d.w d.a d.bArg at_ af_)], Arg.v fr :: out, fr + 1)
    d.G.blocks[b]? = some
      { d.blk with
        body := (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts).toArray
        term := .jump { target := d.armT.join, args := selArgsRev.reverse } } := by
  have hbLt : b < d.F.blocks.size := (Array.getElem?_eq_some_iff.1 d.hb).1
  have hgetB : d.F.blocks[b]! = d.blk := array_getElem!_of_getElem? d.hb
  rw [d.hGEq]; unfold buildIfConvFunc; rw [hgetB]; dsimp only; rw [d.hTerm]; dsimp only
  rw [hnone]; dsimp only
  simp [Array.set!_eq_setIfInBounds, hbLt]

/-- Block lookups for `G` at `b`, `b + 1` (hop), and `n + 1` (fail) in Shape 2 (`commonRes? = some res`). -/
private theorem ifConv_G_blocks_shape2 {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b) {res : Sem.Resource}
    (hsome : (d.armT.failRes?.orElse fun _ => d.armF.failRes?) = some res) :
    let (stmtsT, flagT, fr1) := emitSpeculativeArm d.armT.defs d.off 1 d.armT (3 * d.off)
    let (stmtsF, flagF, fr2) := emitSpeculativeArm d.armF.defs d.off 2 d.armF fr1
    let argsT := d.armT.joinArgs.map (loopMapArg d.armT.defs d.off 1)
    let argsF := d.armF.joinArgs.map (loopMapArg d.armF.defs d.off 2)
    let (selStmts, selArgsRev, fr3) :=
      (argsT.zip argsF).foldl (init := ([], [], fr2)) fun (ss, out, fr) (at_, af_) =>
        if at_ == af_ then (ss, at_ :: out, fr)
        else (ss ++ [Stmt.assign fr (.select d.c d.w d.a d.bArg at_ af_)], Arg.v fr :: out, fr + 1)
    let predStmt := Stmt.assign fr3 (.select d.c d.w d.a d.bArg flagT flagF)
    d.G.blocks[b]? = some
      { d.blk with
        body := (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts ++ [predStmt]).toArray
        term := .br .ne .w64 (.v fr3) (.imm 0)
          { target := d.F.blocks.size + 1, args := [] }
          { target := b + 1, args := [] } } ∧
    d.G.blocks[b + 1]? = some
      ({ params := []
         body := #[]
         term := .jump { target := ifConvRemap b true d.armT.join, args := selArgsRev.reverse }
         cold := d.blk.cold } : Block) ∧
    d.G.blocks[d.F.blocks.size + 1]? = some
      ({ params := [], body := #[], term := .fail res, cold := true } : Block) := by
  have hbLt : b < d.F.blocks.size := (Array.getElem?_eq_some_iff.1 d.hb).1
  have hgetB : d.F.blocks[b]! = d.blk := array_getElem!_of_getElem? d.hb
  have hrm : ∀ l, (if l < b + 1 then l else l + 1) = ifConvRemap b true l := fun l => by
    unfold ifConvRemap
    by_cases h : b + 1 ≤ l
    · have hnl : ¬ l < b + 1 := Nat.not_lt.2 h
      simp [h, hnl]
    · have hlt' : l < b + 1 := Nat.lt_of_not_ge h
      simp [h, hlt']
  let bN : Nat := b
  have hbLtN : bN < d.F.blocks.size := hbLt
  rw [d.hGEq]; unfold buildIfConvFunc; rw [hgetB]; dsimp only; rw [d.hTerm]; dsimp only
  rw [hsome]; dsimp only
  simp only [hrm, List.getElem?_toArray, List.append_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.getElem?_append_right (by simp), List.length_map, List.length_range, Nat.sub_self, List.cons_append]; rfl
  · rw [List.getElem?_append_right (by simp), List.length_map, List.length_range,
      show b + 1 - b = 1 by change bN + 1 - bN = 1; omega, List.cons_append, List.cons_append]; rfl
  · rw [List.getElem?_append_right (by simp; exact Nat.le_trans (Nat.le_of_lt hbLt) (Nat.le_succ _)),
      List.length_map, List.length_range,
      show d.F.blocks.size + 1 - b = (d.F.blocks.size - (b + 1)) + 1 + 1 by
        change d.F.blocks.size + 1 - bN = (d.F.blocks.size - (bN + 1)) + 1 + 1; omega,
      List.cons_append, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_append_right (by simp), List.length_map, List.length_range, Nat.sub_self]; rfl

/-! ## Arm-body register bounds extracted from `IfConvData` -/

private theorem arm_step_regs_and_outer {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b) (u : IfConvUnpacked d) (isT : Bool) :
    let arm := if isT then d.armT else d.armF
    (∀ st ∈ arm.steps,
      (∀ s ∈ st.body, ∀ r ∈ s.defs, arm.defs.contains r = true ∧ r < d.off) ∧
      (∀ o x oa ob res, st.ovf? = some (o, x, oa, ob, res) → arm.defs.contains x = true ∧ x < d.off)) ∧
    (∀ st ∈ arm.steps,
      (∀ s ∈ st.body, ∀ x ∈ s.uses, arm.defs.contains x = false → x < d.off) ∧
      (∀ o x oa ob res, st.ovf? = some (o, x, oa, ob, res) →
        ∀ r ∈ oa.uses ++ ob.uses, arm.defs.contains r = false → r < d.off)) := by
  have hmemDefs : ∀ (arm : DiamondArm) (st : ArmStep) (r : VReg),
      st ∈ arm.steps →
      ((∃ s ∈ st.body, r ∈ s.defs) ∨ (∃ o oa ob res, st.ovf? = some (o, r, oa, ob, res))) →
      arm.defs.contains r = true := by
    intro arm st r hst hr
    have hgo : ∀ (steps : List ArmStep) (acc : Src.NatSet),
        (acc.contains r = true ∨ ∃ st0 ∈ steps,
          (∃ s ∈ st0.body, r ∈ s.defs) ∨ (∃ o oa ob res, st0.ovf? = some (o, r, oa, ob, res))) →
        (steps.foldl (init := acc) fun acc st =>
          let acc1 := st.body.foldl (fun s stmt => stmt.defs.foldl (fun a x => a.insert x) s) acc
          match st.ovf? with
          | some (_, x, _, _, _) => acc1.insert x
          | none => acc1).contains r = true := by
      intro steps
      induction steps with
      | nil =>
          intro acc h
          exact h.elim id fun ⟨_, hm, _⟩ => nomatch hm
      | cons st0 rest ih =>
          intro acc h
          simp only [List.foldl_cons]
          apply ih
          rcases h with hacc | ⟨st1, hmem1, hr1⟩
          · left
            have h1 : (st0.body.foldl (fun s stmt => stmt.defs.foldl (fun a x => a.insert x) s) acc).contains r = true := by
              have hfold : ∀ (ss : List Stmt) (a0 : Src.NatSet), a0.contains r = true →
                  (ss.foldl (fun s stmt => stmt.defs.foldl (fun a x => a.insert x) s) a0).contains r = true := by
                intro ss; induction ss with
                | nil => intro a0 h; exact h
                | cons s0 ss0 ihs =>
                    intro a0 h; apply ihs; rw [natSet_foldl_insert_contains]; exact .inr h
              exact hfold st0.body acc hacc
            cases st0.ovf? with
            | none => exact h1
            | some tup =>
                rcases tup with ⟨_, x, _, _, _⟩
                dsimp only
                rw [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert]
                by_cases hrx : r = x
                · simp [hrx]
                · simp only [hrx, ↓reduceIte]; exact h1
          · simp only [List.mem_cons] at hmem1
            rcases hmem1 with rfl | hmemRest
            · left
              have hfold : ∀ (ss : List Stmt) (a0 : Src.NatSet), (∃ s ∈ ss, r ∈ s.defs) →
                  (ss.foldl (fun s stmt => stmt.defs.foldl (fun a x => a.insert x) s) a0).contains r = true := by
                intro ss; induction ss with
                | nil => intro _ ⟨_, hm, _⟩; cases hm
                | cons s0 ss0 ihs =>
                    intro a0 ⟨s, hs, hrs⟩
                    simp only [List.mem_cons] at hs
                    rcases hs with rfl | hsr
                    · have h0 : (s.defs.foldl (fun a x => a.insert x) a0).contains r = true := by
                        rw [natSet_foldl_insert_contains]; exact .inl hrs
                      have hkeep : ∀ (ts : List Stmt) (b0 : Src.NatSet), b0.contains r = true →
                          (ts.foldl (fun s stmt => stmt.defs.foldl (fun a x => a.insert x) s) b0).contains r = true := by
                        intro ts; induction ts with
                        | nil => intro b0 h; exact h
                        | cons t0 ts0 iht => intro b0 h; apply iht; rw [natSet_foldl_insert_contains]; exact .inr h
                      exact hkeep ss0 _ h0
                    · exact ihs _ ⟨s, hsr, hrs⟩
              rcases hr1 with hbody | ⟨o, oa, ob, res, hov⟩
              · have h1 := hfold st1.body acc hbody
                cases st1.ovf? with
                | none => exact h1
                | some tup =>
                    rcases tup with ⟨_, x, _, _, _⟩
                    dsimp only
                    rw [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert]
                    by_cases hrx : r = x
                    · simp [hrx]
                    · simp only [hrx, ↓reduceIte]; exact h1
              · rw [hov]; dsimp only
                rw [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert]; simp
            · right; exact ⟨st1, hmemRest, hr1⟩
    exact hgo arm.steps .leaf (.inr ⟨st, hst, hr⟩)
  have hregs := u.regsLt
  have hbr : ∀ (curBlk : Label × Block), d.F.blocks[curBlk.1]? = some curBlk.2 → blockRegsLt d.off curBlk.2 = true := by
    intro ⟨_, B⟩ hB
    simp only [funcRegsLt, Bool.and_eq_true, List.all_eq_true] at hregs
    exact hregs.2 B (Array.mem_toList_iff.2 (Array.mem_of_getElem? hB))
  have hforArm : ∀ (arm : DiamondArm) (start : Label),
      b < start → verifyArmMatches d.F b start d.armT.join (d.armT.failRes?.orElse fun _ => d.armF.failRes?) arm = true →
      (∀ st ∈ arm.steps,
        (∀ s ∈ st.body, ∀ r ∈ s.defs, arm.defs.contains r = true ∧ r < d.off) ∧
        (∀ o x oa ob res, st.ovf? = some (o, x, oa, ob, res) → arm.defs.contains x = true ∧ x < d.off)) ∧
      (∀ st ∈ arm.steps,
        (∀ s ∈ st.body, ∀ x ∈ s.uses, arm.defs.contains x = false → x < d.off) ∧
        (∀ o x oa ob res, st.ovf? = some (o, x, oa, ob, res) →
          ∀ r ∈ oa.uses ++ ob.uses, arm.defs.contains r = false → r < d.off)) := by
    intro arm start hltS hv
    unfold verifyArmMatches at hv
    simp only [Bool.and_eq_true] at hv
    have hstep : ∀ st ∈ arm.steps,
        ∃ curBlk, d.F.blocks[st.label]? = some curBlk ∧ curBlk.body.toList = st.body ∧
          (∀ o x oa ob res, st.ovf? = some (o, x, oa, ob, res) →
            ∃ ok ovf, curBlk.term = .brOvf o x oa ob ok ovf) := by
      intro st hst
      obtain ⟨pre, rem, heq⟩ := List.append_of_mem hst
      rw [heq] at hv
      obtain ⟨_, curBlk, hB, _, hbody, hrem⟩ := verifyArmMatches_step_at hltS hv.2
      refine ⟨curBlk, hB, hbody, fun o x oa ob res hov => ?_⟩
      cases rem with
      | nil => rw [hrem.2.1] at hov; cases hov
      | cons nxt _ =>
          obtain ⟨_, o', x', oa', ob', res', ovfEdge, hov', _, ht', _⟩ := hrem
          rw [hov'] at hov; cases hov
          exact ⟨{ target := nxt.label, args := [] }, ovfEdge, ht'⟩
    constructor
    · intro st hst
      obtain ⟨curBlk, hB, hbody, hterm⟩ := hstep st hst
      have hblt := hbr ⟨st.label, curBlk⟩ hB
      simp only [blockRegsLt, Bool.and_eq_true, List.all_eq_true] at hblt
      refine ⟨fun s hs r hr => ⟨hmemDefs arm st r hst (.inl ⟨s, hs, hr⟩), ?_⟩,
              fun o x oa ob res hov => ⟨hmemDefs arm st x hst (.inr ⟨o, oa, ob, res, hov⟩), ?_⟩⟩
      · rw [← hbody] at hs
        exact listLt_mem (hblt.1.1.1.2 s hs).2 hr
      · obtain ⟨ok, ovf, ht⟩ := hterm o x oa ob res hov
        have hd := hblt.1.2
        rw [ht] at hd
        exact listLt_mem hd (by simp [Term.defs])
    · intro st hst
      obtain ⟨curBlk, hB, hbody, hterm⟩ := hstep st hst
      have hblt := hbr ⟨st.label, curBlk⟩ hB
      simp only [blockRegsLt, Bool.and_eq_true, List.all_eq_true] at hblt
      refine ⟨fun s hs x hx _ => ?_, fun o x oa ob res hov r hr _ => ?_⟩
      · rw [← hbody] at hs
        exact listLt_mem (hblt.1.1.1.2 s hs).1 hx
      · obtain ⟨ok, ovf, ht⟩ := hterm o x oa ob res hov
        have hu := hblt.1.1.2
        rw [ht] at hu
        exact listLt_mem hu (by simp [Term.uses, hr])
  cases isT
  · exact hforArm d.armF d.eF.target u.bLtF u.verF
  · exact hforArm d.armT d.eT.target u.bLtT u.verT

private theorem ifConv_enter_rel {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b) (u : IfConvUnpacked d)
    {g : FunId} {vs : List Word} {fr₁ : Frame} (hent : enter p g vs = some fr₁) :
    ∃ fr₂, enter q g vs = some fr₂ ∧ NormalIfConvFrame d true fr₁ fr₂ := by
  simp only [enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hent
  obtain ⟨F0, hF0, ρ, hbp, rfl⟩ := hent
  by_cases hg : g = fi
  · subst hg
    rw [d.hF] at hF0; cases hF0
    have h0NT : (Src.NatSet.ofList d.armT.labels).contains 0 = false := by
      rw [natSet_ofList_contains, decide_eq_false_iff_not]
      intro hmem; exact Nat.not_lt_zero b (verifyArmMatches_labels_gt u.bLtT u.verT 0 hmem)
    have h0NF : (Src.NatSet.ofList d.armF.labels).contains 0 = false := by
      rw [natSet_ofList_contains, decide_eq_false_iff_not]
      intro hmem; exact Nat.not_lt_zero b (verifyArmMatches_labels_gt u.bLtF u.verF 0 hmem)
    obtain ⟨_, _, _, hparDef⟩ := bindParams_agreeOuter (envAgreeOuter_refl d.off d.armT.defs d.armF.defs {}) hbp
    refine ⟨{ fn := g, label := 0, pos := 0, env := ρ, dsts := [] }, ?_, ?_⟩
    · simp [enter, d.hG, ifConv_G_params d, hbp]
    · refine ⟨rfl, rfl, ?_⟩
      simp only [↓reduceIte, ifConvRemap_zero, h0NT, h0NF, envAgreeOuter_refl, true_and]
      refine ⟨hparDef, fun hb0 => ⟨Nat.zero_le _, ?_, (fun i hi => absurd hi (Nat.not_lt_zero _)), (fun h => by cases h)⟩⟩
      intro x hx
      rw [u.b0Empty hb0.symm] at hx
      cases hx
  · have hqF : q.funcs[g]? = some F0 := by rw [d.hOtherF g hg, hF0]
    exact ⟨{ fn := g, label := 0, pos := 0, env := ρ, dsts := [] },
      by simp [enter, hqF, hbp], ⟨rfl, rfl, by simp [hg]⟩⟩

/-! ## Master forward simulation diagram for `ifConvDiamondSite` -/

/-- Total execution of `selStmts` (used when the taken arm overflows and `q` still executes `selStmts`
before `predStmt` branches to `failLbl`). -/
private theorem exec_selStmts_total {c : Cond} {w : Width} {a bArg : Arg} {va vb : Word}
    {mem : X86.Memory} {ctx : Word} {frStart : VReg}
    (haLt : ∀ u ∈ a.uses, u < frStart) (hbLt : ∀ u ∈ bArg.uses, u < frStart) :
    ∀ (pairs : List (Arg × Arg)) (ss : List Stmt) (outRev : List Arg) (fr : VReg)
      (ρ0 ρCur : Env),
      frStart ≤ fr →
      a.eval ρCur = some va → bArg.eval ρCur = some vb →
      execList ρ0 mem ctx ss = some (ρCur, mem) →
      (∀ s ∈ ss, s.isCall = false) →
      (∀ z, z < frStart → ρCur[z]? = ρ0[z]?) →
      (∀ p ∈ pairs,
        (∀ u ∈ p.1.uses, u < frStart) ∧
        (∀ u ∈ p.2.uses, u < frStart) ∧
        (p.1 ≠ p.2 → (∃ vt, p.1.eval ρ0 = some vt) ∧ (∃ vf, p.2.eval ρ0 = some vf))) →
      let (selStmts, _, frOut) :=
        pairs.foldl (init := (ss, outRev, fr)) fun (ss, out, fr) (at_, af_) =>
          if at_ == af_ then (ss, at_ :: out, fr)
          else (ss ++ [Stmt.assign fr (.select c w a bArg at_ af_)], Arg.v fr :: out, fr + 1)
      frStart ≤ frOut ∧
      (∀ s ∈ selStmts, s.isCall = false) ∧
      ∃ ρEnd,
        execList ρ0 mem ctx selStmts = some (ρEnd, mem) ∧
        (∀ z, z < frStart → ρEnd[z]? = ρ0[z]?) := by
  intro pairs
  induction pairs with
  | nil =>
      intro ss outRev fr ρ0 ρCur hle _ _ hex hnc hpres _
      exact ⟨hle, hnc, ρCur, hex, hpres⟩
  | cons p rest ih =>
      rcases p with ⟨at_, af_⟩
      intro ss outRev fr ρ0 ρCur hle haCur hbCur hex hnc hpres hps
      simp only [List.foldl_cons]
      obtain ⟨hatLt, hafLt, hdiff⟩ := hps (at_, af_) (by simp)
      by_cases hsame : (at_ == af_) = true
      · simp only [hsame, ↓reduceIte]
        exact ih ss (at_ :: outRev) fr ρ0 ρCur hle haCur hbCur hex hnc hpres
          (fun p' hp' => hps p' (by simp [hp']))
      · have hne : at_ ≠ af_ := by simpa using hsame
        simp only [hsame, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨⟨vt, hvt0⟩, ⟨vf, hvf0⟩⟩ := hdiff hne
        have hevAt : at_.eval ρCur = some vt := by
          cases at_ with | imm _ => exact hvt0 | v u => rw [Arg.eval, hpres u (hatLt u (by simp [Arg.uses, Arg.vreg?]))]; exact hvt0
        have hevAf : af_.eval ρCur = some vf := by
          cases af_ with | imm _ => exact hvf0 | v u => rw [Arg.eval, hpres u (hafLt u (by simp [Arg.uses, Arg.vreg?]))]; exact hvf0
        let vSel := if c.holds w va vb then vt else vf
        let selSt := Stmt.assign fr (.select c w a bArg at_ af_)
        let ρ1 := ρCur.insert fr vSel
        have hsel_exec : selSt.exec ρCur mem ctx = some (ρ1, mem) := by
          simp only [selSt, Stmt.exec, Rhs.eval, Option.bind_eq_bind, haCur, hbCur,
            hevAt, hevAf, Option.bind_some, vSel, ρ1]
        have hex1 : execList ρ0 mem ctx (ss ++ [selSt]) = some (ρ1, mem) :=
          execList_append_ifconv hex (by simp [execList, hsel_exec])
        have hpres1 : ∀ z, z < frStart → ρ1[z]? = ρ0[z]? := fun z hz => by
          rw [env_insert_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le hz hle))]; exact hpres z hz
        have ha1 : a.eval ρ1 = some va := by
          cases a with | imm _ => exact haCur | v u => rw [Arg.eval, env_insert_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le (haLt u (by simp [Arg.uses, Arg.vreg?])) hle))]; exact haCur
        have hb1 : bArg.eval ρ1 = some vb := by
          cases bArg with | imm _ => exact hbCur | v u => rw [Arg.eval, env_insert_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le (hbLt u (by simp [Arg.uses, Arg.vreg?])) hle))]; exact hbCur
        exact ih (ss ++ [selSt]) (.v fr :: outRev) (fr + 1) ρ0 ρ1 (Nat.le_succ_of_le hle) ha1 hb1 hex1
          (fun s hs => by simp only [List.mem_append, List.mem_singleton] at hs; rcases hs with h1 | rfl; exact hnc s h1; rfl)
          hpres1 (fun p' hp' => hps p' (by simp [hp']))

/-- Concrete execution of `runArmConcrete` only modifies registers in `armDefs`. -/
private theorem runArmConcrete_preserves_nonDefs {armDefs : Src.NatSet} {mem : X86.Memory} {ctx : Word} :
    ∀ {steps : List ArmStep} {ρ₀ ρ₁ : Env},
      (∀ st ∈ steps,
        (∀ s ∈ st.body, ∀ r ∈ s.defs, armDefs.contains r = true) ∧
        (∀ o x oa ob res, st.ovf? = some (o, x, oa, ob, res) → armDefs.contains x = true)) →
      runArmConcrete mem ctx steps ρ₀ = some (.inr ρ₁) →
      (∀ x, armDefs.contains x = false → ρ₁[x]? = ρ₀[x]?) ∧
      (∀ (u : VReg), ρ₀[u]?.isSome = true → ρ₁[u]?.isSome = true)
  | [], ρ₀, ρ₁, _, h => by
      simp only [runArmConcrete, Option.some.injEq, Sum.inr.injEq] at h; subst h
      exact ⟨fun _ _ => rfl, fun _ h => h⟩
  | st :: rest, ρ₀, ρ₁, hds, h => by
      have hst := hds st (by simp)
      simp only [runArmConcrete, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨ρm, mm⟩, hxb, hr⟩ := h
      have hbody : (∀ x, armDefs.contains x = false → ρm[x]? = ρ₀[x]?) ∧
          (∀ (u : VReg), ρ₀[u]?.isSome = true → ρm[u]?.isSome = true) := by
        have hgo : ∀ (ss : List Stmt) (ρa ρb : Env) (ma mb : X86.Memory),
            (∀ s ∈ ss, ∀ r ∈ s.defs, armDefs.contains r = true) →
            execList ρa ma ctx ss = some (ρb, mb) →
            (∀ x, armDefs.contains x = false → ρb[x]? = ρa[x]?) ∧
            (∀ (u : VReg), ρa[u]?.isSome = true → ρb[u]?.isSome = true) := by
          intro ss; induction ss with
          | nil => intro ρa ρb _ _ _ hx; simp [execList] at hx; obtain ⟨rfl, _⟩ := hx; exact ⟨fun _ _ => rfl, fun _ h => h⟩
          | cons s0 ss0 ihs =>
              intro ρa ρb ma mb hds0 hx
              simp only [execList] at hx
              split at hx
              · rename_i ρc mc hxs
                have hstep_pres : ∀ x, armDefs.contains x = false → ρc[x]? = ρa[x]? := by
                  intro x hnot
                  cases s0 with
                  | assign r rhs =>
                      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hxs
                      obtain ⟨_, _, rfl, _⟩ := hxs
                      have hne : r ≠ x := fun heq => by subst heq; have := hds0 (.assign r rhs) (by simp) r (by simp [Stmt.defs]); rw [hnot] at this; cases this
                      exact env_insert_ne _ _ hne
                  | limb r1 r2 rhs =>
                      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hxs
                      obtain ⟨_, _, rfl, _⟩ := hxs
                      have hne1 : r1 ≠ x := fun heq => by subst heq; have := hds0 (.limb r1 r2 rhs) (by simp) r1 (by simp [Stmt.defs]); rw [hnot] at this; cases this
                      have hne2 : r2 ≠ x := fun heq => by subst heq; have := hds0 (.limb r1 r2 rhs) (by simp) r2 (by simp [Stmt.defs]); rw [hnot] at this; cases this
                      rw [env_insert_ne _ _ hne2, env_insert_ne _ _ hne1]
                  | store _ _ _ =>
                      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hxs
                      obtain ⟨_, _, _, _, hw⟩ := hxs
                      cases h : ma.write? _ _ _ with
                      | error _ => rw [h] at hw; cases hw
                      | ok _ => rw [h] at hw; simp only [Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, _⟩ := hw; rfl
                  | call _ _ _ => simp [Stmt.exec] at hxs
                obtain ⟨h1, h2⟩ := ihs ρc ρb mc mb (fun s hs => hds0 s (by simp [hs])) hx
                exact ⟨fun x hn => by rw [h1 x hn, hstep_pres x hn],
                       fun u hu => h2 u (stmt_exec_preserves_isSome hxs u hu)⟩
              · cases hx
        exact hgo st.body ρ₀ ρm mem mm hst.1 hxb
      cases hov : st.ovf? with
      | none =>
          rw [hov] at hr
          obtain ⟨h1, h2⟩ := runArmConcrete_preserves_nonDefs (fun s' hs' => hds s' (by simp [hs'])) hr
          exact ⟨fun x hn => by rw [h1 x hn, hbody.1 x hn], fun u hu => h2 u (hbody.2 u hu)⟩
      | some tup =>
          rcases tup with ⟨o, x, oa, ob, res⟩
          rw [hov] at hr
          simp only [Option.bind_eq_some_iff] at hr
          obtain ⟨va, _, vb, _, hro⟩ := hr
          split at hro
          · cases hro
          · obtain ⟨h1, h2⟩ := runArmConcrete_preserves_nonDefs (fun s' hs' => hds s' (by simp [hs'])) hro
            have hxm := hst.2 o x oa ob res hov
            exact ⟨fun y hn => by
                have hne : x ≠ y := fun heq => by subst heq; rw [hn] at hxm; cases hxm
                rw [h1 y hn, env_insert_ne _ _ hne, hbody.1 y hn],
              fun u hu => h2 u (env_isSome_insert (hbody.2 u hu))⟩

/-- If `runArmConcrete` fails with `.inl failR`, then `arm.failRes? = some failR` and `commonRes? = some failR`. -/
private theorem runArmConcrete_inl_commonRes {F : Func} {b start join : Label}
    {commonRes? : Option Sem.Resource} {arm : DiamondArm} {mem : X86.Memory} {ctx : Word}
    {ρ₀ : Env} {failR : Sem.Resource}
    (hlt : b < start) (hv : verifyArmMatches F b start join commonRes? arm = true)
    (hrun : runArmConcrete mem ctx arm.steps ρ₀ = some (.inl failR)) :
    commonRes? = some failR := by
  unfold verifyArmMatches at hv
  simp only [Bool.and_eq_true] at hv
  have hgo : ∀ (steps : List ArmStep) (s0 : Label) (ρ : Env),
      b < s0 → verifyArmMatches.go F b join commonRes? arm s0 steps = true →
      runArmConcrete mem ctx steps ρ = some (.inl failR) → commonRes? = some failR := by
    intro steps
    induction steps with
    | nil => intro _ _ _ _ hr; simp [runArmConcrete] at hr
    | cons st rest ih =>
        intro s0 ρ hlt0 hv0 hr
        simp only [runArmConcrete, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
        obtain ⟨⟨ρ1, _⟩, _, hrest⟩ := hr
        cases rest with
        | nil =>
            obtain ⟨_, _, _, _, _, _, hovNone, _⟩ := verifyArmMatches_step_at (pre := []) (rem := []) hlt0 hv0
            rw [hovNone] at hrest; simp [runArmConcrete] at hrest
        | cons nxt tail =>
            obtain ⟨_, _, _, _, _, hcn, o, x, oa, ob, res, _, hovSome, hcr, _, _⟩ :=
              verifyArmMatches_step_at (pre := []) (rem := nxt :: tail) hlt0 hv0
            rw [hovSome] at hrest
            simp only [Option.bind_eq_some_iff] at hrest
            obtain ⟨va, _, vb, _, hov⟩ := hrest
            split at hov
            · simp only [Option.some.injEq, Sum.inl.injEq] at hov; subst hov; exact hcr
            · have hvNext : verifyArmMatches.go F b join commonRes? arm nxt.label (nxt :: tail) = true := by
                simp only [verifyArmMatches.go, Bool.and_eq_true, hovSome] at hv0
                have hsEq : st.label = s0 := by simpa using hv0.1.1
                subst hsEq
                cases hB : F.blocks[st.label]? with
                | none => rw [hB] at hv0; simp at hv0
                | some stBlk =>
                    rw [hB] at hv0; simp only [Bool.and_eq_true] at hv0
                    cases ht : stBlk.term with
                    | brOvf _ _ _ _ _ _ =>
                        rw [ht] at hv0; simp only [Bool.and_eq_true] at hv0
                        exact hv0.2.2.2
                    | jump _ | br _ _ _ _ _ _ | ret _ | tail _ _ | fail _ | trap =>
                        rw [ht] at hv0; simp at hv0
              have hsEq : st.label = s0 := by
                simp only [verifyArmMatches.go, Bool.and_eq_true] at hv0
                simpa using hv0.1.1
              subst hsEq
              exact ih nxt.label _ (Nat.lt_trans hlt0 hcn) hvNext hov
  exact hgo arm.steps start ρ₀ hlt hv.2 hrun

private theorem ifConv_speculative_sync {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b) (u : IfConvUnpacked d)
    {mem : X86.Memory} {ctx : Word} {fr₁ fr₂ : Frame} {rest₂ : List Frame}
    (hia : InArmFrame d mem ctx fr₁ fr₂)
    {res : Sem.Resource ⊕ Env}
    (hrun : runArmConcrete mem ctx (if hia.condVal then d.armT else d.armF).steps hia.ρ₁₀ = some res) :
    match res with
    | .inl _ =>
        Sem.Fails (semStep q) { mem, ctx, stack := fr₂ :: rest₂ }
    | .inr ρ₁End =>
        ∀ {vs : List Word} {jBlk : Block} {ρ₁Join : Env},
          evalArgs ρ₁End (if hia.condVal then d.armT else d.armF).joinArgs = some vs →
          d.F.blocks[d.armT.join]? = some jBlk →
          bindParams ρ₁End jBlk.params vs = some ρ₁Join →
          let hasG := (d.armT.failRes?.orElse fun _ => d.armF.failRes?).isSome
          let jLbl := ifConvRemap b hasG d.armT.join
          ∃ c₂ ρ₂Join,
            c₂ = (decide (d.armT.join ≤ b)).toNat ∧
            Sem.Star (semStep q)
              { mem, ctx, stack := fr₂ :: rest₂ }
              c₂
              { mem, ctx, stack := { fr₂ with label := jLbl, pos := 0, env := ρ₂Join } :: rest₂ } ∧
            EnvAgreeOuter d.off d.armT.defs d.armF.defs ρ₁Join ρ₂Join := by
  have hguarDef : ∀ x ∈ d.F.params ++ d.blk.params ++
      d.blk.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ d.a.uses ++ d.bArg.uses,
      hia.ρ₁₀[x]?.isSome = true := by
    intro x hx
    simp only [List.mem_append, List.mem_flatMap] at hx
    rcases hx with (((hfp | hbp) | ⟨st, hst, hxst⟩) | ha) | hb
    · exact hia.hFParams x hfp
    · exact hia.hBParams x hbp
    · obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hst
      have hlt : i < d.blk.body.size := by simpa using hi
      have hsome : d.blk.body[i]? = some st := by
        rw [Array.getElem?_eq_getElem hlt, ← Array.getElem_toList (h := hi), hget]
      exact hia.hBBody i hlt st hsome x (List.mem_append.2 hxst)
    · exact arg_eval_isSome hia.ha x ha
    · exact arg_eval_isSome hia.hb x hb
  have hguarDef2 : ∀ x ∈ d.F.params ++ d.blk.params ++
      d.blk.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ d.a.uses ++ d.bArg.uses,
      fr₂.env[x]?.isSome = true := by
    intro x hx
    have h1 := hguarDef x hx
    cases hget : hia.ρ₁₀[x]? with
    | none => rw [hget] at h1; cases h1
    | some v => rw [hia.hAgree0 x v (u.guarDisjoint x hx) hget]; rfl
  have hblkOuter : ∀ x ∈ d.blk.body.toList.flatMap (·.uses) ++ d.blk.term.uses ++ d.blk.term.edgeUses,
      OuterRegOk d.off d.armT.defs d.armF.defs x := u.outsideUses b d.blk d.hb u.bNotT u.bNotF
  have haOuter : ∀ x ∈ d.a.uses, OuterRegOk d.off d.armT.defs d.armF.defs x := fun x hx =>
    hblkOuter x (by rw [d.hTerm]; simp [Term.uses, hx])
  have hbOuter : ∀ x ∈ d.bArg.uses, OuterRegOk d.off d.armT.defs d.armF.defs x := fun x hx =>
    hblkOuter x (by rw [d.hTerm]; simp [Term.uses, hx])
  have ha2 : d.a.eval fr₂.env = some hia.va := ifConv_outer_eval_arg hia.hAgree0 haOuter hia.ha
  have hb2 : d.bArg.eval fr₂.env = some hia.vb := ifConv_outer_eval_arg hia.hAgree0 hbOuter hia.hb
  -- Register bounds for `armT` and `armF`
  obtain ⟨hregsT, houterT_lt⟩ := arm_step_regs_and_outer d u true
  obtain ⟨hregsF, houterF_lt⟩ := arm_step_regs_and_outer d u false
  -- Outer uses of armT / armF satisfy `OuterRegOk` and are defined in `fr₂.env`
  have houterT_ok : ∀ st ∈ d.armT.steps,
      (∀ s ∈ st.body, ∀ x ∈ s.uses, d.armT.defs.contains x = false → x < d.off ∧ d.armF.defs.contains x = false) ∧
      (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
        ∀ w0 ∈ oa.uses ++ ob.uses, d.armT.defs.contains w0 = false → w0 < d.off ∧ d.armF.defs.contains w0 = false) := by
    intro st hst
    refine ⟨fun s hs x hx hn => ?_, fun o x oa ob r hov w0 hw hn => ?_⟩
    · have hgd := u.guarDisjoint x ((u.outerT st hst).1 s hs x hx hn); exact ⟨hgd.1, hgd.2.2⟩
    · have hgd := u.guarDisjoint w0 ((u.outerT st hst).2 o x oa ob r hov w0 hw hn); exact ⟨hgd.1, hgd.2.2⟩
  have houterF_ok : ∀ st ∈ d.armF.steps,
      (∀ s ∈ st.body, ∀ x ∈ s.uses, d.armF.defs.contains x = false → x < d.off ∧ d.armT.defs.contains x = false) ∧
      (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
        ∀ w0 ∈ oa.uses ++ ob.uses, d.armF.defs.contains w0 = false → w0 < d.off ∧ d.armT.defs.contains w0 = false) := by
    intro st hst
    refine ⟨fun s hs x hx hn => ?_, fun o x oa ob r hov w0 hw hn => ?_⟩
    · have hgd := u.guarDisjoint x ((u.outerF st hst).1 s hs x hx hn); exact ⟨hgd.1, hgd.2.1⟩
    · have hgd := u.guarDisjoint w0 ((u.outerF st hst).2 o x oa ob r hov w0 hw hn); exact ⟨hgd.1, hgd.2.1⟩
  have hdefT2 : ∀ st ∈ d.armT.steps,
      (∀ s ∈ st.body, ∀ x ∈ s.uses, d.armT.defs.contains x = false → fr₂.env[x]?.isSome = true) ∧
      (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
        ∀ w0 ∈ oa.uses ++ ob.uses, d.armT.defs.contains w0 = false → fr₂.env[w0]?.isSome = true) :=
    fun st hst => ⟨fun s hs x hx hn => hguarDef2 x ((u.outerT st hst).1 s hs x hx hn),
      fun o x oa ob r hov w0 hw hn => hguarDef2 w0 ((u.outerT st hst).2 o x oa ob r hov w0 hw hn)⟩
  -- Run total speculative execution of `armT` (k = 1, flagBase = 3 * off)
  have htotT := emitSpeculativeArm_total (arm := d.armT) (armDefs := d.armT.defs)
    (off := d.off) (k := 1) (flagBase := 3 * d.off) (by omega) (by omega)
    u.pureT hregsT houterT_lt hdefT2 (mem := mem) (ctx := ctx)
  rcases hresT : emitSpeculativeArm d.armT.defs d.off 1 d.armT (3 * d.off) with ⟨stmtsT, flagT, fr1⟩
  rw [hresT] at htotT
  obtain ⟨hfr1_ge, hncT, hflagT_uses, ρ₂T, avEndT, hexT, havEndT_def, hjoinAvT, ⟨fvT, hfvT⟩, hpresT⟩ := htotT
  -- Outer uses of `armF` are still defined in `ρ₂T` (since `< d.off`)
  have hdefF2 : ∀ st ∈ d.armF.steps,
      (∀ s ∈ st.body, ∀ x ∈ s.uses, d.armF.defs.contains x = false → ρ₂T[x]?.isSome = true) ∧
      (∀ o x oa ob r, st.ovf? = some (o, x, oa, ob, r) →
        ∀ w0 ∈ oa.uses ++ ob.uses, d.armF.defs.contains w0 = false → ρ₂T[w0]?.isSome = true) := by
    intro st hst
    refine ⟨fun s hs x hx hn => ?_, fun o x oa ob r hov w0 hw hn => ?_⟩
    · have hmem := (u.outerF st hst).1 s hs x hx hn
      rw [hpresT x (.inl (by rw [Nat.one_mul]; exact (u.guarDisjoint x hmem).1))]
      exact hguarDef2 x hmem
    · have hmem := (u.outerF st hst).2 o x oa ob r hov w0 hw hn
      rw [hpresT w0 (.inl (by rw [Nat.one_mul]; exact (u.guarDisjoint w0 hmem).1))]
      exact hguarDef2 w0 hmem
  -- Run total speculative execution of `armF` (k = 2, flagBase = fr1) from `ρ₂T`
  have htotF := emitSpeculativeArm_total (arm := d.armF) (armDefs := d.armF.defs)
    (off := d.off) (k := 2) (flagBase := fr1) (by omega) hfr1_ge
    u.pureF hregsF houterF_lt hdefF2 (mem := mem) (ctx := ctx)
  rcases hresF : emitSpeculativeArm d.armF.defs d.off 2 d.armF fr1 with ⟨stmtsF, flagF, fr2⟩
  rw [hresF] at htotF
  obtain ⟨hfr2_ge, hncF, hflagF_uses, ρ₂F, avEndF, hexF, havEndF_def, hjoinAvF, ⟨fvF, hfvF⟩, hpresF⟩ := htotF
  -- Combined preservation `ρ₂F` vs `fr₂.env` on `< d.off`, `[d.off, 2*off)` (vs `ρ₂T`), and `[3*off, fr1)` (vs `ρ₂T`)
  have hpresF_lt : ∀ z, z < d.off → ρ₂F[z]? = fr₂.env[z]? := fun z hz => by
    rw [hpresF z (.inl (Nat.lt_of_lt_of_le hz (Nat.le_mul_of_pos_left d.off (by decide)))),
        hpresT z (.inl (by rw [Nat.one_mul]; exact hz))]
  have hflagT_inF : flagT.eval ρ₂F = some fvT := by
    cases flagT with
    | imm _ => exact hfvT
    | v r =>
        obtain ⟨hr1, hr2⟩ := hflagT_uses r (by simp [Arg.uses, Arg.vreg?])
        rw [Arg.eval, hpresF r (.inr (.inl ⟨hr1, hr2⟩))]; exact hfvT
  have haF : d.a.eval ρ₂F = some hia.va := by
    cases hda : d.a with
    | imm _ => rw [hda] at ha2; exact ha2
    | v x =>
        rw [hda] at ha2
        rw [Arg.eval, hpresF_lt x (haOuter x (by rw [hda]; simp [Arg.uses, Arg.vreg?])).1]
        exact ha2
  have hbF : d.bArg.eval ρ₂F = some hia.vb := by
    cases hdb : d.bArg with
    | imm _ => rw [hdb] at hb2; exact hb2
    | v x =>
        rw [hdb] at hb2
        rw [Arg.eval, hpresF_lt x (hbOuter x (by rw [hdb]; simp [Arg.uses, Arg.vreg?])).1]
        exact hb2
  -- Helper: `joinArgs` outer uses `< d.off` (from `funcRegsLt`)
  have hjoinOuterLt : ∀ (arm : DiamondArm) (start : Label),
      b < start → verifyArmMatches d.F b start d.armT.join (d.armT.failRes?.orElse fun _ => d.armF.failRes?) arm = true →
      ∀ a ∈ arm.joinArgs, ∀ x ∈ a.uses, x < d.off := by
    intro arm start hltS hv a ha x hx
    obtain ⟨first, tail, hsteps, _⟩ := verifyArmMatches_nonempty hv
    have hnonnil : arm.steps ≠ [] := by rw [hsteps]; intro h; cases h
    have hsplitLast : ∀ (l : List ArmStep), l ≠ [] → ∃ pre last, l = pre ++ [last] := by
      intro l; induction l with
      | nil => intro h; exact absurd rfl h
      | cons a0 t0 iht =>
          intro _
          cases t0 with
          | nil => exact ⟨[], a0, rfl⟩
          | cons b0 t1 =>
              obtain ⟨p0, l0, hpl⟩ := iht (by simp)
              exact ⟨a0 :: p0, l0, by rw [hpl]; rfl⟩
    obtain ⟨pre, last, heq⟩ := hsplitLast arm.steps hnonnil
    unfold verifyArmMatches at hv
    simp only [Bool.and_eq_true] at hv
    rw [heq] at hv
    obtain ⟨_, lastBlk, hB, _, _, _, _, hterm⟩ := verifyArmMatches_step_at (rem := []) hltS hv.2
    have hbr : blockRegsLt d.off lastBlk = true := by
      have hr := u.regsLt; simp only [funcRegsLt, Bool.and_eq_true, List.all_eq_true] at hr
      exact hr.2 lastBlk (Array.mem_toList_iff.2 (Array.mem_of_getElem? hB))
    simp only [blockRegsLt, Bool.and_eq_true] at hbr
    have heu := hbr.2; rw [hterm] at heu
    exact listLt_mem heu (by simp only [Term.edgeUses, Term.edges, List.flatMap_cons, List.flatMap_nil, List.append_nil, argsUses, List.mem_flatMap]; exact ⟨a, ha, hx⟩)
  have hjoinTLt : ∀ a ∈ d.armT.joinArgs, ∀ x ∈ a.uses, x < d.off := hjoinOuterLt d.armT d.eT.target u.bLtT u.verT
  have hjoinFLt : ∀ a ∈ d.armF.joinArgs, ∀ x ∈ a.uses, x < d.off := hjoinOuterLt d.armF d.eF.target u.bLtF u.verF
  have h3off_le_fr2 : 3 * d.off ≤ fr2 := Nat.le_trans hfr1_ge hfr2_ge
  -- Every pair `(at', af')` in `(argsT.zip argsF)` satisfies `< fr2` and differing pairs are defined in `ρ₂F`
  let argsT := d.armT.joinArgs.map (loopMapArg d.armT.defs d.off 1)
  let argsF := d.armF.joinArgs.map (loopMapArg d.armF.defs d.off 2)
  have hpairs_ok : ∀ p0 ∈ argsT.zip argsF,
      (∀ w0 ∈ p0.1.uses, w0 < fr2) ∧ (∀ w0 ∈ p0.2.uses, w0 < fr2) ∧
      (p0.1 ≠ p0.2 → (∃ vt, p0.1.eval ρ₂F = some vt) ∧ (∃ vf, p0.2.eval ρ₂F = some vf)) := by
    intro p0 hp0
    have hzip : argsT.zip argsF = (d.armT.joinArgs.zip d.armF.joinArgs).map
        (fun q => (loopMapArg d.armT.defs d.off 1 q.1, loopMapArg d.armF.defs d.off 2 q.2)) := by
      simp [argsT, argsF, List.zip_map]
    rw [hzip, List.mem_map] at hp0
    obtain ⟨⟨aT, aF⟩, hmemZ, rfl⟩ := hp0
    have hmemT : aT ∈ d.armT.joinArgs := (List.of_mem_zip hmemZ).1
    have hmemF : aF ∈ d.armF.joinArgs := (List.of_mem_zip hmemZ).2
    refine ⟨?_, ?_, ?_⟩
    · intro w0 hw0
      cases aT with
      | imm _ => simp [loopMapArg, Arg.uses, Arg.vreg?] at hw0
      | v x =>
          simp only [loopMapArg, Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hw0; subst hw0
          have hxlt := hjoinTLt (.v x) hmemT x (by simp [Arg.uses, Arg.vreg?])
          by_cases hmemD : d.armT.defs.contains x = true
          · exact Nat.lt_of_lt_of_le (loopMapReg_lt_of_mem (by decide) hmemD hxlt)
              (Nat.le_trans (Nat.mul_le_mul_right d.off (by decide)) h3off_le_fr2)
          · rw [loopMapReg_not_mem (Bool.eq_false_iff.2 hmemD)]
            exact Nat.lt_of_lt_of_le hxlt (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) h3off_le_fr2)
    · intro w0 hw0
      cases aF with
      | imm _ => simp [loopMapArg, Arg.uses, Arg.vreg?] at hw0
      | v x =>
          simp only [loopMapArg, Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hw0; subst hw0
          have hxlt := hjoinFLt (.v x) hmemF x (by simp [Arg.uses, Arg.vreg?])
          by_cases hmemD : d.armF.defs.contains x = true
          · exact Nat.lt_of_lt_of_le (loopMapReg_lt_of_mem (by decide) hmemD hxlt) h3off_le_fr2
          · rw [loopMapReg_not_mem (Bool.eq_false_iff.2 hmemD)]
            exact Nat.lt_of_lt_of_le hxlt (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) h3off_le_fr2)
    · intro hne
      obtain ⟨hdT, hdF⟩ := u.diffJoin (aT, aF) hmemZ hne
      constructor
      · cases aT with
        | imm w => exact ⟨w, rfl⟩
        | v x =>
            have hxlt := hjoinTLt (.v x) hmemT x (by simp [Arg.uses, Arg.vreg?])
            rcases hdT x (by simp [Arg.uses, Arg.vreg?]) with hmemD | hmemG
            · have hav := hjoinAvT (.v x) hmemT x (by simp [Arg.uses, Arg.vreg?]) hmemD
              have hdef := havEndT_def x hav
              have hlt2 : loopMapReg d.armT.defs d.off 1 x < 2 * d.off :=
                loopMapReg_lt_of_mem (by decide) hmemD hxlt
              rw [loopMapArg, Arg.eval, hpresF _ (.inl hlt2)]
              cases hg : ρ₂T[loopMapReg d.armT.defs d.off 1 x]? with
              | none => rw [hg] at hdef; cases hdef
              | some v => exact ⟨v, rfl⟩
            · have hgd := u.guarDisjoint x hmemG
              rw [loopMapArg, loopMapReg_not_mem hgd.2.1, Arg.eval, hpresF_lt x hgd.1]
              have hdef := hguarDef2 x hmemG
              cases hg : fr₂.env[x]? with
              | none => rw [hg] at hdef; cases hdef
              | some v => exact ⟨v, rfl⟩
      · cases aF with
        | imm w => exact ⟨w, rfl⟩
        | v x =>
            rcases hdF x (by simp [Arg.uses, Arg.vreg?]) with hmemD | hmemG
            · have hav := hjoinAvF (.v x) hmemF x (by simp [Arg.uses, Arg.vreg?]) hmemD
              have hdef := havEndF_def x hav
              rw [loopMapArg, Arg.eval]
              cases hg : ρ₂F[loopMapReg d.armF.defs d.off 2 x]? with
              | none => rw [hg] at hdef; cases hdef
              | some v => exact ⟨v, rfl⟩
            · have hgd := u.guarDisjoint x hmemG
              rw [loopMapArg, loopMapReg_not_mem hgd.2.2, Arg.eval, hpresF_lt x hgd.1]
              have hdef := hguarDef2 x hmemG
              cases hg : fr₂.env[x]? with
              | none => rw [hg] at hdef; cases hdef
              | some v => exact ⟨v, rfl⟩
  -- JoinArgs outer uses satisfy `otherDefs.contains x = false` too!
  have hjoinT_ok : ∀ a ∈ d.armT.joinArgs, ∀ x ∈ a.uses, d.armT.defs.contains x = false →
      x < d.off ∧ d.armF.defs.contains x = false := by
    intro a ha x hx hn
    have hxlt := hjoinTLt a ha x hx
    obtain ⟨i, hi, hgetT⟩ := List.getElem_of_mem ha
    have hiF : i < d.armF.joinArgs.length := u.argsLenEq ▸ hi
    have hmemZ : (d.armT.joinArgs[i], d.armF.joinArgs[i]) ∈ d.armT.joinArgs.zip d.armF.joinArgs := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_zip, u.argsLenEq, Nat.min_self]; exact hiF, by simp⟩
    rw [hgetT] at hmemZ
    by_cases heq : loopMapArg d.armT.defs d.off 1 a = loopMapArg d.armF.defs d.off 2 d.armF.joinArgs[i]
    · cases a with
      | imm _ => simp [Arg.uses, Arg.vreg?] at hx
      | v x0 =>
          simp only [Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hx; subst hx
          rw [loopMapArg, loopMapReg_not_mem hn] at heq
          cases hfa : d.armF.joinArgs[i] with
          | imm _ => rw [hfa] at heq; cases heq
          | v y0 =>
              rw [hfa, loopMapArg] at heq; cases heq
              by_cases hfy : d.armF.defs.contains y0 = true
              · exfalso
                have hge := loopMapReg_ge_of_mem (off := d.off) (c := 2) (by decide) hfy
                exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) hge) hxlt)
              · have hfn : d.armF.defs.contains y0 = false := Bool.eq_false_iff.2 hfy
                rw [loopMapReg_not_mem hfn] at hxlt ⊢; exact ⟨hxlt, hfn⟩
    · obtain ⟨hdT, _⟩ := u.diffJoin (a, d.armF.joinArgs[i]) hmemZ heq
      rcases hdT x hx with ht | hmemG
      · rw [hn] at ht; cases ht
      · exact ⟨hxlt, (u.guarDisjoint x hmemG).2.2⟩
  have hjoinF_ok : ∀ a ∈ d.armF.joinArgs, ∀ x ∈ a.uses, d.armF.defs.contains x = false →
      x < d.off ∧ d.armT.defs.contains x = false := by
    intro a ha x hx hn
    have hxlt := hjoinFLt a ha x hx
    obtain ⟨i, hi, hgetF⟩ := List.getElem_of_mem ha
    have hiT : i < d.armT.joinArgs.length := u.argsLenEq.symm ▸ hi
    have hmemZ : (d.armT.joinArgs[i], d.armF.joinArgs[i]) ∈ d.armT.joinArgs.zip d.armF.joinArgs := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_zip, u.argsLenEq, Nat.min_self]; exact hi, by simp⟩
    rw [hgetF] at hmemZ
    by_cases heq : loopMapArg d.armT.defs d.off 1 d.armT.joinArgs[i] = loopMapArg d.armF.defs d.off 2 a
    · cases a with
      | imm _ => simp [Arg.uses, Arg.vreg?] at hx
      | v x0 =>
          simp only [Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hx; subst hx
          rw [loopMapArg, loopMapReg_not_mem hn] at heq
          cases hta : d.armT.joinArgs[i] with
          | imm _ => rw [hta] at heq; cases heq
          | v y0 =>
              rw [hta, loopMapArg] at heq; cases heq
              by_cases hty : d.armT.defs.contains y0 = true
              · exfalso
                have hge := loopMapReg_ge_of_mem (off := d.off) (c := 1) (by decide) hty
                exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) hge) hxlt)
              · have htn : d.armT.defs.contains y0 = false := Bool.eq_false_iff.2 hty
                rw [loopMapReg_not_mem htn] at hxlt ⊢; exact ⟨hxlt, htn⟩
    · obtain ⟨_, hdF⟩ := u.diffJoin (d.armT.joinArgs[i], a) hmemZ heq
      rcases hdF x hx with hf | hmemG
      · rw [hn] at hf; cases hf
      · exact ⟨hxlt, (u.guarDisjoint x hmemG).2.1⟩
  -- Determinism of `execList`
  have hexecDet : ∀ (ρ : Env) (ss : List Stmt) (ρa ρb : Env) (ma mb : X86.Memory),
      execList ρ mem ctx ss = some (ρa, ma) → execList ρ mem ctx ss = some (ρb, mb) → ρa = ρb := by
    intro ρ ss ρa ρb ma mb h1 h2; rw [h1] at h2; cases h2; rfl
  -- Match concrete execution of the taken arm against `ρ₂F`
  have hmatchTaken :
      match res with
      | .inl _ => (if hia.condVal then fvT else fvF) ≠ 0
      | .inr ρ₁End =>
          (if hia.condVal then fvT else fvF) = 0 ∧
          ∀ a ∈ (if hia.condVal then d.armT else d.armF).joinArgs, ∀ v, a.eval ρ₁End = some v →
            (loopMapArg (if hia.condVal then d.armT else d.armF).defs d.off (if hia.condVal then 1 else 2) a).eval ρ₂F = some v := by
    by_cases hcv : hia.condVal = true
    · simp only [hcv, ↓reduceIte] at hrun ⊢
      have hmT := emitSpeculativeArm_matches_concrete (arm := d.armT) (armDefs := d.armT.defs)
        (otherDefs := d.armF.defs) (off := d.off) (k := 1) (flagBase := 3 * d.off)
        (by decide) (Nat.mul_le_mul_right d.off (by decide)) u.pureT hregsT houterT_ok
        (fun x v hlt hnt hnf hv => hia.hAgree0 x v ⟨hlt, hnt, hnf⟩ hv) hdefT2 hjoinT_ok hrun
      rw [hresT] at hmT
      obtain ⟨ρ₂T', hexT', hmT'⟩ := hmT
      have heqT := hexecDet fr₂.env stmtsT ρ₂T ρ₂T' mem mem hexT hexT'
      subst heqT
      cases res with
      | inl failR =>
          obtain ⟨fv', hfv', hne'⟩ := hmT'
          rw [hfvT] at hfv'; cases hfv'; exact hne'
      | inr ρ₁End =>
          obtain ⟨hfv0, hja⟩ := hmT'
          rw [hfvT] at hfv0; cases hfv0
          refine ⟨rfl, fun a ha v hv => ?_⟩
          have h1 := hja a ha v hv
          cases a with
          | imm _ => exact h1
          | v x =>
              have hxlt := hjoinTLt (.v x) ha x (by simp [Arg.uses, Arg.vreg?])
              have hmlt : loopMapReg d.armT.defs d.off 1 x < 2 * d.off := by
                by_cases hmd : d.armT.defs.contains x = true
                · exact loopMapReg_lt_of_mem (by decide) hmd hxlt
                · rw [loopMapReg_not_mem (Bool.eq_false_iff.2 hmd)]
                  exact Nat.lt_of_lt_of_le hxlt (Nat.le_mul_of_pos_left d.off (by decide))
              rw [loopMapArg, Arg.eval, hpresF _ (.inl hmlt)]; exact h1
    · have hcv' : hia.condVal = false := Bool.eq_false_iff.2 hcv
      simp only [hcv', Bool.false_eq_true, ↓reduceIte] at hrun ⊢
      have hmF := emitSpeculativeArm_matches_concrete (arm := d.armF) (armDefs := d.armF.defs)
        (otherDefs := d.armT.defs) (off := d.off) (k := 2) (flagBase := fr1)
        (by decide) hfr1_ge u.pureF hregsF houterF_ok
        (fun x v hlt hnf hnt hv => by
          rw [hpresT x (.inl (by rw [Nat.one_mul]; exact hlt))]
          exact hia.hAgree0 x v ⟨hlt, hnt, hnf⟩ hv)
        hdefF2 hjoinF_ok hrun
      rw [hresF] at hmF
      obtain ⟨ρ₂F', hexF', hmF'⟩ := hmF
      have heqF := hexecDet ρ₂T stmtsF ρ₂F ρ₂F' mem mem hexF hexF'
      subst heqF
      cases res with
      | inl failR =>
          obtain ⟨fv', hfv', hne'⟩ := hmF'
          rw [hfvF] at hfv'; cases hfv'; exact hne'
      | inr ρ₁End =>
          obtain ⟨hfv0, hja⟩ := hmF'
          rw [hfvF] at hfv0; cases hfv0
          exact ⟨rfl, hja⟩
  -- Now split on `res = .inl failR` vs `res = .inr ρ₁End`!
  cases res with
  | inl failR =>
      dsimp only
      have hcr : (d.armT.failRes?.orElse fun _ => d.armF.failRes?) = some failR := by
        cases hcv : hia.condVal
        · rw [hcv] at hrun; exact runArmConcrete_inl_commonRes u.bLtF u.verF hrun
        · rw [hcv] at hrun; exact runArmConcrete_inl_commonRes u.bLtT u.verT hrun
      have hblks2 := ifConv_G_blocks_shape2 d hcr
      rw [hresT] at hblks2; dsimp only at hblks2
      rw [hresF] at hblks2; dsimp only at hblks2
      rcases hselRes : ((argsT.zip argsF).foldl (init := ([], [], fr2)) fun (ss, out, fr) (at_, af_) =>
        if at_ == af_ then (ss, at_ :: out, fr)
        else (ss ++ [Stmt.assign fr (.select d.c d.w d.a d.bArg at_ af_)], Arg.v fr :: out, fr + 1)) with ⟨selStmts, selArgsRev, fr3⟩
      rw [hselRes] at hblks2; dsimp only at hblks2
      obtain ⟨hGb, _, hGfail⟩ := hblks2
      have hselTot := exec_selStmts_total (c := d.c) (w := d.w) (a := d.a) (bArg := d.bArg)
        (va := hia.va) (vb := hia.vb) (mem := mem) (ctx := ctx) (frStart := fr2)
        (fun x hx => Nat.lt_of_lt_of_le (haOuter x hx).1 (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) h3off_le_fr2))
        (fun x hx => Nat.lt_of_lt_of_le (hbOuter x hx).1 (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) h3off_le_fr2))
        (argsT.zip argsF) [] [] fr2 ρ₂F ρ₂F (Nat.le_refl _) haF hbF rfl
        (fun _ h => by cases h) (fun _ _ => rfl) hpairs_ok
      rw [hselRes] at hselTot
      obtain ⟨hfr3_ge, hncSel, ρ₂Sel, hexSel, hpresSel⟩ := hselTot
      -- Evaluate `predStmt = .assign fr3 (.select d.c d.w d.a d.bArg flagT flagF)`
      have haSel : d.a.eval ρ₂Sel = some hia.va := by
        cases hda : d.a with
        | imm _ => rw [hda] at haF; exact haF
        | v x =>
            rw [hda] at haF
            rw [Arg.eval, hpresSel x (Nat.lt_of_lt_of_le (haOuter x (by rw [hda]; simp [Arg.uses, Arg.vreg?])).1 (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) h3off_le_fr2))]
            exact haF
      have hbSel : d.bArg.eval ρ₂Sel = some hia.vb := by
        cases hdb : d.bArg with
        | imm _ => rw [hdb] at hbF; exact hbF
        | v x =>
            rw [hdb] at hbF
            rw [Arg.eval, hpresSel x (Nat.lt_of_lt_of_le (hbOuter x (by rw [hdb]; simp [Arg.uses, Arg.vreg?])).1 (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) h3off_le_fr2))]
            exact hbF
      have hflagT_Sel : flagT.eval ρ₂Sel = some fvT := by
        cases hft : flagT with
        | imm _ => rw [hft] at hflagT_inF; exact hflagT_inF
        | v r =>
            rw [hft] at hflagT_inF
            obtain ⟨_, hr2⟩ := hflagT_uses r (by rw [hft]; simp [Arg.uses, Arg.vreg?])
            rw [Arg.eval, hpresSel r (Nat.lt_of_lt_of_le hr2 hfr2_ge)]; exact hflagT_inF
      have hflagF_Sel : flagF.eval ρ₂Sel = some fvF := by
        cases hff : flagF with
        | imm _ => rw [hff] at hfvF; exact hfvF
        | v r =>
            rw [hff] at hfvF
            obtain ⟨_, hr2⟩ := hflagF_uses r (by rw [hff]; simp [Arg.uses, Arg.vreg?])
            rw [Arg.eval, hpresSel r hr2]; exact hfvF
      let predVal := if hia.condVal then fvT else fvF
      let predStmt := Stmt.assign fr3 (.select d.c d.w d.a d.bArg flagT flagF)
      let ρ₂Pred := ρ₂Sel.insert fr3 predVal
      have hpredExec : predStmt.exec ρ₂Sel mem ctx = some (ρ₂Pred, mem) := by
        simp only [predStmt, Stmt.exec, Rhs.eval, Option.bind_eq_bind, haSel, hbSel,
          hflagT_Sel, hflagF_Sel, Option.bind_some, hia.hcond, predVal, ρ₂Pred]
      have hexAll : execList fr₂.env mem ctx (stmtsT ++ stmtsF ++ selStmts ++ [predStmt]) = some (ρ₂Pred, mem) :=
        execList_append_ifconv (execList_append_ifconv (execList_append_ifconv hexT hexF) hexSel) (by simp [execList, hpredExec])
      have hncAll : ∀ s ∈ stmtsT ++ stmtsF ++ selStmts ++ [predStmt], s.isCall = false := by
        intro s hs; simp only [List.mem_append, List.mem_singleton] at hs
        rcases hs with ((h1 | h2) | h3) | rfl
        · exact hncT s h1
        · exact hncF s h2
        · exact hncSel s h3
        · rfl
      have hfr2_eq : fr₂ = { fn := fi, label := b, pos := d.blk.body.toList.length, env := fr₂.env, dsts := fr₂.dsts } := by
        cases fr₂; simp only [Frame.mk.injEq, Array.length_toList]
        exact ⟨hia.fn2, hia.lbl2, hia.pos2, trivial, trivial⟩
      have hstarBody := execList_star_steps (dsts := fr₂.dsts) (rest := rest₂) d.hG hGb
        d.blk.body.toList (stmtsT ++ stmtsF ++ selStmts ++ [predStmt]) [] fr₂.env ρ₂Pred mem mem
        (by simp [predStmt, List.append_assoc]) hncAll hexAll
      have hlenEnd : d.blk.body.toList.length + (stmtsT ++ stmtsF ++ selStmts ++ [predStmt]).length =
          (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts ++ [predStmt]).toArray.size := by
        simp [List.length_append]
      have hne0 : Cond.ne.holds .w64 predVal 0 = true := by
        dsimp only at hmatchTaken
        simp only [Cond.holds, trunc64, bne_iff_ne]; exact hmatchTaken
      have hbrStep : step q { mem, ctx, stack := { fn := fi, label := b, pos := (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts ++ [predStmt]).toArray.size, env := ρ₂Pred, dsts := fr₂.dsts } :: rest₂ } =
          .next { mem, ctx, stack := { fn := fi, label := d.F.blocks.size + 1, pos := 0, env := ρ₂Pred, dsts := fr₂.dsts } :: rest₂ } false := by
        have hstep := step_br (p := q) (F := d.G) (B := { d.blk with
            body := (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts ++ [predStmt]).toArray
            term := .br .ne .w64 (.v fr3) (.imm 0) { target := d.F.blocks.size + 1, args := [] } { target := b + 1, args := [] } })
          (fr := { fn := fi, label := b, pos := (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts ++ [predStmt]).toArray.size, env := ρ₂Pred, dsts := fr₂.dsts })
          (rest := rest₂) (mem := mem) (ctx := ctx) (va := predVal) (vb := 0)
          d.hG hGb rfl rfl (by simp [Arg.eval, ρ₂Pred]) rfl
        rw [hne0] at hstep; dsimp only at hstep
        rw [takeEdge_ok rfl hGfail rfl] at hstep
        have hlt : ¬ (d.F.blocks.size + 1 ≤ b) := Nat.not_le.2 (Nat.lt_succ_of_lt u.bLt)
        simpa [hlt] using hstep
      have hfailStep : semStep q { mem, ctx, stack := { fn := fi, label := d.F.blocks.size + 1, pos := 0, env := ρ₂Pred, dsts := fr₂.dsts } :: rest₂ } =
          .fail failR := by
        exact semStep_fail.2 (step_fail d.hG hGfail (by simp) rfl)
      rw [hfr2_eq]
      rw [hlenEnd] at hstarBody
      exact ⟨0, _, failR, hstarBody.trans (star_of_step hbrStep), hfailStep⟩
  | inr ρ₁End =>
      intro vs jBlk ρ₁Join hvs hjBlk hbp1
      obtain ⟨hflag0, hjoinMatch⟩ := hmatchTaken
      -- Build `evalArgs` on the chosen shifted args in `ρ₂F`
      have hchosenArgs : evalArgs ρ₂F ((argsT.zip argsF).map fun p => if hia.condVal then p.1 else p.2) = some vs := by
        have hmap : ((argsT.zip argsF).map fun p => if hia.condVal then p.1 else p.2) =
            (if hia.condVal then d.armT else d.armF).joinArgs.map
              (loopMapArg (if hia.condVal then d.armT else d.armF).defs d.off (if hia.condVal then 1 else 2)) := by
          have hlen : argsT.length = argsF.length := by simp [argsT, argsF, u.argsLenEq]
          cases hcv : hia.condVal <;> simp [argsT, argsF, List.map_fst_zip (Nat.le_of_eq hlen), List.map_snd_zip (Nat.le_of_eq hlen.symm)]
        rw [hmap]
        have hgo : ∀ (as : List Arg) (ws : List Word),
            (∀ a ∈ as, ∀ v, a.eval ρ₁End = some v →
              (loopMapArg (if hia.condVal then d.armT else d.armF).defs d.off (if hia.condVal then 1 else 2) a).eval ρ₂F = some v) →
            evalArgs ρ₁End as = some ws →
            evalArgs ρ₂F (as.map (loopMapArg (if hia.condVal then d.armT else d.armF).defs d.off (if hia.condVal then 1 else 2))) = some ws := by
          intro as; induction as with
          | nil => intro ws _ h; simp only [evalArgs_nil, Option.some.injEq] at h; subst h; rfl
          | cons a0 rest0 iha =>
              intro ws hm h
              simp only [evalArgs_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
              obtain ⟨v0, hv0, ws0, hws0, rfl⟩ := h
              simp [evalArgs_cons, hm a0 (by simp) v0 hv0, iha ws0 (fun a' ha' => hm a' (by simp [ha'])) hws0]
        exact hgo _ vs hjoinMatch hvs
      rcases hselRes : ((argsT.zip argsF).foldl (init := ([], [], fr2)) fun (ss, out, fr) (at_, af_) =>
        if at_ == af_ then (ss, at_ :: out, fr)
        else (ss ++ [Stmt.assign fr (.select d.c d.w d.a d.bArg at_ af_)], Arg.v fr :: out, fr + 1)) with ⟨selStmts, selArgsRev, fr3⟩
      have hsel := exec_selStmts (c := d.c) (w := d.w) (a := d.a) (bArg := d.bArg)
        (va := hia.va) (vb := hia.vb) (condVal := hia.condVal) (mem := mem) (ctx := ctx) (frStart := fr2)
        hia.hcond
        (fun x hx => Nat.lt_of_lt_of_le (haOuter x hx).1 (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) h3off_le_fr2))
        (fun x hx => Nat.lt_of_lt_of_le (hbOuter x hx).1 (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) h3off_le_fr2))
        (argsT.zip argsF) [] [] fr2 ρ₂F ρ₂F [] (Nat.le_refl _) haF hbF rfl
        (fun _ h => by cases h) (fun _ _ => rfl) (fun _ h => by cases h) rfl hpairs_ok vs hchosenArgs
      rw [hselRes] at hsel
      obtain ⟨hfr3_ge, hncSel, ρ₂Sel, hexSel, hevalSel, hpresSel⟩ := hsel
      simp only [List.nil_append] at hevalSel
      have hpresSel_lt : ∀ z, z < d.off → ρ₂Sel[z]? = fr₂.env[z]? := fun z hz => by
        rw [hpresSel z (Nat.lt_of_lt_of_le hz (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) h3off_le_fr2)),
            hpresF_lt z hz]
      -- `ρ₁End` agrees with `hia.ρ₁₀` on all `OuterRegOk` regs
      have hEndPres : ∀ x, OuterRegOk d.off d.armT.defs d.armF.defs x → ρ₁End[x]? = hia.ρ₁₀[x]? := by
        intro x hok
        cases hcv : hia.condVal
        · rw [hcv] at hrun
          have hp := runArmConcrete_preserves_nonDefs (armDefs := d.armF.defs)
            (fun st hst => ⟨fun s hs r hr => (hregsF st hst).1 s hs r hr |>.1,
              fun o y oa ob r hov => (hregsF st hst).2 o y oa ob r hov |>.1⟩) hrun
          exact hp.1 x hok.2.2
        · rw [hcv] at hrun
          have hp := runArmConcrete_preserves_nonDefs (armDefs := d.armT.defs)
            (fun st hst => ⟨fun s hs r hr => (hregsT st hst).1 s hs r hr |>.1,
              fun o y oa ob r hov => (hregsT st hst).2 o y oa ob r hov |>.1⟩) hrun
          exact hp.1 x hok.2.1
      have hAgreeSel : EnvAgreeOuter d.off d.armT.defs d.armF.defs ρ₁End ρ₂Sel := fun x v hok hv => by
        rw [hpresSel_lt x hok.1]
        rw [hEndPres x hok] at hv
        exact hia.hAgree0 x v hok hv
      have hfr2_eq : fr₂ = { fn := fi, label := b, pos := d.blk.body.toList.length, env := fr₂.env, dsts := fr₂.dsts } := by
        cases fr₂; simp only [Frame.mk.injEq, Array.length_toList]
        exact ⟨hia.fn2, hia.lbl2, hia.pos2, trivial, trivial⟩
      -- Split on Shape 1 (`commonRes? = none`) vs Shape 2 (`commonRes? = some failR`)
      cases hcr : d.armT.failRes?.orElse fun _ => d.armF.failRes? with
      | none =>
          simp only [Option.isSome_none, ifConvRemap, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          have hGb := ifConv_G_blocks_b_shape1 d hcr
          rw [hresT] at hGb; dsimp only at hGb
          rw [hresF] at hGb; dsimp only at hGb
          rw [hselRes] at hGb; dsimp only at hGb
          have hjBlkG : ∃ jBlkG, d.G.blocks[d.armT.join]? = some jBlkG ∧ jBlkG.params = jBlk.params := by
            by_cases hjb : d.armT.join = b
            · rw [hjb, d.hb] at hjBlk; cases hjBlk
              rw [hjb]; exact ⟨_, hGb, rfl⟩
            · have hgo := ifConv_G_blocks_other d hjBlk hjb
              rw [hcr] at hgo
              simp only [Option.isSome_none, ifConvRemap, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hgo
              exact ⟨_, hgo, rfl⟩
          obtain ⟨jBlkG, hjG, hjPar⟩ := hjBlkG
          obtain ⟨ρ₂Join, hbp2, hAgreeJoin, _⟩ := bindParams_agreeOuter hAgreeSel hbp1
          have hexAll : execList fr₂.env mem ctx (stmtsT ++ stmtsF ++ selStmts) = some (ρ₂Sel, mem) :=
            execList_append_ifconv (execList_append_ifconv hexT hexF) hexSel
          have hncAll : ∀ s ∈ stmtsT ++ stmtsF ++ selStmts, s.isCall = false := by
            intro s hs; simp only [List.mem_append] at hs
            rcases hs with (h1 | h2) | h3
            · exact hncT s h1
            · exact hncF s h2
            · exact hncSel s h3
          have hstarBody := execList_star_steps (dsts := fr₂.dsts) (rest := rest₂) d.hG hGb
            d.blk.body.toList (stmtsT ++ stmtsF ++ selStmts) [] fr₂.env ρ₂Sel mem mem
            (by simp [List.append_assoc]) hncAll hexAll
          have hlenEnd : d.blk.body.toList.length + (stmtsT ++ stmtsF ++ selStmts).length =
              (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts).toArray.size := by
            simp [List.length_append]
          have hjStep : step q
              { mem, ctx, stack := { fn := fi, label := b, pos := (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts).toArray.size, env := ρ₂Sel, dsts := fr₂.dsts } :: rest₂ } =
              .next { mem, ctx, stack := { fn := fi, label := d.armT.join, pos := 0, env := ρ₂Join, dsts := fr₂.dsts } :: rest₂ }
                (decide (d.armT.join ≤ b)) := by
            have hs := step_jump (p := q) (F := d.G)
              (B := { d.blk with body := (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts).toArray,
                                 term := .jump { target := d.armT.join, args := selArgsRev.reverse } })
              (fr := { fn := fi, label := b, pos := (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts).toArray.size, env := ρ₂Sel, dsts := fr₂.dsts })
              (rest := rest₂) (mem := mem) (ctx := ctx) d.hG hGb rfl rfl
            rw [takeEdge_ok hevalSel hjG (by rw [hjPar]; exact hbp2)] at hs
            exact hs
          refine ⟨(decide (d.armT.join ≤ b)).toNat, ρ₂Join, rfl, ?_, hAgreeJoin⟩
          rw [hfr2_eq]; rw [hlenEnd] at hstarBody
          have hcomb := hstarBody.trans (star_of_step hjStep)
          simpa using hcomb
      | some failR =>
          simp only [Option.isSome_some]
          have hblks2 := ifConv_G_blocks_shape2 d hcr
          rw [hresT] at hblks2; dsimp only at hblks2
          rw [hresF] at hblks2; dsimp only at hblks2
          rw [hselRes] at hblks2; dsimp only at hblks2
          obtain ⟨hGb, hGhop, _⟩ := hblks2
          have hjBlkG : ∃ jBlkG, d.G.blocks[ifConvRemap b true d.armT.join]? = some jBlkG ∧ jBlkG.params = jBlk.params := by
            by_cases hjb : d.armT.join = b
            · rw [hjb, d.hb] at hjBlk; cases hjBlk
              rw [hjb, ifConvRemap_b]; exact ⟨_, hGb, rfl⟩
            · have hgo := ifConv_G_blocks_other d hjBlk hjb
              rw [hcr] at hgo; simp only [Option.isSome_some] at hgo
              exact ⟨_, hgo, rfl⟩
          obtain ⟨jBlkG, hjG, hjPar⟩ := hjBlkG
          -- Evaluate `predStmt` → `0`!
          have haSel : d.a.eval ρ₂Sel = some hia.va := by
            cases hda : d.a with
            | imm _ => rw [hda] at haF; exact haF
            | v x =>
                rw [hda] at haF
                rw [Arg.eval, hpresSel x (Nat.lt_of_lt_of_le (haOuter x (by rw [hda]; simp [Arg.uses, Arg.vreg?])).1 (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) h3off_le_fr2))]
                exact haF
          have hbSel : d.bArg.eval ρ₂Sel = some hia.vb := by
            cases hdb : d.bArg with
            | imm _ => rw [hdb] at hbF; exact hbF
            | v x =>
                rw [hdb] at hbF
                rw [Arg.eval, hpresSel x (Nat.lt_of_lt_of_le (hbOuter x (by rw [hdb]; simp [Arg.uses, Arg.vreg?])).1 (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) h3off_le_fr2))]
                exact hbF
          have hflagT_Sel : flagT.eval ρ₂Sel = some fvT := by
            cases hft : flagT with
            | imm _ => rw [hft] at hflagT_inF; exact hflagT_inF
            | v r =>
                rw [hft] at hflagT_inF
                obtain ⟨_, hr2⟩ := hflagT_uses r (by rw [hft]; simp [Arg.uses, Arg.vreg?])
                rw [Arg.eval, hpresSel r (Nat.lt_of_lt_of_le hr2 hfr2_ge)]; exact hflagT_inF
          have hflagF_Sel : flagF.eval ρ₂Sel = some fvF := by
            cases hff : flagF with
            | imm _ => rw [hff] at hfvF; exact hfvF
            | v r =>
                rw [hff] at hfvF
                obtain ⟨_, hr2⟩ := hflagF_uses r (by rw [hff]; simp [Arg.uses, Arg.vreg?])
                rw [Arg.eval, hpresSel r hr2]; exact hfvF
          let predStmt := Stmt.assign fr3 (.select d.c d.w d.a d.bArg flagT flagF)
          let ρ₂Pred := ρ₂Sel.insert fr3 0
          have hpredExec : predStmt.exec ρ₂Sel mem ctx = some (ρ₂Pred, mem) := by
            simp only [predStmt, Stmt.exec, Rhs.eval, Option.bind_eq_bind, haSel, hbSel,
              hflagT_Sel, hflagF_Sel, Option.bind_some, hia.hcond, hflag0, ρ₂Pred]
          -- `selArgsRev.reverse` still evaluates to `vs` in `ρ₂Pred` (all regs `< fr3`)!
          have hevalSelPred : evalArgs ρ₂Pred selArgsRev.reverse = some vs := by
            have hselLt : ∀ a0 ∈ selArgsRev.reverse, ∀ x ∈ a0.uses, x < fr3 := by
              -- Prove directly via induction on the fold that every arg in `outRev` uses regs `< fr`!
              have hfoldLt : ∀ (ps : List (Arg × Arg)) (ss0 : List Stmt) (out0 : List Arg) (fr0 : Nat),
                  fr2 ≤ fr0 →
                  (∀ p0 ∈ ps, (∀ w0 ∈ p0.1.uses, w0 < fr2) ∧ (∀ w0 ∈ p0.2.uses, w0 < fr2)) →
                  (∀ a0 ∈ out0, ∀ x ∈ a0.uses, x < fr0) →
                  let (_, out1, fr1') := ps.foldl (init := (ss0, out0, fr0)) fun (ss, out, fr) (at_, af_) =>
                    if at_ == af_ then (ss, at_ :: out, fr)
                    else (ss ++ [Stmt.assign fr (.select d.c d.w d.a d.bArg at_ af_)], Arg.v fr :: out, fr + 1)
                  ∀ a0 ∈ out1, ∀ x ∈ a0.uses, x < fr1' := by
                intro ps; induction ps with
                | nil => intro _ _ _ _ _ hout; exact hout
                | cons p0 rest0 ihp =>
                    rcases p0 with ⟨aT0, aF0⟩
                    intro ss0 out0 fr0 hle hps0 hout
                    simp only [List.foldl_cons]
                    split
                    · exact ihp ss0 (aT0 :: out0) fr0 hle (fun q hq => hps0 q (by simp [hq])) (fun a0 ha0 x hx => by
                        simp only [List.mem_cons] at ha0; rcases ha0 with rfl | hm
                        · exact Nat.lt_of_lt_of_le ((hps0 (a0, aF0) (by simp)).1 x hx) hle
                        · exact hout a0 hm x hx)
                    · exact ihp _ (.v fr0 :: out0) (fr0 + 1) (Nat.le_trans hle (Nat.le_succ _)) (fun q hq => hps0 q (by simp [hq])) (fun a0 ha0 x hx => by
                        simp only [List.mem_cons] at ha0; rcases ha0 with rfl | hm
                        · simp only [Arg.uses, Arg.vreg?, Option.toList, List.mem_singleton] at hx
                          subst hx; exact Nat.lt_succ_self x
                        · exact Nat.lt_succ_of_lt (hout a0 hm x hx))
              have hlt := hfoldLt (argsT.zip argsF) [] [] fr2 (Nat.le_refl _)
                (fun q hq => ⟨(hpairs_ok q hq).1, (hpairs_ok q hq).2.1⟩) (fun _ h => by cases h)
              rw [hselRes] at hlt
              intro a0 ha0; exact hlt a0 (by simpa using ha0)
            have hgo : ∀ (as : List Arg), (∀ a0 ∈ as, ∀ x ∈ a0.uses, x < fr3) →
                evalArgs ρ₂Pred as = evalArgs ρ₂Sel as := by
              intro as; induction as with
              | nil => intro _; rfl
              | cons a0 as0 iha =>
                  intro hlt
                  have ha0 : a0.eval ρ₂Pred = a0.eval ρ₂Sel := by
                    cases a0 with
                    | imm _ => rfl
                    | v x =>
                        have hxlt := hlt (.v x) (by simp) x (by simp [Arg.uses, Arg.vreg?])
                        rw [Arg.eval, Arg.eval, env_insert_ne _ _ (Nat.ne_of_gt hxlt)]
                  simp [evalArgs_cons, ha0, iha (fun r hr => hlt r (by simp [hr]))]
            rw [hgo selArgsRev.reverse hselLt, hevalSel]
          have hAgreePred : EnvAgreeOuter d.off d.armT.defs d.armF.defs ρ₁End ρ₂Pred := fun x v hok hv => by
            rw [env_insert_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le hok.1 (Nat.le_trans (Nat.le_mul_of_pos_left d.off (by decide)) (Nat.le_trans h3off_le_fr2 hfr3_ge))))]
            exact hAgreeSel x v hok hv
          obtain ⟨ρ₂Join, hbp2, hAgreeJoin, _⟩ := bindParams_agreeOuter hAgreePred hbp1
          have hexAll : execList fr₂.env mem ctx (stmtsT ++ stmtsF ++ selStmts ++ [predStmt]) = some (ρ₂Pred, mem) :=
            execList_append_ifconv (execList_append_ifconv (execList_append_ifconv hexT hexF) hexSel) (by simp [execList, hpredExec])
          have hncAll : ∀ s ∈ stmtsT ++ stmtsF ++ selStmts ++ [predStmt], s.isCall = false := by
            intro s hs; simp only [List.mem_append, List.mem_singleton] at hs
            rcases hs with ((h1 | h2) | h3) | rfl
            · exact hncT s h1
            · exact hncF s h2
            · exact hncSel s h3
            · rfl
          have hstarBody := execList_star_steps (dsts := fr₂.dsts) (rest := rest₂) d.hG hGb
            d.blk.body.toList (stmtsT ++ stmtsF ++ selStmts ++ [predStmt]) [] fr₂.env ρ₂Pred mem mem
            (by simp [predStmt, List.append_assoc]) hncAll hexAll
          have hlenEnd : d.blk.body.toList.length + (stmtsT ++ stmtsF ++ selStmts ++ [predStmt]).length =
              (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts ++ [predStmt]).toArray.size := by
            simp [List.length_append]
          have hbrStep : step q
              { mem, ctx, stack := { fn := fi, label := b, pos := (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts ++ [predStmt]).toArray.size, env := ρ₂Pred, dsts := fr₂.dsts } :: rest₂ } =
              .next { mem, ctx, stack := { fn := fi, label := b + 1, pos := 0, env := ρ₂Pred, dsts := fr₂.dsts } :: rest₂ } false := by
            have hs := step_br (p := q) (F := d.G)
              (B := { d.blk with
                  body := (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts ++ [predStmt]).toArray
                  term := .br .ne .w64 (.v fr3) (.imm 0) { target := d.F.blocks.size + 1, args := [] } { target := b + 1, args := [] } })
              (fr := { fn := fi, label := b, pos := (d.blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts ++ [predStmt]).toArray.size, env := ρ₂Pred, dsts := fr₂.dsts })
              (rest := rest₂) (mem := mem) (ctx := ctx) (va := 0) (vb := 0)
              d.hG hGb rfl rfl (by simp [Arg.eval, ρ₂Pred]) rfl
            have hcond0 : Cond.ne.holds .w64 0 0 = false := by decide
            rw [hcond0] at hs; dsimp only at hs
            rw [takeEdge_ok rfl hGhop rfl] at hs
            have hlt : ¬ (b + 1 ≤ b) := Nat.not_le.2 (Nat.lt_succ_self b)
            simpa [hlt] using hs
          have hchgEq : decide (ifConvRemap b true d.armT.join ≤ b + 1) = decide (d.armT.join ≤ b) := by
            unfold ifConvRemap
            by_cases h : b + 1 ≤ d.armT.join
            · simp only [h, Bool.true_and, decide_true, ↓reduceIte, decide_eq_decide]
              exact Nat.succ_le_succ_iff
            · simp only [h, Bool.true_and, decide_false, Bool.false_eq_true, ↓reduceIte, decide_eq_decide]
              have hleB : d.armT.join ≤ b := Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
              exact ⟨fun _ => hleB, fun _ => Nat.le_succ_of_le hleB⟩
          have hhopStep : step q
              { mem, ctx, stack := { fn := fi, label := b + 1, pos := 0, env := ρ₂Pred, dsts := fr₂.dsts } :: rest₂ } =
              .next { mem, ctx, stack := { fn := fi, label := ifConvRemap b true d.armT.join, pos := 0, env := ρ₂Join, dsts := fr₂.dsts } :: rest₂ }
                (decide (d.armT.join ≤ b)) := by
            have hs := step_jump (p := q) (F := d.G)
              (B := { params := [], body := #[], term := .jump { target := ifConvRemap b true d.armT.join, args := selArgsRev.reverse }, cold := d.blk.cold })
              (fr := { fn := fi, label := b + 1, pos := 0, env := ρ₂Pred, dsts := fr₂.dsts })
              (rest := rest₂) (mem := mem) (ctx := ctx) d.hG hGhop (by simp) rfl
            rw [takeEdge_ok hevalSelPred hjG (by rw [hjPar]; exact hbp2), hchgEq] at hs
            exact hs
          refine ⟨(decide (d.armT.join ≤ b)).toNat, ρ₂Join, rfl, ?_, hAgreeJoin⟩
          rw [hfr2_eq]; rw [hlenEnd] at hstarBody
          have hcomb := (hstarBody.trans (star_of_step hbrStep)).trans (star_of_step hhopStep)
          simpa using hcomb

private theorem step_term_ge {p : Program} {F : Func} {B : Block} {mem : X86.Memory} {ctx : Word}
    {fr : Frame} {rest : List Frame}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hlt : ¬ fr.pos < B.body.size) :
    step p { mem, ctx, stack := fr :: rest } =
      match B.term with
      | .jump e => takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env e
      | .br c w a b' t e =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
            takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env (if c.holds w va vb then t else e)
          | _, _ => .stuck
      | .brOvf o x a b' ok ovf =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
              let (r, carry) := o.eval va vb
              takeEdge F { mem, ctx, stack := fr :: rest } fr rest (fr.env.insert x r) (if carry then ovf else ok)
          | _, _ => .stuck
      | .ret as =>
          match evalArgs fr.env as with
          | none => .stuck
          | some vals =>
              match rest with
              | [] => .done vals mem
              | caller :: rest' =>
                  match bindParams caller.env caller.dsts vals with
                  | some ρ => .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest' } false
                  | none => .stuck
      | .tail g as =>
          match evalArgs fr.env as >>= enter p g with
          | some callee => .next { mem, ctx, stack := callee :: rest } true
          | none => .stuck
      | .fail r => .fail r
      | .trap => .trap := by
  unfold step
  simp only [hf, hb, hlt, ↓reduceDIte]; rfl

private theorem step_jump_ge {p : Program} {F : Func} {B : Block} {mem : X86.Memory} {ctx : Word}
    {fr : Frame} {rest : List Frame} {e : Edge}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hlt : ¬ fr.pos < B.body.size) (ht : B.term = .jump e) :
    step p { mem, ctx, stack := fr :: rest } = takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env e := by
  rw [step_term_ge hf hb hlt, ht]

private theorem step_br_ge {p : Program} {F : Func} {B : Block} {mem : X86.Memory} {ctx : Word}
    {fr : Frame} {rest : List Frame} {c : Cond} {w : Width} {a b : Arg} {t e : Edge} {va vb : Word}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hlt : ¬ fr.pos < B.body.size) (ht : B.term = .br c w a b t e)
    (ha : a.eval fr.env = some va) (hb' : b.eval fr.env = some vb) :
    step p { mem, ctx, stack := fr :: rest } =
      takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env (if c.holds w va vb then t else e) := by
  rw [step_term_ge hf hb hlt, ht]; simp only [ha, hb']

private theorem step_brOvf_ge {p : Program} {F : Func} {B : Block} {mem : X86.Memory} {ctx : Word}
    {fr : Frame} {rest : List Frame} {o : Ovf} {x : VReg} {a b : Arg} {ok ovf : Edge} {va vb : Word}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hlt : ¬ fr.pos < B.body.size) (ht : B.term = .brOvf o x a b ok ovf)
    (ha : a.eval fr.env = some va) (hb' : b.eval fr.env = some vb) :
    step p { mem, ctx, stack := fr :: rest } =
      takeEdge F { mem, ctx, stack := fr :: rest } fr rest (fr.env.insert x (o.eval va vb).1)
        (if (o.eval va vb).2 then ovf else ok) := by
  rw [step_term_ge hf hb hlt, ht]; simp only [ha, hb']

private theorem step_ret_done_ge {p : Program} {F : Func} {B : Block} {mem : X86.Memory} {ctx : Word}
    {fr : Frame} {as : List Arg} {vals : List Word}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hlt : ¬ fr.pos < B.body.size) (ht : B.term = .ret as) (ha : evalArgs fr.env as = some vals) :
    step p { mem, ctx, stack := [fr] } = .done vals mem := by
  rw [step_term_ge hf hb hlt, ht]; simp only [ha]

private theorem step_ret_caller_ge {p : Program} {F : Func} {B : Block} {mem : X86.Memory} {ctx : Word}
    {fr caller : Frame} {rest' : List Frame} {as : List Arg} {vals : List Word} {ρ : Env}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hlt : ¬ fr.pos < B.body.size) (ht : B.term = .ret as) (ha : evalArgs fr.env as = some vals)
    (hp : bindParams caller.env caller.dsts vals = some ρ) :
    step p { mem, ctx, stack := fr :: caller :: rest' } =
      .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest' } false := by
  rw [step_term_ge hf hb hlt, ht]; simp only [ha, hp]

private theorem step_tail_ge {p : Program} {F : Func} {B : Block} {mem : X86.Memory} {ctx : Word}
    {fr callee : Frame} {rest : List Frame} {g : FunId} {as : List Arg} {vs : List Word}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hlt : ¬ fr.pos < B.body.size) (ht : B.term = .tail g as) (ha : evalArgs fr.env as = some vs)
    (he : enter p g vs = some callee) :
    step p { mem, ctx, stack := fr :: rest } = .next { mem, ctx, stack := callee :: rest } true := by
  rw [step_term_ge hf hb hlt, ht]; simp only [ha, Option.bind_eq_bind, Option.bind_some, he]

private theorem step_fail_ge {p : Program} {F : Func} {B : Block} {mem : X86.Memory} {ctx : Word}
    {fr : Frame} {rest : List Frame} {r : Sem.Resource}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hlt : ¬ fr.pos < B.body.size) (ht : B.term = .fail r) :
    step p { mem, ctx, stack := fr :: rest } = .fail r := by
  rw [step_term_ge hf hb hlt, ht]

private theorem step_trap_ge {p : Program} {F : Func} {B : Block} {mem : X86.Memory} {ctx : Word}
    {fr : Frame} {rest : List Frame}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hlt : ¬ fr.pos < B.body.size) (ht : B.term = .trap) :
    step p { mem, ctx, stack := fr :: rest } = .trap := by
  rw [step_term_ge hf hb hlt, ht]

/-- Master forward simulation diagram for `ifConvDiamondSite`. -/
private theorem ifConvDiamondSite_forward {p q : Program} {fi : FunId} {b : Label}
    (d : IfConvData p q fi b) :
    Sem.Forward (semStep p) (semStep q) Eq (IfConvStateRel d) := by
  have u := ifConv_unpack d
  let hasG := (d.armT.failRes?.orElse fun _ => d.armF.failRes?).isSome
  -- Helper: lookup block in `G` matching `uBlk` (same params, same prefix body, remapped edges if `u ≠ b`)
  have hGBlk_params : ∀ {l : Label} {B : Block}, d.F.blocks[l]? = some B →
      ∃ BG, d.G.blocks[ifConvRemap b hasG l]? = some BG ∧ BG.params = B.params := by
    intro l B hB
    by_cases hlb : l = b
    · subst hlb; rw [d.hb] at hB; cases hB
      rw [ifConvRemap_b]
      cases hcr : d.armT.failRes?.orElse fun _ => d.armF.failRes? with
      | none => exact ⟨_, ifConv_G_blocks_b_shape1 d hcr, rfl⟩
      | some _ => exact ⟨_, (ifConv_G_blocks_shape2 d hcr).1, rfl⟩
    · exact ⟨_, ifConv_G_blocks_other d hB hlb, rfl⟩
  -- Helper: prefix body statements of `d.blk` match `d.G.blocks[b]` at every index `< d.blk.body.size`
  have hGb_prefix : ∃ bG, d.G.blocks[b]? = some bG ∧ bG.params = d.blk.params ∧
      d.blk.body.size ≤ bG.body.size ∧
      ∀ i (hi : i < d.blk.body.size), bG.body[i]? = some d.blk.body[i] := by
    cases hcr : d.armT.failRes?.orElse fun _ => d.armF.failRes? with
    | none =>
        have hGb := ifConv_G_blocks_b_shape1 d hcr
        rcases hrT : emitSpeculativeArm d.armT.defs d.off 1 d.armT (3 * d.off) with ⟨sT, fT, fr1⟩
        rw [hrT] at hGb; dsimp only at hGb
        rcases hrF : emitSpeculativeArm d.armF.defs d.off 2 d.armF fr1 with ⟨sF, fF, fr2⟩
        rw [hrF] at hGb; dsimp only at hGb
        rcases hsRes : (((d.armT.joinArgs.map (loopMapArg d.armT.defs d.off 1)).zip
          (d.armF.joinArgs.map (loopMapArg d.armF.defs d.off 2))).foldl (init := ([], [], fr2))
          fun (ss, out, fr) (at_, af_) =>
            if at_ == af_ then (ss, at_ :: out, fr)
            else (ss ++ [Stmt.assign fr (.select d.c d.w d.a d.bArg at_ af_)], Arg.v fr :: out, fr + 1)) with ⟨sSel, sArgs, fr3⟩
        rw [hsRes] at hGb; dsimp only at hGb
        refine ⟨_, hGb, rfl, by simp [List.length_append], fun i hi => ?_⟩
        rw [List.getElem?_toArray, List.append_assoc, List.append_assoc,
          List.getElem?_append_left (by simpa using hi), Array.getElem?_toList, Array.getElem?_eq_getElem hi]
    | some _ =>
        have hblks2 := ifConv_G_blocks_shape2 d hcr
        rcases hrT : emitSpeculativeArm d.armT.defs d.off 1 d.armT (3 * d.off) with ⟨sT, fT, fr1⟩
        rw [hrT] at hblks2; dsimp only at hblks2
        rcases hrF : emitSpeculativeArm d.armF.defs d.off 2 d.armF fr1 with ⟨sF, fF, fr2⟩
        rw [hrF] at hblks2; dsimp only at hblks2
        rcases hsRes : (((d.armT.joinArgs.map (loopMapArg d.armT.defs d.off 1)).zip
          (d.armF.joinArgs.map (loopMapArg d.armF.defs d.off 2))).foldl (init := ([], [], fr2))
          fun (ss, out, fr) (at_, af_) =>
            if at_ == af_ then (ss, at_ :: out, fr)
            else (ss ++ [Stmt.assign fr (.select d.c d.w d.a d.bArg at_ af_)], Arg.v fr :: out, fr + 1)) with ⟨sSel, sArgs, fr3⟩
        rw [hsRes] at hblks2; dsimp only at hblks2
        obtain ⟨hGb, _, _⟩ := hblks2
        refine ⟨_, hGb, rfl, by simp [List.length_append], fun i hi => ?_⟩
        rw [List.getElem?_toArray, List.append_assoc, List.append_assoc, List.append_assoc,
          List.getElem?_append_left (by simpa using hi), Array.getElem?_toList, Array.getElem?_eq_getElem hi]
  -- Helper: executing a `takeEdge` from a non-`b` block in `fi`
  have hTakeEdge_fi : ∀ {s₁ : State} {fr₁ fr₂ : Frame} {rest₁ rest₂ : List Frame}
      {uBlk : Block} {e : Edge} {ρ₁ ρ₂ : Env} {s₁' : State} {chg : Bool},
      fr₁.fn = fi → fr₂.fn = fi → fr₂.dsts = fr₁.dsts →
      fr₂.label = ifConvRemap b hasG fr₁.label →
      fr₁.label ≠ b →
      d.F.blocks[fr₁.label]? = some uBlk →
      (Src.NatSet.ofList d.armT.labels).contains fr₁.label = false →
      (Src.NatSet.ofList d.armF.labels).contains fr₁.label = false →
      e ∈ uBlk.term.edges →
      EnvAgreeOuter d.off d.armT.defs d.armF.defs ρ₁ ρ₂ →
      (∀ x ∈ d.F.params, ρ₁[x]?.isSome = true) →
      takeEdge d.F s₁ fr₁ rest₁ ρ₁ e = .next s₁' chg →
      ∃ s₂', takeEdge d.G { mem := s₁.mem, ctx := s₁.ctx, stack := fr₂ :: rest₂ } fr₂ rest₂ ρ₂
          { e with target := ifConvRemap b hasG e.target } = .next s₂' chg ∧
        (s₂'.mem = s₁'.mem ∧ s₂'.ctx = s₁'.ctx ∧
          ∃ fr₁' fr₂', s₁'.stack = fr₁' :: rest₁ ∧ s₂'.stack = fr₂' :: rest₂ ∧
            NormalIfConvFrame d true fr₁' fr₂') := by
    intro s₁ fr₁ fr₂ rest₁ rest₂ uBlk e ρ₁ ρ₂ s₁' chg hfn1 hfn2 hdst hlbl hne hu huNT huNF heMem hag hfp hte
    unfold takeEdge at hte
    cases htb : d.F.blocks[e.target]? with
    | none => rw [htb] at hte; cases hvs : evalArgs ρ₁ e.args <;> rw [hvs] at hte <;> cases hte
    | some tBlk =>
        rw [htb] at hte
        cases hvs : evalArgs ρ₁ e.args with
        | none => rw [hvs] at hte; cases hte
        | some vs =>
            rw [hvs] at hte; dsimp only at hte
            cases hbp : bindParams ρ₁ tBlk.params vs with
            | none => rw [hbp] at hte; cases hte
            | some ρ₁' =>
                rw [hbp] at hte; simp only [Step.next.injEq] at hte
                obtain ⟨rfl, rfl⟩ := hte
                obtain ⟨hTgtNT, hTgtNF⟩ := u.outsideNoEnter fr₁.label uBlk hu hne huNT huNF e heMem
                have heUses : ∀ a ∈ e.args, ∀ x ∈ a.uses, OuterRegOk d.off d.armT.defs d.armF.defs x := fun a ha x hx =>
                  u.outsideUses fr₁.label uBlk hu huNT huNF x
                    (by simp only [List.mem_append]; right; simp only [Term.edgeUses, List.mem_flatMap]
                        exact ⟨e, heMem, List.mem_flatMap.2 ⟨a, ha, hx⟩⟩)
                have hvs2 := ifConv_outer_evalArgs hag heUses hvs
                obtain ⟨tBlkG, htG, htPar⟩ := hGBlk_params htb
                obtain ⟨ρ₂', hbp2, hag', htParDef⟩ := bindParams_agreeOuter hag hbp
                have hchg : decide (ifConvRemap b hasG e.target ≤ fr₂.label) = decide (e.target ≤ fr₁.label) := by
                  rw [hlbl, decide_eq_decide]; exact ifConvRemap_le_iff b hasG e.target fr₁.label
                have hte2 := takeEdge_ok (F := d.G)
                  (s := { mem := s₁.mem, ctx := s₁.ctx, stack := fr₂ :: rest₂ })
                  (fr := fr₂) (rest := rest₂) (ρ := ρ₂) (e := { e with target := ifConvRemap b hasG e.target })
                  hvs2 htG (by rw [htPar]; exact hbp2)
                rw [hchg] at hte2
                refine ⟨_, hte2, rfl, rfl, _, _, rfl, rfl, ⟨by simp [hfn1, hfn2], hdst, ?_⟩⟩
                simp only [hasG, hfn1, ↓reduceIte, hTgtNT, hTgtNF, hag', true_and]
                refine ⟨fun x hx => bindParams_preserves_isSome hbp x (hfp x hx), fun htbEq => ?_⟩
                rw [htbEq, d.hb] at htb; cases htb
                exact ⟨Nat.zero_le _, htParDef, fun i hi => by omega, fun h => by cases h⟩
  constructor
  · -- `next`
    intro s₁ s₁' s₂ chg hrel hstep
    rcases s₁ with ⟨mem₁, ctx₁, stk₁⟩
    rcases s₂ with ⟨mem₂, ctx₂, stk₂⟩
    obtain ⟨hmem, hctx, hstk⟩ := hrel
    dsimp only at hmem hctx hstk
    subst mem₂; subst ctx₂
    cases hstk with
    | nil =>
        cases hstep' : step p { mem := mem₁, ctx := ctx₁, stack := [] } <;> rw [semStep, hstep'] at hstep <;> cases hstep
        simp [step] at hstep'
    | @cons fr₁ fr₂ rest₁ rest₂ htop hrest =>
        cases hst1 : step p { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } with
        | done _ _ | fail _ | trap | stuck => rw [semStep, hst1] at hstep; cases hstep
        | next s₁'' chg' =>
            rw [semStep, hst1] at hstep; simp only [Step.toSem, Sem.Step.next.injEq] at hstep
            obtain ⟨rfl, rfl⟩ := hstep
            cases htop with
            | normal hnorm =>
                by_cases hfn : fr₁.fn = fi
                · -- Active frame is in modified function `fi`
                  have hbody := hnorm.bodyEq
                  simp only [hfn, ↓reduceIte] at hbody
                  obtain ⟨hlbl, hpos, hNT, hNF, hag, hfp, hbInv⟩ := hbody
                  have hfn2 : fr₂.fn = fi := by rw [hnorm.fnEq, hfn]
                  unfold step at hst1; dsimp only at hst1
                  rw [hfn, d.hF] at hst1; dsimp only at hst1
                  cases hB : d.F.blocks[fr₁.label]? with
                  | none => rw [hB] at hst1; cases hst1
                  | some B =>
                      rw [hB] at hst1; dsimp only at hst1
                      by_cases hltBody : fr₁.pos < B.body.size
                      · -- Executing a statement in `B.body`
                        simp only [hltBody, ↓reduceDIte] at hst1
                        -- Lookup matching block in `G` and statement at `fr₂.pos = fr₁.pos`
                        have hGSt : ∃ BG, d.G.blocks[fr₂.label]? = some BG ∧
                            fr₂.pos < BG.body.size ∧ BG.body[fr₂.pos]? = some B.body[fr₁.pos] := by
                          by_cases hlb : fr₁.label = b
                          · rw [hlb, d.hb] at hB; cases hB
                            obtain ⟨bG, hbG, _, hle, hget⟩ := hGb_prefix
                            rw [hlbl, hlb, ifConvRemap_b]
                            exact ⟨bG, hbG, by omega, by rw [hpos]; exact hget fr₁.pos hltBody⟩
                          · have hGo := ifConv_G_blocks_other d hB hlb
                            rw [hlbl]
                            exact ⟨_, hGo, by rw [hpos]; exact hltBody, by rw [hpos, Array.getElem?_eq_getElem hltBody]⟩
                        obtain ⟨BG, hBG, hltBG, hgetBG⟩ := hGSt
                        have hgetBG' : BG.body[fr₂.pos]'hltBG = B.body[fr₁.pos]'hltBody := by
                          rw [Array.getElem?_eq_getElem hltBG] at hgetBG; exact Option.some.inj hgetBG
                        have hstUses : ∀ x ∈ (B.body[fr₁.pos]'hltBody).uses, OuterRegOk d.off d.armT.defs d.armF.defs x := fun x hx =>
                          u.outsideUses fr₁.label B hB hNT hNF x
                            (by simp only [List.mem_append, List.mem_flatMap]; left; left
                                exact ⟨B.body[fr₁.pos]'hltBody, Array.mem_toList_iff.2 (Array.getElem_mem hltBody), hx⟩)
                        cases hst : B.body[fr₁.pos]'hltBody with
                        | call rs g as =>
                            rw [hst] at hst1; dsimp only at hst1
                            cases hcall : (evalArgs fr₁.env as >>= enter p g) with
                            | none => rw [hcall] at hst1; cases hst1
                            | some callee₁ =>
                                rw [hcall] at hst1; simp only [Step.next.injEq] at hst1
                                obtain ⟨rfl, rfl⟩ := hst1
                                simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hcall
                                obtain ⟨vs, hvs, hent₁⟩ := hcall
                                have hasUses : ∀ a ∈ as, ∀ x ∈ a.uses, OuterRegOk d.off d.armT.defs d.armF.defs x := fun a ha x hx =>
                                  hstUses x (by rw [hst]; simp only [Stmt.uses, argsUses, List.mem_flatMap]; exact ⟨a, ha, hx⟩)
                                have hvs2 := ifConv_outer_evalArgs hag hasUses hvs
                                obtain ⟨callee₂, hent₂, hcalleeRel⟩ := ifConv_enter_rel d u hent₁
                                have hst2 := step_call (p := q) (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂)
                                  (F := d.G) (B := BG) (rs := rs) (g := g) (as := as)
                                  (by rw [hfn2]; exact d.hG) hBG hltBG (by rw [hgetBG', hst]) hvs2 hent₂
                                left
                                refine ⟨1, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                  .cons (.normal hcalleeRel) (.cons ⟨hfn2, rfl, ?_⟩ hrest)⟩
                                simp only [↓reduceIte, hlbl, hpos, hNT, hNF, hag, true_and]
                                refine ⟨hfp, fun hlb => ?_⟩
                                obtain ⟨hposLeB, hbpB, hbodyB, _⟩ := hbInv hlb
                                rw [hlb, d.hb] at hB; cases hB
                                refine ⟨by omega, hbpB, fun i hi st' hst' => by
                                    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel] at hi
                                    exact hbodyB i hi st' hst',
                                  fun _ _ st' hst' => ?_⟩
                                simp only [Nat.add_sub_cancel] at hst'
                                rw [Array.getElem?_eq_getElem hltBody, Option.some.injEq] at hst'
                                subst hst'; rw [hst]
                                exact ⟨fun x hx => by
                                    simp only [Stmt.uses, argsUses, List.mem_flatMap] at hx
                                    obtain ⟨a0, ha0, hx0⟩ := hx
                                    exact evalArgs_isSome hvs a0 ha0 x hx0, rfl⟩
                        | assign _ _ | limb _ _ _ | store _ _ _ =>
                            rw [hst] at hst1; dsimp only at hst1
                            cases hx1 : (B.body[fr₁.pos]'hltBody).exec fr₁.env mem₁ ctx₁ with
                            | none => rw [hst] at hx1; rw [hx1] at hst1; cases hst1
                            | some res1 =>
                                rcases res1 with ⟨ρ₁', mem'⟩
                                rw [hst] at hx1; rw [hx1] at hst1; simp only [Step.next.injEq] at hst1
                                obtain ⟨rfl, rfl⟩ := hst1
                                rw [← hst] at hx1
                                obtain ⟨ρ₂', hx2, hag'⟩ := ifConv_outer_exec_stmt hag hstUses hx1
                                have hnc : (B.body[fr₁.pos]'hltBody).isCall = false := by rw [hst]; rfl
                                have hst2 := step_stmt (p := q) (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂)
                                  (F := d.G) (B := BG) (s := B.body[fr₁.pos]'hltBody)
                                  (by rw [hfn2]; exact d.hG) hBG hltBG hgetBG' hnc hx2
                                left
                                refine ⟨0, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                  .cons (.normal ⟨hfn2, hnorm.dstsEq, ?_⟩) hrest⟩
                                simp only [↓reduceIte, hlbl, hpos, hNT, hNF, hag', true_and]
                                refine ⟨fun x hx => stmt_exec_preserves_isSome hx1 x (hfp x hx), fun hlb => ?_⟩
                                obtain ⟨hposLeB, hbpB, hbodyB, _⟩ := hbInv hlb
                                rw [hlb, d.hb] at hB; cases hB
                                refine ⟨by omega, fun x hx => stmt_exec_preserves_isSome hx1 x (hbpB x hx), fun i hi st' hst' => ?_, fun h => by cases h⟩
                                by_cases hilt : i < fr₁.pos
                                · intro x hx; exact stmt_exec_preserves_isSome hx1 x (hbodyB i hilt st' hst' x hx)
                                · have hieq : i = fr₁.pos := by omega
                                  subst hieq
                                  rw [Array.getElem?_eq_getElem hltBody, Option.some.injEq] at hst'; subst hst'
                                  exact stmt_exec_uses_defs_isSome hx1
                      · -- Executing terminator of `B`
                        simp only [hltBody, ↓reduceDIte] at hst1
                        by_cases hlb : fr₁.label = b
                        · -- Terminator of converted block `b`! Enter `InArmFrame` with 0 steps in `q`!
                          rw [hlb, d.hb] at hB; cases hB
                          rw [d.hTerm] at hst1; dsimp only at hst1
                          cases ha1 : d.a.eval fr₁.env with
                          | none => rw [ha1] at hst1; cases hst1
                          | some va =>
                              rw [ha1] at hst1
                              cases hb1 : d.bArg.eval fr₁.env with
                              | none => rw [hb1] at hst1; cases hst1
                              | some vb =>
                                  rw [hb1] at hst1; dsimp only at hst1
                                  let condVal := d.c.holds d.w va vb
                                  have hcond_def : d.c.holds d.w va vb = condVal := rfl
                                  obtain ⟨hposLeB, hbpB, hbodyB, _⟩ := hbInv hlb
                                  have hposEq : fr₁.pos = d.blk.body.size := by omega
                                  have hpos2Eq : fr₂.pos = d.blk.body.size := by rw [hpos, hposEq]
                                  have hlbl2Eq : fr₂.label = b := by rw [hlbl, hlb, ifConvRemap_b]
                                  have hEnterArm : ∀ (arm : DiamondArm) (eEdge : Edge),
                                      arm = (if condVal then d.armT else d.armF) →
                                      eEdge = (if condVal then d.eT else d.eF) →
                                      b < eEdge.target → eEdge.args = [] →
                                      verifyArmMatches d.F b eEdge.target d.armT.join
                                        (d.armT.failRes?.orElse fun _ => d.armF.failRes?) arm = true →
                                      (∃ c s₂', Sem.Star (semStep q) { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } c s₂' ∧ chg'.toNat ≤ c ∧ IfConvStateRel d s₁'' s₂') ∨
                                        Sem.Fails (semStep q) { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } := by
                                    intro arm eEdge harm heEdge hltE heArgs hver
                                    obtain ⟨first, tail, hstepsEq, hfirstLbl⟩ := verifyArmMatches_nonempty hver
                                    have hvg := hver; unfold verifyArmMatches at hvg
                                    simp only [Bool.and_eq_true] at hvg
                                    rw [hstepsEq] at hvg
                                    obtain ⟨_, firstBlk, hfirstB, hfirstPar, _, _⟩ :=
                                      verifyArmMatches_step_at (pre := []) (cur := first) (rem := tail) hltE hvg.2
                                    rw [hfirstLbl] at hfirstB
                                    rw [← heEdge] at hst1
                                    have hte := takeEdge_ok (F := d.F) (s := { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ }) (fr := fr₁)
                                      (rest := rest₁) (ρ := fr₁.env) (e := eEdge)
                                      (by rw [heArgs]; rfl) hfirstB (by rw [hfirstPar]; rfl)
                                    rw [hte] at hst1; simp only [Step.next.injEq] at hst1
                                    obtain ⟨rfl, rfl⟩ := hst1
                                    have hchgF : decide (eEdge.target ≤ fr₁.label) = false := by
                                      rw [hlb]; exact decide_eq_false (Nat.not_le.2 hltE)
                                    rw [hchgF]
                                    left
                                    refine ⟨0, { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ }, Sem.Star.refl _, Nat.le_refl _, rfl, rfl,
                                      .cons (.inArm ⟨hfn, hfn2, hnorm.dstsEq, hlbl2Eq, hpos2Eq, condVal,
                                        fr₁.env, va, vb, ha1, hb1, hcond_def.symm, hag, hfp, hbpB,
                                        fun i hi => hbodyB i (by omega), [], first, tail,
                                        by rw [← harm, hstepsEq]; rfl, hfirstLbl.symm, Nat.zero_le _, fr₁.env, rfl, rfl⟩) hrest⟩
                                  cases hcv : condVal
                                  · exact hEnterArm d.armF d.eF (by simp [hcv]) (by simp [hcv]) u.bLtF u.eFArgs u.verF
                                  · exact hEnterArm d.armT d.eT (by simp [hcv]) (by simp [hcv]) u.bLtT u.eTArgs u.verT
                        · -- Terminator of a non-`b` block in `fi`
                          have hGo := ifConv_G_blocks_other d hB hlb
                          have htermUses : ∀ x ∈ B.term.uses, OuterRegOk d.off d.armT.defs d.armF.defs x := fun x hx =>
                            u.outsideUses fr₁.label B hB hNT hNF x (by simp only [List.mem_append]; left; right; exact hx)
                          cases ht : B.term with
                          | jump e =>
                              rw [ht] at hst1; dsimp only at hst1
                              obtain ⟨s₂', hte2, hm', hc', fr₁', fr₂', hs1', hs2', hnr'⟩ :=
                                hTakeEdge_fi hfn hfn2 hnorm.dstsEq hlbl hlb hB hNT hNF
                                  (by rw [ht]; simp [Term.edges]) hag hfp hst1
                              have hst2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } = .next s₂' chg' := by
                                have h1 := step_jump_ge (p := q) (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂)
                                  (F := d.G) (B := { B with term := B.term.setEdges (B.term.edges.map fun e => { e with target := ifConvRemap b hasG e.target }) })
                                  (by rw [hfn2]; exact d.hG) (by rw [hlbl]; exact hGo)
                                  (by rw [hpos]; exact hltBody) (by rw [ht]; exact setEdges_remap_jump e _)
                                rw [h1, hte2]
                              left; exact ⟨chg'.toNat, s₂', star_of_step hst2, Nat.le_refl _, hm', hc',
                                by rw [hs1', hs2']; exact .cons (.normal hnr') hrest⟩
                          | br c0 w0 a0 b0 e1 e2 =>
                              rw [ht] at hst1; dsimp only at hst1
                              cases ha1 : a0.eval fr₁.env with
                              | none => rw [ha1] at hst1; cases hst1
                              | some va =>
                                  rw [ha1] at hst1
                                  cases hb1 : b0.eval fr₁.env with
                                  | none => rw [hb1] at hst1; cases hst1
                                  | some vb =>
                                      rw [hb1] at hst1; dsimp only at hst1
                                      have ha2 := ifConv_outer_eval_arg hag (fun x hx => htermUses x (by rw [ht]; simp [Term.uses, hx])) ha1
                                      have hb2 := ifConv_outer_eval_arg hag (fun x hx => htermUses x (by rw [ht]; simp [Term.uses, hx])) hb1
                                      have heMem : (if c0.holds w0 va vb then e1 else e2) ∈ B.term.edges := by
                                        rw [ht]; cases c0.holds w0 va vb <;> simp [Term.edges]
                                      obtain ⟨s₂', hte2, hm', hc', fr₁', fr₂', hs1', hs2', hnr'⟩ :=
                                        hTakeEdge_fi hfn hfn2 hnorm.dstsEq hlbl hlb hB hNT hNF heMem hag hfp hst1
                                      have hst2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } = .next s₂' chg' := by
                                        have h1 := step_br_ge (p := q) (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂)
                                          (F := d.G) (B := { B with term := B.term.setEdges (B.term.edges.map fun e => { e with target := ifConvRemap b hasG e.target }) })
                                          (by rw [hfn2]; exact d.hG) (by rw [hlbl]; exact hGo)
                                          (by rw [hpos]; exact hltBody) (by rw [ht]; exact setEdges_remap_br c0 w0 a0 b0 e1 e2 _)
                                          ha2 hb2
                                        cases hcv : c0.holds w0 va vb <;> rw [hcv] at h1 hte2 <;> simpa using h1.trans hte2
                                      left; exact ⟨chg'.toNat, s₂', star_of_step hst2, Nat.le_refl _, hm', hc',
                                        by rw [hs1', hs2']; exact .cons (.normal hnr') hrest⟩
                          | brOvf o0 x0 a0 b0 okE ovfE =>
                              rw [ht] at hst1; dsimp only at hst1
                              cases ha1 : a0.eval fr₁.env with
                              | none => rw [ha1] at hst1; cases hst1
                              | some va =>
                                  rw [ha1] at hst1
                                  cases hb1 : b0.eval fr₁.env with
                                  | none => rw [hb1] at hst1; cases hst1
                                  | some vb =>
                                      rw [hb1] at hst1; dsimp only at hst1
                                      have ha2 := ifConv_outer_eval_arg hag (fun x hx => htermUses x (by rw [ht]; simp [Term.uses, hx])) ha1
                                      have hb2 := ifConv_outer_eval_arg hag (fun x hx => htermUses x (by rw [ht]; simp [Term.uses, hx])) hb1
                                      have hst2_base := step_brOvf_ge (p := q) (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂)
                                        (F := d.G) (B := { B with term := B.term.setEdges (B.term.edges.map fun e => { e with target := ifConvRemap b hasG e.target }) })
                                        (by rw [hfn2]; exact d.hG) (by rw [hlbl]; exact hGo)
                                        (by rw [hpos]; exact hltBody) (by rw [ht]; exact setEdges_remap_brOvf o0 x0 a0 b0 okE ovfE _)
                                        ha2 hb2
                                      cases hov : (o0.eval va vb).2 with
                                      | true =>
                                          rw [hov] at hst1 hst2_base; simp only [↓reduceIte] at hst1 hst2_base
                                          obtain ⟨s₂', hte2, hm', hc', fr₁', fr₂', hs1', hs2', hnr'⟩ :=
                                            hTakeEdge_fi hfn hfn2 hnorm.dstsEq hlbl hlb hB hNT hNF
                                              (by rw [ht]; simp [Term.edges])
                                              (envAgreeOuter_insert hag x0 (o0.eval va vb).1)
                                              (fun y hy => env_isSome_insert (hfp y hy)) hst1
                                          rw [hte2] at hst2_base
                                          left; exact ⟨chg'.toNat, s₂', star_of_step hst2_base, Nat.le_refl _, hm', hc',
                                            by rw [hs1', hs2']; exact .cons (.normal hnr') hrest⟩
                                      | false =>
                                          rw [hov] at hst1 hst2_base; simp only [Bool.false_eq_true, ↓reduceIte] at hst1 hst2_base
                                          obtain ⟨s₂', hte2, hm', hc', fr₁', fr₂', hs1', hs2', hnr'⟩ :=
                                            hTakeEdge_fi hfn hfn2 hnorm.dstsEq hlbl hlb hB hNT hNF
                                              (by rw [ht]; simp [Term.edges])
                                              (envAgreeOuter_insert hag x0 (o0.eval va vb).1)
                                              (fun y hy => env_isSome_insert (hfp y hy)) hst1
                                          rw [hte2] at hst2_base
                                          left; exact ⟨chg'.toNat, s₂', star_of_step hst2_base, Nat.le_refl _, hm', hc',
                                            by rw [hs1', hs2']; exact .cons (.normal hnr') hrest⟩
                          | ret as =>
                              rw [ht] at hst1; dsimp only at hst1
                              cases hvs : evalArgs fr₁.env as with
                              | none => rw [hvs] at hst1; cases hst1
                              | some vs =>
                                  rw [hvs] at hst1; dsimp only at hst1
                                  have hvs2 := ifConv_outer_evalArgs hag (fun a0 ha0 x hx => htermUses x (by rw [ht]; simp only [Term.uses, argsUses, List.mem_flatMap]; exact ⟨a0, ha0, hx⟩)) hvs
                                  cases hrest with
                                  | nil => cases hst1
                                  | @cons c₁ c₂ cr₁ cr₂ hcallRel hcr =>
                                      dsimp only at hst1
                                      cases hbp : bindParams c₁.env c₁.dsts vs with
                                      | none => rw [hbp] at hst1; cases hst1
                                      | some ρc₁' =>
                                          rw [hbp] at hst1; simp only [Step.next.injEq] at hst1
                                          obtain ⟨rfl, rfl⟩ := hst1
                                          by_cases hcfn : c₁.fn = fi
                                          · have hcb := hcallRel.bodyEq; simp only [hcfn, ↓reduceIte] at hcb
                                            obtain ⟨hclbl, hcpos, hcNT, hcNF, hcag, hcfp, hcbInv⟩ := hcb
                                            obtain ⟨ρc₂', hbp2, hcag', hdstDef⟩ := bindParams_agreeOuter hcag hbp
                                            have hst2 := step_ret_caller_ge (p := q) (mem := mem₁) (ctx := ctx₁) (fr := fr₂)
                                              (caller := c₂) (rest' := cr₂) (F := d.G)
                                              (B := { B with term := B.term.setEdges (B.term.edges.map fun e => { e with target := ifConvRemap b hasG e.target }) })
                                              (by rw [hfn2]; exact d.hG) (by rw [hlbl]; exact hGo)
                                              (by rw [hpos]; exact hltBody) (by dsimp only; rw [ht]; rfl)
                                              hvs2 (by rw [hcallRel.dstsEq]; exact hbp2)
                                            left
                                            refine ⟨0, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                              .cons (.normal ⟨hcallRel.fnEq, rfl, ?_⟩) hcr⟩
                                            simp only [hcfn, ↓reduceIte, hclbl, hcpos, hcNT, hcNF, hcag', true_and]
                                            refine ⟨fun x hx => bindParams_preserves_isSome hbp x (hcfp x hx), fun hclb => ?_⟩
                                            obtain ⟨hcposLe, hcbp, hcbody, hclast⟩ := hcbInv hclb
                                            refine ⟨hcposLe, fun x hx => bindParams_preserves_isSome hbp x (hcbp x hx), fun i hi st' hst' x hx => ?_, fun h => by cases h⟩
                                            by_cases hilt : i < c₁.pos - 1
                                            · exact bindParams_preserves_isSome hbp x (hcbody i hilt st' hst' x hx)
                                            · have hcpos_gt : c₁.pos > 0 := by omega
                                              have hieq : i = c₁.pos - 1 := by omega
                                              subst hieq
                                              obtain ⟨huses, hdefs⟩ := hclast trivial hcpos_gt st' hst'
                                              simp only [List.mem_append] at hx
                                              rcases hx with hu | hd
                                              · exact bindParams_preserves_isSome hbp x (huses x hu)
                                              · rw [hdefs] at hd; exact hdstDef x hd
                                          · have hcb := hcallRel.bodyEq; simp only [hcfn, ↓reduceIte] at hcb
                                            obtain ⟨hclbl, hcpos, hcenv⟩ := hcb
                                            have hst2 := step_ret_caller_ge (p := q) (mem := mem₁) (ctx := ctx₁) (fr := fr₂)
                                              (caller := c₂) (rest' := cr₂) (F := d.G)
                                              (B := { B with term := B.term.setEdges (B.term.edges.map fun e => { e with target := ifConvRemap b hasG e.target }) })
                                              (by rw [hfn2]; exact d.hG) (by rw [hlbl]; exact hGo)
                                              (by rw [hpos]; exact hltBody) (by dsimp only; rw [ht]; rfl)
                                              hvs2 (by rw [hcallRel.dstsEq, hcenv]; exact hbp)
                                            left
                                            refine ⟨0, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                              .cons (.normal ⟨hcallRel.fnEq, rfl, ?_⟩) hcr⟩
                                            simp only [hcfn, ↓reduceIte]; exact ⟨hclbl, hcpos, trivial⟩
                          | tail g as =>
                              rw [ht] at hst1; dsimp only at hst1
                              cases htl : (evalArgs fr₁.env as >>= enter p g) with
                              | none => rw [htl] at hst1; cases hst1
                              | some callee₁ =>
                                  rw [htl] at hst1; simp only [Step.next.injEq] at hst1
                                  obtain ⟨rfl, rfl⟩ := hst1
                                  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at htl
                                  obtain ⟨vs, hvs, hent₁⟩ := htl
                                  have hvs2 := ifConv_outer_evalArgs hag (fun a0 ha0 x hx => htermUses x (by rw [ht]; simp only [Term.uses, argsUses, List.mem_flatMap]; exact ⟨a0, ha0, hx⟩)) hvs
                                  obtain ⟨callee₂, hent₂, hcalleeRel⟩ := ifConv_enter_rel d u hent₁
                                  have hst2 := step_tail_ge (p := q) (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂)
                                    (F := d.G) (B := { B with term := B.term.setEdges (B.term.edges.map fun e => { e with target := ifConvRemap b hasG e.target }) })
                                    (by rw [hfn2]; exact d.hG) (by rw [hlbl]; exact hGo)
                                    (by rw [hpos]; exact hltBody) (by dsimp only; rw [ht]; rfl)
                                    hvs2 hent₂
                                  left; exact ⟨1, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                    .cons (.normal hcalleeRel) hrest⟩
                          | fail _ | trap => rw [ht] at hst1; cases hst1
                · -- Active frame is NOT in `fi` (`fr₂ = fr₁`, `q.funcs[fr₁.fn]? = p.funcs[fr₁.fn]?`)
                  have hbody := hnorm.bodyEq; simp only [hfn, ↓reduceIte] at hbody
                  obtain ⟨hlbl, hpos, henv⟩ := hbody
                  have hfrEq : fr₂ = fr₁ := by
                    cases fr₁; cases fr₂; simp only [Frame.mk.injEq]
                    exact ⟨hnorm.fnEq, hlbl, hpos, henv, hnorm.dstsEq⟩
                  subst fr₂
                  unfold step at hst1; dsimp only at hst1
                  cases hF0 : p.funcs[fr₁.fn]? with
                  | none => rw [hF0] at hst1; cases hst1
                  | some F0 =>
                      rw [hF0] at hst1; dsimp only at hst1
                      have hqF0 : q.funcs[fr₁.fn]? = some F0 := by rw [d.hOtherF fr₁.fn hfn, hF0]
                      cases hB : F0.blocks[fr₁.label]? with
                      | none => rw [hB] at hst1; cases hst1
                      | some B =>
                          rw [hB] at hst1; dsimp only at hst1
                          by_cases hltBody : fr₁.pos < B.body.size
                          · simp only [hltBody, ↓reduceDIte] at hst1
                            cases hst : B.body[fr₁.pos]'hltBody with
                            | call rs g as =>
                                rw [hst] at hst1; dsimp only at hst1
                                cases hcall : (evalArgs fr₁.env as >>= enter p g) with
                                | none => rw [hcall] at hst1; cases hst1
                                | some callee₁ =>
                                    rw [hcall] at hst1; simp only [Step.next.injEq] at hst1
                                    obtain ⟨rfl, rfl⟩ := hst1
                                    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hcall
                                    obtain ⟨vs, hvs, hent₁⟩ := hcall
                                    obtain ⟨callee₂, hent₂, hcalleeRel⟩ := ifConv_enter_rel d u hent₁
                                    have hst2 := step_call (mem := mem₁) (ctx := ctx₁) (rest := rest₂) hqF0 hB hltBody hst hvs hent₂
                                    left
                                    exact ⟨1, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                      .cons (.normal hcalleeRel) (.cons ⟨rfl, rfl, by simp [hfn]⟩ hrest)⟩
                            | assign _ _ | limb _ _ _ | store _ _ _ =>
                                rw [hst] at hst1; dsimp only at hst1
                                cases hx1 : (B.body[fr₁.pos]'hltBody).exec fr₁.env mem₁ ctx₁ with
                                | none => rw [hst] at hx1; rw [hx1] at hst1; cases hst1
                                | some res1 =>
                                    rcases res1 with ⟨ρ₁', mem'⟩
                                    rw [hst] at hx1; rw [hx1] at hst1; simp only [Step.next.injEq] at hst1
                                    obtain ⟨rfl, rfl⟩ := hst1
                                    have hnc : (B.body[fr₁.pos]'hltBody).isCall = false := by rw [hst]; rfl
                                    have hst2 := step_stmt (mem := mem₁) (ctx := ctx₁) (rest := rest₂) hqF0 hB hltBody rfl hnc (by rw [hst]; exact hx1)
                                    left
                                    exact ⟨0, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                      .cons (.normal ⟨rfl, rfl, by simp [hfn]⟩) hrest⟩
                          · simp only [hltBody, ↓reduceDIte] at hst1
                            cases ht : B.term with
                            | jump e =>
                                rw [ht] at hst1; dsimp only at hst1
                                unfold takeEdge at hst1
                                cases htb : F0.blocks[e.target]? with
                                | none => rw [htb] at hst1; cases hvs : evalArgs fr₁.env e.args <;> rw [hvs] at hst1 <;> cases hst1
                                | some tBlk =>
                                    rw [htb] at hst1
                                    cases hvs : evalArgs fr₁.env e.args with
                                    | none => rw [hvs] at hst1; cases hst1
                                    | some vs =>
                                        rw [hvs] at hst1; dsimp only at hst1
                                        cases hbp : bindParams fr₁.env tBlk.params vs with
                                        | none => rw [hbp] at hst1; cases hst1
                                        | some ρ₁' =>
                                            rw [hbp] at hst1; simp only [Step.next.injEq] at hst1
                                            obtain ⟨rfl, rfl⟩ := hst1
                                            have hst2 := step_jump_ge (mem := mem₁) (ctx := ctx₁) (rest := rest₂) hqF0 hB hltBody ht
                                            rw [takeEdge_ok hvs htb hbp] at hst2
                                            left; exact ⟨_, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                              .cons (.normal ⟨rfl, rfl, by simp [hfn]⟩) hrest⟩
                            | br c0 w0 a0 b0 e1 e2 =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases ha1 : a0.eval fr₁.env with
                                | none => rw [ha1] at hst1; cases hst1
                                | some va =>
                                    rw [ha1] at hst1
                                    cases hb1 : b0.eval fr₁.env with
                                    | none => rw [hb1] at hst1; cases hst1
                                    | some vb =>
                                        rw [hb1] at hst1; dsimp only at hst1
                                        let eChosen := if c0.holds w0 va vb then e1 else e2
                                        unfold takeEdge at hst1
                                        cases htb : F0.blocks[eChosen.target]? with
                                        | none => rw [htb] at hst1; cases hvs : evalArgs fr₁.env eChosen.args <;> rw [hvs] at hst1 <;> cases hst1
                                        | some tBlk =>
                                            rw [htb] at hst1
                                            cases hvs : evalArgs fr₁.env eChosen.args with
                                            | none => rw [hvs] at hst1; cases hst1
                                            | some vs =>
                                                rw [hvs] at hst1; dsimp only at hst1
                                                cases hbp : bindParams fr₁.env tBlk.params vs with
                                                | none => rw [hbp] at hst1; cases hst1
                                                | some ρ₁' =>
                                                    rw [hbp] at hst1; simp only [Step.next.injEq] at hst1
                                                    obtain ⟨rfl, rfl⟩ := hst1
                                                    have hst2 := step_br_ge (mem := mem₁) (ctx := ctx₁) (rest := rest₂) hqF0 hB hltBody ht ha1 hb1
                                                    rw [takeEdge_ok hvs htb hbp] at hst2
                                                    left; exact ⟨_, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                                      .cons (.normal ⟨rfl, rfl, by simp [hfn, eChosen]⟩) hrest⟩
                            | brOvf o0 x0 a0 b0 okE ovfE =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases ha1 : a0.eval fr₁.env with
                                | none => rw [ha1] at hst1; cases hst1
                                | some va =>
                                    rw [ha1] at hst1
                                    cases hb1 : b0.eval fr₁.env with
                                    | none => rw [hb1] at hst1; cases hst1
                                    | some vb =>
                                        rw [hb1] at hst1; dsimp only at hst1
                                        have hst2 := step_brOvf_ge (mem := mem₁) (ctx := ctx₁) (rest := rest₂) hqF0 hB hltBody ht ha1 hb1
                                        cases hov : (o0.eval va vb).2 with
                                        | true =>
                                            rw [hov] at hst1 hst2; simp only [↓reduceIte] at hst1 hst2
                                            unfold takeEdge at hst1
                                            cases htb : F0.blocks[ovfE.target]? with
                                            | none => rw [htb] at hst1; cases hvs : evalArgs (fr₁.env.insert x0 (o0.eval va vb).1) ovfE.args <;> rw [hvs] at hst1 <;> cases hst1
                                            | some tBlk =>
                                                rw [htb] at hst1
                                                cases hvs : evalArgs (fr₁.env.insert x0 (o0.eval va vb).1) ovfE.args with
                                                | none => rw [hvs] at hst1; cases hst1
                                                | some vs =>
                                                    rw [hvs] at hst1; dsimp only at hst1
                                                    cases hbp : bindParams (fr₁.env.insert x0 (o0.eval va vb).1) tBlk.params vs with
                                                    | none => rw [hbp] at hst1; cases hst1
                                                    | some ρ₁' =>
                                                        rw [hbp] at hst1; simp only [Step.next.injEq] at hst1
                                                        obtain ⟨rfl, rfl⟩ := hst1
                                                        rw [takeEdge_ok hvs htb hbp] at hst2
                                                        left; exact ⟨_, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                                          .cons (.normal ⟨rfl, rfl, by simp [hfn]⟩) hrest⟩
                                        | false =>
                                            rw [hov] at hst1 hst2; simp only [Bool.false_eq_true, ↓reduceIte] at hst1 hst2
                                            unfold takeEdge at hst1
                                            cases htb : F0.blocks[okE.target]? with
                                            | none => rw [htb] at hst1; cases hvs : evalArgs (fr₁.env.insert x0 (o0.eval va vb).1) okE.args <;> rw [hvs] at hst1 <;> cases hst1
                                            | some tBlk =>
                                                rw [htb] at hst1
                                                cases hvs : evalArgs (fr₁.env.insert x0 (o0.eval va vb).1) okE.args with
                                                | none => rw [hvs] at hst1; cases hst1
                                                | some vs =>
                                                    rw [hvs] at hst1; dsimp only at hst1
                                                    cases hbp : bindParams (fr₁.env.insert x0 (o0.eval va vb).1) tBlk.params vs with
                                                    | none => rw [hbp] at hst1; cases hst1
                                                    | some ρ₁' =>
                                                        rw [hbp] at hst1; simp only [Step.next.injEq] at hst1
                                                        obtain ⟨rfl, rfl⟩ := hst1
                                                        rw [takeEdge_ok hvs htb hbp] at hst2
                                                        left; exact ⟨_, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                                          .cons (.normal ⟨rfl, rfl, by simp [hfn]⟩) hrest⟩
                            | ret as =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases hvs : evalArgs fr₁.env as with
                                | none => rw [hvs] at hst1; cases hst1
                                | some vs =>
                                    rw [hvs] at hst1; dsimp only at hst1
                                    cases hrest with
                                    | nil => cases hst1
                                    | @cons c₁ c₂ cr₁ cr₂ hcallRel hcr =>
                                        dsimp only at hst1
                                        cases hbp : bindParams c₁.env c₁.dsts vs with
                                        | none => rw [hbp] at hst1; cases hst1
                                        | some ρc₁' =>
                                            rw [hbp] at hst1; simp only [Step.next.injEq] at hst1
                                            obtain ⟨rfl, rfl⟩ := hst1
                                            by_cases hcfn : c₁.fn = fi
                                            · have hcb := hcallRel.bodyEq; simp only [hcfn, ↓reduceIte] at hcb
                                              obtain ⟨hclbl, hcpos, hcNT, hcNF, hcag, hcfp, hcbInv⟩ := hcb
                                              obtain ⟨ρc₂', hbp2, hcag', hdstDef⟩ := bindParams_agreeOuter hcag hbp
                                              have hst2 := step_ret_caller_ge (mem := mem₁) (ctx := ctx₁) (caller := c₂) (rest' := cr₂) hqF0 hB hltBody ht hvs (by rw [hcallRel.dstsEq]; exact hbp2)
                                              left
                                              refine ⟨0, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                                .cons (.normal ⟨hcallRel.fnEq, rfl, ?_⟩) hcr⟩
                                              simp only [hcfn, ↓reduceIte, hclbl, hcpos, hcNT, hcNF, hcag', true_and]
                                              refine ⟨fun x hx => bindParams_preserves_isSome hbp x (hcfp x hx), fun hclb => ?_⟩
                                              obtain ⟨hcposLe, hcbp, hcbody, hclast⟩ := hcbInv hclb
                                              refine ⟨hcposLe, fun x hx => bindParams_preserves_isSome hbp x (hcbp x hx), fun i hi st' hst' x hx => ?_, fun h => by cases h⟩
                                              by_cases hilt : i < c₁.pos - 1
                                              · exact bindParams_preserves_isSome hbp x (hcbody i hilt st' hst' x hx)
                                              · have hcpos_gt : c₁.pos > 0 := by omega
                                                have hieq : i = c₁.pos - 1 := by omega
                                                subst hieq
                                                obtain ⟨huses, hdefs⟩ := hclast trivial hcpos_gt st' hst'
                                                simp only [List.mem_append] at hx
                                                rcases hx with hu | hd
                                                · exact bindParams_preserves_isSome hbp x (huses x hu)
                                                · rw [hdefs] at hd; exact hdstDef x hd
                                            · have hcb := hcallRel.bodyEq; simp only [hcfn, ↓reduceIte] at hcb
                                              obtain ⟨hclbl, hcpos, hcenv⟩ := hcb
                                              have hst2 := step_ret_caller_ge (mem := mem₁) (ctx := ctx₁) (caller := c₂) (rest' := cr₂) hqF0 hB hltBody ht hvs (by rw [hcallRel.dstsEq, hcenv]; exact hbp)
                                              left
                                              refine ⟨0, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                                .cons (.normal ⟨hcallRel.fnEq, rfl, ?_⟩) hcr⟩
                                              simp only [hcfn, ↓reduceIte]; exact ⟨hclbl, hcpos, trivial⟩
                            | tail g as =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases htl : (evalArgs fr₁.env as >>= enter p g) with
                                | none => rw [htl] at hst1; cases hst1
                                | some callee₁ =>
                                    rw [htl] at hst1; simp only [Step.next.injEq] at hst1
                                    obtain ⟨rfl, rfl⟩ := hst1
                                    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at htl
                                    obtain ⟨vs, hvs, hent₁⟩ := htl
                                    obtain ⟨callee₂, hent₂, hcalleeRel⟩ := ifConv_enter_rel d u hent₁
                                    have hst2 := step_tail_ge (mem := mem₁) (ctx := ctx₁) (rest := rest₂) hqF0 hB hltBody ht hvs hent₂
                                    left; exact ⟨1, _, star_of_step hst2, Nat.le_refl _, rfl, rfl,
                                      .cons (.normal hcalleeRel) hrest⟩
                            | fail _ | trap => rw [ht] at hst1; cases hst1
            | inArm hia =>
                -- `p` is stepping inside the taken diamond arm while `q` is parked at `(b, d.blk.body.size)`!
                have hverTaken : verifyArmMatches d.F b (if hia.condVal then d.eT.target else d.eF.target)
                    d.armT.join (d.armT.failRes?.orElse fun _ => d.armF.failRes?)
                    (if hia.condVal then d.armT else d.armF) = true := by
                  cases hcv : hia.condVal <;> simp only [↓reduceIte, Bool.false_eq_true, u.verT, u.verF]
                have hltStart : b < (if hia.condVal then d.eT.target else d.eF.target) := by
                  cases hcv : hia.condVal <;> simp only [↓reduceIte, Bool.false_eq_true, u.bLtT, u.bLtF]
                have hpureTaken : checkArmPure (if hia.condVal then d.armT else d.armF)
                    (if hia.condVal then d.armT else d.armF).defs = true := by
                  cases hcv : hia.condVal <;> simp only [↓reduceIte, Bool.false_eq_true, u.pureT, u.pureF]
                have hvg := hverTaken; unfold verifyArmMatches at hvg
                simp only [Bool.and_eq_true] at hvg
                rw [hia.hStepsEq] at hvg
                obtain ⟨hbLtCur, curBlk, hcurB, hcurPar, hcurBody, hremInfo⟩ :=
                  verifyArmMatches_step_at hltStart hvg.2
                -- Every stmt in `hia.curStep.body` is hoistable (non-call, pure)!
                have hcurHoist : hia.curStep.body.all isHoistableStmt = true := by
                  have hgo : ∀ (arm : DiamondArm) (steps : List ArmStep) (av : Src.NatSet),
                      checkArmPure.go arm arm.defs av steps = true →
                      ∀ st ∈ steps, st.body.all isHoistableStmt = true := by
                    intro arm steps; induction steps with
                    | nil => intro _ _ _ h; cases h
                    | cons s0 rs ihs =>
                        intro av h st hst
                        simp only [checkArmPure.go] at h
                        split at h
                        · cases h
                        · rename_i hho
                          have hho' : s0.body.all isHoistableStmt = true := by simpa using hho
                          simp only [List.mem_cons] at hst
                          rcases hst with rfl | hmem
                          · exact hho'
                          · cases hck : checkStmtsAvail _ av s0.body with
                            | none => rw [hck] at h; cases h
                            | some av1 =>
                                rw [hck] at h; dsimp only at h
                                cases hov : s0.ovf? with
                                | none => rw [hov] at h; exact ihs av1 h st hmem
                                | some tup =>
                                    rw [hov] at h; dsimp only at h
                                    split at h
                                    · exact ihs _ h st hmem
                                    · cases h
                  exact hgo _ _ .leaf hpureTaken hia.curStep (by rw [hia.hStepsEq]; simp)
                unfold step at hst1; dsimp only at hst1
                rw [hia.fn1, d.hF] at hst1; dsimp only at hst1; rw [hia.hLbl1, hcurB] at hst1; dsimp only at hst1
                by_cases hltBody : fr₁.pos < curBlk.body.size
                · -- Pure statement step inside `curStep.body`: `q` stays parked (0 steps)!
                  simp only [hltBody, ↓reduceDIte] at hst1
                  have hltLen : fr₁.pos < hia.curStep.body.length := by
                    rw [← hcurBody]; simpa using hltBody
                  have hsMem : curBlk.body[fr₁.pos]'hltBody ∈ hia.curStep.body := by
                    rw [← hcurBody]; exact Array.mem_toList_iff.2 (Array.getElem_mem hltBody)
                  have hsHoist : isHoistableStmt (curBlk.body[fr₁.pos]'hltBody) = true :=
                    (List.all_eq_true.1 hcurHoist) _ hsMem
                  have hgetEq : hia.curStep.body[fr₁.pos]'hltLen = curBlk.body[fr₁.pos]'hltBody := by
                    have h1 : hia.curStep.body[fr₁.pos]? = curBlk.body.toList[fr₁.pos]? := by rw [hcurBody]
                    rw [List.getElem?_eq_getElem hltLen, Array.getElem?_toList, Array.getElem?_eq_getElem hltBody] at h1
                    exact Option.some.inj h1
                  cases hst : curBlk.body[fr₁.pos]'hltBody with
                  | store _ _ _ | call _ _ _ => rw [hst] at hsHoist; simp [isHoistableStmt] at hsHoist
                  | assign _ _ | limb _ _ _ =>
                      rw [hst] at hst1; dsimp only at hst1
                      cases hx1 : (curBlk.body[fr₁.pos]'hltBody).exec fr₁.env mem₁ ctx₁ with
                      | none => rw [hst] at hx1; rw [hx1] at hst1; cases hst1
                      | some res1 =>
                          rcases res1 with ⟨ρ₁', mem'⟩
                          rw [hst] at hx1; rw [hx1] at hst1; simp only [Step.next.injEq] at hst1
                          obtain ⟨rfl, rfl⟩ := hst1
                          have hmemEq : mem' = mem₁ := by
                            simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx1
                            obtain ⟨_, _, _, rfl⟩ := hx1; rfl
                          subst mem'
                          rw [← hst] at hx1
                          have htakeNext : hia.curStep.body.take (fr₁.pos + 1) =
                              hia.curStep.body.take fr₁.pos ++ [curBlk.body[fr₁.pos]'hltBody] := by
                            rw [List.take_add_one, List.getElem?_eq_getElem hltLen, Option.toList_some, hgetEq]
                          have hcurRun' : execList hia.ρStepEntry mem₁ ctx₁ (hia.curStep.body.take (fr₁.pos + 1)) =
                              some (ρ₁', mem₁) := by
                            rw [htakeNext]
                            exact execList_append_ifconv hia.hCurRun (by simp [execList, hx1])
                          left
                          exact ⟨0, { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ }, Sem.Star.refl _, Nat.le_refl _, rfl, rfl,
                            .cons (.inArm ⟨rfl, hia.fn2, hia.dstsEq, hia.lbl2, hia.pos2,
                              hia.condVal, hia.ρ₁₀, hia.va, hia.vb, hia.ha, hia.hb, hia.hcond,
                              hia.hAgree0, hia.hFParams, hia.hBParams, hia.hBBody,
                              hia.preSteps, hia.curStep, hia.remSteps, hia.hStepsEq,
                              rfl, Nat.succ_le_of_lt hltLen, hia.ρStepEntry, hia.hPreRun, hcurRun'⟩) hrest⟩
                · -- End of `curStep.body`: either intermediate `brOvf` or final `jump join`!
                  simp only [hltBody, ↓reduceDIte] at hst1
                  have hposEqLen : fr₁.pos = hia.curStep.body.length := by
                    have hsz : curBlk.body.size = hia.curStep.body.length := by
                      rw [← hcurBody]; simp
                    have := hia.hPosLe; omega
                  have hbodyFull : execList hia.ρStepEntry mem₁ ctx₁ hia.curStep.body = some (fr₁.env, mem₁) := by
                    have h := hia.hCurRun; rw [hposEqLen, List.take_length] at h; exact h
                  cases hrem : hia.remSteps with
                  | nil =>
                      -- Final `jump join` of the taken arm! Synchronize `q` now!
                      rw [hrem] at hremInfo
                      obtain ⟨hjb, hovNone, hcurTerm⟩ := hremInfo
                      rw [hcurTerm] at hst1; dsimp only at hst1
                      unfold takeEdge at hst1
                      cases hjB : d.F.blocks[d.armT.join]? with
                      | none => rw [hjB] at hst1; cases hvs : evalArgs fr₁.env (if hia.condVal then d.armT else d.armF).joinArgs <;> rw [hvs] at hst1 <;> cases hst1
                      | some jBlk =>
                          rw [hjB] at hst1
                          cases hvs : evalArgs fr₁.env (if hia.condVal then d.armT else d.armF).joinArgs with
                          | none => rw [hvs] at hst1; cases hst1
                          | some vs =>
                              rw [hvs] at hst1; dsimp only at hst1
                              cases hbp : bindParams fr₁.env jBlk.params vs with
                              | none => rw [hbp] at hst1; cases hst1
                              | some ρ₁Join =>
                                  rw [hbp] at hst1; simp only [Step.next.injEq] at hst1
                                  obtain ⟨rfl, rfl⟩ := hst1
                                  have hrunFull : runArmConcrete mem₁ ctx₁
                                      (if hia.condVal then d.armT else d.armF).steps hia.ρ₁₀ = some (.inr fr₁.env) := by
                                    rw [hia.hStepsEq, hrem]
                                    apply runArmConcrete_append hia.hPreRun
                                    simp [runArmConcrete, hbodyFull, hovNone]
                                  have hsync := ifConv_speculative_sync d u (rest₂ := rest₂) hia hrunFull hvs hjB hbp
                                  obtain ⟨c₂, ρ₂Join, hc₂Eq, hstar2, hAgreeJoin⟩ := hsync
                                  have hchgMatch : (decide (d.armT.join ≤ fr₁.label)).toNat ≤ c₂ := by
                                    rw [hc₂Eq, hia.hLbl1]
                                    rcases hjb with hleB | hltJ
                                    · have h1 : decide (d.armT.join ≤ b) = true := decide_eq_true hleB
                                      rw [h1]; cases decide (d.armT.join ≤ hia.curStep.label) <;> decide
                                    · have h1 : decide (d.armT.join ≤ hia.curStep.label) = false := decide_eq_false (Nat.not_le.2 hltJ)
                                      rw [h1]; exact Nat.zero_le _
                                  -- `ρ₁Join` still defines `d.F.params` (and `d.blk.params` if `join = b`)!
                                  have hEndFParams : ∀ x ∈ d.F.params, fr₁.env[x]?.isSome = true := by
                                    have hp := runArmConcrete_preserves_nonDefs
                                      (armDefs := (if hia.condVal then d.armT else d.armF).defs)
                                      (by
                                        cases hcv : hia.condVal <;> simp only [↓reduceIte, Bool.false_eq_true]
                                        · have hrf := (arm_step_regs_and_outer d u false).1
                                          exact fun st hst => ⟨fun s hs r hr => (hrf st hst).1 s hs r hr |>.1,
                                            fun o y oa ob r hov => (hrf st hst).2 o y oa ob r hov |>.1⟩
                                        · have hrt := (arm_step_regs_and_outer d u true).1
                                          exact fun st hst => ⟨fun s hs r hr => (hrt st hst).1 s hs r hr |>.1,
                                            fun o y oa ob r hov => (hrt st hst).2 o y oa ob r hov |>.1⟩)
                                      hrunFull
                                    exact fun x hx => hp.2 x (hia.hFParams x hx)
                                  obtain ⟨_, _, _, hjParDef⟩ := bindParams_agreeOuter
                                    (envAgreeOuter_refl d.off d.armT.defs d.armF.defs fr₁.env) hbp
                                  left
                                  refine ⟨c₂, _, hstar2, hchgMatch, rfl, rfl,
                                    .cons (.normal ⟨by simp [hia.fn1, hia.fn2], hia.dstsEq, ?_⟩) hrest⟩
                                  simp only [hia.fn1, ↓reduceIte, u.joinNotT, u.joinNotF, hAgreeJoin, true_and]
                                  refine ⟨fun x hx => bindParams_preserves_isSome hbp x (hEndFParams x hx), fun hjbEq => ?_⟩
                                  rw [hjbEq, d.hb] at hjB; cases hjB
                                  exact ⟨Nat.zero_le _, hjParDef, fun i hi => by omega, fun h => by cases h⟩
                  | cons nxt tail =>
                      -- Intermediate `brOvf`: no-overflow advances `InArmFrame`, overflow discharges via `Sem.Fails`!
                      rw [hrem] at hremInfo
                      obtain ⟨hcn, o, x, oa, ob, res, ovfEdge, hovSome, hcr, hcurTerm, hfailE⟩ := hremInfo
                      rw [hcurTerm] at hst1; dsimp only at hst1
                      cases hoa : oa.eval fr₁.env with
                      | none => rw [hoa] at hst1; cases hst1
                      | some voa =>
                          rw [hoa] at hst1
                          cases hob : ob.eval fr₁.env with
                          | none => rw [hob] at hst1; cases hst1
                          | some vob =>
                              rw [hob] at hst1; dsimp only at hst1
                              cases hovf : (o.eval voa vob).2 with
                              | true =>
                                  -- Overflow! `runArmConcrete` returns `.inl res`, so `q` satisfies `Sem.Fails`!
                                  have hrunFail : runArmConcrete mem₁ ctx₁
                                      (if hia.condVal then d.armT else d.armF).steps hia.ρ₁₀ = some (.inl res) := by
                                    rw [hia.hStepsEq, hrem]
                                    apply runArmConcrete_append hia.hPreRun
                                    simp [runArmConcrete, hbodyFull, hovSome, hoa, hob, hovf]
                                  exact .inr (ifConv_speculative_sync d u (rest₂ := rest₂) hia hrunFail)
                              | false =>
                                  -- No overflow! `p` jumps forward (0 charges) to `nxt`, `q` stays parked (0 steps)!
                                  rw [hovf] at hst1; simp only [Bool.false_eq_true, ↓reduceIte] at hst1
                                  have hvg2 := hverTaken; unfold verifyArmMatches at hvg2
                                  simp only [Bool.and_eq_true] at hvg2
                                  have hsplit : (if hia.condVal then d.armT else d.armF).steps =
                                      (hia.preSteps ++ [hia.curStep]) ++ nxt :: tail := by
                                    rw [hia.hStepsEq, hrem]; simp [List.append_assoc]
                                  rw [hsplit] at hvg2
                                  obtain ⟨_, nxtBlk, hnxtB, hnxtPar, _, _⟩ := verifyArmMatches_step_at hltStart hvg2.2
                                  have hte := takeEdge_ok (F := d.F) (s := { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ }) (fr := fr₁)
                                    (rest := rest₁) (ρ := fr₁.env.insert x (o.eval voa vob).1)
                                    (e := { target := nxt.label, args := [] })
                                    rfl hnxtB (by rw [hnxtPar]; rfl)
                                  rw [hte] at hst1; simp only [Step.next.injEq] at hst1
                                  obtain ⟨rfl, rfl⟩ := hst1
                                  have hchgF : decide (nxt.label ≤ fr₁.label) = false := by
                                    rw [hia.hLbl1]; exact decide_eq_false (Nat.not_le.2 hcn)
                                  rw [hchgF]
                                  have hpreRun' : runArmConcrete mem₁ ctx₁ (hia.preSteps ++ [hia.curStep]) hia.ρ₁₀ =
                                      some (.inr (fr₁.env.insert x (o.eval voa vob).1)) := by
                                    apply runArmConcrete_append hia.hPreRun
                                    simp [runArmConcrete, hbodyFull, hovSome, hoa, hob, hovf]
                                  left
                                  exact ⟨0, { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ }, Sem.Star.refl _, Nat.le_refl _, rfl, rfl,
                                    .cons (.inArm ⟨hia.fn1, hia.fn2, hia.dstsEq, hia.lbl2, hia.pos2,
                                      hia.condVal, hia.ρ₁₀, hia.va, hia.vb, hia.ha, hia.hb, hia.hcond,
                                      hia.hAgree0, hia.hFParams, hia.hBParams, hia.hBBody,
                                      hia.preSteps ++ [hia.curStep], nxt, tail, hsplit,
                                      rfl, Nat.zero_le _, fr₁.env.insert x (o.eval voa vob).1, hpreRun', rfl⟩) hrest⟩
  · -- `final`: `done` / `fail` / `trap` (non-stuck!)
    intro s₁ s₂ r hrel hfin hne
    rcases s₁ with ⟨mem₁, ctx₁, stk₁⟩
    rcases s₂ with ⟨mem₂, ctx₂, stk₂⟩
    obtain ⟨hmem, hctx, hstk⟩ := hrel
    dsimp only at hmem hctx hstk
    subst mem₂; subst ctx₂
    cases hstk with
    | nil =>
        simp [semStep, step, Step.toSem] at hfin
        cases hfin; exact absurd rfl hne
    | @cons fr₁ fr₂ rest₁ rest₂ htop hrest =>
        cases htop with
        | inArm hia =>
            -- Inside `InArmFrame`, every arm block ends in `.jump` or `.brOvf` (never `ret`/`fail`/`trap`)!
            have hverTaken : verifyArmMatches d.F b (if hia.condVal then d.eT.target else d.eF.target)
                d.armT.join (d.armT.failRes?.orElse fun _ => d.armF.failRes?)
                (if hia.condVal then d.armT else d.armF) = true := by
              cases hcv : hia.condVal <;> simp only [↓reduceIte, Bool.false_eq_true, u.verT, u.verF]
            have hltStart : b < (if hia.condVal then d.eT.target else d.eF.target) := by
              cases hcv : hia.condVal <;> simp only [↓reduceIte, Bool.false_eq_true, u.bLtT, u.bLtF]
            have hvg := hverTaken; unfold verifyArmMatches at hvg
            simp only [Bool.and_eq_true] at hvg; rw [hia.hStepsEq] at hvg
            obtain ⟨_, curBlk, hcurB, _, _, hremInfo⟩ := verifyArmMatches_step_at hltStart hvg.2
            cases hst1 : step p { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } with
            | next _ _ => rw [semStep, hst1] at hfin; cases hfin
            | stuck => rw [semStep, hst1] at hfin; cases hfin; exact absurd rfl hne
            | done _ _ | fail _ | trap =>
                unfold step at hst1; dsimp only at hst1
                rw [hia.fn1, d.hF] at hst1; dsimp only at hst1; rw [hia.hLbl1, hcurB] at hst1; dsimp only at hst1
                split at hst1
                · split at hst1 <;> (split at hst1 <;> cases hst1)
                · cases hrem : hia.remSteps with
                  | nil =>
                      rw [hrem] at hremInfo
                      rw [hremInfo.2.2] at hst1; dsimp only at hst1
                      unfold takeEdge at hst1
                      repeat (split at hst1 <;> try cases hst1)
                  | cons nxt tail =>
                      rw [hrem] at hremInfo
                      obtain ⟨_, _, _, _, _, _, _, _, _, hct, _⟩ := hremInfo
                      rw [hct] at hst1; dsimp only at hst1
                      repeat (split at hst1 <;> try cases hst1)
                      all_goals (try unfold takeEdge at hst1; repeat (split at hst1 <;> try cases hst1))
        | normal hnorm =>
            by_cases hfn : fr₁.fn = fi
            · have hbody := hnorm.bodyEq; simp only [hfn, ↓reduceIte] at hbody
              obtain ⟨hlbl, hpos, hNT, hNF, hag, _, _⟩ := hbody
              have hfn2 : fr₂.fn = fi := by rw [hnorm.fnEq, hfn]
              cases hst1 : step p { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } with
              | next _ _ => rw [semStep, hst1] at hfin; cases hfin
              | stuck => rw [semStep, hst1] at hfin; cases hfin; exact absurd rfl hne
              | done vals mem1 =>
                  rw [semStep, hst1] at hfin; cases hfin
                  unfold step at hst1; dsimp only at hst1; rw [hfn, d.hF] at hst1; dsimp only at hst1
                  cases hB : d.F.blocks[fr₁.label]? with
                  | none => rw [hB] at hst1; cases hst1
                  | some B =>
                      rw [hB] at hst1; dsimp only at hst1
                      by_cases hltBody : fr₁.pos < B.body.size
                      · simp only [hltBody, ↓reduceDIte] at hst1
                        split at hst1 <;> (split at hst1 <;> cases hst1)
                      · simp only [hltBody, ↓reduceDIte] at hst1
                        have hlb : fr₁.label ≠ b := by
                          intro heq; rw [heq, d.hb] at hB; cases hB; rw [d.hTerm] at hst1; dsimp only at hst1
                          split at hst1 <;> try cases hst1
                          unfold takeEdge at hst1; repeat (split at hst1 <;> try cases hst1)
                        have hGo := ifConv_G_blocks_other d hB hlb
                        cases ht : B.term with
                        | ret as =>
                            rw [ht] at hst1; dsimp only at hst1
                            cases hvs : evalArgs fr₁.env as with
                            | none => rw [hvs] at hst1; cases hst1
                            | some vs =>
                                rw [hvs] at hst1; dsimp only at hst1
                                cases hrest with
                                | nil =>
                                    simp only [Step.done.injEq] at hst1; obtain ⟨rfl, rfl⟩ := hst1
                                    have hvs2 := ifConv_outer_evalArgs hag
                                      (fun a0 ha0 x hx => u.outsideUses fr₁.label B hB hNT hNF x
                                        (by simp only [List.mem_append]; left; right; rw [ht]
                                            simp only [Term.uses, argsUses, List.mem_flatMap]; exact ⟨a0, ha0, hx⟩)) hvs
                                    have hst2 := step_ret_done_ge (p := q) (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (F := d.G)
                                      (B := { B with term := B.term.setEdges (B.term.edges.map fun e => { e with target := ifConvRemap b hasG e.target }) })
                                      (by rw [hfn2]; exact d.hG) (by rw [hlbl]; exact hGo)
                                      (by rw [hpos]; exact hltBody) (by dsimp only; rw [ht]; rfl) hvs2
                                    exact .inl ⟨0, _, .ok (vs, mem₁), Sem.Star.refl _,
                                      by rw [semStep_done.2 hst2]; exact .done, .ok rfl⟩
                                | cons _ _ => dsimp only at hst1; split at hst1 <;> cases hst1
                        | tail g as =>
                            rw [ht] at hst1; dsimp only at hst1
                            cases h : evalArgs fr₁.env as >>= enter p g <;> rw [h] at hst1 <;> cases hst1
                        | jump _ | br _ _ _ _ _ _ | brOvf _ _ _ _ _ _ | fail _ | trap =>
                            rw [ht] at hst1; dsimp only at hst1; try cases hst1; repeat (split at hst1 <;> try cases hst1)
                            all_goals (try unfold takeEdge at hst1; repeat (split at hst1 <;> try cases hst1))
              | fail res =>
                  rw [semStep, hst1] at hfin; cases hfin
                  unfold step at hst1; dsimp only at hst1; rw [hfn, d.hF] at hst1; dsimp only at hst1
                  cases hB : d.F.blocks[fr₁.label]? with
                  | none => rw [hB] at hst1; cases hst1
                  | some B =>
                      rw [hB] at hst1; dsimp only at hst1
                      by_cases hltBody : fr₁.pos < B.body.size
                      · simp only [hltBody, ↓reduceDIte] at hst1
                        split at hst1 <;> (split at hst1 <;> cases hst1)
                      · simp only [hltBody, ↓reduceDIte] at hst1
                        have hlb : fr₁.label ≠ b := by
                          intro heq; rw [heq, d.hb] at hB; cases hB; rw [d.hTerm] at hst1; dsimp only at hst1
                          split at hst1 <;> try cases hst1
                          unfold takeEdge at hst1; repeat (split at hst1 <;> try cases hst1)
                        have hGo := ifConv_G_blocks_other d hB hlb
                        cases ht : B.term with
                        | fail r0 =>
                            rw [ht] at hst1; dsimp only at hst1; cases hst1
                            have hst2 := step_fail_ge (p := q) (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂) (F := d.G)
                              (B := { B with term := B.term.setEdges (B.term.edges.map fun e => { e with target := ifConvRemap b hasG e.target }) })
                              (by rw [hfn2]; exact d.hG) (by rw [hlbl]; exact hGo)
                              (by rw [hpos]; exact hltBody) (by dsimp only; rw [ht]; rfl)
                            exact .inl ⟨0, _, .resource res, Sem.Star.refl _, by rw [semStep_fail.2 hst2]; exact .fail, .resource res⟩
                        | tail g as =>
                            rw [ht] at hst1; dsimp only at hst1
                            cases h : evalArgs fr₁.env as >>= enter p g <;> rw [h] at hst1 <;> cases hst1
                        | ret as =>
                            rw [ht] at hst1; dsimp only at hst1
                            cases h : evalArgs fr₁.env as with
                            | none => rw [h] at hst1; cases hst1
                            | some vs =>
                                rw [h] at hst1; dsimp only at hst1
                                cases rest₁ with
                                | nil => cases hst1
                                | cons c _ => dsimp only at hst1; cases hb : bindParams c.env c.dsts vs <;> rw [hb] at hst1 <;> cases hst1
                        | jump _ | br _ _ _ _ _ _ | brOvf _ _ _ _ _ _ | trap =>
                            rw [ht] at hst1; dsimp only at hst1; try cases hst1; repeat (split at hst1 <;> try cases hst1)
                            all_goals (try unfold takeEdge at hst1; repeat (split at hst1 <;> try cases hst1))
              | trap =>
                  rw [semStep, hst1] at hfin; cases hfin
                  unfold step at hst1; dsimp only at hst1; rw [hfn, d.hF] at hst1; dsimp only at hst1
                  cases hB : d.F.blocks[fr₁.label]? with
                  | none => rw [hB] at hst1; cases hst1
                  | some B =>
                      rw [hB] at hst1; dsimp only at hst1
                      by_cases hltBody : fr₁.pos < B.body.size
                      · simp only [hltBody, ↓reduceDIte] at hst1
                        split at hst1 <;> (split at hst1 <;> cases hst1)
                      · simp only [hltBody, ↓reduceDIte] at hst1
                        have hlb : fr₁.label ≠ b := by
                          intro heq; rw [heq, d.hb] at hB; cases hB; rw [d.hTerm] at hst1; dsimp only at hst1
                          split at hst1 <;> try cases hst1
                          unfold takeEdge at hst1; repeat (split at hst1 <;> try cases hst1)
                        have hGo := ifConv_G_blocks_other d hB hlb
                        cases ht : B.term with
                        | trap =>
                            have hst2 := step_trap_ge (p := q) (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂) (F := d.G)
                              (B := { B with term := B.term.setEdges (B.term.edges.map fun e => { e with target := ifConvRemap b hasG e.target }) })
                              (by rw [hfn2]; exact d.hG) (by rw [hlbl]; exact hGo)
                              (by rw [hpos]; exact hltBody) (by dsimp only; rw [ht]; rfl)
                            exact .inl ⟨0, _, .trap, Sem.Star.refl _, by rw [semStep_trap.2 hst2]; exact .trap, .trap⟩
                        | tail g as =>
                            rw [ht] at hst1; dsimp only at hst1
                            cases h : evalArgs fr₁.env as >>= enter p g <;> rw [h] at hst1 <;> cases hst1
                        | ret as =>
                            rw [ht] at hst1; dsimp only at hst1
                            cases h : evalArgs fr₁.env as with
                            | none => rw [h] at hst1; cases hst1
                            | some vs =>
                                rw [h] at hst1; dsimp only at hst1
                                cases rest₁ with
                                | nil => cases hst1
                                | cons c _ => dsimp only at hst1; cases hb : bindParams c.env c.dsts vs <;> rw [hb] at hst1 <;> cases hst1
                        | jump _ | br _ _ _ _ _ _ | brOvf _ _ _ _ _ _ | fail _ =>
                            rw [ht] at hst1; dsimp only at hst1; try cases hst1; repeat (split at hst1 <;> try cases hst1)
                            all_goals (try unfold takeEdge at hst1; repeat (split at hst1 <;> try cases hst1))
            · -- `fr₁.fn ≠ fi`
              have hbody := hnorm.bodyEq; simp only [hfn, ↓reduceIte] at hbody
              obtain ⟨hlbl, hpos, henv⟩ := hbody
              have hfrEq : fr₂ = fr₁ := by
                cases fr₁; cases fr₂; simp only [Frame.mk.injEq]
                exact ⟨hnorm.fnEq, hlbl, hpos, henv, hnorm.dstsEq⟩
              subst fr₂
              cases hst1 : step p { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } with
              | next _ _ => rw [semStep, hst1] at hfin; cases hfin
              | stuck => rw [semStep, hst1] at hfin; cases hfin; exact absurd rfl hne
              | done vals mem1 =>
                  rw [semStep, hst1] at hfin; cases hfin
                  unfold step at hst1; dsimp only at hst1
                  cases hF0 : p.funcs[fr₁.fn]? with
                  | none => rw [hF0] at hst1; cases hst1
                  | some F0 =>
                      rw [hF0] at hst1; dsimp only at hst1
                      have hqF0 : q.funcs[fr₁.fn]? = some F0 := by rw [d.hOtherF fr₁.fn hfn, hF0]
                      cases hB : F0.blocks[fr₁.label]? with
                      | none => rw [hB] at hst1; cases hst1
                      | some B =>
                          rw [hB] at hst1; dsimp only at hst1
                          by_cases hltBody : fr₁.pos < B.body.size
                          · simp only [hltBody, ↓reduceDIte] at hst1
                            split at hst1 <;> (split at hst1 <;> cases hst1)
                          · simp only [hltBody, ↓reduceDIte] at hst1
                            cases ht : B.term with
                            | ret as =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases hvs : evalArgs fr₁.env as with
                                | none => rw [hvs] at hst1; cases hst1
                                | some vs =>
                                    rw [hvs] at hst1; dsimp only at hst1
                                    cases hrest with
                                    | nil =>
                                        simp only [Step.done.injEq] at hst1; obtain ⟨rfl, rfl⟩ := hst1
                                        have hst2 := step_ret_done_ge (mem := mem₁) (ctx := ctx₁) hqF0 hB hltBody ht hvs
                                        exact .inl ⟨0, _, .ok (vs, mem₁), Sem.Star.refl _,
                                          by rw [semStep_done.2 hst2]; exact .done, .ok rfl⟩
                                    | cons _ _ => dsimp only at hst1; split at hst1 <;> cases hst1
                            | tail g as =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases h : evalArgs fr₁.env as >>= enter p g <;> rw [h] at hst1 <;> cases hst1
                            | jump _ | br _ _ _ _ _ _ | brOvf _ _ _ _ _ _ | fail _ | trap =>
                                rw [ht] at hst1; dsimp only at hst1; try cases hst1; repeat (split at hst1 <;> try cases hst1)
                                all_goals (try unfold takeEdge at hst1; repeat (split at hst1 <;> try cases hst1))
              | fail res =>
                  rw [semStep, hst1] at hfin; cases hfin
                  unfold step at hst1; dsimp only at hst1
                  cases hF0 : p.funcs[fr₁.fn]? with
                  | none => rw [hF0] at hst1; cases hst1
                  | some F0 =>
                      rw [hF0] at hst1; dsimp only at hst1
                      have hqF0 : q.funcs[fr₁.fn]? = some F0 := by rw [d.hOtherF fr₁.fn hfn, hF0]
                      cases hB : F0.blocks[fr₁.label]? with
                      | none => rw [hB] at hst1; cases hst1
                      | some B =>
                          rw [hB] at hst1; dsimp only at hst1
                          by_cases hltBody : fr₁.pos < B.body.size
                          · simp only [hltBody, ↓reduceDIte] at hst1
                            split at hst1 <;> (split at hst1 <;> cases hst1)
                          · simp only [hltBody, ↓reduceDIte] at hst1
                            cases ht : B.term with
                            | fail r0 =>
                                rw [ht] at hst1; dsimp only at hst1; cases hst1
                                have hst2 := step_fail_ge (mem := mem₁) (ctx := ctx₁) (rest := rest₂) hqF0 hB hltBody ht
                                exact .inl ⟨0, _, .resource res, Sem.Star.refl _, by rw [semStep_fail.2 hst2]; exact .fail, .resource res⟩
                            | tail g as =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases h : evalArgs fr₁.env as >>= enter p g <;> rw [h] at hst1 <;> cases hst1
                            | ret as =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases h : evalArgs fr₁.env as with
                                | none => rw [h] at hst1; cases hst1
                                | some vs =>
                                    rw [h] at hst1; dsimp only at hst1
                                    cases rest₁ with
                                    | nil => cases hst1
                                    | cons c _ => dsimp only at hst1; cases hb : bindParams c.env c.dsts vs <;> rw [hb] at hst1 <;> cases hst1
                            | jump _ | br _ _ _ _ _ _ | brOvf _ _ _ _ _ _ | trap =>
                                rw [ht] at hst1; dsimp only at hst1; try cases hst1; repeat (split at hst1 <;> try cases hst1)
                                all_goals (try unfold takeEdge at hst1; repeat (split at hst1 <;> try cases hst1))
              | trap =>
                  rw [semStep, hst1] at hfin; cases hfin
                  unfold step at hst1; dsimp only at hst1
                  cases hF0 : p.funcs[fr₁.fn]? with
                  | none => rw [hF0] at hst1; cases hst1
                  | some F0 =>
                      rw [hF0] at hst1; dsimp only at hst1
                      have hqF0 : q.funcs[fr₁.fn]? = some F0 := by rw [d.hOtherF fr₁.fn hfn, hF0]
                      cases hB : F0.blocks[fr₁.label]? with
                      | none => rw [hB] at hst1; cases hst1
                      | some B =>
                          rw [hB] at hst1; dsimp only at hst1
                          by_cases hltBody : fr₁.pos < B.body.size
                          · simp only [hltBody, ↓reduceDIte] at hst1
                            split at hst1 <;> (split at hst1 <;> cases hst1)
                          · simp only [hltBody, ↓reduceDIte] at hst1
                            cases ht : B.term with
                            | trap =>
                                have hst2 := step_trap_ge (mem := mem₁) (ctx := ctx₁) (rest := rest₂) hqF0 hB hltBody ht
                                exact .inl ⟨0, _, .trap, Sem.Star.refl _, by rw [semStep_trap.2 hst2]; exact .trap, .trap⟩
                            | tail g as =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases h : evalArgs fr₁.env as >>= enter p g <;> rw [h] at hst1 <;> cases hst1
                            | ret as =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases h : evalArgs fr₁.env as with
                                | none => rw [h] at hst1; cases hst1
                                | some vs =>
                                    rw [h] at hst1; dsimp only at hst1
                                    cases rest₁ with
                                    | nil => cases hst1
                                    | cons c _ => dsimp only at hst1; cases hb : bindParams c.env c.dsts vs <;> rw [hb] at hst1 <;> cases hst1
                            | jump _ | br _ _ _ _ _ _ | brOvf _ _ _ _ _ _ | fail _ =>
                                rw [ht] at hst1; dsimp only at hst1; try cases hst1; repeat (split at hst1 <;> try cases hst1)
                                all_goals (try unfold takeEdge at hst1; repeat (split at hst1 <;> try cases hst1))

/-- Exact clocked simulation (`id` clock bound!) for single-site diamond if-conversion. -/
theorem ifConvDiamondSite_sim {p q : Program} {fi : FunId} {b : Label}
    (h : ifConvDiamondSite p fi b = some q)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id (fun k => eval p k args mem ctx) (fun k => eval q k args mem ctx) := by
  unfold ifConvDiamondSite at h
  cases hpfi : p.funcs[fi]? with
  | none => rw [hpfi] at h; cases h
  | some F =>
      rw [hpfi] at h; dsimp only at h
      cases hb : F.blocks[b]? with
      | none => rw [hb] at h; cases h
      | some blk =>
          rw [hb] at h; dsimp only at h
          cases ht : blk.term with
          | jump _ | brOvf _ _ _ _ _ _ | ret _ | tail _ _ | fail _ | trap => rw [ht] at h; cases h
          | br c w a bArg eT eF =>
              rw [ht] at h; dsimp only at h
              cases hT : extractDiamondArm F b b 4 eT.target with
              | none => rw [hT] at h; cases h
              | some armT =>
                  rw [hT] at h
                  cases hF : extractDiamondArm F b b 4 eF.target with
                  | none => rw [hF] at h; cases h
                  | some armF =>
                      rw [hF] at h; dsimp only at h
                      split at h
                      · rename_i hok
                        cases h
                        have hfiLt : fi < p.funcs.size := (Array.getElem?_eq_some_iff.1 hpfi).1
                        let d : IfConvData p
                            { funcs := p.funcs.set! fi (buildIfConvFunc F b armT armF (nextFreshVReg F)), main := p.main }
                            fi b :=
                          { F, G := buildIfConvFunc F b armT armF (nextFreshVReg F),
                            blk, c, w, a, bArg, eT, eF, armT, armF, off := nextFreshVReg F,
                            hF := hpfi,
                            hG := by simp [Array.set!_eq_setIfInBounds, hfiLt],
                            hGEq := rfl,
                            hOtherF := fun g hg => by simp [Array.set!_eq_setIfInBounds, Ne.symm hg],
                            hMain := rfl, hb, hTerm := ht, hOk := hok }
                        have hdiag := ifConvDiamondSite_forward d
                        have u := ifConv_unpack d
                        cases hinit1 : Lir.State.initial p args mem ctx with
                        | none =>
                            refine ⟨fun k _ => ⟨0, by simp [eval, hinit1]; exact .stuck⟩,
                              fun k hk => by simp [eval, hinit1] at hk⟩
                        | some s₁ =>
                            simp only [Lir.State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff,
                              Option.some.injEq] at hinit1
                            obtain ⟨fr₁, hent₁, rfl⟩ := hinit1
                            obtain ⟨fr₂, hent₂, hfrRel⟩ := ifConv_enter_rel d u hent₁
                            have hinit2 : Lir.State.initial
                                { funcs := p.funcs.set! fi (buildIfConvFunc F b armT armF (nextFreshVReg F)), main := p.main }
                                args mem ctx = some { mem, ctx, stack := [fr₂] } := by
                              rw [Lir.State.initial, hent₂]; rfl
                            have hrel0 : IfConvStateRel d { mem, ctx, stack := [fr₁] } { mem, ctx, stack := [fr₂] } :=
                              ⟨rfl, rfl, .cons (.normal hfrRel) .nil⟩
                            exact hdiag.sim hrel0
                              (runs_eval (by rw [Lir.State.initial, hent₁]; rfl))
                              (runs_eval hinit2)
                      · cases h

/-- Checked single-site diamond if-conversion preserves semantics with `id` clock bound. -/
theorem ifConvDiamondSiteChecked_sim (p : Program) (fi : FunId) (b : Label)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id
      (fun k => eval p k args mem ctx)
      (fun k => eval (ifConvDiamondSiteChecked p fi b).1 k args mem ctx) := by
  have hself : Sem.Sim Eq id
      (fun k => eval p k args mem ctx) (fun k => eval p k args mem ctx) :=
    ⟨fun k _ => ⟨k, Sem.Result.Refines.refl (fun _ => rfl)⟩, fun _ hk => .inl hk⟩
  unfold ifConvDiamondSiteChecked
  cases h : ifConvDiamondSite p fi b with
  | none => exact hself
  | some q =>
      dsimp only
      split
      · exact ifConvDiamondSite_sim h args mem ctx
      · exact hself

/-- Helper: `ifConvDiamondSite` preserves `wellFormed` when guarded by `ifConvDiamondSiteChecked`. -/
theorem ifConvDiamondSiteChecked_wellFormed {p : Program} {fi : FunId} {b : Label}
    (hwf : p.wellFormed = true) :
    (ifConvDiamondSiteChecked p fi b).1.wellFormed = true := by
  unfold ifConvDiamondSiteChecked
  cases hs : ifConvDiamondSite p fi b with
  | none => exact hwf
  | some q =>
      dsimp only
      split
      · rename_i h
        simp only [hwf, Bool.not_true, Bool.false_or] at h
        exact h
      · exact hwf

end IxCC.Lir.Opt

