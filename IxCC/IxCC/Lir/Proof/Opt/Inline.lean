import IxCC.Lir.Opt.Inline
import IxCC.Lir.Proof.Opt.Potential
import IxCC.Lir.Proof.Steps
import IxCC.Lir.Proof.Eval

/-!
# Direct soundness proof for bounded function & self-recursive inlining (`Lir.Opt.Inline`)

Proves `inlineCallSite_sim : Sem.Sim Eq (fun k => 2 * k + 1)` and
`inlineCallSiteChecked_sim` / `inlineCallSiteChecked_wellFormed` directly via
`PotentialForward`, supporting arbitrary non-recursive helper inlining and
arbitrary-depth self-recursive inlining.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Label FunId Width Ext Base Addr Arg Cond BinOp Ovf LimbOp
  Rhs Stmt Edge Term Block Func Program Word Env Frame State Step semStep
  semStep_next semStep_fail semStep_trap semStep_done evalArgs bindParams enter
  takeEdge step step_stmt step_call step_term step_jump step_br step_brOvf
  step_ret_done step_ret_caller step_tail step_fail step_trap star_of_step
  eval eval_mono runs_eval env_insert_self env_insert_ne env_insert_get env_empty)

/-! ## Environment agreement and shifted-register inclusion -/

/-- `ρ₂` agrees with `ρ₁` on all virtual registers strictly below `off`. -/
def EnvAgreeBelow (off : VReg) (ρ₁ ρ₂ : Env) : Prop :=
  ∀ u, u < off → ρ₂[u]? = ρ₁[u]?

/-- Every register bound in `ρ₁` is bound to the same word at `off + v` in `ρ₂`. -/
def EnvShiftIncl (off : VReg) (ρ₁ ρ₂ : Env) : Prop :=
  ∀ v val, ρ₁[v]? = some val → ρ₂[off + v]? = some val

theorem envAgreeBelow_refl (off : VReg) (ρ : Env) : EnvAgreeBelow off ρ ρ :=
  fun _ _ => rfl

theorem envAgreeBelow_insert_lt {off : VReg} {ρ₁ ρ₂ : Env} (h : EnvAgreeBelow off ρ₁ ρ₂)
    {x : VReg} (val : Word) : EnvAgreeBelow off (ρ₁.insert x val) (ρ₂.insert x val) := by
  intro u hu
  rw [env_insert_get, env_insert_get]
  split
  · rfl
  · exact h u hu

theorem envAgreeBelow_insert_ge {off : VReg} {ρ₁ ρ₂ : Env} (h : EnvAgreeBelow off ρ₁ ρ₂)
    {x : VReg} (hx : off ≤ x) (val : Word) : EnvAgreeBelow off ρ₁ (ρ₂.insert x val) := by
  intro u hu
  rw [env_insert_ne ρ₂ val (Nat.ne_of_gt (Nat.lt_of_lt_of_le hu hx))]
  exact h u hu

theorem envShiftIncl_empty (off : VReg) (ρ₂ : Env) : EnvShiftIncl off {} ρ₂ := by
  intro v val h; simp at h

theorem envShiftIncl_insert {off : VReg} {ρ₁ ρ₂ : Env} (h : EnvShiftIncl off ρ₁ ρ₂)
    (v : VReg) (val : Word) : EnvShiftIncl off (ρ₁.insert v val) (ρ₂.insert (off + v) val) := by
  intro w val' hw
  rw [env_insert_get] at hw
  rw [env_insert_get]
  by_cases hvw : v = w
  · subst hvw; simp only [↓reduceIte] at hw ⊢; exact hw
  · have hne : off + v ≠ off + w := fun heq => hvw (Nat.add_left_cancel heq)
    simp only [hvw, hne, ↓reduceIte] at hw ⊢
    exact h w val' hw

theorem bindParams_agreeBelow {off : VReg} :
    ∀ {xs : List VReg} {vs : List Word} {ρ₁ ρ₂ ρ₁' : Env},
      EnvAgreeBelow off ρ₁ ρ₂ →
      bindParams ρ₁ xs vs = some ρ₁' →
      ∃ ρ₂', bindParams ρ₂ xs vs = some ρ₂' ∧ EnvAgreeBelow off ρ₁' ρ₂'
  | [], [], ρ₁, ρ₂, ρ₁', h, hb => by
      simp only [bindParams, Option.some.injEq] at hb; subst hb
      exact ⟨ρ₂, rfl, h⟩
  | x :: xs, v :: vs, ρ₁, ρ₂, ρ₁', h, hb => by
      simp only [bindParams] at hb ⊢
      exact bindParams_agreeBelow (envAgreeBelow_insert_lt h v) hb
  | [], _ :: _, _, _, _, _, hb | _ :: _, [], _, _, _, _, hb => by simp [bindParams] at hb

theorem bindParams_shift {off : VReg} :
    ∀ {xs : List VReg} {vs : List Word} {ρC ρP ρ₂ ρC' : Env},
      EnvAgreeBelow off ρP ρ₂ →
      EnvShiftIncl off ρC ρ₂ →
      bindParams ρC xs vs = some ρC' →
      ∃ ρ₂', bindParams ρ₂ (xs.map (off + ·)) vs = some ρ₂' ∧
        EnvAgreeBelow off ρP ρ₂' ∧ EnvShiftIncl off ρC' ρ₂'
  | [], [], ρC, ρP, ρ₂, ρC', hp, hc, hb => by
      simp only [bindParams, Option.some.injEq] at hb; subst hb
      exact ⟨ρ₂, rfl, hp, hc⟩
  | x :: xs, v :: vs, ρC, ρP, ρ₂, ρC', hp, hc, hb => by
      simp only [List.map_cons, bindParams] at hb ⊢
      exact bindParams_shift
        (envAgreeBelow_insert_ge hp (Nat.le_add_right off x) v)
        (envShiftIncl_insert hc x v) hb
  | [], _ :: _, _, _, _, _, _, _, hb | _ :: _, [], _, _, _, _, _, _, hb => by
      simp [bindParams] at hb

/-! ## Caller operations under `EnvAgreeBelow` -/

private theorem listLt_mem {off : VReg} {xs : List VReg} (h : listLt off xs = true)
    {x : VReg} (hx : x ∈ xs) : x < off := by
  simp only [listLt, List.all_eq_true, decide_eq_true_eq] at h
  exact h x hx

theorem arg_eval_agreeBelow {off : VReg} {ρ₁ ρ₂ : Env} (h : EnvAgreeBelow off ρ₁ ρ₂)
    {a : Arg} (ha : listLt off a.uses = true) : a.eval ρ₂ = a.eval ρ₁ := by
  cases a with
  | imm _ => rfl
  | v x => exact h x (listLt_mem ha (by simp [Arg.uses, Arg.vreg?]))

theorem evalArgs_agreeBelow {off : VReg} {ρ₁ ρ₂ : Env} (h : EnvAgreeBelow off ρ₁ ρ₂) :
    ∀ {as : List Arg}, (∀ a ∈ as, listLt off a.uses = true) →
      evalArgs ρ₂ as = evalArgs ρ₁ as
  | [], _ => rfl
  | a :: rest, ha => by
      simp only [evalArgs, List.mapM_cons,
        arg_eval_agreeBelow h (ha a (by simp)),
        show List.mapM (Arg.eval ρ₂) rest = List.mapM (Arg.eval ρ₁) rest from
          evalArgs_agreeBelow h (fun a' h' => ha a' (by simp [h']))]

theorem listLt_append {off : VReg} {xs ys : List VReg} :
    listLt off (xs ++ ys) = true ↔ listLt off xs = true ∧ listLt off ys = true := by
  simp [listLt]

theorem listLt_flatMap_uses {off : VReg} {as : List Arg}
    (h : listLt off (as.flatMap Arg.uses) = true) :
    ∀ a ∈ as, listLt off a.uses = true := by
  intro a ha
  simp only [listLt, List.all_eq_true, decide_eq_true_eq] at h ⊢
  intro x hx
  exact h x (List.mem_flatMap.2 ⟨a, ha, hx⟩)

theorem addr_eval_agreeBelow {off : VReg} {ρ₁ ρ₂ : Env} {ctx : Word}
    (h : EnvAgreeBelow off ρ₁ ρ₂) {m : Addr} (hm : listLt off m.uses = true) :
    m.eval ρ₂ ctx = m.eval ρ₁ ctx := by
  rcases m with ⟨base, idx, disp⟩
  cases base with
  | none =>
      cases idx with
      | none => rfl
      | some p =>
          rcases p with ⟨x, s⟩
          simp only [Addr.eval, h x (listLt_mem hm (by simp [Addr.uses]))]
  | some b =>
      cases b with
      | ctx =>
          cases idx with
          | none => rfl
          | some p =>
              rcases p with ⟨x, s⟩
              simp only [Addr.eval, h x (listLt_mem hm (by simp [Addr.uses]))]
      | v bx =>
          have hbx := h bx (listLt_mem hm (by simp [Addr.uses, Base.uses]))
          cases idx with
          | none => simp only [Addr.eval, hbx]
          | some p =>
              rcases p with ⟨x, s⟩
              simp only [Addr.eval, hbx, h x (listLt_mem hm (by simp [Addr.uses]))]

theorem rhs_eval_agreeBelow {off : VReg} {ρ₁ ρ₂ : Env} {mem : X86.Memory} {ctx : Word}
    (h : EnvAgreeBelow off ρ₁ ρ₂) {r : Rhs} (hr : listLt off r.uses = true) :
    r.eval ρ₂ mem ctx = r.eval ρ₁ mem ctx := by
  cases r with
  | arg a => exact arg_eval_agreeBelow h hr
  | bin o w a b =>
      simp only [Rhs.uses, listLt_append] at hr
      simp only [Rhs.eval, arg_eval_agreeBelow h hr.1, arg_eval_agreeBelow h hr.2]
  | load w e m =>
      simp only [Rhs.eval, addr_eval_agreeBelow h hr]
  | addr m => exact addr_eval_agreeBelow h hr
  | select c w a b t f =>
      simp only [Rhs.uses, listLt_append] at hr
      simp only [Rhs.eval, arg_eval_agreeBelow h hr.1.1.1, arg_eval_agreeBelow h hr.1.1.2,
        arg_eval_agreeBelow h hr.1.2, arg_eval_agreeBelow h hr.2]
  | test c w a b =>
      simp only [Rhs.uses, listLt_append] at hr
      simp only [Rhs.eval, arg_eval_agreeBelow h hr.1, arg_eval_agreeBelow h hr.2]
  | bsr64 a =>
      simp only [Rhs.eval, arg_eval_agreeBelow h hr]

theorem limb_eval_agreeBelow {off : VReg} {ρ₁ ρ₂ : Env}
    (h : EnvAgreeBelow off ρ₁ ρ₂) {op : LimbOp} (hop : listLt off op.uses = true) :
    op.eval ρ₂ = op.eval ρ₁ := by
  cases op with
  | mulWide64 a b =>
      simp only [LimbOp.uses, listLt_append] at hop
      simp only [LimbOp.eval, arg_eval_agreeBelow h hop.1, arg_eval_agreeBelow h hop.2]
  | divWide64 hi lo d =>
      simp only [LimbOp.uses, listLt_append] at hop
      simp only [LimbOp.eval, arg_eval_agreeBelow h hop.1.1, arg_eval_agreeBelow h hop.1.2,
        arg_eval_agreeBelow h hop.2]
  | addCarry64 a b c =>
      simp only [LimbOp.uses, listLt_append] at hop
      simp only [LimbOp.eval, arg_eval_agreeBelow h hop.1.1, arg_eval_agreeBelow h hop.1.2,
        arg_eval_agreeBelow h hop.2]
  | subBorrow64 a b c =>
      simp only [LimbOp.uses, listLt_append] at hop
      simp only [LimbOp.eval, arg_eval_agreeBelow h hop.1.1, arg_eval_agreeBelow h hop.1.2,
        arg_eval_agreeBelow h hop.2]

theorem stmt_exec_agreeBelow {off : VReg} {ρ₁ ρ₂ ρ₁' : Env} {mem mem' : X86.Memory} {ctx : Word}
    (h : EnvAgreeBelow off ρ₁ ρ₂) {s : Stmt} (hs : listLt off s.uses = true)
    (hx : s.exec ρ₁ mem ctx = some (ρ₁', mem')) :
    ∃ ρ₂', s.exec ρ₂ mem ctx = some (ρ₂', mem') ∧ EnvAgreeBelow off ρ₁' ρ₂' := by
  cases s with
  | assign x r =>
      simp only [Stmt.uses] at hs
      simp only [Stmt.exec, rhs_eval_agreeBelow h hs]
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hx
      obtain ⟨v, hv, rfl, rfl⟩ := hx
      exact ⟨ρ₂.insert x v, by simp [hv], envAgreeBelow_insert_lt h v⟩
  | limb r1 r2 op =>
      simp only [Stmt.uses] at hs
      simp only [Stmt.exec, limb_eval_agreeBelow h hs]
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hx
      obtain ⟨⟨v1, v2⟩, hv, rfl, rfl⟩ := hx
      exact ⟨(ρ₂.insert r1 v1).insert r2 v2, by simp [hv],
        envAgreeBelow_insert_lt (envAgreeBelow_insert_lt h v1) v2⟩
  | store w m a =>
      simp only [Stmt.uses, listLt_append] at hs
      simp only [Stmt.exec, addr_eval_agreeBelow h hs.1, arg_eval_agreeBelow h hs.2]
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
      obtain ⟨addr, haddr, val, hval, hwr⟩ := hx
      cases hw : mem.write? w addr val with
      | error _ => rw [hw] at hwr; cases hwr
      | ok mem'' =>
          rw [hw] at hwr; simp only [Option.some.injEq, Prod.mk.injEq] at hwr
          obtain ⟨rfl, rfl⟩ := hwr
          exact ⟨ρ₂, by simp [haddr, hval, hw], h⟩
  | call _ _ _ => simp [Stmt.exec] at hx

/-! ## Shifted callee operations under `EnvShiftIncl` -/

theorem shiftArg_eval {off : VReg} {ρ₁ ρ₂ : Env} (h : EnvShiftIncl off ρ₁ ρ₂)
    {a : Arg} {v : Word} (ha : a.eval ρ₁ = some v) : (shiftArg off a).eval ρ₂ = some v := by
  cases a with
  | imm w => exact ha
  | v x => exact h x v ha

theorem shiftArgs_eval {off : VReg} {ρ₁ ρ₂ : Env} (h : EnvShiftIncl off ρ₁ ρ₂) :
    ∀ {as : List Arg} {vs : List Word},
      evalArgs ρ₁ as = some vs → evalArgs ρ₂ (as.map (shiftArg off)) = some vs
  | [], vs, ha => by simp only [evalArgs, List.mapM_nil, pure, Option.some.injEq] at ha; subst ha; rfl
  | a :: rest, vs, ha => by
      simp only [evalArgs, List.mapM_cons, pure, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at ha
      obtain ⟨v, hv, vs', hvs', rfl⟩ := ha
      simp only [List.map_cons, evalArgs, List.mapM_cons, shiftArg_eval h hv,
        show List.mapM (Arg.eval ρ₂) (rest.map (shiftArg off)) = some vs' from shiftArgs_eval h hvs',
        Option.bind_eq_bind, Option.bind_some, pure]

theorem shiftAddr_eval {off : VReg} {ρ₁ ρ₂ : Env} {ctx : Word} (h : EnvShiftIncl off ρ₁ ρ₂)
    {m : Addr} {v : Word} (hm : m.eval ρ₁ ctx = some v) : (shiftAddr off m).eval ρ₂ ctx = some v := by
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
          simp [shiftAddr, Addr.eval, h x vx hvx]
  | some b =>
      cases b with
      | ctx =>
          cases idx with
          | none => exact hm
          | some p =>
              rcases p with ⟨x, s⟩
              simp only [Addr.eval, Option.bind_eq_bind, Option.bind_some, Option.map_eq_map,
                Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hm
              obtain ⟨_, ⟨vx, hvx, rfl⟩, rfl⟩ := hm
              simp [shiftAddr, shiftBase, Addr.eval, h x vx hvx]
      | v bx =>
          cases idx with
          | none =>
              simp only [Addr.eval, Option.bind_eq_bind, Option.bind_some,
                Option.bind_eq_some_iff, Option.some.injEq] at hm
              obtain ⟨vb, hvb, rfl⟩ := hm
              simp [shiftAddr, shiftBase, Addr.eval, h bx vb hvb]
          | some p =>
              rcases p with ⟨x, s⟩
              simp only [Addr.eval, Option.bind_eq_bind, Option.map_eq_map,
                Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hm
              obtain ⟨vb, hvb, _, ⟨vx, hvx, rfl⟩, rfl⟩ := hm
              simp [shiftAddr, shiftBase, Addr.eval, h bx vb hvb, h x vx hvx]

theorem shiftRhs_eval {off : VReg} {ρ₁ ρ₂ : Env} {mem : X86.Memory} {ctx : Word}
    (h : EnvShiftIncl off ρ₁ ρ₂) {r : Rhs} {v : Word} (hr : r.eval ρ₁ mem ctx = some v) :
    (shiftRhs off r).eval ρ₂ mem ctx = some v := by
  cases r with
  | arg a => exact shiftArg_eval h hr
  | bin o w a b =>
      simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
      obtain ⟨va, ha, vb, hb, ho⟩ := hr
      simp only [shiftRhs, Rhs.eval, Option.bind_eq_bind, shiftArg_eval h ha, shiftArg_eval h hb,
        Option.bind_some]
      exact ho
  | load w e m =>
      simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
      obtain ⟨va, ha, hl⟩ := hr
      simp only [shiftRhs, Rhs.eval, Option.bind_eq_bind, shiftAddr_eval h ha, Option.bind_some]
      exact hl
  | addr m => exact shiftAddr_eval h hr
  | select c w a b t f =>
      simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      obtain ⟨va, ha, vb, hb, vt, ht, vf, hf, rfl⟩ := hr
      simp only [shiftRhs, Rhs.eval, Option.bind_eq_bind, shiftArg_eval h ha, shiftArg_eval h hb,
        shiftArg_eval h ht, shiftArg_eval h hf, Option.bind_some]
  | test c w a b =>
      simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      obtain ⟨va, ha, vb, hb, rfl⟩ := hr
      simp only [shiftRhs, Rhs.eval, Option.bind_eq_bind, shiftArg_eval h ha, shiftArg_eval h hb,
        Option.bind_some]
  | bsr64 a =>
      simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
      obtain ⟨va, ha, hb⟩ := hr
      simp only [shiftRhs, Rhs.eval, Option.bind_eq_bind, shiftArg_eval h ha, Option.bind_some]
      exact hb

theorem shiftLimb_eval {off : VReg} {ρ₁ ρ₂ : Env} (h : EnvShiftIncl off ρ₁ ρ₂)
    {op : LimbOp} {v : Word × Word} (hop : op.eval ρ₁ = some v) :
    (shiftLimb off op).eval ρ₂ = some v := by
  cases op with
  | mulWide64 a b =>
      simp only [LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hop
      obtain ⟨va, ha, vb, hb, ho⟩ := hop
      simp only [shiftLimb, LimbOp.eval, Option.bind_eq_bind, shiftArg_eval h ha, shiftArg_eval h hb,
        Option.bind_some]
      exact ho
  | divWide64 hi lo d =>
      simp only [LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hop
      obtain ⟨v1, h1, v2, h2, v3, h3, ho⟩ := hop
      simp only [shiftLimb, LimbOp.eval, Option.bind_eq_bind, shiftArg_eval h h1, shiftArg_eval h h2,
        shiftArg_eval h h3, Option.bind_some]
      exact ho
  | addCarry64 a b c =>
      simp only [LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hop
      obtain ⟨v1, h1, v2, h2, v3, h3, ho⟩ := hop
      simp only [shiftLimb, LimbOp.eval, Option.bind_eq_bind, shiftArg_eval h h1, shiftArg_eval h h2,
        shiftArg_eval h h3, Option.bind_some]
      exact ho
  | subBorrow64 a b c =>
      simp only [LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hop
      obtain ⟨v1, h1, v2, h2, v3, h3, ho⟩ := hop
      simp only [shiftLimb, LimbOp.eval, Option.bind_eq_bind, shiftArg_eval h h1, shiftArg_eval h h2,
        shiftArg_eval h h3, Option.bind_some]
      exact ho

theorem shiftStmt_exec {off : VReg} {ρC ρP ρ₂ ρC' : Env} {mem mem' : X86.Memory} {ctx : Word}
    (hp : EnvAgreeBelow off ρP ρ₂) (hc : EnvShiftIncl off ρC ρ₂)
    {s : Stmt} (hx : s.exec ρC mem ctx = some (ρC', mem')) :
    ∃ ρ₂', (shiftStmt off s).exec ρ₂ mem ctx = some (ρ₂', mem') ∧
      EnvAgreeBelow off ρP ρ₂' ∧ EnvShiftIncl off ρC' ρ₂' := by
  cases s with
  | assign x r =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hx
      obtain ⟨v, hv, rfl, rfl⟩ := hx
      exact ⟨ρ₂.insert (off + x) v, by simp [shiftStmt, Stmt.exec, shiftRhs_eval hc hv],
        envAgreeBelow_insert_ge hp (Nat.le_add_right off x) v, envShiftIncl_insert hc x v⟩
  | limb r1 r2 op =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hx
      obtain ⟨⟨v1, v2⟩, hv, rfl, rfl⟩ := hx
      exact ⟨(ρ₂.insert (off + r1) v1).insert (off + r2) v2,
        by simp [shiftStmt, Stmt.exec, shiftLimb_eval hc hv],
        envAgreeBelow_insert_ge (envAgreeBelow_insert_ge hp (Nat.le_add_right off r1) v1)
          (Nat.le_add_right off r2) v2,
        envShiftIncl_insert (envShiftIncl_insert hc r1 v1) r2 v2⟩
  | store w m a =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
      obtain ⟨addr, haddr, val, hval, hwr⟩ := hx
      cases hw : mem.write? w addr val with
      | error _ => rw [hw] at hwr; cases hwr
      | ok mem'' =>
          rw [hw] at hwr; simp only [Option.some.injEq, Prod.mk.injEq] at hwr
          obtain ⟨rfl, rfl⟩ := hwr
          exact ⟨ρ₂, by simp [shiftStmt, Stmt.exec, shiftAddr_eval hc haddr, shiftArg_eval hc hval, hw],
            hp, hc⟩
  | call _ _ _ => simp [Stmt.exec] at hx

/-! ## Block lookup lemmas for `buildInlinedFunc` -/

private theorem getElem?_append_left {α : Type} {xs ys : List α} {i : Nat} (h : i < xs.length) :
    (xs ++ ys)[i]? = xs[i]? := by
  rw [List.getElem?_append_left h]

private theorem getElem?_append_right {α : Type} {xs ys : List α} {i : Nat} (h : xs.length ≤ i) :
    (xs ++ ys)[i]? = ys[i - xs.length]? := by
  rw [List.getElem?_append_right h]

private theorem nodup_tailFreshRs (callee : Func) (rs : List VReg) (off : VReg) (j : Nat) :
    (inlineTailFreshRs callee rs off j).Nodup := by
  unfold inlineTailFreshRs
  have h : ∀ (xs : List Nat) (base : Nat), xs.Nodup → (xs.map (base + ·)).Nodup := by
    intro xs base hn
    induction xs with
    | nil => simp
    | cons a rest ih =>
        rw [List.nodup_cons] at hn
        rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, ih hn.2⟩
        intro hm; rw [List.mem_map] at hm
        obtain ⟨b, hb, heq⟩ := hm
        have : b = a := Nat.add_left_cancel heq
        subst this; exact hn.1 hb
  exact h (List.range rs.length) _ List.nodup_range

private theorem mem_tailFreshRs_ge {callee : Func} {rs : List VReg} {off : VReg} {j r : Nat}
    (h : r ∈ inlineTailFreshRs callee rs off j) : off ≤ r := by
  unfold inlineTailFreshRs at h
  dsimp only at h
  rw [List.mem_map] at h
  obtain ⟨i, _, rfl⟩ := h
  exact Nat.le_trans (Nat.le_add_right off _)
    (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))

private theorem bindParams_of_eq_len' :
    ∀ (ρ : Env) (ps : List VReg) (vs : List Word),
      ps.length = vs.length → ∃ ρ', bindParams ρ ps vs = some ρ'
  | ρ, [], [], _ => ⟨ρ, rfl⟩
  | ρ, p :: ps, v :: vs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      exact bindParams_of_eq_len' (ρ.insert p v) ps vs h
  | _, [], _ :: _, h | _, _ :: _, [], h => by simp at h

private theorem bindParams_len_eq' :
    ∀ {ρ ρ' : Env} {ps : List VReg} {vs : List Word},
      bindParams ρ ps vs = some ρ' → ps.length = vs.length
  | _, _, [], [], _ => rfl
  | _, _, _ :: _, _ :: _, h => by simp only [bindParams] at h; rw [List.length_cons, List.length_cons, bindParams_len_eq' h]
  | _, _, [], _ :: _, h | _, _, _ :: _, [], h => by simp [bindParams] at h

private theorem bindParams_nodup_evalArgs' :
    ∀ {ps : List VReg} {vs : List Word} {ρ ρ' : Env},
      ps.Nodup →
      bindParams ρ ps vs = some ρ' →
      evalArgs ρ' (ps.map .v) = some vs ∧ (∀ u, u ∉ ps → ρ'[u]? = ρ[u]?)
  | [], [], ρ, ρ', _, h => by
      simp only [bindParams, Option.some.injEq] at h; subst h
      exact ⟨rfl, fun _ _ => rfl⟩
  | p :: ps, v :: vs, ρ, ρ', hnd, h => by
      rw [List.nodup_cons] at hnd
      simp only [bindParams] at h
      obtain ⟨hev, hpres⟩ := bindParams_nodup_evalArgs' hnd.2 h
      refine ⟨?_, ?_⟩
      · have hp : ρ'[p]? = some v := by rw [hpres p hnd.1, env_insert_self]
        unfold evalArgs at hev ⊢
        simp only [List.map_cons, List.mapM_cons, Arg.eval, hp, Option.bind_eq_bind,
          Option.bind_some, hev, Option.pure_def]
      · intro u hu
        rw [List.mem_cons, not_or] at hu
        rw [hpres u hu.2, env_insert_ne _ _ (Ne.symm hu.1)]
  | [], _ :: _, _, _, _, h | _ :: _, [], _, _, _, h => by simp [bindParams] at h

private theorem inlineCalleeBlock_params (callee : Func) (callBlk : Label) (blk : Block)
    (rs : List VReg) (off : VReg) (j : Nat) (b : Block) :
    (inlineCalleeBlock callee callBlk blk rs off j b).params =
      if j == 0 then callee.params.map (off + ·) else b.params.map (off + ·) := by
  unfold inlineCalleeBlock; cases b.term <;> rfl

private theorem inlineCalleeBlock_body_lt {callee : Func} {callBlk : Label} {blk : Block}
    {rs : List VReg} {off : VReg} {j pos : Nat} {b : Block} (hlt : pos < b.body.size) :
    ∃ hlt2 : pos < (inlineCalleeBlock callee callBlk blk rs off j b).body.size,
      (inlineCalleeBlock callee callBlk blk rs off j b).body[pos]'hlt2 = shiftStmt off (b.body[pos]'hlt) := by
  unfold inlineCalleeBlock
  cases b.term with
  | tail g tas =>
      have hlt2 : pos < ((b.body.map (shiftStmt off)).push
          (.call (inlineTailFreshRs callee rs off j) g (tas.map (shiftArg off)))).size := by
        simp; omega
      refine ⟨hlt2, ?_⟩
      dsimp only
      rw [Array.getElem_push_lt (by simp; omega)]
      simp
  | jump _ | br _ _ _ _ _ _ | brOvf _ _ _ _ _ _ | ret _ | fail _ | trap =>
      exact ⟨by simp [hlt], by simp⟩

private theorem inlineCalleeBlock_tail {callee : Func} {callBlk : Label} {blk : Block}
    {rs : List VReg} {off : VReg} {j : Nat} {b : Block} {g : FunId} {tas : List Arg}
    (ht : b.term = .tail g tas) :
    (inlineCalleeBlock callee callBlk blk rs off j b).body.size = b.body.size + 1 ∧
    (∀ hlt : b.body.size < (inlineCalleeBlock callee callBlk blk rs off j b).body.size,
      (inlineCalleeBlock callee callBlk blk rs off j b).body[b.body.size]'hlt =
        .call (inlineTailFreshRs callee rs off j) g (tas.map (shiftArg off))) ∧
    (inlineCalleeBlock callee callBlk blk rs off j b).term =
      .jump { target := callBlk + (callee.blocks.size + 1), args := (inlineTailFreshRs callee rs off j).map .v } := by
  unfold inlineCalleeBlock
  rw [ht]; dsimp only
  refine ⟨by simp, fun hlt => ?_, rfl⟩
  have heq : (b.body.map (shiftStmt off)).size = b.body.size := by simp
  simpa [heq] using Array.getElem_push_eq (xs := b.body.map (shiftStmt off))
    (x := .call (inlineTailFreshRs callee rs off j) g (tas.map (shiftArg off)))

private theorem inlineCalleeBlock_nonTail {callee : Func} {callBlk : Label} {blk : Block}
    {rs : List VReg} {off : VReg} {j : Nat} {b : Block}
    (hnt : ∀ g tas, b.term ≠ .tail g tas) :
    (inlineCalleeBlock callee callBlk blk rs off j b).body.size = b.body.size ∧
    (inlineCalleeBlock callee callBlk blk rs off j b).term =
      rewriteCalleeTerm off (callBlk + 1) (callBlk + (callee.blocks.size + 1)) b.term := by
  unfold inlineCalleeBlock
  cases ht : b.term with
  | tail g tas => exact absurd ht (hnt g tas)
  | jump _ | br _ _ _ _ _ _ | brOvf _ _ _ _ _ _ | ret _ | fail _ | trap =>
      exact ⟨by simp, rfl⟩

section Layout

variable (caller callee : Func) (callBlk callPos : Nat) (blk : Block)
  (rs : List VReg) (as : List Arg) (off : VReg)

private def callBlkNew : Block :=
  { blk with
    body := (blk.body.toList.take callPos).toArray
    term := .jump { target := callBlk + 1, args := as } }

private def contBlkNew : Block :=
  { params := rs
    body := (blk.body.toList.drop (callPos + 1)).toArray
    term := remapCallerTerm callBlk (callee.blocks.size + 1) blk.term
    cold := blk.cold }

private theorem buildInlined_blocks_lt {b : Label} {B : Block}
    (hcall : callBlk < caller.blocks.size) (hb : b < callBlk) (hB : caller.blocks[b]? = some B) :
    (buildInlinedFunc caller callee callBlk callPos blk rs as off).blocks[b]? =
      some { B with term := remapCallerTerm callBlk (callee.blocks.size + 1) B.term } := by
  unfold buildInlinedFunc
  dsimp only
  rw [List.getElem?_toArray]
  have hlen : ((caller.blocks.toList.take callBlk).map fun b =>
      { b with term := remapCallerTerm callBlk (callee.blocks.size + 1) b.term }).length = callBlk := by
    simp [Nat.min_eq_left (Nat.le_of_lt hcall)]
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (by rw [hlen]; exact hb)]
  rw [List.getElem?_map, List.getElem?_take_of_lt hb, Array.getElem?_toList, hB]
  rfl

private theorem buildInlined_blocks_callBlk (hcall : callBlk < caller.blocks.size) :
    (buildInlinedFunc caller callee callBlk callPos blk rs as off).blocks[callBlk]? =
      some (callBlkNew callBlk callPos blk as) := by
  unfold buildInlinedFunc callBlkNew
  dsimp only
  rw [List.getElem?_toArray]
  have hlen : ((caller.blocks.toList.take callBlk).map fun b =>
      { b with term := remapCallerTerm callBlk (callee.blocks.size + 1) b.term }).length = callBlk := by
    simp [Nat.min_eq_left (Nat.le_of_lt hcall)]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [hlen]; exact Nat.le_refl _), hlen, Nat.sub_self]
  rfl

private theorem buildInlined_blocks_inlined {j : Label} {B : Block}
    (hcall : callBlk < caller.blocks.size) (hB : callee.blocks[j]? = some B) :
    (buildInlinedFunc caller callee callBlk callPos blk rs as off).blocks[callBlk + 1 + j]? =
      some (inlineCalleeBlock callee callBlk blk rs off j B) := by
  have hj : j < callee.blocks.size := (Array.getElem?_eq_some_iff.1 hB).1
  unfold buildInlinedFunc
  dsimp only
  rw [List.getElem?_toArray]
  have hlen1 : ((caller.blocks.toList.take callBlk).map fun b =>
      { b with term := remapCallerTerm callBlk (callee.blocks.size + 1) b.term }).length = callBlk := by
    simp [Nat.min_eq_left (Nat.le_of_lt hcall)]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [hlen1]; omega), hlen1]
  rw [show callBlk + 1 + j - callBlk = j + 1 by omega]
  simp only [List.singleton_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simp [hj])]
  rw [List.getElem?_map, List.getElem?_zipIdx]
  simp [Array.getElem?_toList, hB]

private theorem buildInlined_blocks_cont (hcall : callBlk < caller.blocks.size) :
    (buildInlinedFunc caller callee callBlk callPos blk rs as off).blocks[callBlk + (callee.blocks.size + 1)]? =
      some (contBlkNew callee callBlk callPos blk rs) := by
  unfold buildInlinedFunc contBlkNew
  dsimp only
  rw [List.getElem?_toArray]
  have hlen1 : ((caller.blocks.toList.take callBlk).map fun b =>
      { b with term := remapCallerTerm callBlk (callee.blocks.size + 1) b.term }).length = callBlk := by
    simp [Nat.min_eq_left (Nat.le_of_lt hcall)]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [hlen1]; omega), hlen1]
  rw [show callBlk + (callee.blocks.size + 1) - callBlk = callee.blocks.size + 1 by omega]
  simp only [List.singleton_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp)]
  simp

private theorem buildInlined_blocks_gt {b : Nat} {B : Block}
    (hcall : callBlk < caller.blocks.size) (hb : callBlk < b) (hB : caller.blocks[b]? = some B) :
    (buildInlinedFunc caller callee callBlk callPos blk rs as off).blocks[b + (callee.blocks.size + 1)]? =
      some { B with term := remapCallerTerm callBlk (callee.blocks.size + 1) B.term } := by
  unfold buildInlinedFunc
  dsimp only
  rw [List.getElem?_toArray]
  have hlen1 : ((caller.blocks.toList.take callBlk).map fun b =>
      { b with term := remapCallerTerm callBlk (callee.blocks.size + 1) b.term }).length = callBlk := by
    simp [Nat.min_eq_left (Nat.le_of_lt hcall)]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [hlen1]; omega), hlen1]
  rw [show b + (callee.blocks.size + 1) - callBlk = (b - callBlk - 1 + callee.blocks.size + 1) + 1 by omega]
  simp only [List.singleton_append, List.getElem?_cons_succ]
  have hlen2 : (callee.blocks.toList.zipIdx.map fun x =>
      inlineCalleeBlock callee callBlk blk rs off x.2 x.1).length = callee.blocks.size := by
    simp
  rw [List.getElem?_append_right (by rw [hlen2]; omega), hlen2]
  rw [show b - callBlk - 1 + callee.blocks.size + 1 - callee.blocks.size = (b - callBlk - 1) + 1 by omega]
  simp only [List.getElem?_cons_succ, List.getElem?_map, List.getElem?_drop, Array.getElem?_toList]
  rw [show callBlk + 1 + (b - callBlk - 1) = b by omega, hB]
  rfl

private theorem remapCallerLabel_le_iff (callBlk delta t b : Nat) (_hb : b ≠ callBlk) :
    decide (remapCallerLabel callBlk delta t ≤ remapCallerLabel callBlk delta b) = decide (t ≤ b) := by
  change decide ((if t ≤ callBlk then t else t + delta) ≤ (if b ≤ callBlk then b else b + delta)) = decide (t ≤ b)
  split <;> split
  · rfl
  · simp only [decide_eq_decide]; exact ⟨fun _ => by omega, fun _ => by omega⟩
  · simp only [decide_eq_decide]; exact ⟨fun _ => by omega, fun _ => by omega⟩
  · simp only [decide_eq_decide]; exact ⟨fun _ => by omega, fun _ => by omega⟩

private theorem remapCallerLabel_le_cont (callBlk delta t : Nat) (hd : 0 < delta) :
    decide (remapCallerLabel callBlk delta t ≤ callBlk + delta) = decide (t ≤ callBlk) := by
  change decide ((if t ≤ callBlk then t else t + delta) ≤ callBlk + delta) = decide (t ≤ callBlk)
  split <;> (simp only [decide_eq_decide]; exact ⟨fun _ => by omega, fun _ => by omega⟩)

end Layout

/-! ## Simulation relation & amortized potential -/

/-- Normal (1-to-1) frame relation between source frame `fr₁` and target frame `fr₂`.
Only suspended (`isTop = false`) frames require `dsts` agreement; active top frames never read `dsts`. -/
def NormalFrameRel (fi : FunId) (callBlk callPos M : Nat) (off : VReg) (isTop : Bool)
    (fr₁ fr₂ : Frame) : Prop :=
  if fr₁.fn = fi then
    fr₂.fn = fi ∧
    EnvAgreeBelow off fr₁.env fr₂.env ∧
    (isTop = false → fr₂.dsts = fr₁.dsts) ∧
    (fr₁.label ≠ callBlk → fr₂.label = remapCallerLabel callBlk (M + 1) fr₁.label ∧ fr₂.pos = fr₁.pos) ∧
    (fr₁.label = callBlk → fr₁.pos ≤ callPos → fr₂.label = callBlk ∧ fr₂.pos = fr₁.pos) ∧
    (fr₁.label = callBlk → callPos < fr₁.pos → fr₂.label = callBlk + (M + 1) ∧ fr₂.pos = fr₁.pos - (callPos + 1))
  else
    fr₂ = fr₁

/-- Inlined (2-to-1) frame pair relation: active callee frame `frC` sitting on top of
suspended caller frame `frP` at `(callBlk, callPos + 1)` matches one frame `fr₂` in the
spliced callee region `[callBlk + 1, callBlk + M]`. -/
def InlinedPairRel (callee : Func) (fi gi : FunId) (callBlk callPos M : Nat) (rs : List VReg) (off : VReg)
    (isTop : Bool) (frC frP fr₂ : Frame) : Prop :=
  frP.fn = fi ∧ frP.label = callBlk ∧ frP.pos = callPos + 1 ∧ frP.dsts = rs ∧
  frC.fn = gi ∧ frC.label < M ∧
  (∀ B, callee.blocks[frC.label]? = some B → frC.pos ≤ B.body.size) ∧
  fr₂.fn = fi ∧ fr₂.label = callBlk + 1 + frC.label ∧ fr₂.pos = frC.pos ∧
  (isTop = false → fr₂.dsts = frC.dsts.map (off + ·)) ∧
  EnvAgreeBelow off frP.env fr₂.env ∧
  EnvShiftIncl off frC.env fr₂.env

/-- Stack relation pairing frames 1-to-1 normally, 2-to-1 across active inlined calls,
and 1-to-1 across suspended `.tail`-in-callee call frames (which hop via `jump contLbl` on return). -/
inductive InlineStackRel (callee : Func) (fi gi : FunId) (callBlk callPos M : Nat) (rs : List VReg) (off : VReg) :
    Bool → List Frame → List Frame → Prop
  | nil {isTop} : InlineStackRel callee fi gi callBlk callPos M rs off isTop [] []
  | normal {isTop fr₁ fr₂ s₁ s₂} :
      NormalFrameRel fi callBlk callPos M off isTop fr₁ fr₂ →
      InlineStackRel callee fi gi callBlk callPos M rs off false s₁ s₂ →
      InlineStackRel callee fi gi callBlk callPos M rs off isTop (fr₁ :: s₁) (fr₂ :: s₂)
  | inlined {isTop frC frP fr₂ s₁ s₂} :
      InlinedPairRel callee fi gi callBlk callPos M rs off isTop frC frP fr₂ →
      InlineStackRel callee fi gi callBlk callPos M rs off false s₁ s₂ →
      InlineStackRel callee fi gi callBlk callPos M rs off isTop (frC :: frP :: s₁) (fr₂ :: s₂)
  | tailReturn {frP fr₂ s₁ s₂} {j : Nat} {B : Block} {g : FunId} {tas : List Arg} :
      frP.fn = fi → frP.label = callBlk → frP.pos = callPos + 1 → frP.dsts = rs →
      j < M → callee.blocks[j]? = some B → B.term = .tail g tas →
      fr₂.fn = fi → fr₂.label = callBlk + 1 + j → fr₂.pos = B.body.size + 1 →
      fr₂.dsts = inlineTailFreshRs callee rs off j →
      EnvAgreeBelow off frP.env fr₂.env →
      InlineStackRel callee fi gi callBlk callPos M rs off false s₁ s₂ →
      InlineStackRel callee fi gi callBlk callPos M rs off false (frP :: s₁) (fr₂ :: s₂)

/-- State relation for single-site inlining. -/
def InlineStateRel (callee : Func) (fi gi : FunId) (callBlk callPos M : Nat) (rs : List VReg) (off : VReg)
    (s₁ s₂ : State) : Prop :=
  s₂.mem = s₁.mem ∧ s₂.ctx = s₁.ctx ∧
  InlineStackRel callee fi gi callBlk callPos M rs off true s₁.stack s₂.stack

/-- Per-frame potential on target state `s₂`: `1` before the inlined call site in `fi`, `0` elsewhere. -/
def inlineFramePot (fi : FunId) (callBlk callPos : Nat) (fr : Frame) : Nat :=
  if fr.fn == fi && (decide (fr.label < callBlk) || (fr.label == callBlk && decide (fr.pos ≤ callPos))) then 1 else 0

theorem inlineFramePot_le_one (fi : FunId) (callBlk callPos : Nat) (fr : Frame) :
    inlineFramePot fi callBlk callPos fr ≤ 1 := by
  unfold inlineFramePot; split <;> omega

/-- Total stack potential on target state `s₂`. -/
def inlinePot (fi : FunId) (callBlk callPos : Nat) (s₂ : State) : Nat :=
  (s₂.stack.map (inlineFramePot fi callBlk callPos)).sum

/-! ## Helper lemmas for `enter` and `takeEdge` under inlining -/

private theorem enter_rel {p q : Program} {fi : FunId} {caller caller' callee : Func}
    {callBlk callPos : Nat} {off : VReg}
    (hpfi : p.funcs[fi]? = some caller)
    (hq : q = { p with funcs := p.funcs.set! fi caller' })
    (hpar : caller'.params = caller.params)
    {g : FunId} {vs : List Word} {fr₁ : Frame}
    (hent : enter p g vs = some fr₁) :
    ∃ fr₂, enter q g vs = some fr₂ ∧
      NormalFrameRel fi callBlk callPos callee.blocks.size off true fr₁ fr₂ := by
  have hfiLt : fi < p.funcs.size := (Array.getElem?_eq_some_iff.1 hpfi).1
  simp only [enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hent
  obtain ⟨F, hF, ρ, hbp, rfl⟩ := hent
  by_cases hg : g = fi
  · subst hg
    rw [hpfi] at hF; cases hF
    have hqF : q.funcs[g]? = some caller' := by
      rw [hq]; simp [Array.set!_eq_setIfInBounds, hfiLt]
    refine ⟨{ fn := g, label := 0, pos := 0, env := ρ, dsts := [] }, ?_, ?_⟩
    · simp [enter, hqF, hpar, hbp]
    · simp only [NormalFrameRel, ↓reduceIte, envAgreeBelow_refl, true_and]
      refine ⟨(fun h => by cases h), fun _ => ⟨by unfold remapCallerLabel; simp, trivial⟩,
        fun hcb _ => ⟨hcb, trivial⟩, fun _ hgt => by omega⟩
  · have hqF : q.funcs[g]? = some F := by
      rw [hq]; simp [Array.set!_eq_setIfInBounds, Ne.symm hg, hF]
    exact ⟨{ fn := g, label := 0, pos := 0, env := ρ, dsts := [] },
      by simp [enter, hqF, hbp], by simp [NormalFrameRel, hg]⟩

/-! ## Master potential forward simulation theorem -/

private theorem blockRegsLt_of_func {F : Func} {off : VReg} (h : funcRegsLt F off = true)
    {b : Label} {B : Block} (hB : F.blocks[b]? = some B) : blockRegsLt off B = true := by
  simp only [funcRegsLt, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 B (Array.mem_toList_iff.2 (Array.mem_of_getElem? hB))

private theorem stmt_uses_lt_of_block {off : VReg} {B : Block} (h : blockRegsLt off B = true)
    {pos : Nat} (hpos : pos < B.body.size) : listLt off B.body[pos].uses = true := by
  simp only [blockRegsLt, Bool.and_eq_true, List.all_eq_true] at h
  have hmem : B.body[pos] ∈ B.body.toList := Array.mem_toList_iff.2 (Array.getElem_mem hpos)
  exact (h.1.1.1.2 B.body[pos] hmem).1

private theorem term_uses_lt_of_block {off : VReg} {B : Block} (h : blockRegsLt off B = true) :
    listLt off B.term.uses = true ∧ listLt off B.term.edgeUses = true := by
  simp only [blockRegsLt, Bool.and_eq_true] at h
  exact ⟨h.1.1.2, h.2⟩

private theorem edge_args_lt_of_term {off : VReg} {t : Term} (h : listLt off t.edgeUses = true)
    {e : Edge} (he : e ∈ t.edges) : ∀ a ∈ e.args, listLt off a.uses = true := by
  intro a ha
  simp only [Term.edgeUses] at h
  simp only [listLt, List.all_eq_true, decide_eq_true_eq] at h ⊢
  intro x hx
  exact h x (List.mem_flatMap.2 ⟨e, he, List.mem_flatMap.2 ⟨a, ha, hx⟩⟩)

private theorem calleeBlockOk_of {callee : Func} {nArgs nRes : Nat}
    (h : calleeInlineOk callee nArgs nRes = true) {j : Label} {B : Block}
    (hB : callee.blocks[j]? = some B) : calleeBlockOk callee.blocks.size callee.results B = true := by
  unfold calleeInlineOk at h
  cases hb0 : callee.blocks[0]? with
  | none => rw [hb0] at h; cases h
  | some b0 =>
      rw [hb0] at h
      simp only [Bool.and_eq_true, List.all_eq_true] at h
      exact h.2 B (Array.mem_toList_iff.2 (Array.mem_of_getElem? hB))

private theorem single_star_of_step {q : Program} {s s' : State} {b : Bool}
    (h : step q s = .next s' b) : Sem.Star (semStep q) s b.toNat s' :=
  star_of_step h

private theorem step_at_term {p : Program} {F : Func} {B : Block} {mem : X86.Memory} {ctx : Word}
    {fr : Frame} {rest : List Frame}
    (hF : p.funcs[fr.fn]? = some F) (hB : F.blocks[fr.label]? = some B)
    (hlt : ¬ fr.pos < B.body.size) :
    step p { mem, ctx, stack := fr :: rest } =
      match B.term with
      | .jump e => takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env e
      | .br c w a b' t f =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
              takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env
                (if c.holds w va vb then t else f)
          | _, _ => .stuck
      | .brOvf o x a b' ok ovf =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
              let (r, carry) := o.eval va vb
              takeEdge F { mem, ctx, stack := fr :: rest } fr rest
                (fr.env.insert x r) (if carry then ovf else ok)
          | _, _ => .stuck
      | .ret ras =>
          match evalArgs fr.env ras with
          | none => .stuck
          | some vals =>
              match rest with
              | [] => .done vals mem
              | c :: rest' =>
                  match bindParams c.env c.dsts vals with
                  | some ρ => .next { mem, ctx, stack := { c with env := ρ, dsts := [] } :: rest' } false
                  | none => .stuck
      | .tail g tas =>
          match evalArgs fr.env tas >>= enter p g with
          | some calleeF => .next { mem, ctx, stack := calleeF :: rest } true
          | none => .stuck
      | .fail r => .fail r
      | .trap => .trap := by
  unfold step; dsimp only; rw [hF]; dsimp only; rw [hB]; simp only [hlt, ↓reduceDIte]
  cases B.term with
  | jump _ | fail _ | trap => rfl
  | br _ _ a b' _ _ | brOvf _ _ a b' _ _ =>
      cases a.eval fr.env <;> cases b'.eval fr.env <;> rfl
  | ret ras =>
      cases evalArgs fr.env ras with
      | none => rfl
      | some vals =>
          cases rest with
          | nil => rfl
          | cons c rest' => cases bindParams c.env c.dsts vals <;> rfl
  | tail g tas =>
      cases evalArgs fr.env tas >>= enter p g <;> rfl

theorem inlineCallSite_forward {p q : Program} {fi gi : FunId} {callBlk callPos : Nat}
    {caller callee : Func} {blk : Block} {rs : List VReg} {as : List Arg}
    (hpfi : p.funcs[fi]? = some caller)
    (hcall : caller.blocks[callBlk]? = some blk)
    (hpos : blk.body[callPos]? = some (.call rs gi as))
    (hpgi : p.funcs[gi]? = some callee)
    (hregs : funcRegsLt caller (nextFreshVReg caller) = true)
    (hok : calleeInlineOk callee as.length rs.length = true)
    (hq : q = { funcs := p.funcs.set! fi (buildInlinedFunc caller callee callBlk callPos blk rs as (nextFreshVReg caller)), main := p.main }) :
    PotentialForward (semStep p) (semStep q) Eq
      (InlineStateRel callee fi gi callBlk callPos callee.blocks.size rs (nextFreshVReg caller))
      (fun _ s₂ => inlinePot fi callBlk callPos s₂) 2 := by
  let off := nextFreshVReg caller
  let M := callee.blocks.size
  let delta := M + 1
  let caller' := buildInlinedFunc caller callee callBlk callPos blk rs as off
  have hfiLt : fi < p.funcs.size := (Array.getElem?_eq_some_iff.1 hpfi).1
  have hcallLt : callBlk < caller.blocks.size := (Array.getElem?_eq_some_iff.1 hcall).1
  have hposLt : callPos < blk.body.size := (Array.getElem?_eq_some_iff.1 hpos).1
  have hqfi : q.funcs[fi]? = some caller' := by
    rw [hq]; simp [Array.set!_eq_setIfInBounds, hfiLt, caller', off]
  have hcaller'_par : caller'.params = caller.params := rfl
  have hblk_regs : blockRegsLt off blk = true := blockRegsLt_of_func hregs hcall
  have hcall_args_lt : ∀ a ∈ as, listLt off a.uses = true := by
    have hst := stmt_uses_lt_of_block hblk_regs hposLt
    rw [(Array.getElem?_eq_some_iff.1 hpos).2] at hst
    exact listLt_flatMap_uses hst
  -- Extract callee entry properties from `hok`
  have hcal_props : ∃ b0, callee.blocks[0]? = some b0 ∧ b0.params = [] ∧
      as.length = callee.params.length ∧ rs.length = callee.results ∧ 0 < M := by
    unfold calleeInlineOk at hok
    cases hb0 : callee.blocks[0]? with
    | none => rw [hb0] at hok; cases hok
    | some b0 =>
        rw [hb0] at hok
        simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hok
        exact ⟨b0, rfl, hok.1.1.1, hok.1.1.2, hok.1.2, (Array.getElem?_eq_some_iff.1 hb0).1⟩
  obtain ⟨calB0, hcalB0, hcalB0_par, has_len, hrs_len, hMpos⟩ := hcal_props
  -- Helper: caller `takeEdge` matching in `caller'`
  have callerTakeEdge : ∀ (mem : X86.Memory) (ctx : Word) (fr₁ fr₂ : Frame) (rest₁ rest₂ : List Frame)
      (ρ₁ ρ₂ : Env) (e : Edge) (s₁' : State) (b : Bool),
      fr₁.fn = fi → fr₂.fn = fi →
      EnvAgreeBelow off ρ₁ ρ₂ →
      (∀ a ∈ e.args, listLt off a.uses = true) →
      (fr₁.label ≠ callBlk ∧ fr₂.label = remapCallerLabel callBlk delta fr₁.label ∨
       fr₁.label = callBlk ∧ fr₂.label = callBlk + delta) →
              InlineStackRel callee fi gi callBlk callPos M rs off false rest₁ rest₂ →
      takeEdge caller { mem, ctx, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ₁ e = .next s₁' b →
      ∃ s₂', takeEdge caller' { mem, ctx, stack := fr₂ :: rest₂ } fr₂ rest₂ ρ₂ (remapCallerEdge callBlk delta e) = .next s₂' b ∧
        InlineStateRel callee fi gi callBlk callPos M rs off s₁' s₂' ∧
        b.toNat + inlinePot fi callBlk callPos s₂' ≤
          2 * b.toNat + inlinePot fi callBlk callPos { mem, ctx, stack := fr₂ :: rest₂ } := by
    intro mem ctx fr₁ fr₂ rest₁ rest₂ ρ₁ ρ₂ e s₁' b hfn1 hfn2 hag heargs hlbl hrest hte
    unfold takeEdge at hte
    cases hev : evalArgs ρ₁ e.args with
    | none => rw [hev] at hte; cases hte
    | some vs =>
        cases hftgt : caller.blocks[e.target]? with
        | none => rw [hev, hftgt] at hte; cases hte
        | some tgtB =>
            rw [hev, hftgt] at hte; dsimp only at hte
            cases hbp : bindParams ρ₁ tgtB.params vs with
            | none => rw [hbp] at hte; cases hte
            | some ρ₁' =>
                rw [hbp] at hte
                simp only [Step.next.injEq] at hte
                obtain ⟨rfl, rfl⟩ := hte
                have hev2 : evalArgs ρ₂ (remapCallerEdge callBlk delta e).args = some vs := by
                  simp only [remapCallerEdge]; rw [evalArgs_agreeBelow hag heargs, hev]
                obtain ⟨ρ₂', hbp2, hag'⟩ := bindParams_agreeBelow hag hbp
                have htgt2 : ∃ tgtB', caller'.blocks[remapCallerLabel callBlk delta e.target]? = some tgtB' ∧
                    tgtB'.params = tgtB.params := by
                  by_cases hlt : e.target < callBlk
                  · have hle : e.target ≤ callBlk := Nat.le_of_lt hlt
                    refine ⟨{ tgtB with term := remapCallerTerm callBlk delta tgtB.term }, ?_, rfl⟩
                    simp only [remapCallerLabel, hle, ↓reduceIte]
                    exact buildInlined_blocks_lt caller callee callBlk callPos blk rs as off hcallLt hlt hftgt
                  · by_cases heq : e.target = callBlk
                    · rw [heq] at hftgt ⊢
                      rw [hcall] at hftgt; cases hftgt
                      refine ⟨callBlkNew callBlk callPos blk as, ?_, rfl⟩
                      simp only [remapCallerLabel, Nat.le_refl, ↓reduceIte]
                      exact buildInlined_blocks_callBlk caller callee callBlk callPos blk rs as off hcallLt
                    · have hgt : callBlk < e.target :=
                        Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
                      have hnle : ¬ e.target ≤ callBlk := Nat.not_le_of_gt hgt
                      refine ⟨{ tgtB with term := remapCallerTerm callBlk delta tgtB.term }, ?_, rfl⟩
                      simp only [remapCallerLabel, hnle, ↓reduceIte]
                      exact buildInlined_blocks_gt caller callee callBlk callPos blk rs as off hcallLt hgt hftgt
                obtain ⟨tgtB', htgt2', hpar2⟩ := htgt2
                have hdelta_pos : 0 < delta := by dsimp [delta]; omega
                have hchg : decide (remapCallerLabel callBlk delta e.target ≤ fr₂.label) = decide (e.target ≤ fr₁.label) := by
                  rcases hlbl with ⟨hne, hfr2l⟩ | ⟨heq, hfr2l⟩
                  · rw [hfr2l]; exact remapCallerLabel_le_iff callBlk delta e.target fr₁.label hne
                  · rw [heq, hfr2l]; exact remapCallerLabel_le_cont callBlk delta e.target hdelta_pos
                have hte2 : takeEdge caller' { mem, ctx, stack := fr₂ :: rest₂ } fr₂ rest₂ ρ₂
                    (remapCallerEdge callBlk delta e) =
                    .next { mem, ctx, stack := { fr₂ with label := remapCallerLabel callBlk delta e.target, pos := 0, env := ρ₂' } :: rest₂ }
                      (decide (e.target ≤ fr₁.label)) := by
                  rw [← hchg]
                  exact takeEdge_ok hev2 htgt2' (by rw [hpar2]; exact hbp2)
                refine ⟨_, hte2, ⟨rfl, rfl, .normal ?_ hrest⟩, ?_⟩
                · simp only [NormalFrameRel, hfn1, ↓reduceIte]
                  refine ⟨hfn2, hag', (fun h => by cases h), ?_, ?_, ?_⟩
                  · intro _; exact ⟨rfl, trivial⟩
                  · intro heq _; rw [heq]; unfold remapCallerLabel; simp
                  · intro _ hgt; omega
                · simp only [inlinePot, List.map_cons, List.sum_cons]
                  by_cases hback : e.target ≤ fr₁.label
                  · simp only [hback, decide_true, Bool.toNat_true]
                    have hp' := inlineFramePot_le_one fi callBlk callPos
                      { fr₂ with label := remapCallerLabel callBlk delta e.target, pos := 0, env := ρ₂' }
                    omega
                  · simp only [hback, decide_false, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                    -- Forward edge in caller: `fr₁.label < e.target`!
                    have hpot_le : inlineFramePot fi callBlk callPos
                        { fr₂ with label := remapCallerLabel callBlk delta e.target, pos := 0, env := ρ₂' } ≤
                        inlineFramePot fi callBlk callPos fr₂ := by
                      rcases hlbl with ⟨hne, hfr2l⟩ | ⟨heq, hfr2l⟩
                      · by_cases hlt : fr₁.label < callBlk
                        · have : inlineFramePot fi callBlk callPos fr₂ = 1 := by
                            unfold inlineFramePot; rw [hfn2, hfr2l]; unfold remapCallerLabel
                            have hle : fr₁.label ≤ callBlk := Nat.le_of_lt hlt
                            simp [hle, hlt]
                          rw [this]; exact inlineFramePot_le_one ..
                        · have hgt1 : callBlk < fr₁.label := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
                          have hgt2 : callBlk < e.target := Nat.lt_trans hgt1 (Nat.lt_of_not_ge hback)
                          have hnle2 : ¬ e.target ≤ callBlk := Nat.not_le_of_gt hgt2
                          have : inlineFramePot fi callBlk callPos
                              { fr₂ with label := remapCallerLabel callBlk delta e.target, pos := 0, env := ρ₂' } = 0 := by
                            unfold inlineFramePot; unfold remapCallerLabel
                            simp only [hfn2, beq_self_eq_true, Bool.true_and, hnle2, ↓reduceIte]
                            have h1 : ¬ e.target + delta < callBlk := Nat.not_lt_of_ge (Nat.le_trans (Nat.le_of_lt hgt2) (Nat.le_add_right _ _))
                            have h2 : e.target + delta ≠ callBlk := Nat.ne_of_gt (Nat.lt_of_lt_of_le hgt2 (Nat.le_add_right _ _))
                            simp [h1, h2]
                          omega
                      · have hgt2 : callBlk < e.target := by rw [← heq]; exact Nat.lt_of_not_ge hback
                        have hnle2 : ¬ e.target ≤ callBlk := Nat.not_le_of_gt hgt2
                        have : inlineFramePot fi callBlk callPos
                            { fr₂ with label := remapCallerLabel callBlk delta e.target, pos := 0, env := ρ₂' } = 0 := by
                          unfold inlineFramePot; unfold remapCallerLabel
                          simp only [hfn2, beq_self_eq_true, Bool.true_and, hnle2, ↓reduceIte]
                          have h1 : ¬ e.target + delta < callBlk := Nat.not_lt_of_ge (Nat.le_trans (Nat.le_of_lt hgt2) (Nat.le_add_right _ _))
                          have h2 : e.target + delta ≠ callBlk := Nat.ne_of_gt (Nat.lt_of_lt_of_le hgt2 (Nat.le_add_right _ _))
                          simp [h1, h2]
                        omega
                    omega
  -- Helper: callee internal `takeEdge` matching inside `[callBlk + 1, callBlk + M]`
  have calleeTakeEdge : ∀ (mem : X86.Memory) (ctx : Word) (frC frP fr₂ : Frame) (rest₁ rest₂ : List Frame)
      (ρC ρ₂ : Env) (e : Edge) (s₁' : State) (b : Bool),
      frP.fn = fi → frP.label = callBlk → frP.pos = callPos + 1 → frP.dsts = rs →
      frC.fn = gi → frC.label < M →
      fr₂.fn = fi → fr₂.label = callBlk + 1 + frC.label →
      EnvAgreeBelow off frP.env ρ₂ → EnvShiftIncl off ρC ρ₂ →
      e.target ≠ 0 → e.target < M →
      InlineStackRel callee fi gi callBlk callPos M rs off false rest₁ rest₂ →
      takeEdge callee { mem, ctx, stack := frC :: frP :: rest₁ } frC (frP :: rest₁) ρC e = .next s₁' b →
      ∃ s₂', takeEdge caller' { mem, ctx, stack := fr₂ :: rest₂ } fr₂ rest₂ ρ₂
          (shiftEdge off (callBlk + 1) e) = .next s₂' b ∧
        InlineStateRel callee fi gi callBlk callPos M rs off s₁' s₂' ∧
        b.toNat + inlinePot fi callBlk callPos s₂' ≤
          2 * b.toNat + inlinePot fi callBlk callPos { mem, ctx, stack := fr₂ :: rest₂ } := by
    intro mem ctx frC frP fr₂ rest₁ rest₂ ρC ρ₂ e s₁' b hPfn hPlbl hPpos hPdst hCfn hClbl
      h2fn h2lbl hag hincl he0 helt hrest hte
    unfold takeEdge at hte
    cases hev : evalArgs ρC e.args with
    | none => rw [hev] at hte; cases hte
    | some vs =>
        cases hctgt : callee.blocks[e.target]? with
        | none => rw [hev, hctgt] at hte; cases hte
        | some tgtB =>
            rw [hev, hctgt] at hte; dsimp only at hte
            cases hbp : bindParams ρC tgtB.params vs with
            | none => rw [hbp] at hte; cases hte
            | some ρC' =>
                rw [hbp] at hte
                simp only [Step.next.injEq] at hte
                obtain ⟨rfl, rfl⟩ := hte
                have hev2 := shiftArgs_eval hincl hev
                have htgt2 := buildInlined_blocks_inlined caller callee callBlk callPos blk rs as off hcallLt hctgt
                have hpar2 : (inlineCalleeBlock callee callBlk blk rs off e.target tgtB).params =
                    tgtB.params.map (off + ·) := by
                  rw [inlineCalleeBlock_params]; simp [he0]
                obtain ⟨ρ₂', hbp2, hag', hincl'⟩ := bindParams_shift hag hincl hbp
                have hchg : decide (callBlk + 1 + e.target ≤ fr₂.label) = decide (e.target ≤ frC.label) := by
                  rw [h2lbl]; by_cases hle : e.target ≤ frC.label <;> simp [hle] <;> omega
                have hte2 : takeEdge caller' { mem, ctx, stack := fr₂ :: rest₂ } fr₂ rest₂ ρ₂
                    (shiftEdge off (callBlk + 1) e) =
                    .next { mem, ctx, stack := { fr₂ with label := callBlk + 1 + e.target, pos := 0, env := ρ₂' } :: rest₂ }
                      (decide (e.target ≤ frC.label)) := by
                  rw [← hchg]
                  exact takeEdge_ok hev2 htgt2 (by rw [hpar2]; exact hbp2)
                have hp_old : inlineFramePot fi callBlk callPos fr₂ = 0 := by
                  unfold inlineFramePot; rw [h2fn, h2lbl]
                  have h1 : ¬ callBlk + 1 + frC.label < callBlk := by omega
                  have h2 : callBlk + 1 + frC.label ≠ callBlk := by omega
                  simp [h1, h2]
                have hp_new : inlineFramePot fi callBlk callPos
                    { fr₂ with label := callBlk + 1 + e.target, pos := 0, env := ρ₂' } = 0 := by
                  unfold inlineFramePot; rw [h2fn]
                  have h1 : ¬ callBlk + 1 + e.target < callBlk := by omega
                  have h2 : callBlk + 1 + e.target ≠ callBlk := by omega
                  simp [h1, h2]
                refine ⟨_, hte2, ⟨rfl, rfl, .inlined ⟨hPfn, hPlbl, hPpos, hPdst, hCfn, helt,
                  (fun _ _ => Nat.zero_le _), h2fn, rfl, rfl, (fun h => by cases h), hag', hincl'⟩ hrest⟩, ?_⟩
                simp only [inlinePot, List.map_cons, List.sum_cons, hp_old, hp_new]
                omega
  -- Helper: match `.ret` of a top frame `fr₁` (`b = false`, `c = 0`)
  have matchNormalRet : ∀ (mem : X86.Memory) (ctx : Word) (fr₁ fr₂ : Frame) (rest₁ rest₂ : List Frame)
      (vs : List Word) (s₁' : State) (b : Bool),
      InlineStackRel callee fi gi callBlk callPos M rs off false rest₁ rest₂ →
      step q { mem, ctx, stack := fr₂ :: rest₂ } =
        (match rest₂ with
         | [] => Step.done vs mem
         | c :: rest' =>
             match bindParams c.env c.dsts vs with
             | some ρ => Step.next { mem, ctx, stack := { c with env := ρ, dsts := [] } :: rest' } false
             | none => Step.stuck) →
      (match rest₁ with
       | [] => Step.done vs mem
       | c :: rest' =>
           match bindParams c.env c.dsts vs with
           | some ρ => Step.next { mem, ctx, stack := { c with env := ρ, dsts := [] } :: rest' } false
           | none => Step.stuck) = .next s₁' b →
      ∃ s₂', Sem.Star (semStep q) { mem, ctx, stack := fr₂ :: rest₂ } b.toNat s₂' ∧
        InlineStateRel callee fi gi callBlk callPos M rs off s₁' s₂' ∧
        b.toNat + inlinePot fi callBlk callPos s₂' ≤
          2 * b.toNat + inlinePot fi callBlk callPos { mem, ctx, stack := fr₂ :: rest₂ } := by
    intro mem ctx fr₁ fr₂ rest₁ rest₂ vs s₁' b hrest hqstep hret
    cases hrest with
    | nil => cases hret
    | @normal _ c₁ c₂ r₁ r₂ hc hr =>
        dsimp only at hret hqstep
        cases hbp : bindParams c₁.env c₁.dsts vs with
        | none => rw [hbp] at hret; cases hret
        | some ρc₁' =>
            rw [hbp] at hret; simp only [Step.next.injEq] at hret; obtain ⟨rfl, rfl⟩ := hret
            by_cases hcfn : c₁.fn = fi
            · simp only [NormalFrameRel, hcfn, ↓reduceIte] at hc
              obtain ⟨hc2fn, hcag, hcdst, hcl1, hcl2, hcl3⟩ := hc
              obtain ⟨ρc₂', hbp2, hcag'⟩ := bindParams_agreeBelow hcag hbp
              rw [hcdst trivial, hbp2] at hqstep
              refine ⟨_, single_star_of_step hqstep, ⟨rfl, rfl, .normal ?_ hr⟩, ?_⟩
              · simp only [NormalFrameRel, hcfn, ↓reduceIte]
                exact ⟨hc2fn, hcag', (fun h => by cases h), hcl1, hcl2, hcl3⟩
              · simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                have : inlineFramePot fi callBlk callPos { c₂ with env := ρc₂', dsts := [] } =
                    inlineFramePot fi callBlk callPos c₂ := rfl
                omega
            · simp only [NormalFrameRel, hcfn, ↓reduceIte] at hc
              subst hc
              rw [hbp] at hqstep
              refine ⟨_, single_star_of_step hqstep, ⟨rfl, rfl, .normal (by simp [NormalFrameRel, hcfn]) hr⟩, ?_⟩
              simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
              have : inlineFramePot fi callBlk callPos { c₂ with env := ρc₁', dsts := [] } =
                  inlineFramePot fi callBlk callPos c₂ := rfl
              omega
    | @inlined _ cC cP c₂ r₁ r₂ hpair hr =>
        dsimp only at hret hqstep
        obtain ⟨hPfn, hPlbl, hPpos, hPdst, hCfn, hClbl, hCposLe, h2fn, h2lbl, h2pos, h2dst, hag, hincl⟩ := hpair
        cases hbp : bindParams cC.env cC.dsts vs with
        | none => rw [hbp] at hret; cases hret
        | some ρC' =>
            rw [hbp] at hret; simp only [Step.next.injEq] at hret; obtain ⟨rfl, rfl⟩ := hret
            obtain ⟨ρ₂', hbp2, hag', hincl'⟩ := bindParams_shift hag hincl hbp
            rw [h2dst rfl, hbp2] at hqstep
            refine ⟨_, single_star_of_step hqstep, ⟨rfl, rfl, .inlined ⟨hPfn, hPlbl, hPpos, hPdst, hCfn, hClbl,
              hCposLe, h2fn, h2lbl, h2pos, (fun h => by cases h), hag', hincl'⟩ hr⟩, ?_⟩
            simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
            have : inlineFramePot fi callBlk callPos { c₂ with env := ρ₂', dsts := [] } =
                inlineFramePot fi callBlk callPos c₂ := rfl
            omega
    | @tailReturn cP c₂ r₁ r₂ j Bt g tas hPfn hPlbl hPpos hPdst hj hBt hBterm hc2fn hc2lbl hc2pos hc2dst hag hr =>
        dsimp only at hret hqstep
        cases hbp : bindParams cP.env cP.dsts vs with
        | none => rw [hbp] at hret; cases hret
        | some ρP' =>
            rw [hbp] at hret; simp only [Step.next.injEq] at hret; obtain ⟨rfl, rfl⟩ := hret
            have hlen : (inlineTailFreshRs callee rs off j).length = vs.length := by
              rw [inlineTailFreshRs, List.length_map, List.length_range, ← hPdst]
              exact bindParams_len_eq' hbp
            obtain ⟨ρ₂_mid, hbp_mid⟩ := bindParams_of_eq_len' c₂.env (inlineTailFreshRs callee rs off j) vs hlen
            obtain ⟨hev_mid, hpres_mid⟩ := bindParams_nodup_evalArgs' (nodup_tailFreshRs callee rs off j) hbp_mid
            have hag_mid : EnvAgreeBelow off cP.env ρ₂_mid := by
              intro r hr_lt
              have hnotmem : r ∉ inlineTailFreshRs callee rs off j := fun hm =>
                Nat.not_lt_of_ge (mem_tailFreshRs_ge hm) hr_lt
              rw [hpres_mid r hnotmem]
              exact hag r hr_lt
            obtain ⟨ρ₂', hbp2, hag'⟩ := bindParams_agreeBelow hag_mid (by rw [hPdst] at hbp; exact hbp)
            rw [hc2dst, hbp_mid] at hqstep
            -- Step 2: from `c₂` at `(callBlk + 1 + j, Bt.body.size + 1)`, jump to `contBlk` (`callBlk + delta`)!
            have hBt2 := buildInlined_blocks_inlined caller callee callBlk callPos blk rs as off hcallLt hBt
            obtain ⟨hBt2_sz, _, hBt2_term⟩ := inlineCalleeBlock_tail (callee := callee) (callBlk := callBlk) (blk := blk)
              (rs := rs) (off := off) (j := j) hBterm
            have hcont := buildInlined_blocks_cont caller callee callBlk callPos blk rs as off hcallLt
            have hstep2_q : step q { mem, ctx, stack := { c₂ with env := ρ₂_mid, dsts := [] } :: r₂ } =
                .next { mem, ctx, stack := { c₂ with label := callBlk + delta, pos := 0, env := ρ₂', dsts := [] } :: r₂ } false := by
              have hpos_eq : ({ c₂ with env := ρ₂_mid, dsts := [] } : Frame).pos =
                  (inlineCalleeBlock callee callBlk blk rs off j Bt).body.size := by
                simp [hc2pos, hBt2_sz]
              rw [step_jump (p := q) (F := caller') (B := inlineCalleeBlock callee callBlk blk rs off j Bt)
                (by rw [hc2fn]; exact hqfi) (by rw [hc2lbl]; exact hBt2) hpos_eq hBt2_term]
              have hte2 := takeEdge_ok (F := caller')
                (s := { mem, ctx, stack := { c₂ with env := ρ₂_mid, dsts := [] } :: r₂ })
                (fr := { c₂ with env := ρ₂_mid, dsts := [] }) (rest := r₂) (ρ := ρ₂_mid)
                (e := { target := callBlk + delta, args := (inlineTailFreshRs callee rs off j).map .v })
                hev_mid hcont hbp2
              have hfwd : decide (callBlk + delta ≤ ({ c₂ with env := ρ₂_mid, dsts := [] } : Frame).label) = false := by
                simp only [hc2lbl, delta]; simp; omega
              rwa [hfwd] at hte2
            have hstar : Sem.Star (semStep q) { mem, ctx, stack := fr₂ :: c₂ :: r₂ } 0
                { mem, ctx, stack := { c₂ with label := callBlk + delta, pos := 0, env := ρ₂', dsts := [] } :: r₂ } :=
              .free (by rw [semStep, hqstep]; rfl) (.free (by rw [semStep, hstep2_q]; rfl) (.refl _))
            refine ⟨_, hstar, ⟨rfl, rfl, .normal ?_ hr⟩, ?_⟩
            · simp only [NormalFrameRel, hPfn, ↓reduceIte]
              exact ⟨hc2fn, hag', (fun h => by cases h), fun hne => absurd hPlbl hne,
                fun _ hle => by omega, fun _ _ => ⟨rfl, by omega⟩⟩
            · simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
              have hp_old : inlineFramePot fi callBlk callPos c₂ = 0 := by
                unfold inlineFramePot; rw [hc2fn, hc2lbl]
                have h1 : ¬ callBlk + 1 + j < callBlk := by omega
                have h2 : callBlk + 1 + j ≠ callBlk := by omega
                simp [h1, h2]
              have hp_new : inlineFramePot fi callBlk callPos
                  { c₂ with label := callBlk + delta, pos := 0, env := ρ₂', dsts := [] } = 0 := by
                unfold inlineFramePot; rw [hc2fn]
                have h1 : ¬ callBlk + delta < callBlk := by omega
                simp [h1]
              rw [hp_old, hp_new]; omega
  -- Construct `PotentialForward`
  refine ⟨by omega, ?_, ?_⟩
  · -- `next`
    intro s₁ s₁' s₂ b hrel hstep1
    rw [semStep_next] at hstep1
    rcases s₁ with ⟨mem₁, ctx₁, st₁⟩
    rcases s₂ with ⟨mem₂, ctx₂, st₂⟩
    obtain ⟨hmem_eq, hctx_eq, hstack⟩ := hrel
    obtain rfl : mem₁ = mem₂ := hmem_eq.symm
    obtain rfl : ctx₁ = ctx₂ := hctx_eq.symm
    cases hstack with
    | nil => simp [step] at hstep1
    | @normal _ fr₁ fr₂ rest₁ rest₂ hfr hrest =>
        by_cases hfn : fr₁.fn = fi
        · -- Top frame is in `fi` (`caller` vs `caller'`)
          simp only [NormalFrameRel, hfn, ↓reduceIte] at hfr
          obtain ⟨h2fn, hag, _, hlbl_ne, hlbl_le, hlbl_gt⟩ := hfr
          unfold step at hstep1; dsimp only at hstep1
          rw [hfn, hpfi] at hstep1; dsimp only at hstep1
          cases hB : caller.blocks[fr₁.label]? with
          | none => rw [hB] at hstep1; cases hstep1
          | some B =>
              rw [hB] at hstep1; dsimp only at hstep1
              have hBregs := blockRegsLt_of_func hregs hB
              -- Case split: is `fr₁.label = callBlk`?
              by_cases hcb : fr₁.label = callBlk
              · -- Inside `callBlk`!
                have hBeq : B = blk := by rw [hcb, hcall] at hB; exact Option.some.inj hB.symm
                obtain rfl : blk = B := hBeq.symm
                by_cases hlt_pos : fr₁.pos < callPos
                · -- Before the inlined call (`fr₁.pos < callPos`)
                  have hltB : fr₁.pos < blk.body.size := by omega
                  simp only [hltB, ↓reduceDIte] at hstep1
                  obtain ⟨h2lbl, h2pos⟩ := hlbl_le hcb (Nat.le_of_lt hlt_pos)
                  have hB2 := buildInlined_blocks_callBlk caller callee callBlk callPos blk rs as off hcallLt
                  have hltB2 : fr₂.pos < (callBlkNew callBlk callPos blk as).body.size := by
                    simp [callBlkNew, h2pos, Nat.min_eq_left (Nat.le_of_lt hposLt), hlt_pos]
                  have hstmt_eq : (callBlkNew callBlk callPos blk as).body[fr₂.pos]'hltB2 = blk.body[fr₁.pos]'hltB := by
                    simp [callBlkNew, h2pos, List.getElem_take]
                  have hst_uses := stmt_uses_lt_of_block hBregs hltB
                  cases hs : blk.body[fr₁.pos]'hltB with
                  | call rs' g' as' =>
                      rw [hs] at hstep1 hst_uses; dsimp only at hstep1
                      cases hev : evalArgs fr₁.env as' with
                      | none => rw [hev] at hstep1; cases hstep1
                      | some vs =>
                          rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                          cases hent : enter p g' vs with
                          | none => rw [hent] at hstep1; cases hstep1
                          | some calFr₁ =>
                              rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1
                              obtain ⟨rfl, rfl⟩ := hstep1
                              have hev2 : evalArgs fr₂.env as' = some vs := by
                                rw [evalArgs_agreeBelow hag (listLt_flatMap_uses hst_uses), hev]
                              obtain ⟨calFr₂, hent2, hcalRel⟩ :=
                                enter_rel (callee := callee) (callBlk := callBlk) (callPos := callPos) (off := off) hpfi hq hcaller'_par hent
                              have hstep2 := step_call (p := q) (F := caller') (B := callBlkNew callBlk callPos blk as)
                                (fr := fr₂) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                                (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) hltB2
                                (by rw [hstmt_eq, hs]) hev2 hent2
                              refine .inl ⟨1, _, single_star_of_step hstep2, ⟨rfl, rfl, .normal hcalRel (.normal ?_ hrest)⟩, ?_⟩
                              · simp only [NormalFrameRel, ↓reduceIte]
                                exact ⟨h2fn, hag, fun _ => trivial, fun hne => absurd hcb hne,
                                  fun _ _ => ⟨h2lbl, by omega⟩, fun _ hgt => by omega⟩
                              · simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_true]
                                have hc1 := inlineFramePot_le_one fi callBlk callPos calFr₂
                                have hc2 : inlineFramePot fi callBlk callPos { fr₂ with pos := fr₂.pos + 1, dsts := rs' } ≤
                                    inlineFramePot fi callBlk callPos fr₂ := by
                                  unfold inlineFramePot; rw [h2fn, h2lbl, h2pos]
                                  have : fr₁.pos + 1 ≤ callPos := by omega
                                  simp [Nat.lt_irrefl, Nat.le_of_lt hlt_pos, this]
                                omega
                  | assign _ _ | limb _ _ _ | store _ _ _ =>
                      rw [hs] at hstep1 hst_uses; dsimp only at hstep1
                      cases hx : (blk.body[fr₁.pos]'hltB).exec fr₁.env mem₁ ctx₁ with
                      | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                      | some p' =>
                          rcases p' with ⟨ρ₁', mem₁'⟩
                          have hx' := hx
                          rw [hs] at hx; rw [hx] at hstep1
                          simp only [Step.next.injEq] at hstep1
                          obtain ⟨rfl, rfl⟩ := hstep1
                          obtain ⟨ρ₂', hx2, hag'⟩ := stmt_exec_agreeBelow hag (by rw [hs]; exact hst_uses) hx'
                          have hnc : (blk.body[fr₁.pos]'hltB).isCall = false := by rw [hs]; rfl
                          have hstep2 := step_stmt (p := q) (F := caller') (B := callBlkNew callBlk callPos blk as)
                            (fr := fr₂) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                            (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) hltB2 hstmt_eq hnc hx2
                          refine .inl ⟨0, _, single_star_of_step hstep2, ⟨rfl, rfl, .normal ?_ hrest⟩, ?_⟩
                          · simp only [NormalFrameRel, ↓reduceIte]
                            exact ⟨h2fn, hag', (fun h => by cases h), fun hne => absurd hcb hne,
                              fun _ _ => ⟨h2lbl, by omega⟩, fun _ hgt => by omega⟩
                          · simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                            have hc2 : inlineFramePot fi callBlk callPos { fr₂ with pos := fr₂.pos + 1, env := ρ₂' } =
                                inlineFramePot fi callBlk callPos fr₂ := by
                              unfold inlineFramePot; rw [h2fn, h2lbl, h2pos]
                              have : fr₁.pos + 1 ≤ callPos := by omega
                              simp [Nat.lt_irrefl, Nat.le_of_lt hlt_pos, this]
                            omega
                · by_cases heq_pos : fr₁.pos = callPos
                  · -- AT THE INLINED CALL SITE (`fr₁.pos = callPos`)!!
                    have hltB : fr₁.pos < blk.body.size := by omega
                    simp only [hltB, ↓reduceDIte] at hstep1
                    have hget : blk.body[fr₁.pos]'hltB = .call rs gi as := by
                      have := (Array.getElem?_eq_some_iff.1 hpos).2
                      simpa [heq_pos] using this
                    rw [hget] at hstep1; dsimp only at hstep1
                    cases hev : evalArgs fr₁.env as with
                    | none => rw [hev] at hstep1; cases hstep1
                    | some vs =>
                        rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                        cases hent : enter p gi vs with
                        | none => rw [hent] at hstep1; cases hstep1
                        | some calFr₁ =>
                            rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1
                            obtain ⟨rfl, rfl⟩ := hstep1
                            unfold enter at hent; rw [hpgi] at hent
                            simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
                              Option.some.injEq] at hent
                            obtain ⟨ρC0, hbpC0, rfl⟩ := hent
                            obtain ⟨h2lbl, h2pos⟩ := hlbl_le hcb (by omega)
                            have hB2 := buildInlined_blocks_callBlk caller callee callBlk callPos blk rs as off hcallLt
                            have hpos2_eq : fr₂.pos = (callBlkNew callBlk callPos blk as).body.size := by
                              simp [callBlkNew, h2pos, heq_pos, Nat.min_eq_left (Nat.le_of_lt hposLt)]
                            have hev2 : evalArgs fr₂.env as = some vs := by
                              rw [evalArgs_agreeBelow hag hcall_args_lt, hev]
                            have hB_in0 := buildInlined_blocks_inlined caller callee callBlk callPos blk rs as off hcallLt hcalB0
                            obtain ⟨ρ₂', hbp2, hag', hincl'⟩ :=
                              bindParams_shift hag (envShiftIncl_empty off fr₂.env) hbpC0
                            have hpar0 : (inlineCalleeBlock callee callBlk blk rs off 0 calB0).params =
                                callee.params.map (off + ·) := by rw [inlineCalleeBlock_params]; rfl
                            have hstep2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } =
                                .next { mem := mem₁, ctx := ctx₁, stack := { fr₂ with label := callBlk + 1, pos := 0, env := ρ₂' } :: rest₂ } false := by
                              rw [step_jump (p := q) (F := caller') (B := callBlkNew callBlk callPos blk as)
                                (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) hpos2_eq rfl]
                              have hte2 := takeEdge_ok (F := caller') (s := { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ })
                                (fr := fr₂) (rest := rest₂) (ρ := fr₂.env) (e := { target := callBlk + 1, args := as })
                                hev2 hB_in0 (by rw [hpar0]; exact hbp2)
                              have hfwd : decide (callBlk + 1 ≤ fr₂.label) = false := by rw [h2lbl]; simp
                              rwa [hfwd] at hte2
                            have hp_old : inlineFramePot fi callBlk callPos fr₂ = 1 := by
                              unfold inlineFramePot; rw [h2fn, h2lbl, h2pos, heq_pos]; simp
                            have hp_new : inlineFramePot fi callBlk callPos
                                { fr₂ with label := callBlk + 1, pos := 0, env := ρ₂' } = 0 := by
                              unfold inlineFramePot; rw [h2fn]
                              have h1 : ¬ callBlk + 1 < callBlk := by omega
                              simp [h1]
                            -- `b = true` (source `.call`), `c = 0` (target forward `.jump`), pot drops `1 -> 0`!
                            refine .inl ⟨0, _, single_star_of_step hstep2, ⟨rfl, rfl, .inlined ?_ hrest⟩, ?_⟩
                            · exact ⟨rfl, hcb, by dsimp; omega, rfl, rfl, hMpos, (fun _ _ => Nat.zero_le _), h2fn, by simp, rfl, (fun h => by cases h), hag', hincl'⟩
                            · simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_true,
                                Nat.mul_zero, Nat.zero_add, hp_old, hp_new]
                              omega
                  · -- After the inlined call (`callPos < fr₁.pos`) -> executes in `contBlk`!
                    have hgt_pos : callPos < fr₁.pos := by omega
                    obtain ⟨h2lbl, h2pos⟩ := hlbl_gt hcb hgt_pos
                    have hB2 := buildInlined_blocks_cont caller callee callBlk callPos blk rs as off hcallLt
                    by_cases hltB : fr₁.pos < blk.body.size
                    · -- Statement in `contBlk`
                      simp only [hltB, ↓reduceDIte] at hstep1
                      have hltB2 : fr₂.pos < (contBlkNew callee callBlk callPos blk rs).body.size := by
                        simp [contBlkNew, h2pos]; omega
                      have hstmt_eq : (contBlkNew callee callBlk callPos blk rs).body[fr₂.pos]'hltB2 =
                          blk.body[fr₁.pos]'hltB := by
                        simp only [contBlkNew, h2pos, List.getElem_toArray, List.getElem_drop,
                          Array.getElem_toList]
                        congr 1; omega
                      have hst_uses := stmt_uses_lt_of_block hBregs hltB
                      cases hs : blk.body[fr₁.pos]'hltB with
                      | call rs' g' as' =>
                          rw [hs] at hstep1 hst_uses; dsimp only at hstep1
                          cases hev : evalArgs fr₁.env as' with
                          | none => rw [hev] at hstep1; cases hstep1
                          | some vs =>
                              rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                              cases hent : enter p g' vs with
                              | none => rw [hent] at hstep1; cases hstep1
                              | some calFr₁ =>
                                  rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1
                                  obtain ⟨rfl, rfl⟩ := hstep1
                                  have hev2 : evalArgs fr₂.env as' = some vs := by
                                    rw [evalArgs_agreeBelow hag (listLt_flatMap_uses hst_uses), hev]
                                  obtain ⟨calFr₂, hent2, hcalRel⟩ :=
                                    enter_rel (callee := callee) (callBlk := callBlk) (callPos := callPos) (off := off) hpfi hq hcaller'_par hent
                                  have hstep2 := step_call (p := q) (F := caller') (B := contBlkNew callee callBlk callPos blk rs)
                                    (fr := fr₂) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                                    (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) hltB2
                                    (by rw [hstmt_eq, hs]) hev2 hent2
                                  refine .inl ⟨1, _, single_star_of_step hstep2, ⟨rfl, rfl, .normal hcalRel (.normal ?_ hrest)⟩, ?_⟩
                                  · simp only [NormalFrameRel, ↓reduceIte]
                                    exact ⟨h2fn, hag, fun _ => trivial, fun hne => absurd hcb hne,
                                      fun _ hle => by omega, fun _ _ => ⟨h2lbl, by omega⟩⟩
                                  · simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_true]
                                    have hc1 := inlineFramePot_le_one fi callBlk callPos calFr₂
                                    have hp0 : inlineFramePot fi callBlk callPos { fr₂ with pos := fr₂.pos + 1, dsts := rs' } = 0 := by
                                      unfold inlineFramePot; rw [h2fn, h2lbl]
                                      simp
                                    omega
                      | assign _ _ | limb _ _ _ | store _ _ _ =>
                          rw [hs] at hstep1 hst_uses; dsimp only at hstep1
                          cases hx : (blk.body[fr₁.pos]'hltB).exec fr₁.env mem₁ ctx₁ with
                          | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                          | some p' =>
                              rcases p' with ⟨ρ₁', mem₁'⟩
                              have hx' := hx
                              rw [hs] at hx; rw [hx] at hstep1
                              simp only [Step.next.injEq] at hstep1
                              obtain ⟨rfl, rfl⟩ := hstep1
                              obtain ⟨ρ₂', hx2, hag'⟩ := stmt_exec_agreeBelow hag (by rw [hs]; exact hst_uses) hx'
                              have hnc : (blk.body[fr₁.pos]'hltB).isCall = false := by rw [hs]; rfl
                              have hstep2 := step_stmt (p := q) (F := caller') (B := contBlkNew callee callBlk callPos blk rs)
                                (fr := fr₂) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                                (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) hltB2 hstmt_eq hnc hx2
                              refine .inl ⟨0, _, single_star_of_step hstep2, ⟨rfl, rfl, .normal ?_ hrest⟩, ?_⟩
                              · simp only [NormalFrameRel, ↓reduceIte]
                                exact ⟨h2fn, hag', (fun h => by cases h), fun hne => absurd hcb hne,
                                  fun _ hle => by omega, fun _ _ => ⟨h2lbl, by omega⟩⟩
                              · simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                                have hp0 : inlineFramePot fi callBlk callPos { fr₂ with pos := fr₂.pos + 1, env := ρ₂' } = 0 := by
                                  unfold inlineFramePot; rw [h2fn, h2lbl]
                                  simp
                                omega
                    · -- Terminator of `contBlk` (only reachable when `fr₁.pos = blk.body.size` or `≥`)
                      simp only [hltB, ↓reduceDIte] at hstep1
                      have hltB2 : ¬ fr₂.pos < (contBlkNew callee callBlk callPos blk rs).body.size := by
                        simp [contBlkNew, h2pos]; omega
                      have hstep2_unfold := step_at_term (p := q) (F := caller')
                        (B := contBlkNew callee callBlk callPos blk rs)
                        (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂)
                        (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) hltB2
                      obtain ⟨htuses, hedges⟩ := term_uses_lt_of_block hBregs
                      cases ht : blk.term with
                      | jump e =>
                          rw [ht] at hstep1 hedges; dsimp only at hstep1
                          obtain ⟨s₂', hte2, hrel', hpot'⟩ := callerTakeEdge mem₁ ctx₁ fr₁ fr₂ rest₁ rest₂ fr₁.env fr₂.env e s₁' b
                            hfn h2fn hag (edge_args_lt_of_term hedges (by simp [Term.edges])) (.inr ⟨hcb, h2lbl⟩) hrest hstep1
                          rw [contBlkNew, ht, remapCallerTerm] at hstep2_unfold; dsimp only at hstep2_unfold
                          exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                      | br c w a b' t f =>
                          rw [ht] at hstep1 htuses hedges; dsimp only at hstep1
                          simp only [Term.uses, listLt_append] at htuses
                          cases ha : a.eval fr₁.env with
                          | none => rw [ha] at hstep1; cases hstep1
                          | some va =>
                              cases hb' : b'.eval fr₁.env with
                              | none => rw [ha, hb'] at hstep1; cases hstep1
                              | some vb =>
                                  rw [ha, hb'] at hstep1; dsimp only at hstep1
                                  rw [contBlkNew, ht, remapCallerTerm] at hstep2_unfold; dsimp only at hstep2_unfold
                                  simp only [arg_eval_agreeBelow hag htuses.1, arg_eval_agreeBelow hag htuses.2, ha, hb'] at hstep2_unfold
                                  cases hcond : c.holds w va vb <;> rw [hcond] at hstep1 hstep2_unfold
                                  · obtain ⟨s₂', hte2, hrel', hpot'⟩ := callerTakeEdge mem₁ ctx₁ fr₁ fr₂ rest₁ rest₂ fr₁.env fr₂.env f s₁' b
                                      hfn h2fn hag (edge_args_lt_of_term hedges (by simp [Term.edges])) (.inr ⟨hcb, h2lbl⟩) hrest hstep1
                                    exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                                  · obtain ⟨s₂', hte2, hrel', hpot'⟩ := callerTakeEdge mem₁ ctx₁ fr₁ fr₂ rest₁ rest₂ fr₁.env fr₂.env t s₁' b
                                      hfn h2fn hag (edge_args_lt_of_term hedges (by simp [Term.edges])) (.inr ⟨hcb, h2lbl⟩) hrest hstep1
                                    exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                      | brOvf o x a b' ok ovf =>
                          rw [ht] at hstep1 htuses hedges; dsimp only at hstep1
                          simp only [Term.uses, listLt_append] at htuses
                          cases ha : a.eval fr₁.env with
                          | none => rw [ha] at hstep1; cases hstep1
                          | some va =>
                              cases hb' : b'.eval fr₁.env with
                              | none => rw [ha, hb'] at hstep1; cases hstep1
                              | some vb =>
                                  rw [ha, hb'] at hstep1; dsimp only at hstep1
                                  rw [contBlkNew, ht, remapCallerTerm] at hstep2_unfold; dsimp only at hstep2_unfold
                                  simp only [arg_eval_agreeBelow hag htuses.1, arg_eval_agreeBelow hag htuses.2, ha, hb'] at hstep2_unfold
                                  cases hovf : (o.eval va vb).2 <;> simp only [hovf, Bool.false_eq_true, ↓reduceIte] at hstep1 hstep2_unfold
                                  · obtain ⟨s₂', hte2, hrel', hpot'⟩ := callerTakeEdge mem₁ ctx₁ fr₁ fr₂ rest₁ rest₂
                                      (fr₁.env.insert x (o.eval va vb).1) (fr₂.env.insert x (o.eval va vb).1) ok s₁' b
                                      hfn h2fn (envAgreeBelow_insert_lt hag _) (edge_args_lt_of_term hedges (by simp [Term.edges])) (.inr ⟨hcb, h2lbl⟩) hrest hstep1
                                    exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                                  · obtain ⟨s₂', hte2, hrel', hpot'⟩ := callerTakeEdge mem₁ ctx₁ fr₁ fr₂ rest₁ rest₂
                                      (fr₁.env.insert x (o.eval va vb).1) (fr₂.env.insert x (o.eval va vb).1) ovf s₁' b
                                      hfn h2fn (envAgreeBelow_insert_lt hag _) (edge_args_lt_of_term hedges (by simp [Term.edges])) (.inr ⟨hcb, h2lbl⟩) hrest hstep1
                                    exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                      | ret ras =>
                          rw [ht] at hstep1 htuses; dsimp only at hstep1
                          cases hev : evalArgs fr₁.env ras with
                          | none => rw [hev] at hstep1; cases hstep1
                          | some vs =>
                              rw [hev] at hstep1; dsimp only at hstep1
                              simp only [contBlkNew, ht, remapCallerTerm] at hstep2_unfold
                              simp only [evalArgs_agreeBelow hag (listLt_flatMap_uses htuses), hev] at hstep2_unfold
                              obtain ⟨s₂', hstar, hrel', hpot'⟩ := matchNormalRet mem₁ ctx₁ fr₁ fr₂ rest₁ rest₂ vs s₁' b hrest hstep2_unfold hstep1
                              exact .inl ⟨b.toNat, s₂', hstar, hrel', hpot'⟩
                      | tail g tas =>
                          rw [ht] at hstep1 htuses; dsimp only at hstep1
                          cases hev : evalArgs fr₁.env tas with
                          | none => rw [hev] at hstep1; cases hstep1
                          | some vs =>
                              rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                              cases hent : enter p g vs with
                              | none => rw [hent] at hstep1; cases hstep1
                              | some calFr₁ =>
                                  rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1
                                  obtain ⟨rfl, rfl⟩ := hstep1
                                  obtain ⟨calFr₂, hent2, hcalRel⟩ :=
                                    enter_rel (callee := callee) (callBlk := callBlk) (callPos := callPos) (off := off) hpfi hq hcaller'_par hent
                                  simp only [contBlkNew, ht, remapCallerTerm] at hstep2_unfold
                                  simp only [evalArgs_agreeBelow hag (listLt_flatMap_uses htuses), hev,
                                    Option.bind_eq_bind, Option.bind_some, hent2] at hstep2_unfold
                                  refine .inl ⟨1, _, single_star_of_step hstep2_unfold, ⟨rfl, rfl, .normal hcalRel hrest⟩, ?_⟩
                                  simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_true]
                                  have := inlineFramePot_le_one fi callBlk callPos calFr₂
                                  omega
                      | fail _ | trap => rw [ht] at hstep1; cases hstep1
              · -- `fr₁.label ≠ callBlk` in `caller`!
                obtain ⟨h2lbl, h2pos⟩ := hlbl_ne hcb
                have hB2 : caller'.blocks[fr₂.label]? = some { B with term := remapCallerTerm callBlk delta B.term } := by
                  rw [h2lbl]
                  by_cases hlt : fr₁.label < callBlk
                  · have hle : fr₁.label ≤ callBlk := Nat.le_of_lt hlt
                    simp only [remapCallerLabel, hle, ↓reduceIte]
                    exact buildInlined_blocks_lt caller callee callBlk callPos blk rs as off hcallLt hlt hB
                  · have hgt : callBlk < fr₁.label :=
                      Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hcb)
                    have hnle : ¬ fr₁.label ≤ callBlk := Nat.not_le_of_gt hgt
                    simp only [remapCallerLabel, hnle, ↓reduceIte]
                    exact buildInlined_blocks_gt caller callee callBlk callPos blk rs as off hcallLt hgt hB
                by_cases hltB : fr₁.pos < B.body.size
                · -- Statement in block `fr₁.label ≠ callBlk`
                  simp only [hltB, ↓reduceDIte] at hstep1
                  have hltB2 : fr₂.pos < ({ B with term := remapCallerTerm callBlk delta B.term } : Block).body.size := by
                    simpa [h2pos] using hltB
                  have hstmt_eq : ({ B with term := remapCallerTerm callBlk delta B.term } : Block).body[fr₂.pos]'hltB2 =
                      B.body[fr₁.pos]'hltB := by simp [h2pos]
                  have hst_uses := stmt_uses_lt_of_block hBregs hltB
                  cases hs : B.body[fr₁.pos]'hltB with
                  | call rs' g' as' =>
                      rw [hs] at hstep1 hst_uses; dsimp only at hstep1
                      cases hev : evalArgs fr₁.env as' with
                      | none => rw [hev] at hstep1; cases hstep1
                      | some vs =>
                          rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                          cases hent : enter p g' vs with
                          | none => rw [hent] at hstep1; cases hstep1
                          | some calFr₁ =>
                              rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1
                              obtain ⟨rfl, rfl⟩ := hstep1
                              have hev2 : evalArgs fr₂.env as' = some vs := by
                                rw [evalArgs_agreeBelow hag (listLt_flatMap_uses hst_uses), hev]
                              obtain ⟨calFr₂, hent2, hcalRel⟩ :=
                                enter_rel (callee := callee) (callBlk := callBlk) (callPos := callPos) (off := off) hpfi hq hcaller'_par hent
                              have hstep2 := step_call (p := q) (F := caller') (B := { B with term := remapCallerTerm callBlk delta B.term })
                                (fr := fr₂) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                                (by rw [h2fn]; exact hqfi) hB2 hltB2 (by rw [hstmt_eq, hs]) hev2 hent2
                              refine .inl ⟨1, _, single_star_of_step hstep2, ⟨rfl, rfl, .normal hcalRel (.normal ?_ hrest)⟩, ?_⟩
                              · simp only [NormalFrameRel, ↓reduceIte]
                                exact ⟨h2fn, hag, fun _ => trivial, fun _ => ⟨h2lbl, by omega⟩,
                                  fun h => absurd h hcb, fun h => absurd h hcb⟩
                              · simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_true]
                                have hc1 := inlineFramePot_le_one fi callBlk callPos calFr₂
                                have hc2 : inlineFramePot fi callBlk callPos { fr₂ with pos := fr₂.pos + 1, dsts := rs' } =
                                    inlineFramePot fi callBlk callPos fr₂ := by
                                  unfold inlineFramePot; rw [h2fn, h2lbl]
                                  have hne2 : remapCallerLabel callBlk (callee.blocks.size + 1) fr₁.label ≠ callBlk := by
                                    unfold remapCallerLabel; split
                                    · exact hcb
                                    · rename_i hn
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_not_ge hn) (Nat.le_add_right _ _))
                                  simp [hne2]
                                omega
                  | assign _ _ | limb _ _ _ | store _ _ _ =>
                      rw [hs] at hstep1 hst_uses; dsimp only at hstep1
                      cases hx : (B.body[fr₁.pos]'hltB).exec fr₁.env mem₁ ctx₁ with
                      | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                      | some p' =>
                          rcases p' with ⟨ρ₁', mem₁'⟩
                          have hx' := hx
                          rw [hs] at hx; rw [hx] at hstep1
                          simp only [Step.next.injEq] at hstep1
                          obtain ⟨rfl, rfl⟩ := hstep1
                          obtain ⟨ρ₂', hx2, hag'⟩ := stmt_exec_agreeBelow hag (by rw [hs]; exact hst_uses) hx'
                          have hnc : (B.body[fr₁.pos]'hltB).isCall = false := by rw [hs]; rfl
                          have hstep2 := step_stmt (p := q) (F := caller') (B := { B with term := remapCallerTerm callBlk delta B.term })
                            (fr := fr₂) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                            (by rw [h2fn]; exact hqfi) hB2 hltB2 hstmt_eq hnc hx2
                          refine .inl ⟨0, _, single_star_of_step hstep2, ⟨rfl, rfl, .normal ?_ hrest⟩, ?_⟩
                          · simp only [NormalFrameRel, ↓reduceIte]
                            exact ⟨h2fn, hag', (fun h => by cases h), fun _ => ⟨h2lbl, by omega⟩,
                              fun h => absurd h hcb, fun h => absurd h hcb⟩
                          · simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                            have hc2 : inlineFramePot fi callBlk callPos { fr₂ with pos := fr₂.pos + 1, env := ρ₂' } =
                                inlineFramePot fi callBlk callPos fr₂ := by
                              unfold inlineFramePot; rw [h2fn, h2lbl]
                              have hne2 : remapCallerLabel callBlk (callee.blocks.size + 1) fr₁.label ≠ callBlk := by
                                unfold remapCallerLabel; split
                                · exact hcb
                                · rename_i hn
                                  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_not_ge hn) (Nat.le_add_right _ _))
                              simp [hne2]
                            omega
                · -- Terminator in block `fr₁.label ≠ callBlk`
                  simp only [hltB, ↓reduceDIte] at hstep1
                  have hltB2 : ¬ fr₂.pos < ({ B with term := remapCallerTerm callBlk delta B.term } : Block).body.size := by
                    simpa [h2pos] using hltB
                  have hstep2_unfold := step_at_term (p := q) (F := caller')
                    (B := { B with term := remapCallerTerm callBlk delta B.term })
                    (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂)
                    (by rw [h2fn]; exact hqfi) hB2 hltB2
                  obtain ⟨htuses, hedges⟩ := term_uses_lt_of_block hBregs
                  cases ht : B.term with
                  | jump e =>
                      rw [ht] at hstep1 hedges; dsimp only at hstep1
                      obtain ⟨s₂', hte2, hrel', hpot'⟩ := callerTakeEdge mem₁ ctx₁ fr₁ fr₂ rest₁ rest₂ fr₁.env fr₂.env e s₁' b
                        hfn h2fn hag (edge_args_lt_of_term hedges (by simp [Term.edges])) (.inl ⟨hcb, h2lbl⟩) hrest hstep1
                      rw [ht, remapCallerTerm] at hstep2_unfold; dsimp only at hstep2_unfold
                      exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                  | br c w a b' t f =>
                      rw [ht] at hstep1 htuses hedges; dsimp only at hstep1
                      simp only [Term.uses, listLt_append] at htuses
                      cases ha : a.eval fr₁.env with
                      | none => rw [ha] at hstep1; cases hstep1
                      | some va =>
                          cases hb' : b'.eval fr₁.env with
                          | none => rw [ha, hb'] at hstep1; cases hstep1
                          | some vb =>
                              rw [ha, hb'] at hstep1; dsimp only at hstep1
                              rw [ht, remapCallerTerm] at hstep2_unfold; dsimp only at hstep2_unfold
                              simp only [arg_eval_agreeBelow hag htuses.1, arg_eval_agreeBelow hag htuses.2, ha, hb'] at hstep2_unfold
                              cases hcond : c.holds w va vb <;> rw [hcond] at hstep1 hstep2_unfold
                              · obtain ⟨s₂', hte2, hrel', hpot'⟩ := callerTakeEdge mem₁ ctx₁ fr₁ fr₂ rest₁ rest₂ fr₁.env fr₂.env f s₁' b
                                  hfn h2fn hag (edge_args_lt_of_term hedges (by simp [Term.edges])) (.inl ⟨hcb, h2lbl⟩) hrest hstep1
                                exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                              · obtain ⟨s₂', hte2, hrel', hpot'⟩ := callerTakeEdge mem₁ ctx₁ fr₁ fr₂ rest₁ rest₂ fr₁.env fr₂.env t s₁' b
                                  hfn h2fn hag (edge_args_lt_of_term hedges (by simp [Term.edges])) (.inl ⟨hcb, h2lbl⟩) hrest hstep1
                                exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                  | brOvf o x a b' ok ovf =>
                      rw [ht] at hstep1 htuses hedges; dsimp only at hstep1
                      simp only [Term.uses, listLt_append] at htuses
                      cases ha : a.eval fr₁.env with
                      | none => rw [ha] at hstep1; cases hstep1
                      | some va =>
                          cases hb' : b'.eval fr₁.env with
                          | none => rw [ha, hb'] at hstep1; cases hstep1
                          | some vb =>
                              rw [ha, hb'] at hstep1; dsimp only at hstep1
                              rw [ht, remapCallerTerm] at hstep2_unfold; dsimp only at hstep2_unfold
                              simp only [arg_eval_agreeBelow hag htuses.1, arg_eval_agreeBelow hag htuses.2, ha, hb'] at hstep2_unfold
                              cases hovf : (o.eval va vb).2 <;> simp only [hovf, Bool.false_eq_true, ↓reduceIte] at hstep1 hstep2_unfold
                              · obtain ⟨s₂', hte2, hrel', hpot'⟩ := callerTakeEdge mem₁ ctx₁ fr₁ fr₂ rest₁ rest₂
                                  (fr₁.env.insert x (o.eval va vb).1) (fr₂.env.insert x (o.eval va vb).1) ok s₁' b
                                  hfn h2fn (envAgreeBelow_insert_lt hag _) (edge_args_lt_of_term hedges (by simp [Term.edges])) (.inl ⟨hcb, h2lbl⟩) hrest hstep1
                                exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                              · obtain ⟨s₂', hte2, hrel', hpot'⟩ := callerTakeEdge mem₁ ctx₁ fr₁ fr₂ rest₁ rest₂
                                  (fr₁.env.insert x (o.eval va vb).1) (fr₂.env.insert x (o.eval va vb).1) ovf s₁' b
                                  hfn h2fn (envAgreeBelow_insert_lt hag _) (edge_args_lt_of_term hedges (by simp [Term.edges])) (.inl ⟨hcb, h2lbl⟩) hrest hstep1
                                exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                  | ret ras =>
                      rw [ht] at hstep1 htuses; dsimp only at hstep1
                      cases hev : evalArgs fr₁.env ras with
                      | none => rw [hev] at hstep1; cases hstep1
                      | some vs =>
                          rw [hev] at hstep1; dsimp only at hstep1
                          simp only [ht, remapCallerTerm] at hstep2_unfold
                          simp only [evalArgs_agreeBelow hag (listLt_flatMap_uses htuses), hev] at hstep2_unfold
                          obtain ⟨s₂', hstar, hrel', hpot'⟩ := matchNormalRet mem₁ ctx₁ fr₁ fr₂ rest₁ rest₂ vs s₁' b hrest hstep2_unfold hstep1
                          exact .inl ⟨b.toNat, s₂', hstar, hrel', hpot'⟩
                  | tail g tas =>
                      rw [ht] at hstep1 htuses; dsimp only at hstep1
                      cases hev : evalArgs fr₁.env tas with
                      | none => rw [hev] at hstep1; cases hstep1
                      | some vs =>
                          rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                          cases hent : enter p g vs with
                          | none => rw [hent] at hstep1; cases hstep1
                          | some calFr₁ =>
                              rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1
                              obtain ⟨rfl, rfl⟩ := hstep1
                              obtain ⟨calFr₂, hent2, hcalRel⟩ :=
                                enter_rel (callee := callee) (callBlk := callBlk) (callPos := callPos) (off := off) hpfi hq hcaller'_par hent
                              simp only [ht, remapCallerTerm] at hstep2_unfold
                              simp only [evalArgs_agreeBelow hag (listLt_flatMap_uses htuses), hev,
                                Option.bind_eq_bind, Option.bind_some, hent2] at hstep2_unfold
                              refine .inl ⟨1, _, single_star_of_step hstep2_unfold, ⟨rfl, rfl, .normal hcalRel hrest⟩, ?_⟩
                              simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_true]
                              have := inlineFramePot_le_one fi callBlk callPos calFr₂
                              omega
                  | fail _ | trap => rw [ht] at hstep1; cases hstep1
        · -- Top frame is in some other function `fr₁.fn ≠ fi` (`fr₂ = fr₁`)
          simp only [NormalFrameRel, hfn, ↓reduceIte] at hfr
          obtain rfl : fr₁ = fr₂ := hfr.symm
          unfold step at hstep1; dsimp only at hstep1
          cases hF : p.funcs[fr₁.fn]? with
          | none => rw [hF] at hstep1; cases hstep1
          | some F =>
              have hqF : q.funcs[fr₁.fn]? = some F := by
                rw [hq]; simp [Array.set!_eq_setIfInBounds, Ne.symm hfn, hF]
              rw [hF] at hstep1; dsimp only at hstep1
              cases hB : F.blocks[fr₁.label]? with
              | none => rw [hB] at hstep1; cases hstep1
              | some B =>
                  rw [hB] at hstep1; dsimp only at hstep1
                  have hp0 : inlineFramePot fi callBlk callPos fr₁ = 0 := by
                    unfold inlineFramePot; simp [hfn]
                  by_cases hltB : fr₁.pos < B.body.size
                  · simp only [hltB, ↓reduceDIte] at hstep1
                    cases hs : B.body[fr₁.pos]'hltB with
                    | call rs' g' as' =>
                        rw [hs] at hstep1; dsimp only at hstep1
                        cases hev : evalArgs fr₁.env as' with
                        | none => rw [hev] at hstep1; cases hstep1
                        | some vs =>
                            rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                            cases hent : enter p g' vs with
                            | none => rw [hent] at hstep1; cases hstep1
                            | some calFr₁ =>
                                rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1
                                obtain ⟨rfl, rfl⟩ := hstep1
                                obtain ⟨calFr₂, hent2, hcalRel⟩ :=
                                  enter_rel (callee := callee) (callBlk := callBlk) (callPos := callPos) (off := off) hpfi hq hcaller'_par hent
                                have hstep2 := step_call (p := q) (F := F) (B := B)
                                  (fr := fr₁) (rest := rest₂) (mem := mem₁) (ctx := ctx₁) hqF hB hltB hs hev hent2
                                refine .inl ⟨1, _, single_star_of_step hstep2,
                                  ⟨rfl, rfl, .normal hcalRel (.normal (by simp [NormalFrameRel, hfn]) hrest)⟩, ?_⟩
                                simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_true]
                                have hc1 := inlineFramePot_le_one fi callBlk callPos calFr₂
                                have hc2 : inlineFramePot fi callBlk callPos { fr₁ with pos := fr₁.pos + 1, dsts := rs' } = 0 := by
                                  unfold inlineFramePot; simp [hfn]
                                omega
                    | assign _ _ | limb _ _ _ | store _ _ _ =>
                        rw [hs] at hstep1; dsimp only at hstep1
                        cases hx : (B.body[fr₁.pos]'hltB).exec fr₁.env mem₁ ctx₁ with
                        | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                        | some p' =>
                            rcases p' with ⟨ρ₁', mem₁'⟩
                            have hx' := hx
                            rw [hs] at hx; rw [hx] at hstep1
                            simp only [Step.next.injEq] at hstep1
                            obtain ⟨rfl, rfl⟩ := hstep1
                            have hnc : (B.body[fr₁.pos]'hltB).isCall = false := by rw [hs]; rfl
                            have hstep2 := step_stmt (p := q) (F := F) (B := B)
                              (fr := fr₁) (rest := rest₂) (mem := mem₁) (ctx := ctx₁) hqF hB hltB rfl hnc hx'
                            refine .inl ⟨0, _, single_star_of_step hstep2,
                              ⟨rfl, rfl, .normal (by simp [NormalFrameRel, hfn]) hrest⟩, ?_⟩
                            simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                            have hc2 : inlineFramePot fi callBlk callPos { fr₁ with pos := fr₁.pos + 1, env := ρ₁' } = 0 := by
                              unfold inlineFramePot; simp [hfn]
                            omega
                  · simp only [hltB, ↓reduceDIte] at hstep1
                    have hstep2_unfold := step_at_term (p := q) (F := F) (B := B)
                      (mem := mem₁) (ctx := ctx₁) (fr := fr₁) (rest := rest₂) hqF hB hltB
                    have sameTakeEdge : ∀ (ρ : Env) (e : Edge),
                        takeEdge F { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ e = .next s₁' b →
                        ∃ s₂', takeEdge F { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } fr₁ rest₂ ρ e = .next s₂' b ∧
                          InlineStateRel callee fi gi callBlk callPos M rs off s₁' s₂' ∧
                          b.toNat + inlinePot fi callBlk callPos s₂' ≤
                            2 * b.toNat + inlinePot fi callBlk callPos { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } := by
                      intro ρ e hte
                      unfold takeEdge at hte
                      cases hev : evalArgs ρ e.args with
                      | none => rw [hev] at hte; cases hte
                      | some vs =>
                          cases htgt : F.blocks[e.target]? with
                          | none => rw [hev, htgt] at hte; cases hte
                          | some tgtB =>
                              rw [hev, htgt] at hte; dsimp only at hte
                              cases hbp : bindParams ρ tgtB.params vs with
                              | none => rw [hbp] at hte; cases hte
                              | some ρ' =>
                                  rw [hbp] at hte; simp only [Step.next.injEq] at hte; obtain ⟨rfl, rfl⟩ := hte
                                  refine ⟨_, takeEdge_ok hev htgt hbp,
                                    ⟨rfl, rfl, .normal (by simp [NormalFrameRel, hfn]) hrest⟩, ?_⟩
                                  simp only [inlinePot, List.map_cons, List.sum_cons, hp0]
                                  have : inlineFramePot fi callBlk callPos { fr₁ with label := e.target, pos := 0, env := ρ' } = 0 := by
                                    unfold inlineFramePot; simp [hfn]
                                  omega
                    cases ht : B.term with
                    | jump e =>
                        rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                        obtain ⟨s₂', hte2, hrel', hpot'⟩ := sameTakeEdge fr₁.env e hstep1
                        exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                    | br c w a b' t f =>
                        rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                        cases ha : a.eval fr₁.env with
                        | none => rw [ha] at hstep1; cases hstep1
                        | some va =>
                            cases hb' : b'.eval fr₁.env with
                            | none => rw [ha, hb'] at hstep1; cases hstep1
                            | some vb =>
                                rw [ha, hb'] at hstep1 hstep2_unfold
                                obtain ⟨s₂', hte2, hrel', hpot'⟩ := sameTakeEdge fr₁.env (if c.holds w va vb then t else f) hstep1
                                exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                    | brOvf o x a b' ok ovf =>
                        rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                        cases ha : a.eval fr₁.env with
                        | none => rw [ha] at hstep1; cases hstep1
                        | some va =>
                            cases hb' : b'.eval fr₁.env with
                            | none => rw [ha, hb'] at hstep1; cases hstep1
                            | some vb =>
                                rw [ha, hb'] at hstep1 hstep2_unfold
                                obtain ⟨s₂', hte2, hrel', hpot'⟩ := sameTakeEdge (fr₁.env.insert x (o.eval va vb).1)
                                  (if (o.eval va vb).2 then ovf else ok) hstep1
                                exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                    | ret ras =>
                        rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                        cases hev : evalArgs fr₁.env ras with
                        | none => rw [hev] at hstep1; cases hstep1
                        | some vs =>
                            rw [hev] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                            obtain ⟨s₂', hstar, hrel', hpot'⟩ := matchNormalRet mem₁ ctx₁ fr₁ fr₁ rest₁ rest₂ vs s₁' b hrest hstep2_unfold hstep1
                            exact .inl ⟨b.toNat, s₂', hstar, hrel', hpot'⟩
                    | tail g tas =>
                        rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                        cases hev : evalArgs fr₁.env tas with
                        | none => rw [hev] at hstep1; cases hstep1
                        | some vs =>
                            rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                            cases hent : enter p g vs with
                            | none => rw [hent] at hstep1; cases hstep1
                            | some calFr₁ =>
                                rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1
                                obtain ⟨rfl, rfl⟩ := hstep1
                                obtain ⟨calFr₂, hent2, hcalRel⟩ :=
                                  enter_rel (callee := callee) (callBlk := callBlk) (callPos := callPos) (off := off) hpfi hq hcaller'_par hent
                                simp only [hev, Option.bind_eq_bind, Option.bind_some, hent2] at hstep2_unfold
                                refine .inl ⟨1, _, single_star_of_step hstep2_unfold, ⟨rfl, rfl, .normal hcalRel hrest⟩, ?_⟩
                                simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_true, hp0]
                                have := inlineFramePot_le_one fi callBlk callPos calFr₂
                                omega
                    | fail _ | trap => rw [ht] at hstep1; cases hstep1
    | @inlined _ frC frP fr₂ rest₁ rest₂ hpair hrest =>
        -- Top is an INLINED callee frame `frC` sitting on `frP`, matched by `fr₂` inside `[callBlk+1, callBlk+M]`!
        obtain ⟨hPfn, hPlbl, hPpos, hPdst, hCfn, hClbl, hCposLe, h2fn, h2lbl, h2pos, h2dst, hag, hincl⟩ := hpair
        unfold step at hstep1; dsimp only at hstep1
        rw [hCfn, hpgi] at hstep1; dsimp only at hstep1
        cases hB : callee.blocks[frC.label]? with
        | none => rw [hB] at hstep1; cases hstep1
        | some B =>
            rw [hB] at hstep1; dsimp only at hstep1
            have hBok := calleeBlockOk_of hok hB
            have hB2 := buildInlined_blocks_inlined caller callee callBlk callPos blk rs as off hcallLt hB
            have hp0 : inlineFramePot fi callBlk callPos fr₂ = 0 := by
              unfold inlineFramePot; rw [h2fn, h2lbl]
              have h1 : ¬ callBlk + 1 + frC.label < callBlk := by omega
              have h2 : callBlk + 1 + frC.label ≠ callBlk := by omega
              simp [h1, h2]
            by_cases hltB : frC.pos < B.body.size
            · -- Statement inside inlined callee
              simp only [hltB, ↓reduceDIte] at hstep1
              obtain ⟨hltB2', hstmt_eq'⟩ := inlineCalleeBlock_body_lt (callee := callee)
                (callBlk := callBlk) (blk := blk) (rs := rs) (off := off) (j := frC.label) hltB
              have hltB2 : fr₂.pos < (inlineCalleeBlock callee callBlk blk rs off frC.label B).body.size := by
                rwa [h2pos]
              have hstmt_eq : (inlineCalleeBlock callee callBlk blk rs off frC.label B).body[fr₂.pos]'hltB2 =
                  shiftStmt off (B.body[frC.pos]'hltB) := by
                simp only [h2pos]; exact hstmt_eq'
              have hCposLe_next : ∀ B', callee.blocks[frC.label]? = some B' → frC.pos + 1 ≤ B'.body.size := by
                intro B' hB'; rw [hB] at hB'; cases hB'; omega
              cases hs : B.body[frC.pos]'hltB with
              | call rs' g' as' =>
                  rw [hs] at hstep1; dsimp only at hstep1
                  cases hev : evalArgs frC.env as' with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g' vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1
                          obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 := shiftArgs_eval hincl hev
                          obtain ⟨calFr₂, hent2, hcalRel⟩ :=
                            enter_rel (callee := callee) (callBlk := callBlk) (callPos := callPos) (off := off) hpfi hq hcaller'_par hent
                          have hstep2 := step_call (p := q) (F := caller') (B := inlineCalleeBlock callee callBlk blk rs off frC.label B)
                            (fr := fr₂) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                            (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) hltB2
                            (by rw [hstmt_eq, hs]; rfl) hev2 hent2
                          refine .inl ⟨1, _, single_star_of_step hstep2,
                            ⟨rfl, rfl, .normal hcalRel (.inlined ⟨hPfn, hPlbl, hPpos, hPdst, rfl, hClbl,
                              hCposLe_next, h2fn, h2lbl, by dsimp; omega, fun _ => rfl, hag, hincl⟩ hrest)⟩, ?_⟩
                          simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_true, hp0]
                          have hc1 := inlineFramePot_le_one fi callBlk callPos calFr₂
                          have hc2 : inlineFramePot fi callBlk callPos
                              { fr₂ with pos := fr₂.pos + 1, dsts := rs'.map (off + ·) } = 0 := by
                            unfold inlineFramePot; rw [h2fn, h2lbl]
                            have h1 : ¬ callBlk + 1 + frC.label < callBlk := by omega
                            have h2 : callBlk + 1 + frC.label ≠ callBlk := by omega
                            simp [h1, h2]
                          omega
              | assign _ _ | limb _ _ _ | store _ _ _ =>
                  rw [hs] at hstep1; dsimp only at hstep1
                  cases hx : (B.body[frC.pos]'hltB).exec frC.env mem₁ ctx₁ with
                  | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                  | some p' =>
                      rcases p' with ⟨ρC', mem₁'⟩
                      have hx' := hx
                      rw [hs] at hx; rw [hx] at hstep1
                      simp only [Step.next.injEq] at hstep1
                      obtain ⟨rfl, rfl⟩ := hstep1
                      obtain ⟨ρ₂', hx2, hag', hincl'⟩ := shiftStmt_exec hag hincl hx'
                      have hnc : (shiftStmt off (B.body[frC.pos]'hltB)).isCall = false := by
                        rw [hs]; rfl
                      have hstep2 := step_stmt (p := q) (F := caller') (B := inlineCalleeBlock callee callBlk blk rs off frC.label B)
                        (fr := fr₂) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                        (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) hltB2 hstmt_eq hnc hx2
                      refine .inl ⟨0, _, single_star_of_step hstep2,
                        ⟨rfl, rfl, .inlined ⟨hPfn, hPlbl, hPpos, hPdst, rfl, hClbl,
                          hCposLe_next, h2fn, h2lbl, by dsimp; omega, (fun h => by cases h), hag', hincl'⟩ hrest⟩, ?_⟩
                      simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero, hp0]
                      have hc2 : inlineFramePot fi callBlk callPos { fr₂ with pos := fr₂.pos + 1, env := ρ₂' } = 0 := by
                        unfold inlineFramePot; rw [h2fn, h2lbl]
                        have h1 : ¬ callBlk + 1 + frC.label < callBlk := by omega
                        have h2 : callBlk + 1 + frC.label ≠ callBlk := by omega
                        simp [h1, h2]
                      omega
            · -- Terminator inside inlined callee!
              simp only [hltB, ↓reduceDIte] at hstep1
              have hposEq : frC.pos = B.body.size := by have := hCposLe B hB; omega
              have hedgesOk : ∀ e ∈ B.term.edges, e.target ≠ 0 ∧ e.target < M := by
                simp only [calleeBlockOk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne,
                  decide_eq_true_eq] at hBok
                exact hBok.2
              cases ht : B.term with
              | jump e =>
                  obtain ⟨hsz, hterm⟩ := inlineCalleeBlock_nonTail (callee := callee) (callBlk := callBlk)
                    (blk := blk) (rs := rs) (off := off) (j := frC.label) (by rw [ht]; intro _ _ h; cases h)
                  have hstep2_unfold := step_at_term (p := q) (F := caller')
                    (B := inlineCalleeBlock callee callBlk blk rs off frC.label B)
                    (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂)
                    (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) (by rw [hsz, h2pos]; exact hltB)
                  rw [hterm, ht] at hstep2_unfold; rw [ht] at hstep1; dsimp only [rewriteCalleeTerm] at hstep1 hstep2_unfold
                  have he := hedgesOk e (by simp [ht, Term.edges])
                  obtain ⟨s₂', hte2, hrel', hpot'⟩ := calleeTakeEdge mem₁ ctx₁ frC frP fr₂ rest₁ rest₂ frC.env fr₂.env e s₁' b
                    hPfn hPlbl hPpos hPdst hCfn hClbl h2fn h2lbl hag hincl he.1 he.2 hrest hstep1
                  exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
              | br c w a b' t f =>
                  obtain ⟨hsz, hterm⟩ := inlineCalleeBlock_nonTail (callee := callee) (callBlk := callBlk)
                    (blk := blk) (rs := rs) (off := off) (j := frC.label) (by rw [ht]; intro _ _ h; cases h)
                  have hstep2_unfold := step_at_term (p := q) (F := caller')
                    (B := inlineCalleeBlock callee callBlk blk rs off frC.label B)
                    (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂)
                    (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) (by rw [hsz, h2pos]; exact hltB)
                  rw [hterm, ht] at hstep2_unfold; rw [ht] at hstep1; dsimp only [rewriteCalleeTerm] at hstep1 hstep2_unfold
                  cases ha : a.eval frC.env with
                  | none => rw [ha] at hstep1; cases hstep1
                  | some va =>
                      cases hb' : b'.eval frC.env with
                      | none => rw [ha, hb'] at hstep1; cases hstep1
                      | some vb =>
                          rw [ha, hb'] at hstep1; dsimp only at hstep1
                          rw [shiftArg_eval hincl ha, shiftArg_eval hincl hb'] at hstep2_unfold; dsimp only at hstep2_unfold
                          cases hcond : c.holds w va vb <;> rw [hcond] at hstep1 hstep2_unfold
                          · have he := hedgesOk f (by simp [ht, Term.edges])
                            obtain ⟨s₂', hte2, hrel', hpot'⟩ := calleeTakeEdge mem₁ ctx₁ frC frP fr₂ rest₁ rest₂ frC.env fr₂.env f s₁' b
                              hPfn hPlbl hPpos hPdst hCfn hClbl h2fn h2lbl hag hincl he.1 he.2 hrest hstep1
                            exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                          · have he := hedgesOk t (by simp [ht, Term.edges])
                            obtain ⟨s₂', hte2, hrel', hpot'⟩ := calleeTakeEdge mem₁ ctx₁ frC frP fr₂ rest₁ rest₂ frC.env fr₂.env t s₁' b
                              hPfn hPlbl hPpos hPdst hCfn hClbl h2fn h2lbl hag hincl he.1 he.2 hrest hstep1
                            exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
              | brOvf o x a b' ok ovf =>
                  obtain ⟨hsz, hterm⟩ := inlineCalleeBlock_nonTail (callee := callee) (callBlk := callBlk)
                    (blk := blk) (rs := rs) (off := off) (j := frC.label) (by rw [ht]; intro _ _ h; cases h)
                  have hstep2_unfold := step_at_term (p := q) (F := caller')
                    (B := inlineCalleeBlock callee callBlk blk rs off frC.label B)
                    (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂)
                    (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) (by rw [hsz, h2pos]; exact hltB)
                  rw [hterm, ht] at hstep2_unfold; rw [ht] at hstep1; dsimp only [rewriteCalleeTerm] at hstep1 hstep2_unfold
                  cases ha : a.eval frC.env with
                  | none => rw [ha] at hstep1; cases hstep1
                  | some va =>
                      cases hb' : b'.eval frC.env with
                      | none => rw [ha, hb'] at hstep1; cases hstep1
                      | some vb =>
                          rw [ha, hb'] at hstep1; dsimp only at hstep1
                          rw [shiftArg_eval hincl ha, shiftArg_eval hincl hb'] at hstep2_unfold; dsimp only at hstep2_unfold
                          have hag' := envAgreeBelow_insert_ge hag (Nat.le_add_right off x) (o.eval va vb).1
                          have hincl' := envShiftIncl_insert hincl x (o.eval va vb).1
                          cases hovf : (o.eval va vb).2 <;> simp only [hovf, Bool.false_eq_true, ↓reduceIte] at hstep1 hstep2_unfold
                          · have he := hedgesOk ok (by simp [ht, Term.edges])
                            obtain ⟨s₂', hte2, hrel', hpot'⟩ := calleeTakeEdge mem₁ ctx₁ frC frP fr₂ rest₁ rest₂
                              (frC.env.insert x (o.eval va vb).1) (fr₂.env.insert (off + x) (o.eval va vb).1) ok s₁' b
                              hPfn hPlbl hPpos hPdst hCfn hClbl h2fn h2lbl hag' hincl' he.1 he.2 hrest hstep1
                            exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                          · have he := hedgesOk ovf (by simp [ht, Term.edges])
                            obtain ⟨s₂', hte2, hrel', hpot'⟩ := calleeTakeEdge mem₁ ctx₁ frC frP fr₂ rest₁ rest₂
                              (frC.env.insert x (o.eval va vb).1) (fr₂.env.insert (off + x) (o.eval va vb).1) ovf s₁' b
                              hPfn hPlbl hPpos hPdst hCfn hClbl h2fn h2lbl hag' hincl' he.1 he.2 hrest hstep1
                            exact .inl ⟨b.toNat, s₂', single_star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
              | ret ras =>
                  -- Return from inlined callee -> forward jump to `contBlk`, collapsing 2-to-1 pair back to 1-to-1 normal frame!
                  obtain ⟨hsz, hterm⟩ := inlineCalleeBlock_nonTail (callee := callee) (callBlk := callBlk)
                    (blk := blk) (rs := rs) (off := off) (j := frC.label) (by rw [ht]; intro _ _ h; cases h)
                  have hstep2_unfold := step_at_term (p := q) (F := caller')
                    (B := inlineCalleeBlock callee callBlk blk rs off frC.label B)
                    (mem := mem₁) (ctx := ctx₁) (fr := fr₂) (rest := rest₂)
                    (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) (by rw [hsz, h2pos]; exact hltB)
                  rw [hterm, ht] at hstep2_unfold; rw [ht] at hstep1; dsimp only [rewriteCalleeTerm] at hstep1 hstep2_unfold
                  cases hev : evalArgs frC.env ras with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; dsimp only at hstep1
                      cases hbp : bindParams frP.env frP.dsts vs with
                      | none => rw [hbp] at hstep1; cases hstep1
                      | some ρP' =>
                          rw [hbp] at hstep1
                          simp only [Step.next.injEq] at hstep1
                          obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 := shiftArgs_eval hincl hev
                          have hcont := buildInlined_blocks_cont caller callee callBlk callPos blk rs as off hcallLt
                          obtain ⟨ρ₂', hbp2, hag'⟩ := bindParams_agreeBelow hag (by rw [hPdst] at hbp; exact hbp)
                          have hte2 : takeEdge caller' { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } fr₂ rest₂ fr₂.env
                              { target := callBlk + delta, args := ras.map (shiftArg off) } =
                              .next { mem := mem₁, ctx := ctx₁, stack := { fr₂ with label := callBlk + delta, pos := 0, env := ρ₂' } :: rest₂ } false := by
                            have h1 := takeEdge_ok (F := caller') (s := { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ })
                              (fr := fr₂) (rest := rest₂) (ρ := fr₂.env)
                              (e := { target := callBlk + delta, args := ras.map (shiftArg off) })
                              hev2 hcont hbp2
                            have hfwd : decide (callBlk + delta ≤ fr₂.label) = false := by
                              rw [h2lbl]; refine decide_eq_false (Nat.not_le_of_gt ?_)
                              change callBlk + 1 + (frC.label : Nat) < callBlk + (callee.blocks.size + 1)
                              rw [Nat.add_assoc, Nat.add_comm 1 frC.label]
                              exact Nat.add_lt_add_left (Nat.add_lt_add_right hClbl 1) callBlk
                            rwa [hfwd] at h1
                          have hstep2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } =
                              .next { mem := mem₁, ctx := ctx₁, stack := { fr₂ with label := callBlk + delta, pos := 0, env := ρ₂' } :: rest₂ } false :=
                            hstep2_unfold.trans hte2
                          have hp_cont : inlineFramePot fi callBlk callPos
                              { fr₂ with label := callBlk + delta, pos := 0, env := ρ₂' } = 0 := by
                            unfold inlineFramePot; rw [h2fn]
                            have h1 : ¬ callBlk + delta < callBlk := by omega
                            simp [h1]
                          refine .inl ⟨0, _, single_star_of_step hstep2, ⟨rfl, rfl, .normal ?_ hrest⟩, ?_⟩
                          · simp only [NormalFrameRel, hPfn, ↓reduceIte]
                            exact ⟨h2fn, hag', (fun h => by cases h), fun hne => absurd hPlbl hne,
                              fun _ hle => by omega, fun _ _ => ⟨rfl, by omega⟩⟩
                          · simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_false,
                              Nat.zero_add, Nat.mul_zero, hp0, hp_cont]
                            omega
              | tail g tas =>
                  -- Tail call inside inlined callee -> normal call in `q` returning via `.tailReturn` trampoline!
                  rw [ht] at hstep1; dsimp only at hstep1
                  cases hev : evalArgs frC.env tas with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1
                          obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 := shiftArgs_eval hincl hev
                          obtain ⟨calFr₂, hent2, hcalRel⟩ :=
                            enter_rel (callee := callee) (callBlk := callBlk) (callPos := callPos) (off := off) hpfi hq hcaller'_par hent
                          obtain ⟨hB2_sz, hB2_last, _⟩ := inlineCalleeBlock_tail (callBlk := callBlk)
                            (blk := blk) (rs := rs) (off := off) (j := frC.label) ht
                          have hltB2 : fr₂.pos < (inlineCalleeBlock callee callBlk blk rs off frC.label B).body.size := by
                            rw [h2pos, hposEq, hB2_sz]; omega
                          have hstmt2 : (inlineCalleeBlock callee callBlk blk rs off frC.label B).body[fr₂.pos]'hltB2 =
                              .call (inlineTailFreshRs callee rs off frC.label) g (tas.map (shiftArg off)) := by
                            simp only [h2pos, hposEq]
                            exact hB2_last (by rw [hB2_sz]; omega)
                          have hstep2 := step_call (p := q) (F := caller')
                            (B := inlineCalleeBlock callee callBlk blk rs off frC.label B)
                            (fr := fr₂) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                            (by rw [h2fn]; exact hqfi) (by rw [h2lbl]; exact hB2) hltB2 hstmt2 hev2 hent2
                          refine .inl ⟨1, _, single_star_of_step hstep2,
                            ⟨rfl, rfl, .normal hcalRel (.tailReturn hPfn hPlbl hPpos hPdst hClbl hB ht
                              h2fn h2lbl (by rw [h2pos, hposEq]) rfl hag hrest)⟩, ?_⟩
                          simp only [inlinePot, List.map_cons, List.sum_cons, Bool.toNat_true, hp0]
                          have hc1 := inlineFramePot_le_one fi callBlk callPos calFr₂
                          have hc2 : inlineFramePot fi callBlk callPos
                              { fr₂ with pos := fr₂.pos + 1, dsts := inlineTailFreshRs callee rs off frC.label } = 0 := by
                            unfold inlineFramePot; rw [h2fn, h2lbl]
                            have h1 : ¬ callBlk + 1 + frC.label < callBlk := by omega
                            have h2 : callBlk + 1 + frC.label ≠ callBlk := by omega
                            simp [h1, h2]
                          omega
              | fail _ | trap => rw [ht] at hstep1; cases hstep1
  · -- `final`
    intro s₁ s₂ r hrel hfin hne
    rcases s₁ with ⟨mem₁, ctx₁, st₁⟩
    rcases s₂ with ⟨mem₂, ctx₂, st₂⟩
    obtain ⟨hmem_eq, hctx_eq, hstack⟩ := hrel
    obtain rfl : mem₁ = mem₂ := hmem_eq.symm
    obtain rfl : ctx₁ = ctx₂ := hctx_eq.symm
    cases hstack with
    | nil =>
        have hst : step p { mem := mem₁, ctx := ctx₁, stack := [] } = .stuck := rfl
        rw [semStep, hst] at hfin; cases hfin; exact absurd rfl hne
    | @normal _ fr₁ fr₂ rest₁ rest₂ hfr hrest =>
        by_cases hfn : fr₁.fn = fi
        · simp only [NormalFrameRel, hfn, ↓reduceIte] at hfr
          obtain ⟨h2fn, hag, _, hlbl_ne, hlbl_le, hlbl_gt⟩ := hfr
          have hstep_unfold : semStep p { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } =
              (step p { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ }).toSem := rfl
          unfold step at hstep_unfold; dsimp only at hstep_unfold
          rw [hfn, hpfi] at hstep_unfold; dsimp only at hstep_unfold
          cases hB : caller.blocks[fr₁.label]? with
          | none => rw [hB] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
          | some B =>
              rw [hB] at hstep_unfold; dsimp only at hstep_unfold
              have hBregs := blockRegsLt_of_func hregs hB
              by_cases hltB : fr₁.pos < B.body.size
              · simp only [hltB, ↓reduceDIte] at hstep_unfold
                cases hs : B.body[fr₁.pos]'hltB with
                | call rs' g' as' =>
                    rw [hs] at hstep_unfold; dsimp only at hstep_unfold
                    cases hev : evalArgs fr₁.env as' >>= enter p g' with
                    | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                    | some _ => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                | assign _ _ | limb _ _ _ | store _ _ _ =>
                    rw [hs] at hstep_unfold; dsimp only at hstep_unfold
                    cases hx : (B.body[fr₁.pos]'hltB).exec fr₁.env mem₁ ctx₁ with
                    | none => rw [hs] at hx; rw [hx] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                    | some _ => rw [hs] at hx; rw [hx] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
              · simp only [hltB, ↓reduceDIte] at hstep_unfold
                have hgt_cb : fr₁.label = callBlk → callPos < fr₁.pos := by
                  intro hcb; have hBeq : B = blk := by rw [hcb, hcall] at hB; exact Option.some.inj hB.symm
                  obtain rfl : blk = B := hBeq.symm; omega
                have hB2_term : ∃ B2, caller'.blocks[fr₂.label]? = some B2 ∧
                    ¬ fr₂.pos < B2.body.size ∧ B2.term = remapCallerTerm callBlk delta B.term := by
                  by_cases hcb : fr₁.label = callBlk
                  · have hBeq : B = blk := by rw [hcb, hcall] at hB; exact Option.some.inj hB.symm
                    obtain rfl : blk = B := hBeq.symm
                    obtain ⟨h2lbl, h2pos⟩ := hlbl_gt hcb (hgt_cb hcb)
                    refine ⟨contBlkNew callee callBlk callPos blk rs,
                      by rw [h2lbl]; exact buildInlined_blocks_cont caller callee callBlk callPos blk rs as off hcallLt,
                      by simp [contBlkNew, h2pos]; omega, rfl⟩
                  · obtain ⟨h2lbl, h2pos⟩ := hlbl_ne hcb
                    have hB2' : caller'.blocks[fr₂.label]? = some { B with term := remapCallerTerm callBlk delta B.term } := by
                      rw [h2lbl]
                      by_cases hlt : fr₁.label < callBlk
                      · have hle : fr₁.label ≤ callBlk := Nat.le_of_lt hlt
                        simp only [remapCallerLabel, hle, ↓reduceIte]
                        exact buildInlined_blocks_lt caller callee callBlk callPos blk rs as off hcallLt hlt hB
                      · have hgt : callBlk < fr₁.label :=
                          Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hcb)
                        have hnle : ¬ fr₁.label ≤ callBlk := Nat.not_le_of_gt hgt
                        simp only [remapCallerLabel, hnle, ↓reduceIte]
                        exact buildInlined_blocks_gt caller callee callBlk callPos blk rs as off hcallLt hgt hB
                    exact ⟨_, hB2', by simpa [h2pos] using hltB, rfl⟩
                obtain ⟨B2, hB2, hltB2, hterm2⟩ := hB2_term
                obtain ⟨htuses, _⟩ := term_uses_lt_of_block hBregs
                cases ht : B.term with
                | fail res =>
                    rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                    rw [hstep_unfold] at hfin; cases hfin
                    have h2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } = .fail res := by
                      unfold step; dsimp only; rw [h2fn, hqfi]; dsimp only; rw [hB2]; simp [hltB2, hterm2, ht, remapCallerTerm]
                    exact .inl ⟨0, _, .resource res, .refl _, by rw [semStep, h2]; exact .fail, .resource res⟩
                | trap =>
                    rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                    rw [hstep_unfold] at hfin; cases hfin
                    have h2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } = .trap := by
                      unfold step; dsimp only; rw [h2fn, hqfi]; dsimp only; rw [hB2]; simp [hltB2, hterm2, ht, remapCallerTerm]
                    exact .inl ⟨0, _, .trap, .refl _, by rw [semStep, h2]; exact .trap, .trap⟩
                | ret ras =>
                    rw [ht] at hstep_unfold htuses; dsimp only at hstep_unfold
                    cases hev : evalArgs fr₁.env ras with
                    | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                    | some vs =>
                        rw [hev] at hstep_unfold
                        cases hrest with
                        | nil =>
                            rw [hstep_unfold] at hfin; cases hfin
                            have hev2 : evalArgs fr₂.env ras = some vs := by
                              rw [evalArgs_agreeBelow hag (listLt_flatMap_uses htuses), hev]
                            have h2 : step q { mem := mem₁, ctx := ctx₁, stack := [fr₂] } = .done vs mem₁ := by
                              unfold step; dsimp only; rw [h2fn, hqfi]; dsimp only; rw [hB2]; simp [hltB2, hterm2, ht, remapCallerTerm, hev2]
                            exact .inl ⟨0, _, .ok (vs, mem₁), .refl _, by rw [semStep, h2]; exact .done, .ok rfl⟩
                        | normal _ _ | inlined _ _ =>
                            dsimp only at hstep_unfold
                            cases hbp : bindParams _ _ vs with
                            | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                            | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                        | tailReturn _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                            dsimp only at hstep_unfold
                            cases hbp : bindParams _ _ vs with
                            | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                            | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                | jump e =>
                    rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                    unfold takeEdge at hstep_unfold
                    cases hev : evalArgs fr₁.env e.args with
                    | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                    | some vs =>
                        cases htgt : caller.blocks[e.target]? with
                        | none => rw [hev, htgt] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                        | some tb =>
                            rw [hev, htgt] at hstep_unfold; dsimp only at hstep_unfold
                            cases hbp : bindParams fr₁.env tb.params vs with
                            | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                            | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                | br c w a b' t f =>
                    rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                    cases ha : a.eval fr₁.env with
                    | none => rw [ha] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                    | some va =>
                        cases hb' : b'.eval fr₁.env with
                        | none => rw [ha, hb'] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                        | some vb =>
                            rw [ha, hb'] at hstep_unfold; dsimp only at hstep_unfold
                            unfold takeEdge at hstep_unfold
                            cases hev : evalArgs fr₁.env (if c.holds w va vb then t else f).args with
                            | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                            | some vs =>
                                cases htgt : caller.blocks[(if c.holds w va vb then t else f).target]? with
                                | none => rw [hev, htgt] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                | some tb =>
                                    rw [hev, htgt] at hstep_unfold; dsimp only at hstep_unfold
                                    cases hbp : bindParams fr₁.env tb.params vs with
                                    | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                    | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                | brOvf o x a b' ok ovf =>
                    rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                    cases ha : a.eval fr₁.env with
                    | none => rw [ha] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                    | some va =>
                        cases hb' : b'.eval fr₁.env with
                        | none => rw [ha, hb'] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                        | some vb =>
                            rw [ha, hb'] at hstep_unfold; dsimp only at hstep_unfold
                            unfold takeEdge at hstep_unfold
                            cases hev : evalArgs (fr₁.env.insert x (o.eval va vb).1) (if (o.eval va vb).2 then ovf else ok).args with
                            | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                            | some vs =>
                                cases htgt : caller.blocks[(if (o.eval va vb).2 then ovf else ok).target]? with
                                | none => rw [hev, htgt] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                | some tb =>
                                    rw [hev, htgt] at hstep_unfold; dsimp only at hstep_unfold
                                    cases hbp : bindParams (fr₁.env.insert x (o.eval va vb).1) tb.params vs with
                                    | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                    | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                | tail g tas =>
                    rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                    cases hev : evalArgs fr₁.env tas >>= enter p g with
                    | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                    | some _ => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
        · -- `fr₁.fn ≠ fi`, `fr₂ = fr₁`
          simp only [NormalFrameRel, hfn, ↓reduceIte] at hfr
          obtain rfl : fr₁ = fr₂ := hfr.symm
          have hstep_unfold : semStep p { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } =
              (step p { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ }).toSem := rfl
          unfold step at hstep_unfold; dsimp only at hstep_unfold
          cases hF : p.funcs[fr₁.fn]? with
          | none => rw [hF] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
          | some F =>
              have hqF : q.funcs[fr₁.fn]? = some F := by
                rw [hq]; simp [Array.set!_eq_setIfInBounds, Ne.symm hfn, hF]
              rw [hF] at hstep_unfold; dsimp only at hstep_unfold
              cases hB : F.blocks[fr₁.label]? with
              | none => rw [hB] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
              | some B =>
                  rw [hB] at hstep_unfold; dsimp only at hstep_unfold
                  by_cases hltB : fr₁.pos < B.body.size
                  · simp only [hltB, ↓reduceDIte] at hstep_unfold
                    cases hs : B.body[fr₁.pos]'hltB with
                    | call _ g' as' =>
                        rw [hs] at hstep_unfold; dsimp only at hstep_unfold
                        cases hev : evalArgs fr₁.env as' >>= enter p g' with
                        | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                        | some _ => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                    | assign _ _ | limb _ _ _ | store _ _ _ =>
                        rw [hs] at hstep_unfold; dsimp only at hstep_unfold
                        cases hx : (B.body[fr₁.pos]'hltB).exec fr₁.env mem₁ ctx₁ with
                        | none => rw [hs] at hx; rw [hx] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                        | some _ => rw [hs] at hx; rw [hx] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                  · simp only [hltB, ↓reduceDIte] at hstep_unfold
                    cases ht : B.term with
                    | fail res =>
                        rw [ht] at hstep_unfold; dsimp only at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                        have h2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } = .fail res := by
                          unfold step; dsimp only; rw [hqF]; dsimp only; rw [hB]; simp [hltB, ht]
                        exact .inl ⟨0, _, .resource res, .refl _, by rw [semStep, h2]; exact .fail, .resource res⟩
                    | trap =>
                        rw [ht] at hstep_unfold; dsimp only at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                        have h2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } = .trap := by
                          unfold step; dsimp only; rw [hqF]; dsimp only; rw [hB]; simp [hltB, ht]
                        exact .inl ⟨0, _, .trap, .refl _, by rw [semStep, h2]; exact .trap, .trap⟩
                    | ret ras =>
                        rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                        cases hev : evalArgs fr₁.env ras with
                        | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                        | some vs =>
                            rw [hev] at hstep_unfold
                            cases hrest with
                            | nil =>
                                rw [hstep_unfold] at hfin; cases hfin
                                have h2 : step q { mem := mem₁, ctx := ctx₁, stack := [fr₁] } = .done vs mem₁ := by
                                  unfold step; dsimp only; rw [hqF]; dsimp only; rw [hB]; simp [hltB, ht, hev]
                                exact .inl ⟨0, _, .ok (vs, mem₁), .refl _, by rw [semStep, h2]; exact .done, .ok rfl⟩
                            | normal _ _ | inlined _ _ =>
                                dsimp only at hstep_unfold
                                cases hbp : bindParams _ _ vs with
                                | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                            | tailReturn _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                                dsimp only at hstep_unfold
                                cases hbp : bindParams _ _ vs with
                                | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                    | jump e =>
                        rw [ht] at hstep_unfold; dsimp only at hstep_unfold; unfold takeEdge at hstep_unfold
                        cases hev : evalArgs fr₁.env e.args with
                        | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                        | some vs =>
                            cases htgt : F.blocks[e.target]? with
                            | none => rw [hev, htgt] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                            | some tb =>
                                rw [hev, htgt] at hstep_unfold; dsimp only at hstep_unfold
                                cases hbp : bindParams fr₁.env tb.params vs with
                                | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                    | br c w a b' t f =>
                        rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                        cases ha : a.eval fr₁.env with
                        | none => rw [ha] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                        | some va =>
                            cases hb' : b'.eval fr₁.env with
                            | none => rw [ha, hb'] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                            | some vb =>
                                rw [ha, hb'] at hstep_unfold; dsimp only at hstep_unfold; unfold takeEdge at hstep_unfold
                                cases hev : evalArgs fr₁.env (if c.holds w va vb then t else f).args with
                                | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                | some vs =>
                                    cases htgt : F.blocks[(if c.holds w va vb then t else f).target]? with
                                    | none => rw [hev, htgt] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                    | some tb =>
                                        rw [hev, htgt] at hstep_unfold; dsimp only at hstep_unfold
                                        cases hbp : bindParams fr₁.env tb.params vs with
                                        | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                        | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                    | brOvf o x a b' ok ovf =>
                        rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                        cases ha : a.eval fr₁.env with
                        | none => rw [ha] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                        | some va =>
                            cases hb' : b'.eval fr₁.env with
                            | none => rw [ha, hb'] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                            | some vb =>
                                rw [ha, hb'] at hstep_unfold; dsimp only at hstep_unfold; unfold takeEdge at hstep_unfold
                                cases hev : evalArgs (fr₁.env.insert x (o.eval va vb).1) (if (o.eval va vb).2 then ovf else ok).args with
                                | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                | some vs =>
                                    cases htgt : F.blocks[(if (o.eval va vb).2 then ovf else ok).target]? with
                                    | none => rw [hev, htgt] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                    | some tb =>
                                        rw [hev, htgt] at hstep_unfold; dsimp only at hstep_unfold
                                        cases hbp : bindParams (fr₁.env.insert x (o.eval va vb).1) tb.params vs with
                                        | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                        | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                    | tail g tas =>
                        rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                        cases hev : evalArgs fr₁.env tas >>= enter p g with
                        | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                        | some _ => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
    | @inlined _ frC frP fr₂ rest₁ rest₂ hpair hrest =>
        -- Inside an inlined callee: only `.fail` and `.trap` can be non-stuck `Final` (`.ret` always has `frP` beneath)!
        obtain ⟨_, _, _, _, hCfn, _, _, h2fn, h2lbl, h2pos, _, _, _⟩ := hpair
        have hstep_unfold : semStep p { mem := mem₁, ctx := ctx₁, stack := frC :: frP :: rest₁ } =
            (step p { mem := mem₁, ctx := ctx₁, stack := frC :: frP :: rest₁ }).toSem := rfl
        unfold step at hstep_unfold; dsimp only at hstep_unfold
        rw [hCfn, hpgi] at hstep_unfold; dsimp only at hstep_unfold
        cases hB : callee.blocks[frC.label]? with
        | none => rw [hB] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
        | some B =>
            rw [hB] at hstep_unfold; dsimp only at hstep_unfold
            have hB2 := buildInlined_blocks_inlined caller callee callBlk callPos blk rs as off hcallLt hB
            by_cases hltB : frC.pos < B.body.size
            · simp only [hltB, ↓reduceDIte] at hstep_unfold
              cases hs : B.body[frC.pos]'hltB with
              | call _ g' as' =>
                  rw [hs] at hstep_unfold; dsimp only at hstep_unfold
                  cases hev : evalArgs frC.env as' >>= enter p g' with
                  | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                  | some _ => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
              | assign _ _ | limb _ _ _ | store _ _ _ =>
                  rw [hs] at hstep_unfold; dsimp only at hstep_unfold
                  cases hx : (B.body[frC.pos]'hltB).exec frC.env mem₁ ctx₁ with
                  | none => rw [hs] at hx; rw [hx] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                  | some _ => rw [hs] at hx; rw [hx] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
            · simp only [hltB, ↓reduceDIte] at hstep_unfold
              cases ht : B.term with
              | fail res =>
                  rw [ht] at hstep_unfold; dsimp only at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                  obtain ⟨hsz, hterm⟩ := inlineCalleeBlock_nonTail (callee := callee) (callBlk := callBlk)
                    (blk := blk) (rs := rs) (off := off) (j := frC.label) (by rw [ht]; intro _ _ h; cases h)
                  have hltB2 : ¬ fr₂.pos < (inlineCalleeBlock callee callBlk blk rs off frC.label B).body.size := by
                    rw [hsz, h2pos]; exact hltB
                  have h2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } = .fail res := by
                    unfold step; dsimp only; rw [h2fn, hqfi]; dsimp only; rw [h2lbl, hB2]; simp [hltB2, hterm, ht, rewriteCalleeTerm]
                  exact .inl ⟨0, _, .resource res, .refl _, by rw [semStep, h2]; exact .fail, .resource res⟩
              | trap =>
                  rw [ht] at hstep_unfold; dsimp only at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
                  obtain ⟨hsz, hterm⟩ := inlineCalleeBlock_nonTail (callee := callee) (callBlk := callBlk)
                    (blk := blk) (rs := rs) (off := off) (j := frC.label) (by rw [ht]; intro _ _ h; cases h)
                  have hltB2 : ¬ fr₂.pos < (inlineCalleeBlock callee callBlk blk rs off frC.label B).body.size := by
                    rw [hsz, h2pos]; exact hltB
                  have h2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₂ :: rest₂ } = .trap := by
                    unfold step; dsimp only; rw [h2fn, hqfi]; dsimp only; rw [h2lbl, hB2]; simp [hltB2, hterm, ht, rewriteCalleeTerm]
                  exact .inl ⟨0, _, .trap, .refl _, by rw [semStep, h2]; exact .trap, .trap⟩
              | ret ras =>
                  rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                  cases hev : evalArgs frC.env ras with
                  | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                  | some vs =>
                      rw [hev] at hstep_unfold; dsimp only at hstep_unfold
                      cases hbp : bindParams frP.env frP.dsts vs with
                      | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                      | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
              | tail g tas =>
                  rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                  cases hev : evalArgs frC.env tas >>= enter p g with
                  | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                  | some _ => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
              | jump e =>
                  rw [ht] at hstep_unfold; dsimp only at hstep_unfold; unfold takeEdge at hstep_unfold
                  cases hev : evalArgs frC.env e.args with
                  | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                  | some vs =>
                      cases htgt : callee.blocks[e.target]? with
                      | none => rw [hev, htgt] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                      | some tb =>
                          rw [hev, htgt] at hstep_unfold; dsimp only at hstep_unfold
                          cases hbp : bindParams frC.env tb.params vs with
                          | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                          | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
              | br c w a b' t f =>
                  rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                  cases ha : a.eval frC.env with
                  | none => rw [ha] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                  | some va =>
                      cases hb' : b'.eval frC.env with
                      | none => rw [ha, hb'] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                      | some vb =>
                          rw [ha, hb'] at hstep_unfold; dsimp only at hstep_unfold; unfold takeEdge at hstep_unfold
                          cases hev : evalArgs frC.env (if c.holds w va vb then t else f).args with
                          | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                          | some vs =>
                              cases htgt : callee.blocks[(if c.holds w va vb then t else f).target]? with
                              | none => rw [hev, htgt] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                              | some tb =>
                                  rw [hev, htgt] at hstep_unfold; dsimp only at hstep_unfold
                                  cases hbp : bindParams frC.env tb.params vs with
                                  | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                  | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin
              | brOvf o x a b' ok ovf =>
                  rw [ht] at hstep_unfold; dsimp only at hstep_unfold
                  cases ha : a.eval frC.env with
                  | none => rw [ha] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                  | some va =>
                      cases hb' : b'.eval frC.env with
                      | none => rw [ha, hb'] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                      | some vb =>
                          rw [ha, hb'] at hstep_unfold; dsimp only at hstep_unfold; unfold takeEdge at hstep_unfold
                          cases hev : evalArgs (frC.env.insert x (o.eval va vb).1) (if (o.eval va vb).2 then ovf else ok).args with
                          | none => rw [hev] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                          | some vs =>
                              cases htgt : callee.blocks[(if (o.eval va vb).2 then ovf else ok).target]? with
                              | none => rw [hev, htgt] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                              | some tb =>
                                  rw [hev, htgt] at hstep_unfold; dsimp only at hstep_unfold
                                  cases hbp : bindParams (frC.env.insert x (o.eval va vb).1) tb.params vs with
                                  | none => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin; exact absurd rfl hne
                                  | some _ => rw [hbp] at hstep_unfold; rw [hstep_unfold] at hfin; cases hfin

/-! ## Public simulation & well-formedness theorems for single-site inlining -/

/-- **Single-site call inlining simulation**: `inlineCallSite p fi callBlk callPos = some q`
simulates `p` with exact value/memory equality and clock map `k ↦ 2 * k + 1`. -/
theorem inlineCallSite_sim {p q : Program} {fi : FunId} {callBlk callPos : Nat}
    (h : inlineCallSite p fi callBlk callPos = some q)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq (fun k => 2 * k + 1)
      (fun k => eval p k args mem ctx) (fun k => eval q k args mem ctx) := by
  unfold inlineCallSite at h
  cases hpfi : p.funcs[fi]? with
  | none => rw [hpfi] at h; cases h
  | some caller =>
      rw [hpfi] at h; dsimp only at h
      cases hcall : caller.blocks[callBlk]? with
      | none => rw [hcall] at h; cases h
      | some blk =>
          rw [hcall] at h; dsimp only at h
          cases hpos : blk.body[callPos]? with
          | none => rw [hpos] at h; cases h
          | some s =>
              rw [hpos] at h
              cases s with
              | assign _ _ | limb _ _ _ | store _ _ _ => cases h
              | call rs gi as =>
                  dsimp only at h
                  cases hpgi : p.funcs[gi]? with
                  | none => rw [hpgi] at h; cases h
                  | some callee =>
                      rw [hpgi] at h; dsimp only at h
                      split at h
                      · rename_i hcond
                        cases h
                        simp only [Bool.and_eq_true] at hcond
                        obtain ⟨hregs, hok⟩ := hcond
                        have hfwd := inlineCallSite_forward hpfi hcall hpos hpgi hregs hok rfl
                        cases hinit1 : Lir.State.initial p args mem ctx with
                        | none =>
                            refine ⟨fun k _ => ⟨0, by simp [eval, hinit1]; exact .stuck⟩,
                              fun k hk => by simp [eval, hinit1] at hk⟩
                        | some s₁ =>
                            simp only [Lir.State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff,
                              Option.some.injEq] at hinit1
                            obtain ⟨fr₁, hent₁, rfl⟩ := hinit1
                            obtain ⟨fr₂, hent₂, hfrRel⟩ :=
                              enter_rel (callee := callee)
                                (caller' := buildInlinedFunc caller callee callBlk callPos blk rs as (nextFreshVReg caller))
                                (callBlk := callBlk) (callPos := callPos)
                                (off := nextFreshVReg caller) hpfi rfl rfl hent₁
                            have hinit2 : Lir.State.initial
                                { funcs := p.funcs.set! fi (buildInlinedFunc caller callee callBlk callPos blk rs as (nextFreshVReg caller)), main := p.main }
                                args mem ctx = some { mem, ctx, stack := [fr₂] } := by
                              unfold Lir.State.initial; rw [hent₂]; rfl
                            have hrel0 : InlineStateRel callee fi gi callBlk callPos callee.blocks.size rs
                                (nextFreshVReg caller) { mem, ctx, stack := [fr₁] } { mem, ctx, stack := [fr₂] } :=
                              ⟨rfl, rfl, .normal hfrRel .nil⟩
                            have hpot0 : inlinePot fi callBlk callPos { mem, ctx, stack := [fr₂] } ≤ 1 := by
                              simp only [inlinePot, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
                              exact inlineFramePot_le_one fi callBlk callPos fr₂
                            exact hfwd.sim hrel0 hpot0
                              (runs_eval (by simp [Lir.State.initial, hent₁]))
                              (runs_eval hinit2)
                      · cases h

theorem inlineCallSiteChecked_wellFormed {p : Program} {fi : FunId} {callBlk callPos : Nat}
    (hwf : p.wellFormed = true) :
    (inlineCallSiteChecked p fi callBlk callPos).1.wellFormed = true := by
  unfold inlineCallSiteChecked
  cases inlineCallSite p fi callBlk callPos with
  | none => exact hwf
  | some q =>
      dsimp only
      split
      · rename_i h; simp [hwf] at h; exact h
      · exact hwf

theorem inlineCallSiteChecked_sim (p : Program) (fi : FunId) (callBlk callPos : Nat)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq (fun k => 2 * k + 1)
      (fun k => eval p k args mem ctx)
      (fun k => eval (inlineCallSiteChecked p fi callBlk callPos).1 k args mem ctx) := by
  have hself : Sem.Sim Eq (fun k => 2 * k + 1)
      (fun k => eval p k args mem ctx) (fun k => eval p k args mem ctx) := by
    refine ⟨fun k _ => ⟨k, Sem.Result.Refines.refl (fun _ => rfl)⟩, fun k hk => ?_⟩
    by_cases h1 : eval p k args mem ctx = .timeout
    · exact .inl h1
    · exfalso
      have hm := eval_mono p args mem ctx (by omega : k ≤ 2 * k + 1) h1
      dsimp only at hm
      rw [hk] at hm
      exact h1 hm.symm
  unfold inlineCallSiteChecked
  cases h : inlineCallSite p fi callBlk callPos with
  | none => exact hself
  | some q =>
      dsimp only
      split
      · exact inlineCallSite_sim h args mem ctx
      · exact hself

/-! ## Single-site `.tail` call inlining soundness (`inlineTailSite_sim`) -/

section TailInline

private theorem buildTailInlined_blocks_lt {caller callee : Func} {tailBlk : Nat} {blk : Block}
    {as : List Arg} {off : VReg} {b : Nat} {B : Block}
    (hb : b < tailBlk) (hB : caller.blocks[b]? = some B) :
    (buildTailInlinedFunc caller callee tailBlk blk as off).blocks[b]? =
      some { B with term := remapCallerTerm tailBlk callee.blocks.size B.term } := by
  unfold buildTailInlinedFunc
  dsimp only
  rw [List.getElem?_toArray]
  have hlt_call : b < caller.blocks.size := (Array.getElem?_eq_some_iff.1 hB).1
  have hlen1 : ((caller.blocks.toList.take tailBlk).map fun b =>
      { b with term := remapCallerTerm tailBlk callee.blocks.size b.term }).length =
      min tailBlk caller.blocks.size := by simp
  have hmin : b < min tailBlk caller.blocks.size := Nat.lt_min.2 ⟨hb, hlt_call⟩
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (by rw [hlen1]; exact hmin)]
  rw [List.getElem?_map, List.getElem?_take_of_lt hb, Array.getElem?_toList, hB]
  rfl

private theorem buildTailInlined_blocks_tailBlk {caller callee : Func} {tailBlk : Nat} {blk : Block}
    {as : List Arg} {off : VReg} (htail : tailBlk < caller.blocks.size) :
    (buildTailInlinedFunc caller callee tailBlk blk as off).blocks[tailBlk]? =
      some { blk with term := .jump { target := tailBlk + 1, args := as } } := by
  unfold buildTailInlinedFunc
  dsimp only
  rw [List.getElem?_toArray]
  have hlen1 : ((caller.blocks.toList.take tailBlk).map fun b =>
      { b with term := remapCallerTerm tailBlk callee.blocks.size b.term }).length = tailBlk := by
    simp [Nat.min_eq_left (Nat.le_of_lt htail)]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [hlen1]; exact Nat.le_refl _), hlen1, Nat.sub_self]
  rfl

private theorem buildTailInlined_blocks_inlined {caller callee : Func} {tailBlk : Nat} {blk : Block}
    {as : List Arg} {off : VReg} {j : Nat} {B : Block}
    (htail : tailBlk < caller.blocks.size) (hB : callee.blocks[j]? = some B) :
    (buildTailInlinedFunc caller callee tailBlk blk as off).blocks[tailBlk + 1 + j]? =
      some (inlineTailCalleeBlock callee tailBlk blk off j B) := by
  have hj : j < callee.blocks.size := (Array.getElem?_eq_some_iff.1 hB).1
  unfold buildTailInlinedFunc
  dsimp only
  rw [List.getElem?_toArray]
  have hlen1 : ((caller.blocks.toList.take tailBlk).map fun b =>
      { b with term := remapCallerTerm tailBlk callee.blocks.size b.term }).length = tailBlk := by
    simp [Nat.min_eq_left (Nat.le_of_lt htail)]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [hlen1]; omega), hlen1]
  rw [show tailBlk + 1 + j - tailBlk = j + 1 by omega]
  simp only [List.singleton_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simp [hj])]
  rw [List.getElem?_map, List.getElem?_zipIdx]
  simp [Array.getElem?_toList, hB]

private theorem buildTailInlined_blocks_gt {caller callee : Func} {tailBlk : Nat} {blk : Block}
    {as : List Arg} {off : VReg} {b : Nat} {B : Block}
    (htail : tailBlk < caller.blocks.size) (hb : tailBlk < b) (hB : caller.blocks[b]? = some B) :
    (buildTailInlinedFunc caller callee tailBlk blk as off).blocks[b + callee.blocks.size]? =
      some { B with term := remapCallerTerm tailBlk callee.blocks.size B.term } := by
  unfold buildTailInlinedFunc
  dsimp only
  rw [List.getElem?_toArray]
  have hlen1 : ((caller.blocks.toList.take tailBlk).map fun b =>
      { b with term := remapCallerTerm tailBlk callee.blocks.size b.term }).length = tailBlk := by
    simp [Nat.min_eq_left (Nat.le_of_lt htail)]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [hlen1]; omega), hlen1]
  rw [show b + callee.blocks.size - tailBlk = (b - tailBlk - 1 + callee.blocks.size) + 1 by omega]
  simp only [List.singleton_append, List.getElem?_cons_succ]
  have hlen2 : (callee.blocks.toList.zipIdx.map fun x =>
      inlineTailCalleeBlock callee tailBlk blk off x.2 x.1).length = callee.blocks.size := by
    simp
  rw [List.getElem?_append_right (by rw [hlen2]; omega), hlen2]
  rw [show b - tailBlk - 1 + callee.blocks.size - callee.blocks.size = b - tailBlk - 1 by omega]
  rw [List.getElem?_map, List.getElem?_drop, Array.getElem?_toList]
  rw [show tailBlk + 1 + (b - tailBlk - 1) = b by omega, hB]
  rfl

/-- 1-to-1 frame relation for `.tail` inlining: either a normal frame (`fi` remapped or `≠ fi` identical),
or an inlined callee frame `gi` executing inside `fi`'s spliced region `[tailBlk + 1, tailBlk + M]`. -/
inductive TailFrameRel (fi gi : FunId) (tailBlk M : Nat) (off : VReg) (isTop : Bool) :
    Frame → Frame → Prop where
  | other {fr : Frame} :
      fr.fn ≠ fi →
      TailFrameRel fi gi tailBlk M off isTop fr fr
  | caller {fr₁ fr₂ : Frame} :
      fr₁.fn = fi → fr₂.fn = fi →
      fr₂.label = remapCallerLabel tailBlk M fr₁.label →
      fr₂.pos = fr₁.pos →
      EnvAgreeBelow off fr₁.env fr₂.env →
      (isTop = false → fr₂.dsts = fr₁.dsts) →
      TailFrameRel fi gi tailBlk M off isTop fr₁ fr₂
  | inlined {fr₁ fr₂ : Frame} :
      fr₁.fn = gi → fr₁.label < M →
      fr₂.fn = fi → fr₂.label = tailBlk + 1 + fr₁.label →
      fr₂.pos = fr₁.pos →
      EnvShiftIncl off fr₁.env fr₂.env →
      (isTop = false → fr₂.dsts = fr₁.dsts.map (off + ·)) →
      TailFrameRel fi gi tailBlk M off isTop fr₁ fr₂

inductive TailStackRel (fi gi : FunId) (tailBlk M : Nat) (off : VReg) :
    Bool → List Frame → List Frame → Prop where
  | nil {isTop} : TailStackRel fi gi tailBlk M off isTop [] []
  | cons {isTop fr₁ fr₂ r₁ r₂} :
      TailFrameRel fi gi tailBlk M off isTop fr₁ fr₂ →
      TailStackRel fi gi tailBlk M off false r₁ r₂ →
      TailStackRel fi gi tailBlk M off isTop (fr₁ :: r₁) (fr₂ :: r₂)

def TailStateRel (fi gi : FunId) (tailBlk M : Nat) (off : VReg) (s₁ s₂ : State) : Prop :=
  s₂.mem = s₁.mem ∧ s₂.ctx = s₁.ctx ∧
  TailStackRel fi gi tailBlk M off true s₁.stack s₂.stack

def tailFramePot (fi : FunId) (tailBlk : Nat) (fr : Frame) : Nat :=
  if fr.fn == fi && decide (fr.label ≤ tailBlk) then 1 else 0

def tailPot (fi : FunId) (tailBlk : Nat) (s₂ : State) : Nat :=
  (s₂.stack.map (tailFramePot fi tailBlk)).sum

private theorem tailFramePot_le_one (fi : FunId) (tailBlk : Nat) (fr : Frame) :
    tailFramePot fi tailBlk fr ≤ 1 := by
  unfold tailFramePot; split <;> omega

private theorem tailPot_cons (fi : FunId) (tailBlk : Nat) (mem : X86.Memory) (ctx : Word)
    (fr : Frame) (rest : List Frame) :
    tailPot fi tailBlk { mem, ctx, stack := fr :: rest } =
      tailFramePot fi tailBlk fr + (rest.map (tailFramePot fi tailBlk)).sum := rfl

private theorem tail_enter_rel {p q : Program} {fi gi : FunId} {caller caller' : Func}
    {tailBlk M : Nat} {off : VReg}
    (hpfi : p.funcs[fi]? = some caller)
    (hq : q = { funcs := p.funcs.set! fi caller', main := p.main })
    (hpar : caller'.params = caller.params)
    {g : FunId} {vs : List Word} {fr₁ : Frame} (hent : enter p g vs = some fr₁) :
    ∃ fr₂, enter q g vs = some fr₂ ∧ TailFrameRel fi gi tailBlk M off true fr₁ fr₂ := by
  simp only [enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hent
  obtain ⟨F, hF, ρ, hbp, rfl⟩ := hent
  have hfiLt : fi < p.funcs.size := (Array.getElem?_eq_some_iff.1 hpfi).1
  by_cases hgf : g = fi
  · subst hgf
    rw [hpfi] at hF; cases hF
    have hqfi : q.funcs[g]? = some caller' := by rw [hq]; simp [Array.set!_eq_setIfInBounds, hfiLt]
    refine ⟨{ fn := g, label := 0, pos := 0, env := ρ, dsts := [] },
      by simp [enter, hqfi, hpar, hbp],
      .caller rfl rfl (by simp [remapCallerLabel]) rfl (envAgreeBelow_refl off ρ) (fun h => by cases h)⟩
  · have hqg : q.funcs[g]? = some F := by
      rw [hq]; simp [Array.set!_eq_setIfInBounds, Ne.symm hgf, hF]
    exact ⟨{ fn := g, label := 0, pos := 0, env := ρ, dsts := [] },
      by simp [enter, hqg, hbp], .other hgf⟩

private theorem tail_ret_rel {fi gi : FunId} {tailBlk M : Nat} {off : VReg}
    {mem : X86.Memory} {ctx : Word} {rest₁ rest₂ : List Frame} {vs : List Word}
    {s₁' : State} {b : Bool}
    (hrest : TailStackRel fi gi tailBlk M off false rest₁ rest₂)
    (hret : (match rest₁ with
        | [] => Step.done vs mem
        | c :: rest' => match bindParams c.env c.dsts vs with
            | some ρ => .next { mem, ctx, stack := { fn := c.fn, label := c.label, pos := c.pos, env := ρ } :: rest' } false
            | none => .stuck) = .next s₁' b) :
    ∃ fr₂' rest₂',
      (match rest₂ with
        | [] => Step.done vs mem
        | c :: rest' => match bindParams c.env c.dsts vs with
            | some ρ => .next { mem, ctx, stack := { fn := c.fn, label := c.label, pos := c.pos, env := ρ } :: rest' } false
            | none => .stuck) = .next { mem, ctx, stack := fr₂' :: rest₂' } false ∧
      b = false ∧
      TailStateRel fi gi tailBlk M off s₁' { mem, ctx, stack := fr₂' :: rest₂' } ∧
      (rest₂.map (tailFramePot fi tailBlk)).sum =
        tailFramePot fi tailBlk fr₂' + (rest₂'.map (tailFramePot fi tailBlk)).sum := by
  cases hrest with
  | nil => cases hret
  | cons hcal hrr =>
      rename_i c₁ c₂ r₁' r₂'
      dsimp only at hret ⊢
      cases hbp1 : bindParams c₁.env c₁.dsts vs with
      | none => rw [hbp1] at hret; cases hret
      | some ρ₁' =>
          rw [hbp1] at hret; simp only [Step.next.injEq] at hret
          obtain ⟨rfl, rfl⟩ := hret
          cases hcal with
          | other hne =>
              rw [hbp1]
              exact ⟨{ fn := c₁.fn, label := c₁.label, pos := c₁.pos, env := ρ₁', dsts := [] }, r₂',
                rfl, rfl, ⟨rfl, rfl, .cons (.other hne) hrr⟩, rfl⟩
          | caller hfn1 hfn2 hlbl hpos hagr hdsts =>
              have hd := hdsts rfl
              obtain ⟨ρ₂', hbp2, hagr'⟩ := bindParams_agreeBelow hagr hbp1
              rw [hd, hbp2]
              exact ⟨{ fn := c₂.fn, label := c₂.label, pos := c₂.pos, env := ρ₂', dsts := [] }, r₂',
                rfl, rfl, ⟨rfl, rfl, .cons (.caller hfn1 hfn2 hlbl hpos hagr' (fun h => by cases h)) hrr⟩, rfl⟩
          | inlined hfn1 hltM hfn2 hlbl hpos hsh hdsts =>
              have hd := hdsts rfl
              obtain ⟨ρ₂', hbp2, _, hsh'⟩ := bindParams_shift (envAgreeBelow_refl off c₂.env) hsh hbp1
              rw [hd, hbp2]
              exact ⟨{ fn := c₂.fn, label := c₂.label, pos := c₂.pos, env := ρ₂', dsts := [] }, r₂',
                rfl, rfl, ⟨rfl, rfl, .cons (.inlined hfn1 hltM hfn2 hlbl hpos hsh' (fun h => by cases h)) hrr⟩, rfl⟩

theorem inlineTailSite_forward {p q : Program} {fi gi : FunId} {tailBlk : Nat}
    {caller callee : Func} {blk : Block} {as : List Arg} {off : VReg}
    (hpfi : p.funcs[fi]? = some caller)
    (htail : caller.blocks[tailBlk]? = some blk)
    (hterm : blk.term = .tail gi as)
    (hpgi : p.funcs[gi]? = some callee)
    (hregs : funcRegsLt caller off = true)
    (hok : calleeInlineOk callee as.length caller.results = true)
    (hq : q = { funcs := p.funcs.set! fi (buildTailInlinedFunc caller callee tailBlk blk as off), main := p.main }) :
    PotentialForward (semStep p) (semStep q) Eq
      (TailStateRel fi gi tailBlk callee.blocks.size off)
      (fun _ s₂ => tailPot fi tailBlk s₂) 2 where
  mult_pos := by omega
  next := by
    intro s₁ s₁' s₂ b ⟨hmem, hctx, hstack⟩ hstep
    have hstep1 : step p s₁ = .next s₁' b := semStep_next.1 hstep
    have hfiLt : fi < p.funcs.size := (Array.getElem?_eq_some_iff.1 hpfi).1
    have htailLt : tailBlk < caller.blocks.size := (Array.getElem?_eq_some_iff.1 htail).1
    let caller' := buildTailInlinedFunc caller callee tailBlk blk as off
    have hqfi : q.funcs[fi]? = some caller' := by rw [hq]; simp [Array.set!_eq_setIfInBounds, hfiLt, caller']
    have hpar' : caller'.params = caller.params := rfl
    have hMpos : 0 < callee.blocks.size := by
      unfold calleeInlineOk at hok
      cases hb0 : callee.blocks[0]? with
      | none => rw [hb0] at hok; cases hok
      | some _ => exact (Array.getElem?_eq_some_iff.1 hb0).1
    have hM0 : callee.blocks[0]? ≠ none := by
      unfold calleeInlineOk at hok; cases hb0 : callee.blocks[0]? <;> simp_all
    have hlenAs : as.length = callee.params.length := by
      unfold calleeInlineOk at hok
      cases hb0 : callee.blocks[0]? with
      | none => rw [hb0] at hok; cases hok
      | some _ =>
          rw [hb0] at hok; simp only [Bool.and_eq_true, beq_iff_eq] at hok
          exact hok.1.1.2
    cases hs1 : s₁.stack with
    | nil =>
        have : step p s₁ = .stuck := by unfold step; rw [hs1]
        rw [this] at hstep1; cases hstep1
    | cons fr₁ rest₁ =>
        cases hs2 : s₂.stack with
        | nil => rw [hs1, hs2] at hstack; cases hstack
        | cons fr₂ rest₂ =>
            rw [hs1, hs2] at hstack
            cases hstack with
            | cons hfr hrest =>
                have hs1Eq : s₁ = { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ } := by
                  cases s₁; cases hs1; rfl
                have hs2Eq : s₂ = { mem := s₁.mem, ctx := s₁.ctx, stack := fr₂ :: rest₂ } := by
                  cases s₂; cases hs2; cases hmem; cases hctx; rfl
                rw [hs1Eq] at hstep1
                cases hfr with
                | other hne =>
                    have hpotEq : tailFramePot fi tailBlk fr₁ = 0 := by
                      unfold tailFramePot; simp [hne]
                    have hfnEq : q.funcs[fr₁.fn]? = p.funcs[fr₁.fn]? := by
                      rw [hq]; simp [Array.set!_eq_setIfInBounds, Ne.symm hne]
                    unfold step at hstep1; dsimp only at hstep1
                    cases hF : p.funcs[fr₁.fn]? with
                    | none => rw [hF] at hstep1; cases hstep1
                    | some F =>
                        have hG : q.funcs[fr₁.fn]? = some F := hfnEq.trans hF
                        rw [hF] at hstep1; dsimp only at hstep1
                        cases hB : F.blocks[fr₁.label]? with
                        | none => rw [hB] at hstep1; cases hstep1
                        | some B =>
                            rw [hB] at hstep1; dsimp only at hstep1
                            by_cases hlt : fr₁.pos < B.body.size
                            · simp only [hlt, ↓reduceDIte] at hstep1
                              cases hst : B.body[fr₁.pos] with
                              | assign _ _ | limb _ _ _ | store _ _ _ =>
                                  rw [hst] at hstep1; dsimp only at hstep1; rw [← hst] at hstep1
                                  cases hex : (B.body[fr₁.pos]).exec fr₁.env s₁.mem s₁.ctx with
                                  | none => rw [hex] at hstep1; cases hstep1
                                  | some res =>
                                      obtain ⟨ρ', mem'⟩ := res
                                      rw [hex] at hstep1; simp only [Step.next.injEq] at hstep1
                                      obtain ⟨rfl, rfl⟩ := hstep1
                                      have hstep2 : step q s₂ = .next
                                          { mem := mem', ctx := s₁.ctx,
                                            stack := { fr₁ with pos := fr₁.pos + 1, env := ρ' } :: rest₂ } false := by
                                        rw [hs2Eq]; unfold step; simp only [hG, hB, hlt, ↓reduceDIte]
                                        rw [hst]; dsimp only; rw [← hst, hex]
                                      refine .inl ⟨0, _, single_star_of_step hstep2,
                                        ⟨rfl, rfl, .cons (.other hne) hrest⟩, ?_⟩
                                      rw [hs2Eq, tailPot_cons, tailPot_cons, hpotEq]
                                      simp [tailFramePot, hne]
                              | call rs g cas =>
                                  rw [hst] at hstep1; dsimp only at hstep1
                                  cases hev : evalArgs fr₁.env cas with
                                  | none => rw [hev] at hstep1; cases hstep1
                                  | some vs =>
                                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                                      cases hent1 : enter p g vs with
                                      | none => rw [hent1] at hstep1; cases hstep1
                                      | some cal1 =>
                                          rw [hent1] at hstep1; simp only [Step.next.injEq] at hstep1
                                          obtain ⟨rfl, rfl⟩ := hstep1
                                          obtain ⟨cal2, hent2, hcalRel⟩ := tail_enter_rel hpfi hq hpar' hent1
                                          have hstep2 : step q s₂ = .next
                                              { mem := s₁.mem, ctx := s₁.ctx,
                                                stack := cal2 :: { fr₁ with pos := fr₁.pos + 1, dsts := rs } :: rest₂ } true := by
                                            rw [hs2Eq]; unfold step
                                            simp only [hG, hB, hlt, ↓reduceDIte, hst, hev, Option.bind_eq_bind, Option.bind_some, hent2]
                                          refine .inl ⟨1, _, single_star_of_step hstep2,
                                            ⟨rfl, rfl, .cons hcalRel (.cons (.other hne) hrest)⟩, ?_⟩
                                          simp only [hs2Eq, tailPot, List.map_cons, List.sum_cons, Bool.toNat_true]
                                          have hcalPot := tailFramePot_le_one fi tailBlk cal2
                                          have h1 : tailFramePot fi tailBlk { fr₁ with pos := fr₁.pos + 1, dsts := rs } = 0 := by
                                            unfold tailFramePot; simp [hne]
                                          rw [h1, hpotEq]; omega
                            · simp only [hlt, ↓reduceDIte] at hstep1
                              have hst2_eq := step_at_term (p := q) (F := F) (B := B)
                                (mem := s₁.mem) (ctx := s₁.ctx) (fr := fr₁) (rest := rest₂) hG hB hlt
                              have htake : ∀ (ρ : Env) (e : Edge),
                                  takeEdge F { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ e = .next s₁' b →
                                  ∃ s₂', takeEdge F { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₂ } fr₁ rest₂ ρ e = .next s₂' b ∧
                                    TailStateRel fi gi tailBlk callee.blocks.size off s₁' s₂' ∧
                                    b.toNat + tailPot fi tailBlk s₂' ≤ 2 * b.toNat + tailPot fi tailBlk s₂ := by
                                intro ρ e hte
                                unfold takeEdge at hte ⊢
                                cases hev : evalArgs ρ e.args with
                                | none => rw [hev] at hte; cases hte
                                | some vs =>
                                    cases htb : F.blocks[e.target]? with
                                    | none => rw [hev, htb] at hte; cases hte
                                    | some tB =>
                                        rw [hev, htb] at hte; dsimp only at hte
                                        cases hbp : bindParams ρ tB.params vs with
                                        | none => rw [hbp] at hte; cases hte
                                        | some ρ' =>
                                            rw [hbp] at hte; simp only [Step.next.injEq] at hte
                                            obtain ⟨rfl, rfl⟩ := hte
                                            refine ⟨{ mem := s₁.mem, ctx := s₁.ctx, stack := { fn := fr₁.fn, label := e.target, pos := 0, env := ρ', dsts := fr₁.dsts } :: rest₂ },
                                              by simp only [hbp],
                                              ⟨rfl, rfl, .cons (.other hne) hrest⟩, ?_⟩
                                            rw [hs2Eq, tailPot_cons, tailPot_cons]
                                            simp [tailFramePot, hne]; omega
                              cases ht : B.term with
                              | jump e =>
                                  rw [ht] at hstep1 hst2_eq; dsimp only at hstep1 hst2_eq
                                  obtain ⟨s₂', hte2, hrel', hpot'⟩ := htake fr₁.env e hstep1
                                  exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                              | br c w a b' t f =>
                                  rw [ht] at hstep1 hst2_eq; dsimp only at hstep1 hst2_eq
                                  cases ha : a.eval fr₁.env with
                                  | none => rw [ha] at hstep1; cases hstep1
                                  | some va =>
                                      cases hb : b'.eval fr₁.env with
                                      | none => rw [ha, hb] at hstep1; cases hstep1
                                      | some vb =>
                                          rw [ha, hb] at hstep1 hst2_eq; dsimp only at hstep1 hst2_eq
                                          obtain ⟨s₂', hte2, hrel', hpot'⟩ := htake fr₁.env _ hstep1
                                          exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                              | brOvf o x a b' ok ovf =>
                                  rw [ht] at hstep1 hst2_eq; dsimp only at hstep1 hst2_eq
                                  cases ha : a.eval fr₁.env with
                                  | none => rw [ha] at hstep1; cases hstep1
                                  | some va =>
                                      cases hb : b'.eval fr₁.env with
                                      | none => rw [ha, hb] at hstep1; cases hstep1
                                      | some vb =>
                                          rw [ha, hb] at hstep1 hst2_eq; dsimp only at hstep1 hst2_eq
                                          obtain ⟨s₂', hte2, hrel', hpot'⟩ := htake _ _ hstep1
                                          exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                              | ret ras =>
                                  rw [ht] at hstep1 hst2_eq; dsimp only at hstep1 hst2_eq
                                  cases hev : evalArgs fr₁.env ras with
                                  | none => rw [hev] at hstep1; cases hstep1
                                  | some vs =>
                                      rw [hev] at hstep1 hst2_eq; dsimp only at hstep1 hst2_eq
                                      obtain ⟨fr₂', rest₂', hret2, rfl, hrel', hpotR⟩ := tail_ret_rel hrest hstep1
                                      have hstep2 : step q s₂ = .next { mem := s₁.mem, ctx := s₁.ctx, stack := fr₂' :: rest₂' } false := by
                                        rw [hs2Eq, hst2_eq, hret2]
                                      refine .inl ⟨0, _, single_star_of_step hstep2, hrel', ?_⟩
                                      rw [hs2Eq, tailPot_cons, tailPot_cons, hpotEq, hpotR]
                                      simp only [Bool.toNat_false]; omega
                              | tail g tas =>
                                  rw [ht] at hstep1 hst2_eq; dsimp only at hstep1 hst2_eq
                                  cases hev : evalArgs fr₁.env tas with
                                  | none => rw [hev] at hstep1; cases hstep1
                                  | some vs =>
                                      rw [hev] at hstep1 hst2_eq
                                      simp only [Option.bind_eq_bind, Option.bind_some] at hstep1 hst2_eq
                                      cases hent1 : enter p g vs with
                                      | none => rw [hent1] at hstep1; cases hstep1
                                      | some cal1 =>
                                          rw [hent1] at hstep1; simp only [Step.next.injEq] at hstep1
                                          obtain ⟨rfl, rfl⟩ := hstep1
                                          obtain ⟨cal2, hent2, hcalRel⟩ := tail_enter_rel hpfi hq hpar' hent1
                                          have hstep2 : step q s₂ = .next { mem := s₁.mem, ctx := s₁.ctx, stack := cal2 :: rest₂ } true := by
                                            rw [hs2Eq, hst2_eq, hent2]
                                          refine .inl ⟨1, _, single_star_of_step hstep2,
                                            ⟨rfl, rfl, .cons hcalRel hrest⟩, ?_⟩
                                          rw [hs2Eq, tailPot_cons, tailPot_cons, hpotEq]
                                          have := tailFramePot_le_one fi tailBlk cal2
                                          simp only [Bool.toNat_true]; omega
                              | fail _ => rw [ht] at hstep1; cases hstep1
                              | trap => rw [ht] at hstep1; cases hstep1
                | caller hfn1 hfn2 hlbl hpos hagr _ =>
                    unfold step at hstep1; dsimp only at hstep1
                    rw [hfn1, hpfi] at hstep1; dsimp only at hstep1
                    cases hB : caller.blocks[fr₁.label]? with
                    | none => rw [hB] at hstep1; cases hstep1
                    | some B =>
                        have hBregs := blockRegsLt_of_func hregs hB
                        rw [hB] at hstep1; dsimp only at hstep1
                        -- Lookup `B'` in `caller'` at `fr₂.label = remapCallerLabel tailBlk M fr₁.label`
                        have hB2_info : ∃ B', caller'.blocks[fr₂.label]? = some B' ∧
                            B'.body = B.body ∧
                            (fr₁.label ≠ tailBlk → B'.term = remapCallerTerm tailBlk callee.blocks.size B.term) ∧
                            (fr₁.label = tailBlk → B'.term = .jump { target := tailBlk + 1, args := as }) := by
                          rcases Nat.lt_trichotomy fr₁.label tailBlk with hltL | heqL | hgtL
                          · refine ⟨{ B with term := remapCallerTerm tailBlk callee.blocks.size B.term }, ?_, rfl,
                              fun _ => rfl, fun h => absurd h (Nat.ne_of_lt hltL)⟩
                            rw [hlbl, remapCallerLabel]; simp only [Nat.le_of_lt hltL, ↓reduceIte]
                            exact buildTailInlined_blocks_lt hltL hB
                          · have hBeq : B = blk := by rw [heqL, htail] at hB; cases hB; rfl
                            subst hBeq
                            refine ⟨{ B with term := .jump { target := tailBlk + 1, args := as } }, ?_, rfl,
                              fun h => absurd heqL h, fun _ => rfl⟩
                            rw [hlbl, heqL, remapCallerLabel]; simp only [Nat.le_refl, ↓reduceIte]
                            exact buildTailInlined_blocks_tailBlk htailLt
                          · refine ⟨{ B with term := remapCallerTerm tailBlk callee.blocks.size B.term }, ?_, rfl,
                              fun _ => rfl, fun h => absurd h (Nat.ne_of_gt hgtL)⟩
                            rw [hlbl, remapCallerLabel]; simp only [Nat.not_le.2 hgtL, ↓reduceIte]
                            exact buildTailInlined_blocks_gt htailLt hgtL hB
                        obtain ⟨B', hB', hbodyEq, htermNe, htermEq⟩ := hB2_info
                        by_cases hlt : fr₁.pos < B.body.size
                        · simp only [hlt, ↓reduceDIte] at hstep1
                          have hlt2 : fr₂.pos < B'.body.size := by rw [hpos, hbodyEq]; exact hlt
                          have hgetEq : B'.body[fr₂.pos]'hlt2 = B.body[fr₁.pos]'hlt := by
                            simp [hpos, hbodyEq]
                          have huses := stmt_uses_lt_of_block hBregs hlt
                          cases hst : B.body[fr₁.pos] with
                          | assign _ _ | limb _ _ _ | store _ _ _ =>
                              rw [hst] at hstep1; dsimp only at hstep1; rw [← hst] at hstep1
                              cases hex : (B.body[fr₁.pos]).exec fr₁.env s₁.mem s₁.ctx with
                              | none => rw [hex] at hstep1; cases hstep1
                              | some res =>
                                  obtain ⟨ρ₁', mem'⟩ := res
                                  rw [hex] at hstep1; simp only [Step.next.injEq] at hstep1
                                  obtain ⟨rfl, rfl⟩ := hstep1
                                  obtain ⟨ρ₂', hex2, hagr'⟩ := stmt_exec_agreeBelow hagr huses hex
                                  have hstep2 : step q s₂ = .next
                                      { mem := mem', ctx := s₁.ctx,
                                        stack := { fr₂ with pos := fr₂.pos + 1, env := ρ₂' } :: rest₂ } false := by
                                    rw [hs2Eq]; unfold step; simp only [hfn2, hqfi, hB', hlt2, ↓reduceDIte, hgetEq]
                                    rw [hst]; dsimp only; rw [← hst, hex2]
                                  refine .inl ⟨0, _, single_star_of_step hstep2,
                                    ⟨rfl, rfl, .cons (.caller rfl hfn2 hlbl (by simp [hpos]) hagr' (fun h => by cases h)) hrest⟩, ?_⟩
                                  rw [hs2Eq, tailPot_cons, tailPot_cons]; simp [tailFramePot]
                          | call rs g cas =>
                              rw [hst] at hstep1; dsimp only at hstep1
                              cases hev : evalArgs fr₁.env cas with
                              | none => rw [hev] at hstep1; cases hstep1
                              | some vs =>
                                  rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                                  cases hent1 : enter p g vs with
                                  | none => rw [hent1] at hstep1; cases hstep1
                                  | some cal1 =>
                                      rw [hent1] at hstep1; simp only [Step.next.injEq] at hstep1
                                      obtain ⟨rfl, rfl⟩ := hstep1
                                      have hcasLt : ∀ a ∈ cas, listLt off a.uses = true := by
                                        have h1 := huses; rw [hst] at h1
                                        exact listLt_flatMap_uses h1
                                      have hev2 := (evalArgs_agreeBelow hagr hcasLt).trans hev
                                      obtain ⟨cal2, hent2, hcalRel⟩ := tail_enter_rel hpfi hq hpar' hent1
                                      have hstep2 : step q s₂ = .next
                                          { mem := s₁.mem, ctx := s₁.ctx,
                                            stack := cal2 :: { fr₂ with pos := fr₂.pos + 1, dsts := rs } :: rest₂ } true := by
                                        rw [hs2Eq]; unfold step
                                        simp only [hfn2, hqfi, hB', hlt2, ↓reduceDIte, hgetEq, hst, hev2,
                                          Option.bind_eq_bind, Option.bind_some, hent2]
                                      refine .inl ⟨1, _, single_star_of_step hstep2,
                                        ⟨rfl, rfl, .cons hcalRel (.cons (.caller rfl hfn2 hlbl (by simp [hpos]) hagr (fun _ => rfl)) hrest)⟩, ?_⟩
                                      simp only [hs2Eq, tailPot, List.map_cons, List.sum_cons, Bool.toNat_true]
                                      have := tailFramePot_le_one fi tailBlk cal2
                                      have hfpEq : tailFramePot fi tailBlk { fr₂ with pos := fr₂.pos + 1, dsts := rs } =
                                          tailFramePot fi tailBlk fr₂ := rfl
                                      rw [hfpEq]; omega
                        · simp only [hlt, ↓reduceDIte] at hstep1
                          have hlt2 : ¬(fr₂.pos < B'.body.size) := by rw [hpos, hbodyEq]; exact hlt
                          have hst2_eq := step_at_term (p := q) (F := caller') (B := B')
                            (mem := s₁.mem) (ctx := s₁.ctx) (fr := fr₂) (rest := rest₂)
                            (by rw [hfn2]; exact hqfi) hB' hlt2
                          by_cases hAtTail : fr₁.label = tailBlk
                          · -- **THE INLINED `.tail gi as` SITE (`tailBlk → tailBlk + 1`)!**
                            have hBeq : B = blk := by rw [hAtTail, htail] at hB; cases hB; rfl
                            have hBt : B.term = .tail gi as := by rw [hBeq, hterm]
                            have hBt2 : B'.term = .jump { target := tailBlk + 1, args := as } := htermEq hAtTail
                            rw [hBt] at hstep1; dsimp only at hstep1
                            rw [hBt2] at hst2_eq; dsimp only at hst2_eq
                            cases hev1 : evalArgs fr₁.env as with
                            | none => rw [hev1] at hstep1; cases hstep1
                            | some vs =>
                                rw [hev1] at hstep1
                                simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                                cases hent1 : enter p gi vs with
                                | none => rw [hent1] at hstep1; cases hstep1
                                | some cal1 =>
                                    rw [hent1] at hstep1; simp only [Step.next.injEq] at hstep1
                                    obtain ⟨rfl, rfl⟩ := hstep1
                                    simp only [enter, hpgi, Option.bind_eq_bind, Option.bind_some,
                                      Option.bind_eq_some_iff, Option.some.injEq] at hent1
                                    obtain ⟨ρC, hbpC, rfl⟩ := hent1
                                    have hasLt : ∀ a ∈ as, listLt off a.uses = true := by
                                      have hu := (term_uses_lt_of_block hBregs).1
                                      rw [hBt] at hu
                                      exact listLt_flatMap_uses hu
                                    have hev2 := (evalArgs_agreeBelow hagr hasLt).trans hev1
                                    cases hb0 : callee.blocks[0]? with
                                    | none => exact absurd hb0 hM0
                                    | some cb0 =>
                                        have hB2_0 : caller'.blocks[tailBlk + 1]? =
                                            some (inlineTailCalleeBlock callee tailBlk blk off 0 cb0) := by
                                          simpa using buildTailInlined_blocks_inlined (caller := caller) (callee := callee)
                                            (tailBlk := tailBlk) (blk := blk) (as := as) (off := off) htailLt hb0
                                        obtain ⟨ρ₂', hbp2, _, hsh'⟩ := bindParams_shift
                                          (envAgreeBelow_refl off fr₂.env) (envShiftIncl_empty off fr₂.env) hbpC
                                        have hte2 : takeEdge caller' { mem := s₁.mem, ctx := s₁.ctx, stack := fr₂ :: rest₂ }
                                            fr₂ rest₂ fr₂.env { target := tailBlk + 1, args := as } =
                                            .next
                                              { mem := s₁.mem, ctx := s₁.ctx,
                                                stack := { fn := fr₂.fn, label := tailBlk + 1, pos := 0, env := ρ₂', dsts := fr₂.dsts } :: rest₂ }
                                              false := by
                                          have hlbl_eq : fr₂.label = tailBlk := by
                                            simp [hlbl, hAtTail, remapCallerLabel]
                                          have hnf : decide (tailBlk + 1 ≤ fr₂.label) = false := by
                                            rw [hlbl_eq]; exact decide_eq_false (Nat.not_succ_le_self tailBlk)
                                          have hpar0 : (inlineTailCalleeBlock callee tailBlk blk off 0 cb0).params =
                                              callee.params.map (off + ·) := by
                                            simp [inlineTailCalleeBlock]
                                          have hte := takeEdge_ok (F := caller')
                                            (s := { mem := s₁.mem, ctx := s₁.ctx, stack := fr₂ :: rest₂ })
                                            (fr := fr₂) (rest := rest₂) (ρ := fr₂.env)
                                            (e := { target := tailBlk + 1, args := as })
                                            hev2 hB2_0 (by rw [hpar0]; exact hbp2)
                                          dsimp only at hte
                                          rw [hnf] at hte
                                          exact hte
                                        have hstep2 : step q s₂ = .next
                                            { mem := s₁.mem, ctx := s₁.ctx,
                                              stack := { fn := fr₂.fn, label := tailBlk + 1, pos := 0, env := ρ₂', dsts := fr₂.dsts } :: rest₂ }
                                            false := by rw [hs2Eq, hst2_eq, hte2]
                                        refine .inl ⟨0, _, single_star_of_step hstep2,
                                          ⟨rfl, rfl, .cons (.inlined rfl hMpos hfn2 (by simp) rfl hsh' (fun h => by cases h)) hrest⟩, ?_⟩
                                        -- Potential drop: `tailFramePot` goes `1 → 0`, paying the 1 source `.tail` charge!
                                        rw [hs2Eq, tailPot_cons, tailPot_cons]
                                        have hlbl_eq : fr₂.label = tailBlk := by
                                          simp [hlbl, hAtTail, remapCallerLabel]
                                        have hp1 : tailFramePot fi tailBlk fr₂ = 1 := by
                                          unfold tailFramePot; simp [hfn2, hlbl_eq]
                                        have hp2 : tailFramePot fi tailBlk
                                            { fn := fr₂.fn, label := tailBlk + 1, pos := 0, env := ρ₂', dsts := fr₂.dsts } = 0 := by
                                          unfold tailFramePot; simp [hfn2]
                                        rw [hp1, hp2]; simp only [Bool.toNat_true]; omega
                          · -- Regular caller block (`fr₁.label ≠ tailBlk`)
                            have hBt2 := htermNe hAtTail
                            have htu := term_uses_lt_of_block hBregs
                            have htakeCaller : ∀ (ρ₁' ρ₂' : Env) (e : Edge),
                                EnvAgreeBelow off ρ₁' ρ₂' →
                                e ∈ B.term.edges →
                                takeEdge caller { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ₁' e = .next s₁' b →
                                ∃ s₂', takeEdge caller' { mem := s₁.mem, ctx := s₁.ctx, stack := fr₂ :: rest₂ } fr₂ rest₂ ρ₂'
                                    (remapCallerEdge tailBlk callee.blocks.size e) = .next s₂' b ∧
                                  TailStateRel fi gi tailBlk callee.blocks.size off s₁' s₂' ∧
                                  b.toNat + tailPot fi tailBlk s₂' ≤ 2 * b.toNat + tailPot fi tailBlk s₂ := by
                              intro ρ₁' ρ₂' e hagr' heMem hte1
                              unfold takeEdge at hte1 ⊢
                              cases hev1 : evalArgs ρ₁' e.args with
                              | none => rw [hev1] at hte1; cases hte1
                              | some vs =>
                                  cases htb : caller.blocks[e.target]? with
                                  | none => rw [hev1, htb] at hte1; cases hte1
                                  | some tB =>
                                      rw [hev1, htb] at hte1; dsimp only at hte1
                                      cases hbp1 : bindParams ρ₁' tB.params vs with
                                      | none => rw [hbp1] at hte1; cases hte1
                                      | some ρ₁'' =>
                                          rw [hbp1] at hte1; simp only [Step.next.injEq] at hte1
                                          obtain ⟨rfl, rfl⟩ := hte1
                                          have heLt : ∀ a ∈ e.args, listLt off a.uses = true :=
                                            edge_args_lt_of_term htu.2 heMem
                                          have hev2 := (evalArgs_agreeBelow hagr' heLt).trans hev1
                                          have htb2 : ∃ tB', caller'.blocks[remapCallerLabel tailBlk callee.blocks.size e.target]? = some tB' ∧
                                              tB'.params = tB.params := by
                                            rcases Nat.lt_trichotomy e.target tailBlk with hltT | heqT | hgtT
                                            · refine ⟨{ tB with term := remapCallerTerm tailBlk callee.blocks.size tB.term }, ?_, rfl⟩
                                              rw [remapCallerLabel]; simp only [Nat.le_of_lt hltT, ↓reduceIte]
                                              exact buildTailInlined_blocks_lt hltT htb
                                            · have hTeq : tB = blk := by rw [heqT, htail] at htb; cases htb; rfl
                                              subst hTeq
                                              refine ⟨{ tB with term := .jump { target := tailBlk + 1, args := as } }, ?_, rfl⟩
                                              rw [heqT, remapCallerLabel]; simp only [Nat.le_refl, ↓reduceIte]
                                              exact buildTailInlined_blocks_tailBlk htailLt
                                            · refine ⟨{ tB with term := remapCallerTerm tailBlk callee.blocks.size tB.term }, ?_, rfl⟩
                                              rw [remapCallerLabel]; simp only [Nat.not_le.2 hgtT, ↓reduceIte]
                                              exact buildTailInlined_blocks_gt htailLt hgtT htb
                                          obtain ⟨tB', htb2', hparT⟩ := htb2
                                          obtain ⟨ρ₂'', hbp2, hagr''⟩ := bindParams_agreeBelow hagr' hbp1
                                          have hchg : decide (remapCallerLabel tailBlk callee.blocks.size e.target ≤ fr₂.label) =
                                              decide (e.target ≤ fr₁.label) := by
                                            rw [hlbl]; exact remapCallerLabel_le_iff tailBlk callee.blocks.size e.target fr₁.label hAtTail
                                          refine ⟨{ mem := s₁.mem, ctx := s₁.ctx, stack := { fn := fr₂.fn, label := remapCallerLabel tailBlk callee.blocks.size e.target, pos := 0, env := ρ₂'', dsts := fr₂.dsts } :: rest₂ },
                                            by simp [remapCallerEdge, hev2, htb2', hparT, hbp2]; exact hchg,
                                            ⟨rfl, rfl, .cons (.caller hfn1 hfn2 rfl rfl hagr'' (fun h => by cases h)) hrest⟩, ?_⟩
                                          rw [hs2Eq, tailPot_cons, tailPot_cons]
                                          by_cases hle : e.target ≤ fr₁.label
                                          · have h1 := tailFramePot_le_one fi tailBlk
                                              { fn := fr₂.fn, label := remapCallerLabel tailBlk callee.blocks.size e.target, pos := 0, env := ρ₂'', dsts := fr₂.dsts }
                                            simp [hle]; omega
                                          · have hgt : fr₁.label < e.target := Nat.lt_of_not_le hle
                                            have hpotMono : tailFramePot fi tailBlk
                                                { fn := fr₂.fn, label := remapCallerLabel tailBlk callee.blocks.size e.target, pos := 0, env := ρ₂'', dsts := fr₂.dsts } ≤
                                                tailFramePot fi tailBlk fr₂ := by
                                              by_cases hT : e.target ≤ tailBlk
                                              · have hL1 : fr₁.label ≤ tailBlk := Nat.le_of_lt (Nat.lt_of_lt_of_le hgt hT)
                                                have hR : tailFramePot fi tailBlk fr₂ = 1 := by
                                                  unfold tailFramePot
                                                  simp [hfn2, hlbl, remapCallerLabel, hL1]
                                                rw [hR]; exact tailFramePot_le_one _ _ _
                                              · have hnle : ¬ (e.target + callee.blocks.size ≤ tailBlk) :=
                                                  fun h => hT (Nat.le_trans (Nat.le_add_right _ _) h)
                                                have hL : tailFramePot fi tailBlk
                                                    { fn := fr₂.fn, label := remapCallerLabel tailBlk callee.blocks.size e.target, pos := 0, env := ρ₂'', dsts := fr₂.dsts } = 0 := by
                                                  unfold tailFramePot
                                                  simp [remapCallerLabel, hT, hnle]
                                                rw [hL]; exact Nat.zero_le _
                                            simp [hle]; omega
                            cases ht : B.term with
                            | jump e =>
                                rw [ht] at hstep1; rw [hBt2, ht] at hst2_eq; dsimp only [remapCallerTerm] at hst2_eq; dsimp only at hstep1 hst2_eq
                                obtain ⟨s₂', hte2, hrel', hpot'⟩ := htakeCaller fr₁.env fr₂.env e hagr (by simp [ht, Term.edges]) hstep1
                                exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                            | br c w a b' t f =>
                                rw [ht] at hstep1; rw [hBt2, ht] at hst2_eq; dsimp only [remapCallerTerm] at hst2_eq; dsimp only at hstep1 hst2_eq
                                have hab := htu.1; rw [ht] at hab; simp only [Term.uses, listLt_append] at hab
                                cases ha : a.eval fr₁.env with
                                | none => rw [ha] at hstep1; cases hstep1
                                | some va =>
                                    cases hb : b'.eval fr₁.env with
                                    | none => rw [ha, hb] at hstep1; cases hstep1
                                    | some vb =>
                                        rw [ha, hb] at hstep1
                                        rw [(arg_eval_agreeBelow hagr hab.1).trans ha, (arg_eval_agreeBelow hagr hab.2).trans hb] at hst2_eq
                                        dsimp only at hstep1 hst2_eq
                                        cases hc : c.holds w va vb <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at hstep1 hst2_eq
                                        · obtain ⟨s₂', hte2, hrel', hpot'⟩ := htakeCaller fr₁.env fr₂.env f hagr (by simp [ht, Term.edges]) hstep1
                                          exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                                        · obtain ⟨s₂', hte2, hrel', hpot'⟩ := htakeCaller fr₁.env fr₂.env t hagr (by simp [ht, Term.edges]) hstep1
                                          exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                            | brOvf o x a b' ok ovf =>
                                rw [ht] at hstep1; rw [hBt2, ht] at hst2_eq; dsimp only [remapCallerTerm] at hst2_eq; dsimp only at hstep1 hst2_eq
                                have hab := htu.1; rw [ht] at hab; simp only [Term.uses, listLt_append] at hab
                                cases ha : a.eval fr₁.env with
                                | none => rw [ha] at hstep1; cases hstep1
                                | some va =>
                                    cases hb : b'.eval fr₁.env with
                                    | none => rw [ha, hb] at hstep1; cases hstep1
                                    | some vb =>
                                        rw [ha, hb] at hstep1
                                        rw [(arg_eval_agreeBelow hagr hab.1).trans ha, (arg_eval_agreeBelow hagr hab.2).trans hb] at hst2_eq
                                        dsimp only at hstep1 hst2_eq
                                        have hagr' := envAgreeBelow_insert_lt hagr (o.eval va vb).1 (x := x)
                                        cases hcar : (o.eval va vb).2 <;> simp only [hcar, Bool.false_eq_true, ↓reduceIte] at hstep1 hst2_eq
                                        · obtain ⟨s₂', hte2, hrel', hpot'⟩ := htakeCaller _ _ ok hagr' (by simp [ht, Term.edges]) hstep1
                                          exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                                        · obtain ⟨s₂', hte2, hrel', hpot'⟩ := htakeCaller _ _ ovf hagr' (by simp [ht, Term.edges]) hstep1
                                          exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                            | ret ras =>
                                rw [ht] at hstep1; rw [hBt2, ht] at hst2_eq; dsimp only [remapCallerTerm] at hst2_eq; dsimp only at hstep1 hst2_eq
                                have hrasLt : ∀ a ∈ ras, listLt off a.uses = true := by
                                  have hu := htu.1; rw [ht] at hu; exact listLt_flatMap_uses hu
                                cases hev1 : evalArgs fr₁.env ras with
                                | none => rw [hev1] at hstep1; cases hstep1
                                | some vs =>
                                    rw [hev1] at hstep1; rw [(evalArgs_agreeBelow hagr hrasLt).trans hev1] at hst2_eq
                                    dsimp only at hstep1 hst2_eq
                                    obtain ⟨fr₂', rest₂', hret2, rfl, hrel', hpotR⟩ := tail_ret_rel hrest hstep1
                                    have hstep2 : step q s₂ = .next { mem := s₁.mem, ctx := s₁.ctx, stack := fr₂' :: rest₂' } false := by
                                      rw [hs2Eq, hst2_eq, hret2]
                                    refine .inl ⟨0, _, single_star_of_step hstep2, hrel', ?_⟩
                                    rw [hs2Eq, tailPot_cons, tailPot_cons, hpotR]
                                    simp only [Bool.toNat_false]; omega
                            | tail g tas =>
                                rw [ht] at hstep1; rw [hBt2, ht] at hst2_eq; dsimp only [remapCallerTerm] at hst2_eq; dsimp only at hstep1 hst2_eq
                                have htasLt : ∀ a ∈ tas, listLt off a.uses = true := by
                                  have hu := htu.1; rw [ht] at hu; exact listLt_flatMap_uses hu
                                cases hev1 : evalArgs fr₁.env tas with
                                | none => rw [hev1] at hstep1; cases hstep1
                                | some vs =>
                                    rw [hev1] at hstep1; rw [(evalArgs_agreeBelow hagr htasLt).trans hev1] at hst2_eq
                                    simp only [Option.bind_eq_bind, Option.bind_some] at hstep1 hst2_eq
                                    cases hent1 : enter p g vs with
                                    | none => rw [hent1] at hstep1; cases hstep1
                                    | some cal1 =>
                                        rw [hent1] at hstep1; simp only [Step.next.injEq] at hstep1
                                        obtain ⟨rfl, rfl⟩ := hstep1
                                        obtain ⟨cal2, hent2, hcalRel⟩ := tail_enter_rel hpfi hq hpar' hent1
                                        have hstep2 : step q s₂ = .next { mem := s₁.mem, ctx := s₁.ctx, stack := cal2 :: rest₂ } true := by
                                          rw [hs2Eq, hst2_eq, hent2]
                                        refine .inl ⟨1, _, single_star_of_step hstep2,
                                          ⟨rfl, rfl, .cons hcalRel hrest⟩, ?_⟩
                                        rw [hs2Eq, tailPot_cons, tailPot_cons]
                                        have := tailFramePot_le_one fi tailBlk cal2
                                        simp only [Bool.toNat_true]; omega
                            | fail _ => rw [ht] at hstep1; cases hstep1
                            | trap => rw [ht] at hstep1; cases hstep1
                | inlined hfn1 hltM hfn2 hlbl hpos hsh _ =>
                    have hpot0 : tailFramePot fi tailBlk fr₂ = 0 := by
                      unfold tailFramePot
                      have hgt : ¬ (tailBlk + 1 + fr₁.label ≤ tailBlk) := by omega
                      simp [hfn2, hlbl, hgt]
                    unfold step at hstep1; dsimp only at hstep1
                    rw [hfn1, hpgi] at hstep1; dsimp only at hstep1
                    cases hB : callee.blocks[fr₁.label]? with
                    | none => rw [hB] at hstep1; cases hstep1
                    | some B =>
                        rw [hB] at hstep1; dsimp only at hstep1
                        have hB2 : caller'.blocks[fr₂.label]? =
                            some (inlineTailCalleeBlock callee tailBlk blk off fr₁.label B) := by
                          rw [hlbl]
                          exact buildTailInlined_blocks_inlined (caller := caller) (callee := callee)
                            (tailBlk := tailBlk) (blk := blk) (as := as) (off := off) htailLt hB
                        have hcbOk := calleeBlockOk_of hok hB
                        by_cases hlt : fr₁.pos < B.body.size
                        · simp only [hlt, ↓reduceDIte] at hstep1
                          have hlt2 : fr₂.pos < (inlineTailCalleeBlock callee tailBlk blk off fr₁.label B).body.size := by
                            simp [inlineTailCalleeBlock, hpos, hlt]
                          have hget2 : (inlineTailCalleeBlock callee tailBlk blk off fr₁.label B).body[fr₂.pos]'hlt2 =
                              shiftStmt off (B.body[fr₁.pos]'hlt) := by
                            simp [inlineTailCalleeBlock, hpos]
                          cases hst : B.body[fr₁.pos] with
                          | assign _ _ | limb _ _ _ | store _ _ _ =>
                              rw [hst] at hstep1; dsimp only at hstep1; rw [← hst] at hstep1
                              cases hex : (B.body[fr₁.pos]).exec fr₁.env s₁.mem s₁.ctx with
                              | none => rw [hex] at hstep1; cases hstep1
                              | some res =>
                                  obtain ⟨ρ₁', mem'⟩ := res
                                  rw [hex] at hstep1; simp only [Step.next.injEq] at hstep1
                                  obtain ⟨rfl, rfl⟩ := hstep1
                                  obtain ⟨ρ₂', hex2, _, hsh'⟩ := shiftStmt_exec (envAgreeBelow_refl off fr₂.env) hsh hex
                                  have hstep2 : step q s₂ = .next
                                      { mem := mem', ctx := s₁.ctx,
                                        stack := { fr₂ with pos := fr₂.pos + 1, env := ρ₂' } :: rest₂ } false := by
                                    rw [hs2Eq]; unfold step
                                    simp only [hfn2, hqfi, hB2, hlt2, ↓reduceDIte, hget2]
                                    rw [hst] at hex2 ⊢; dsimp only [shiftStmt] at hex2 ⊢; rw [hex2]
                                  refine .inl ⟨0, _, single_star_of_step hstep2,
                                    ⟨rfl, rfl, .cons (.inlined rfl hltM hfn2 hlbl (by simp [hpos]) hsh' (fun h => by cases h)) hrest⟩, ?_⟩
                                  rw [hs2Eq, tailPot_cons, tailPot_cons, hpot0]
                                  have : tailFramePot fi tailBlk { fr₂ with pos := fr₂.pos + 1, env := ρ₂' } = 0 := hpot0
                                  rw [this]; simp only [Bool.toNat_false]; omega
                          | call rs g cas =>
                              rw [hst] at hstep1; dsimp only at hstep1
                              cases hev : evalArgs fr₁.env cas with
                              | none => rw [hev] at hstep1; cases hstep1
                              | some vs =>
                                  rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                                  cases hent1 : enter p g vs with
                                  | none => rw [hent1] at hstep1; cases hstep1
                                  | some cal1 =>
                                      rw [hent1] at hstep1; simp only [Step.next.injEq] at hstep1
                                      obtain ⟨rfl, rfl⟩ := hstep1
                                      have hev2 := shiftArgs_eval hsh hev
                                      obtain ⟨cal2, hent2, hcalRel⟩ := tail_enter_rel hpfi hq hpar' hent1
                                      have hstep2 : step q s₂ = .next
                                          { mem := s₁.mem, ctx := s₁.ctx,
                                            stack := cal2 :: { fr₂ with pos := fr₂.pos + 1, dsts := rs.map (off + ·) } :: rest₂ } true := by
                                        rw [hs2Eq]; unfold step
                                        simp only [hfn2, hqfi, hB2, hlt2, ↓reduceDIte, hget2, hst, shiftStmt, hev2,
                                          Option.bind_eq_bind, Option.bind_some, hent2]
                                      refine .inl ⟨1, _, single_star_of_step hstep2,
                                        ⟨rfl, rfl, .cons hcalRel (.cons (.inlined rfl hltM hfn2 hlbl (by simp [hpos]) hsh (fun _ => rfl)) hrest)⟩, ?_⟩
                                      simp only [hs2Eq, tailPot, List.map_cons, List.sum_cons, Bool.toNat_true, hpot0]
                                      have h1 := tailFramePot_le_one fi tailBlk cal2
                                      have h2 : tailFramePot fi tailBlk { fr₂ with pos := fr₂.pos + 1, dsts := rs.map (off + ·) } = 0 := hpot0
                                      rw [h2]; omega
                        · simp only [hlt, ↓reduceDIte] at hstep1
                          have hlt2 : ¬(fr₂.pos < (inlineTailCalleeBlock callee tailBlk blk off fr₁.label B).body.size) := by
                            simp [inlineTailCalleeBlock, hpos, hlt]
                          have hst2_eq := step_at_term (p := q) (F := caller')
                            (B := inlineTailCalleeBlock callee tailBlk blk off fr₁.label B)
                            (mem := s₁.mem) (ctx := s₁.ctx) (fr := fr₂) (rest := rest₂)
                            (by rw [hfn2]; exact hqfi) hB2 hlt2
                          have htakeInl : ∀ (ρ₁' ρ₂' : Env) (e : Edge),
                              EnvShiftIncl off ρ₁' ρ₂' →
                              e ∈ B.term.edges →
                              takeEdge callee { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ₁' e = .next s₁' b →
                              ∃ s₂', takeEdge caller' { mem := s₁.mem, ctx := s₁.ctx, stack := fr₂ :: rest₂ } fr₂ rest₂ ρ₂'
                                  (shiftEdge off (tailBlk + 1) e) = .next s₂' b ∧
                                TailStateRel fi gi tailBlk callee.blocks.size off s₁' s₂' ∧
                                b.toNat + tailPot fi tailBlk s₂' ≤ 2 * b.toNat + tailPot fi tailBlk s₂ := by
                            intro ρ₁' ρ₂' e hsh' heMem hte1
                            unfold takeEdge at hte1 ⊢
                            cases hev1 : evalArgs ρ₁' e.args with
                            | none => rw [hev1] at hte1; cases hte1
                            | some vs =>
                                cases htb : callee.blocks[e.target]? with
                                | none => rw [hev1, htb] at hte1; cases hte1
                                | some tB =>
                                    rw [hev1, htb] at hte1; dsimp only at hte1
                                    cases hbp1 : bindParams ρ₁' tB.params vs with
                                    | none => rw [hbp1] at hte1; cases hte1
                                    | some ρ₁'' =>
                                        rw [hbp1] at hte1; simp only [Step.next.injEq] at hte1
                                        obtain ⟨rfl, rfl⟩ := hte1
                                        simp only [calleeBlockOk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, decide_eq_true_eq] at hcbOk
                                        obtain ⟨htNe0, htLtM⟩ := hcbOk.2 e heMem
                                        have hev2 := shiftArgs_eval hsh' hev1
                                        have htb2 : caller'.blocks[tailBlk + 1 + e.target]? =
                                            some (inlineTailCalleeBlock callee tailBlk blk off e.target tB) :=
                                          buildTailInlined_blocks_inlined (caller := caller) (callee := callee)
                                            (tailBlk := tailBlk) (blk := blk) (as := as) (off := off) htailLt htb
                                        obtain ⟨ρ₂'', hbp2, _, hsh''⟩ := bindParams_shift (envAgreeBelow_refl off ρ₂') hsh' hbp1
                                        have hchg : decide (tailBlk + 1 + e.target ≤ fr₂.label) = decide (e.target ≤ fr₁.label) := by
                                          rw [hlbl]; simp only [decide_eq_decide]
                                          exact ⟨fun h => Nat.le_of_add_le_add_left h, fun h => Nat.add_le_add_left h _⟩
                                        have hparT : (inlineTailCalleeBlock callee tailBlk blk off e.target tB).params =
                                            tB.params.map (off + ·) := by
                                          simp [inlineTailCalleeBlock, htNe0]
                                        refine ⟨{ mem := s₁.mem, ctx := s₁.ctx, stack := { fn := fr₂.fn, label := tailBlk + 1 + e.target, pos := 0, env := ρ₂'', dsts := fr₂.dsts } :: rest₂ },
                                          by simp [shiftEdge, hev2, htb2, hparT, hbp2]; exact hchg,
                                          ⟨rfl, rfl, .cons (.inlined hfn1 htLtM hfn2 rfl rfl hsh'' (fun h => by cases h)) hrest⟩, ?_⟩
                                        rw [hs2Eq, tailPot_cons, tailPot_cons, hpot0]
                                        have : tailFramePot fi tailBlk
                                            { fn := fr₂.fn, label := tailBlk + 1 + e.target, pos := 0, env := ρ₂'', dsts := fr₂.dsts } = 0 := by
                                          unfold tailFramePot
                                          have hgt : ¬ (tailBlk + 1 + e.target ≤ tailBlk) := by omega
                                          simp [hfn2, hgt]
                                        rw [this]; omega
                          dsimp only [inlineTailCalleeBlock] at hst2_eq
                          cases ht : B.term with
                          | jump e =>
                              rw [ht] at hstep1 hst2_eq; dsimp only [rewriteTailCalleeTerm] at hst2_eq
                              dsimp only at hstep1 hst2_eq
                              obtain ⟨s₂', hte2, hrel', hpot'⟩ := htakeInl fr₁.env fr₂.env e hsh (by simp [ht, Term.edges]) hstep1
                              exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                          | br c w a b' t f =>
                              rw [ht] at hstep1 hst2_eq; dsimp only [rewriteTailCalleeTerm] at hst2_eq
                              dsimp only at hstep1 hst2_eq
                              cases ha : a.eval fr₁.env with
                              | none => rw [ha] at hstep1; cases hstep1
                              | some va =>
                                  cases hb : b'.eval fr₁.env with
                                  | none => rw [ha, hb] at hstep1; cases hstep1
                                  | some vb =>
                                      rw [ha, hb] at hstep1
                                      rw [shiftArg_eval hsh ha, shiftArg_eval hsh hb] at hst2_eq
                                      dsimp only at hstep1 hst2_eq
                                      cases hc : c.holds w va vb <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at hstep1 hst2_eq
                                      · obtain ⟨s₂', hte2, hrel', hpot'⟩ := htakeInl fr₁.env fr₂.env f hsh (by simp [ht, Term.edges]) hstep1
                                        exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                                      · obtain ⟨s₂', hte2, hrel', hpot'⟩ := htakeInl fr₁.env fr₂.env t hsh (by simp [ht, Term.edges]) hstep1
                                        exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                          | brOvf o x a b' ok ovf =>
                              rw [ht] at hstep1 hst2_eq; dsimp only [rewriteTailCalleeTerm] at hst2_eq
                              dsimp only at hstep1 hst2_eq
                              cases ha : a.eval fr₁.env with
                              | none => rw [ha] at hstep1; cases hstep1
                              | some va =>
                                  cases hb : b'.eval fr₁.env with
                                  | none => rw [ha, hb] at hstep1; cases hstep1
                                  | some vb =>
                                      rw [ha, hb] at hstep1
                                      rw [shiftArg_eval hsh ha, shiftArg_eval hsh hb] at hst2_eq
                                      dsimp only at hstep1 hst2_eq
                                      have hsh' := envShiftIncl_insert hsh x (o.eval va vb).1
                                      cases hcar : (o.eval va vb).2 <;> simp only [hcar, Bool.false_eq_true, ↓reduceIte] at hstep1 hst2_eq
                                      · obtain ⟨s₂', hte2, hrel', hpot'⟩ := htakeInl _ _ ok hsh' (by simp [ht, Term.edges]) hstep1
                                        exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                                      · obtain ⟨s₂', hte2, hrel', hpot'⟩ := htakeInl _ _ ovf hsh' (by simp [ht, Term.edges]) hstep1
                                        exact .inl ⟨b.toNat, s₂', single_star_of_step (by rw [hs2Eq, hst2_eq, hte2]), hrel', hpot'⟩
                          | ret ras =>
                              rw [ht] at hstep1 hst2_eq; dsimp only [rewriteTailCalleeTerm] at hst2_eq
                              dsimp only at hstep1 hst2_eq
                              cases hev1 : evalArgs fr₁.env ras with
                              | none => rw [hev1] at hstep1; cases hstep1
                              | some vs =>
                                  rw [hev1] at hstep1; rw [shiftArgs_eval hsh hev1] at hst2_eq
                                  dsimp only at hstep1 hst2_eq
                                  obtain ⟨fr₂', rest₂', hret2, rfl, hrel', hpotR⟩ := tail_ret_rel hrest hstep1
                                  have hstep2 : step q s₂ = .next { mem := s₁.mem, ctx := s₁.ctx, stack := fr₂' :: rest₂' } false := by
                                    rw [hs2Eq, hst2_eq, hret2]
                                  refine .inl ⟨0, _, single_star_of_step hstep2, hrel', ?_⟩
                                  rw [hs2Eq, tailPot_cons, tailPot_cons, hpot0, hpotR]
                                  simp only [Bool.toNat_false]; omega
                          | tail g tas =>
                              rw [ht] at hstep1 hst2_eq; dsimp only [rewriteTailCalleeTerm] at hst2_eq
                              dsimp only at hstep1 hst2_eq
                              cases hev1 : evalArgs fr₁.env tas with
                              | none => rw [hev1] at hstep1; cases hstep1
                              | some vs =>
                                  rw [hev1] at hstep1; rw [shiftArgs_eval hsh hev1] at hst2_eq
                                  simp only [Option.bind_eq_bind, Option.bind_some] at hstep1 hst2_eq
                                  cases hent1 : enter p g vs with
                                  | none => rw [hent1] at hstep1; cases hstep1
                                  | some cal1 =>
                                      rw [hent1] at hstep1; simp only [Step.next.injEq] at hstep1
                                      obtain ⟨rfl, rfl⟩ := hstep1
                                      obtain ⟨cal2, hent2, hcalRel⟩ := tail_enter_rel hpfi hq hpar' hent1
                                      have hstep2 : step q s₂ = .next { mem := s₁.mem, ctx := s₁.ctx, stack := cal2 :: rest₂ } true := by
                                        rw [hs2Eq, hst2_eq, hent2]
                                      refine .inl ⟨1, _, single_star_of_step hstep2,
                                        ⟨rfl, rfl, .cons hcalRel hrest⟩, ?_⟩
                                      rw [hs2Eq, tailPot_cons, tailPot_cons, hpot0]
                                      have := tailFramePot_le_one fi tailBlk cal2
                                      simp only [Bool.toNat_true]; omega
                          | fail _ => rw [ht] at hstep1; cases hstep1
                          | trap => rw [ht] at hstep1; cases hstep1
  final := by
    intro s₁ s₂ r ⟨hmem, hctx, hstack⟩ hfin hne
    have hfiLt : fi < p.funcs.size := (Array.getElem?_eq_some_iff.1 hpfi).1
    have htailLt : tailBlk < caller.blocks.size := (Array.getElem?_eq_some_iff.1 htail).1
    let caller' := buildTailInlinedFunc caller callee tailBlk blk as off
    have hqfi : q.funcs[fi]? = some caller' := by rw [hq]; simp [Array.set!_eq_setIfInBounds, hfiLt, caller']
    have hst1 : semStep p s₁ = (step p s₁).toSem := rfl
    cases hs1 : s₁.stack with
    | nil =>
        have : step p s₁ = .stuck := by unfold step; rw [hs1]
        rw [this] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
    | cons fr₁ rest₁ =>
        cases hs2 : s₂.stack with
        | nil => rw [hs1, hs2] at hstack; cases hstack
        | cons fr₂ rest₂ =>
            rw [hs1, hs2] at hstack
            cases hstack with
            | cons hfr hrest =>
                have hs1Eq : s₁ = { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ } := by
                  cases s₁; cases hs1; rfl
                have hs2Eq : s₂ = { mem := s₁.mem, ctx := s₁.ctx, stack := fr₂ :: rest₂ } := by
                  cases s₂; cases hs2; cases hmem; cases hctx; rfl
                rw [hs1Eq] at hst1 hfin
                have hnotEdge : ∀ {F : Func} {ρ : Env} {e : Edge},
                    Sem.Final (takeEdge F { mem := s₁.mem, ctx := s₁.ctx, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ e).toSem r → False := by
                  intro F ρ e hf
                  unfold takeEdge at hf
                  cases hev : evalArgs ρ e.args with
                  | none => rw [hev] at hf; cases hf; exact absurd rfl hne
                  | some vs =>
                      cases htb : F.blocks[e.target]? with
                      | none => rw [hev, htb] at hf; cases hf; exact absurd rfl hne
                      | some tB =>
                          rw [hev, htb] at hf; dsimp only at hf
                          cases hbp : bindParams ρ tB.params vs with
                          | none => rw [hbp] at hf; cases hf; exact absurd rfl hne
                          | some _ => rw [hbp] at hf; cases hf
                cases hfr with
                | other hneF =>
                    have hfnEq : q.funcs[fr₁.fn]? = p.funcs[fr₁.fn]? := by
                      rw [hq]; simp [Array.set!_eq_setIfInBounds, Ne.symm hneF]
                    unfold step at hst1; dsimp only at hst1
                    cases hF : p.funcs[fr₁.fn]? with
                    | none => rw [hF] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                    | some F =>
                        have hG : q.funcs[fr₁.fn]? = some F := hfnEq.trans hF
                        rw [hF] at hst1; dsimp only at hst1
                        cases hB : F.blocks[fr₁.label]? with
                        | none => rw [hB] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                        | some B =>
                            rw [hB] at hst1; dsimp only at hst1
                            by_cases hlt : fr₁.pos < B.body.size
                            · simp only [hlt, ↓reduceDIte] at hst1
                              cases hst : B.body[fr₁.pos] with
                              | assign _ _ | limb _ _ _ | store _ _ _ =>
                                  rw [hst] at hst1; dsimp only at hst1; rw [← hst] at hst1
                                  cases hex : (B.body[fr₁.pos]).exec fr₁.env s₁.mem s₁.ctx with
                                  | some _ => rw [hex] at hst1; rw [hst1] at hfin; cases hfin
                                  | none => rw [hex] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                              | call _ g cas =>
                                  rw [hst] at hst1; dsimp only at hst1
                                  cases hb : (evalArgs fr₁.env cas >>= enter p g) with
                                  | some _ => rw [hb] at hst1; rw [hst1] at hfin; cases hfin
                                  | none => rw [hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                            · simp only [hlt, ↓reduceDIte] at hst1
                              have hst2_eq := step_at_term (p := q) (F := F) (B := B)
                                (mem := s₁.mem) (ctx := s₁.ctx) (fr := fr₁) (rest := rest₂) hG hB hlt
                              cases ht : B.term with
                              | ret ras =>
                                  rw [ht] at hst1 hst2_eq; dsimp only at hst1 hst2_eq
                                  cases hev : evalArgs fr₁.env ras with
                                  | none => rw [hev] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                  | some vs =>
                                      rw [hev] at hst1 hst2_eq; dsimp only at hst1 hst2_eq
                                      cases rest₁ with
                                      | cons c₁ r₁' =>
                                          dsimp only at hst1
                                          cases hbp : bindParams c₁.env c₁.dsts vs with
                                          | some _ => rw [hbp] at hst1; rw [hst1] at hfin; cases hfin
                                          | none => rw [hbp] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                      | nil =>
                                          cases hrest
                                          rw [hst1] at hfin; cases hfin
                                          exact .inl ⟨0, s₂, .ok (vs, s₁.mem), .refl _,
                                            by change Sem.Final (step q s₂).toSem _; rw [hs2Eq, hst2_eq]; exact .done, .ok rfl⟩
                              | fail res =>
                                  rw [ht] at hst1 hst2_eq; rw [hst1] at hfin; cases hfin
                                  exact .inl ⟨0, s₂, .resource res, .refl _,
                                    by change Sem.Final (step q s₂).toSem _; rw [hs2Eq, hst2_eq]; exact .fail, .resource res⟩
                              | trap =>
                                  rw [ht] at hst1 hst2_eq; rw [hst1] at hfin; cases hfin
                                  exact .inl ⟨0, s₂, .trap, .refl _,
                                    by change Sem.Final (step q s₂).toSem _; rw [hs2Eq, hst2_eq]; exact .trap, .trap⟩
                              | jump _ => rw [ht] at hst1; dsimp only at hst1; rw [hst1] at hfin; exact absurd hfin hnotEdge
                              | br _ _ a b' _ _ =>
                                  rw [ht] at hst1; dsimp only at hst1
                                  cases ha : a.eval fr₁.env with
                                  | none => rw [ha] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                  | some _ =>
                                      cases hb : b'.eval fr₁.env with
                                      | none => rw [ha, hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                      | some _ => rw [ha, hb] at hst1; dsimp only at hst1; rw [hst1] at hfin; exact absurd hfin hnotEdge
                              | brOvf _ _ a b' _ _ =>
                                  rw [ht] at hst1; dsimp only at hst1
                                  cases ha : a.eval fr₁.env with
                                  | none => rw [ha] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                  | some _ =>
                                      cases hb : b'.eval fr₁.env with
                                      | none => rw [ha, hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                      | some _ => rw [ha, hb] at hst1; dsimp only at hst1; rw [hst1] at hfin; exact absurd hfin hnotEdge
                              | tail g tas =>
                                  rw [ht] at hst1; dsimp only at hst1
                                  cases hb : (evalArgs fr₁.env tas >>= enter p g) with
                                  | some _ => rw [hb] at hst1; rw [hst1] at hfin; cases hfin
                                  | none => rw [hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                | caller hfn1 hfn2 hlbl hpos hagr _ =>
                    unfold step at hst1; dsimp only at hst1
                    rw [hfn1, hpfi] at hst1; dsimp only at hst1
                    cases hB : caller.blocks[fr₁.label]? with
                    | none => rw [hB] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                    | some B =>
                        have hBregs := blockRegsLt_of_func hregs hB
                        rw [hB] at hst1; dsimp only at hst1
                        by_cases hlt : fr₁.pos < B.body.size
                        · simp only [hlt, ↓reduceDIte] at hst1
                          cases hst : B.body[fr₁.pos] with
                          | assign _ _ | limb _ _ _ | store _ _ _ =>
                              rw [hst] at hst1; dsimp only at hst1; rw [← hst] at hst1
                              cases hex : (B.body[fr₁.pos]).exec fr₁.env s₁.mem s₁.ctx with
                              | some _ => rw [hex] at hst1; rw [hst1] at hfin; cases hfin
                              | none => rw [hex] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                          | call _ g cas =>
                              rw [hst] at hst1; dsimp only at hst1
                              cases hb : (evalArgs fr₁.env cas >>= enter p g) with
                              | some _ => rw [hb] at hst1; rw [hst1] at hfin; cases hfin
                              | none => rw [hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                        · simp only [hlt, ↓reduceDIte] at hst1
                          by_cases hAtTail : fr₁.label = tailBlk
                          · have hBeq : B = blk := by rw [hAtTail, htail] at hB; cases hB; rfl
                            rw [hBeq, hterm] at hst1; dsimp only at hst1
                            cases hb : (evalArgs fr₁.env as >>= enter p gi) with
                            | some _ => rw [hb] at hst1; rw [hst1] at hfin; cases hfin
                            | none => rw [hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                          · have hB2 : caller'.blocks[fr₂.label]? =
                                some { B with term := remapCallerTerm tailBlk callee.blocks.size B.term } := by
                              rcases Nat.lt_trichotomy fr₁.label tailBlk with hltL | heqL | hgtL
                              · rw [hlbl, remapCallerLabel]; simp only [Nat.le_of_lt hltL, ↓reduceIte]
                                exact buildTailInlined_blocks_lt hltL hB
                              · exact absurd heqL hAtTail
                              · rw [hlbl, remapCallerLabel]; simp only [Nat.not_le.2 hgtL, ↓reduceIte]
                                exact buildTailInlined_blocks_gt htailLt hgtL hB
                            have hlt2 : ¬(fr₂.pos < B.body.size) := by rw [hpos]; exact hlt
                            have hst2_eq := step_at_term (p := q) (F := caller')
                              (B := { B with term := remapCallerTerm tailBlk callee.blocks.size B.term })
                              (mem := s₁.mem) (ctx := s₁.ctx) (fr := fr₂) (rest := rest₂)
                              (by rw [hfn2]; exact hqfi) hB2 hlt2
                            cases ht : B.term with
                            | ret ras =>
                                rw [ht] at hst1 hst2_eq; dsimp only [remapCallerTerm] at hst2_eq; dsimp only at hst1 hst2_eq
                                have hrasLt : ∀ a ∈ ras, listLt off a.uses = true := by
                                  have hu := (term_uses_lt_of_block hBregs).1; rw [ht] at hu; exact listLt_flatMap_uses hu
                                cases hev1 : evalArgs fr₁.env ras with
                                | none => rw [hev1] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                | some vs =>
                                    rw [hev1] at hst1; rw [(evalArgs_agreeBelow hagr hrasLt).trans hev1] at hst2_eq
                                    dsimp only at hst1 hst2_eq
                                    cases rest₁ with
                                    | cons c₁ r₁' =>
                                        dsimp only at hst1
                                        cases hbp : bindParams c₁.env c₁.dsts vs with
                                        | some _ => rw [hbp] at hst1; rw [hst1] at hfin; cases hfin
                                        | none => rw [hbp] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                    | nil =>
                                        cases hrest
                                        rw [hst1] at hfin; cases hfin
                                        exact .inl ⟨0, s₂, .ok (vs, s₁.mem), .refl _,
                                          by change Sem.Final (step q s₂).toSem _; rw [hs2Eq, hst2_eq]; exact .done, .ok rfl⟩
                            | fail res =>
                                rw [ht] at hst1 hst2_eq; dsimp only [remapCallerTerm] at hst2_eq; rw [hst1] at hfin; cases hfin
                                exact .inl ⟨0, s₂, .resource res, .refl _,
                                  by change Sem.Final (step q s₂).toSem _; rw [hs2Eq, hst2_eq]; exact .fail, .resource res⟩
                            | trap =>
                                rw [ht] at hst1 hst2_eq; dsimp only [remapCallerTerm] at hst2_eq; rw [hst1] at hfin; cases hfin
                                exact .inl ⟨0, s₂, .trap, .refl _,
                                  by change Sem.Final (step q s₂).toSem _; rw [hs2Eq, hst2_eq]; exact .trap, .trap⟩
                            | jump _ => rw [ht] at hst1; dsimp only at hst1; rw [hst1] at hfin; exact absurd hfin hnotEdge
                            | br _ _ a b' _ _ =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases ha : a.eval fr₁.env with
                                | none => rw [ha] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                | some _ =>
                                    cases hb : b'.eval fr₁.env with
                                    | none => rw [ha, hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                    | some _ => rw [ha, hb] at hst1; dsimp only at hst1; rw [hst1] at hfin; exact absurd hfin hnotEdge
                            | brOvf _ _ a b' _ _ =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases ha : a.eval fr₁.env with
                                | none => rw [ha] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                | some _ =>
                                    cases hb : b'.eval fr₁.env with
                                    | none => rw [ha, hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                    | some _ => rw [ha, hb] at hst1; dsimp only at hst1; rw [hst1] at hfin; exact absurd hfin hnotEdge
                            | tail g tas =>
                                rw [ht] at hst1; dsimp only at hst1
                                cases hb : (evalArgs fr₁.env tas >>= enter p g) with
                                | some _ => rw [hb] at hst1; rw [hst1] at hfin; cases hfin
                                | none => rw [hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                | inlined hfn1 _ hfn2 hlbl hpos hsh _ =>
                    unfold step at hst1; dsimp only at hst1
                    rw [hfn1, hpgi] at hst1; dsimp only at hst1
                    cases hB : callee.blocks[fr₁.label]? with
                    | none => rw [hB] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                    | some B =>
                        rw [hB] at hst1; dsimp only at hst1
                        have hB2 : caller'.blocks[fr₂.label]? =
                            some (inlineTailCalleeBlock callee tailBlk blk off fr₁.label B) := by
                          rw [hlbl]
                          exact buildTailInlined_blocks_inlined (caller := caller) (callee := callee)
                            (tailBlk := tailBlk) (blk := blk) (as := as) (off := off) htailLt hB
                        by_cases hlt : fr₁.pos < B.body.size
                        · simp only [hlt, ↓reduceDIte] at hst1
                          cases hst : B.body[fr₁.pos] with
                          | assign _ _ | limb _ _ _ | store _ _ _ =>
                              rw [hst] at hst1; dsimp only at hst1; rw [← hst] at hst1
                              cases hex : (B.body[fr₁.pos]).exec fr₁.env s₁.mem s₁.ctx with
                              | some _ => rw [hex] at hst1; rw [hst1] at hfin; cases hfin
                              | none => rw [hex] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                          | call _ g cas =>
                              rw [hst] at hst1; dsimp only at hst1
                              cases hb : (evalArgs fr₁.env cas >>= enter p g) with
                              | some _ => rw [hb] at hst1; rw [hst1] at hfin; cases hfin
                              | none => rw [hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                        · simp only [hlt, ↓reduceDIte] at hst1
                          have hlt2 : ¬(fr₂.pos < (inlineTailCalleeBlock callee tailBlk blk off fr₁.label B).body.size) := by
                            simp [inlineTailCalleeBlock, hpos, hlt]
                          have hst2_eq := step_at_term (p := q) (F := caller')
                            (B := inlineTailCalleeBlock callee tailBlk blk off fr₁.label B)
                            (mem := s₁.mem) (ctx := s₁.ctx) (fr := fr₂) (rest := rest₂)
                            (by rw [hfn2]; exact hqfi) hB2 hlt2
                          dsimp only [inlineTailCalleeBlock] at hst2_eq
                          cases ht : B.term with
                          | ret ras =>
                              rw [ht] at hst1 hst2_eq; dsimp only [rewriteTailCalleeTerm] at hst2_eq
                              dsimp only at hst1 hst2_eq
                              cases hev1 : evalArgs fr₁.env ras with
                              | none => rw [hev1] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                              | some vs =>
                                  rw [hev1] at hst1; rw [shiftArgs_eval hsh hev1] at hst2_eq
                                  dsimp only at hst1 hst2_eq
                                  cases rest₁ with
                                  | cons c₁ r₁' =>
                                      dsimp only at hst1
                                      cases hbp : bindParams c₁.env c₁.dsts vs with
                                      | some _ => rw [hbp] at hst1; rw [hst1] at hfin; cases hfin
                                      | none => rw [hbp] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                  | nil =>
                                      cases hrest
                                      rw [hst1] at hfin; cases hfin
                                      exact .inl ⟨0, s₂, .ok (vs, s₁.mem), .refl _,
                                        by change Sem.Final (step q s₂).toSem _; rw [hs2Eq, hst2_eq]; exact .done, .ok rfl⟩
                          | fail res =>
                              rw [ht] at hst1 hst2_eq; dsimp only [rewriteTailCalleeTerm] at hst2_eq
                              rw [hst1] at hfin; cases hfin
                              exact .inl ⟨0, s₂, .resource res, .refl _,
                                by change Sem.Final (step q s₂).toSem _; rw [hs2Eq, hst2_eq]; exact .fail, .resource res⟩
                          | trap =>
                              rw [ht] at hst1 hst2_eq; dsimp only [rewriteTailCalleeTerm] at hst2_eq
                              rw [hst1] at hfin; cases hfin
                              exact .inl ⟨0, s₂, .trap, .refl _,
                                by change Sem.Final (step q s₂).toSem _; rw [hs2Eq, hst2_eq]; exact .trap, .trap⟩
                          | jump _ => rw [ht] at hst1; dsimp only at hst1; rw [hst1] at hfin; exact absurd hfin hnotEdge
                          | br _ _ a b' _ _ =>
                              rw [ht] at hst1; dsimp only at hst1
                              cases ha : a.eval fr₁.env with
                              | none => rw [ha] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                              | some _ =>
                                  cases hb : b'.eval fr₁.env with
                                  | none => rw [ha, hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                  | some _ => rw [ha, hb] at hst1; dsimp only at hst1; rw [hst1] at hfin; exact absurd hfin hnotEdge
                          | brOvf _ _ a b' _ _ =>
                              rw [ht] at hst1; dsimp only at hst1
                              cases ha : a.eval fr₁.env with
                              | none => rw [ha] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                              | some _ =>
                                  cases hb : b'.eval fr₁.env with
                                  | none => rw [ha, hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne
                                  | some _ => rw [ha, hb] at hst1; dsimp only at hst1; rw [hst1] at hfin; exact absurd hfin hnotEdge
                          | tail g tas =>
                              rw [ht] at hst1; dsimp only at hst1
                              cases hb : (evalArgs fr₁.env tas >>= enter p g) with
                              | some _ => rw [hb] at hst1; rw [hst1] at hfin; cases hfin
                              | none => rw [hb] at hst1; rw [hst1] at hfin; cases hfin; exact absurd rfl hne

theorem inlineTailSite_sim {p q : Program} {fi : FunId} {tailBlk : Label}
    (h : inlineTailSite p fi tailBlk = some q)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq (fun k => 2 * k + 1)
      (fun k => eval p k args mem ctx) (fun k => eval q k args mem ctx) := by
  unfold inlineTailSite at h
  cases hpfi : p.funcs[fi]? with
  | none => rw [hpfi] at h; cases h
  | some caller =>
      rw [hpfi] at h; dsimp only at h
      cases htail : caller.blocks[tailBlk]? with
      | none => rw [htail] at h; cases h
      | some blk =>
          rw [htail] at h; dsimp only at h
          cases hterm : blk.term with
          | jump _ | br _ _ _ _ _ _ | brOvf _ _ _ _ _ _ | ret _ | fail _ | trap =>
              rw [hterm] at h; cases h
          | tail gi as =>
              rw [hterm] at h; dsimp only at h
              cases hpgi : p.funcs[gi]? with
              | none => rw [hpgi] at h; cases h
              | some callee =>
                  rw [hpgi] at h; dsimp only at h
                  split at h
                  · rename_i hcond
                    cases h
                    simp only [Bool.and_eq_true] at hcond
                    obtain ⟨hregs, hok⟩ := hcond
                    have hfwd := inlineTailSite_forward hpfi htail hterm hpgi hregs hok rfl
                    cases hinit1 : Lir.State.initial p args mem ctx with
                    | none =>
                        refine ⟨fun k _ => ⟨0, by simp [eval, hinit1]; exact .stuck⟩,
                          fun k hk => by simp [eval, hinit1] at hk⟩
                    | some s₁ =>
                        simp only [Lir.State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff,
                          Option.some.injEq] at hinit1
                        obtain ⟨fr₁, hent₁, rfl⟩ := hinit1
                        obtain ⟨fr₂, hent₂, hfrRel⟩ :=
                          tail_enter_rel (gi := gi) (M := callee.blocks.size)
                            (caller' := buildTailInlinedFunc caller callee tailBlk blk as (nextFreshVReg caller))
                            (tailBlk := tailBlk) (off := nextFreshVReg caller) hpfi rfl rfl hent₁
                        have hinit2 : Lir.State.initial
                            { funcs := p.funcs.set! fi (buildTailInlinedFunc caller callee tailBlk blk as (nextFreshVReg caller)), main := p.main }
                            args mem ctx = some { mem, ctx, stack := [fr₂] } := by
                          unfold Lir.State.initial; rw [hent₂]; rfl
                        have hrel0 : TailStateRel fi gi tailBlk callee.blocks.size (nextFreshVReg caller)
                            { mem, ctx, stack := [fr₁] } { mem, ctx, stack := [fr₂] } :=
                          ⟨rfl, rfl, .cons hfrRel .nil⟩
                        have hpot0 : tailPot fi tailBlk { mem, ctx, stack := [fr₂] } ≤ 1 := by
                          simp only [tailPot, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
                          exact tailFramePot_le_one fi tailBlk fr₂
                        exact hfwd.sim hrel0 hpot0
                          (runs_eval (by unfold Lir.State.initial; rw [hent₁]; rfl))
                          (runs_eval hinit2)
                  · cases h

theorem inlineTailSiteChecked_wellFormed {p : Program} {fi : FunId} {tailBlk : Label}
    (hwf : p.wellFormed = true) :
    (inlineTailSiteChecked p fi tailBlk).1.wellFormed = true := by
  unfold inlineTailSiteChecked
  cases inlineTailSite p fi tailBlk with
  | none => exact hwf
  | some q =>
      dsimp only
      split
      · rename_i h; simp [hwf] at h; exact h
      · exact hwf

theorem inlineTailSiteChecked_sim (p : Program) (fi : FunId) (tailBlk : Label)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq (fun k => 2 * k + 1)
      (fun k => eval p k args mem ctx)
      (fun k => eval (inlineTailSiteChecked p fi tailBlk).1 k args mem ctx) := by
  have hself : Sem.Sim Eq (fun k => 2 * k + 1)
      (fun k => eval p k args mem ctx) (fun k => eval p k args mem ctx) := by
    refine ⟨fun k _ => ⟨k, Sem.Result.Refines.refl (fun _ => rfl)⟩, fun k hk => ?_⟩
    by_cases h1 : eval p k args mem ctx = .timeout
    · exact .inl h1
    · exfalso
      have hm := eval_mono p args mem ctx (by omega : k ≤ 2 * k + 1) h1
      dsimp only at hm
      rw [hk] at hm
      exact h1 hm.symm
  unfold inlineTailSiteChecked
  cases h : inlineTailSite p fi tailBlk with
  | none => exact hself
  | some q =>
      dsimp only
      split
      · exact inlineTailSite_sim h args mem ctx
      · exact hself

end TailInline

end IxCC.Lir.Opt

