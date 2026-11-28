import IxCC.Lir.Opt.Check
import IxCC.Lir.Proof.Opt.Arith
import IxCC.Lir.Proof.Opt.Mem
import IxCC.Lir.Proof.Steps
import IxCC.Src.Proof.NatMap

/-!
# Segment and invariant soundness for `Lir.Opt.check`

Proves the straight-line verification lemmas used by `IxCC.Lir.Proof.Opt.Sim`:
- `SymExpr.eval_isMemFree`, `SymExpr.eval_isTotal`, `SymExpr.eval_subst`,
  `SymExpr.norm_snapsLt`.
- `BlockInv.Holds` and `SegInv` (relating source and target register maps,
  symbolic write logs, snapshot tables, and collected safety facts).
- `stepSrcList_sound`, `stepTgtList_sound`, `stepTotalTgtList_sound`, `checkSeg_sound`
  (showing `execList` of `seg2` succeeds with **exact** `mem₁` whenever `seg1` succeeds).
- `checkArgEquiv_sound`, `checkArgsEquiv_sound`, `checkEntails_sound`,
  `checkAfterCall_sound`.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Label FunId Width Ext Base Addr Arg Cond BinOp Ovf LimbOp
  Rhs Stmt Edge Term Block Func Word Env evalArgs bindParams execList loadWord
  dispWord sext sarWord shiftMask env_insert_self env_insert_ne env_insert_get env_empty)

/-! ## Basic `SymExpr` structural properties -/

theorem SymExpr.eval_isMemFree {ρ : Env} {ctx : Word} {snaps1 snaps2 : MemSnaps} :
    ∀ {e : SymExpr}, e.isMemFree = true → e.eval ρ ctx snaps1 = e.eval ρ ctx snaps2
  | .reg _, _ | .imm _, _ | .ctx, _ => rfl
  | .bin _ _ a b, h | .test _ _ a b, h | .mulHi a b, h => by
      simp only [SymExpr.isMemFree, Bool.and_eq_true] at h
      simp only [SymExpr.eval, eval_isMemFree (snaps1 := snaps1) (snaps2 := snaps2) h.1,
        eval_isMemFree (snaps1 := snaps1) (snaps2 := snaps2) h.2]
  | .select _ _ a b t f, h => by
      simp only [SymExpr.isMemFree, Bool.and_eq_true] at h
      simp only [SymExpr.eval, eval_isMemFree (snaps1 := snaps1) (snaps2 := snaps2) h.1.1.1,
        eval_isMemFree (snaps1 := snaps1) (snaps2 := snaps2) h.1.1.2,
        eval_isMemFree (snaps1 := snaps1) (snaps2 := snaps2) h.1.2,
        eval_isMemFree (snaps1 := snaps1) (snaps2 := snaps2) h.2]
  | .bsr64 a, h => by simp only [SymExpr.eval, eval_isMemFree (e := a) (snaps1 := snaps1) (snaps2 := snaps2) h]
  | .divQ a b c, h | .divR a b c, h | .addCLo a b c, h | .addCHi a b c, h
  | .subBLo a b c, h | .subBHi a b c, h => by
      simp only [SymExpr.isMemFree, Bool.and_eq_true] at h
      simp only [SymExpr.eval, eval_isMemFree (snaps1 := snaps1) (snaps2 := snaps2) h.1.1,
        eval_isMemFree (snaps1 := snaps1) (snaps2 := snaps2) h.1.2,
        eval_isMemFree (snaps1 := snaps1) (snaps2 := snaps2) h.2]
  | .load .., h => by simp [SymExpr.isMemFree] at h

theorem PFact.holds_snaps_congr {ρ : Env} {ctx : Word} {snaps1 snaps2 : MemSnaps} {f : PFact}
    (hm : f.isMemFree = true) (h : f.Holds ρ ctx snaps1) : f.Holds ρ ctx snaps2 := by
  simp only [PFact.isMemFree, Bool.and_eq_true] at hm
  obtain ⟨v1, v2, h1, h2, hc⟩ := h
  rw [SymExpr.eval_isMemFree (snaps2 := snaps2) hm.1] at h1
  rw [SymExpr.eval_isMemFree (snaps2 := snaps2) hm.2] at h2
  exact ⟨v1, v2, h1, h2, hc⟩

theorem SymExpr.eval_isTotal {ρ : Env} {ctx : Word} {snaps : MemSnaps} :
    ∀ {e : SymExpr}, e.isTotal = true → (∀ x ∈ e.vars, ρ[x]?.isSome = true) →
      ∃ v, e.eval ρ ctx snaps = some v
  | .reg x, _, hdef => by
      have hx : ρ[x]?.isSome = true := hdef x (by simp [SymExpr.vars])
      cases hg : ρ[x]? with
      | none => simp [hg] at hx
      | some v => exact ⟨v, hg⟩
  | .imm w, _, _ => ⟨w, rfl⟩
  | .ctx, _, _ => ⟨ctx, rfl⟩
  | .bin o w a b, ht, hdef => by
      simp only [SymExpr.isTotal, Bool.and_eq_true] at ht
      obtain ⟨⟨hta, htb⟩, hop⟩ := ht
      obtain ⟨va, ha⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) hta (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vb, hb⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) htb (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      rw [Bool.or_eq_true] at hop
      rcases hop with htot | hnz
      · cases o <;> simp [binOpIsTotal] at htot <;>
          exact ⟨_, by simp only [SymExpr.eval, Option.bind_eq_bind, ha, hb, Option.bind_some, BinOp.eval]; rfl⟩
      · cases b with
        | imm k =>
            have hne : (w.truncate k == 0) = false := by simpa [bne] using hnz
            simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
            cases o <;>
              exact ⟨_, by simp only [SymExpr.eval, Option.bind_eq_bind, ha, Option.bind_some, BinOp.eval, hne,
                Bool.false_eq_true, ↓reduceIte]; rfl⟩
        | _ => cases hnz
  | .select c w a b t f, ht, hdef => by
      simp only [SymExpr.isTotal, Bool.and_eq_true] at ht
      obtain ⟨⟨⟨hta, htb⟩, htt⟩, htf⟩ := ht
      obtain ⟨va, ha⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) hta (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vb, hb⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) htb (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vt, ht'⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) htt (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vf, hf'⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) htf (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      exact ⟨if c.holds w va vb then vt else vf,
        by simp only [SymExpr.eval, Option.bind_eq_bind, ha, hb, ht', hf', Option.bind_some]⟩
  | .test c w a b, ht, hdef => by
      simp only [SymExpr.isTotal, Bool.and_eq_true] at ht
      obtain ⟨va, ha⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.1 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vb, hb⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.2 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      exact ⟨if c.holds w va vb then 1 else 0,
        by simp only [SymExpr.eval, Option.bind_eq_bind, ha, hb, Option.bind_some]⟩
  | .bsr64 a, ht, _ => by
      cases a with
      | imm k =>
          have hne : (k == 0) = false := by simpa [SymExpr.isTotal, bne] using ht
          exact ⟨UInt64.ofNat k.toNat.log2,
            by simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_some, hne, Bool.false_eq_true, ↓reduceIte]⟩
      | _ => simp [SymExpr.isTotal] at ht
  | .mulHi a b, ht, hdef => by
      simp only [SymExpr.isTotal, Bool.and_eq_true] at ht
      obtain ⟨va, ha⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.1 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vb, hb⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.2 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      exact ⟨UInt64.ofNat ((va.toNat * vb.toNat) / 2 ^ 64),
        by simp only [SymExpr.eval, Option.bind_eq_bind, ha, hb, Option.bind_some]⟩
  | .addCLo a b c, ht, hdef => by
      simp only [SymExpr.isTotal, Bool.and_eq_true] at ht
      obtain ⟨va, ha⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.1.1 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vb, hb⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.1.2 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vc, hc⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.2 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      exact ⟨_, by simp only [SymExpr.eval, Option.bind_eq_bind, ha, hb, hc, Option.bind_some]; rfl⟩
  | .addCHi a b c, ht, hdef => by
      simp only [SymExpr.isTotal, Bool.and_eq_true] at ht
      obtain ⟨va, ha⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.1.1 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vb, hb⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.1.2 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vc, hc⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.2 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      exact ⟨_, by simp only [SymExpr.eval, Option.bind_eq_bind, ha, hb, hc, Option.bind_some]; rfl⟩
  | .subBLo a b c, ht, hdef => by
      simp only [SymExpr.isTotal, Bool.and_eq_true] at ht
      obtain ⟨va, ha⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.1.1 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vb, hb⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.1.2 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vc, hc⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.2 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      exact ⟨_, by simp only [SymExpr.eval, Option.bind_eq_bind, ha, hb, hc, Option.bind_some]; rfl⟩
  | .subBHi a b c, ht, hdef => by
      simp only [SymExpr.isTotal, Bool.and_eq_true] at ht
      obtain ⟨va, ha⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.1.1 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vb, hb⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.1.2 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      obtain ⟨vc, hc⟩ := eval_isTotal (ctx := ctx) (snaps := snaps) ht.2 (fun x hx => hdef x (by simp [SymExpr.vars, hx]))
      exact ⟨_, by simp only [SymExpr.eval, Option.bind_eq_bind, ha, hb, hc, Option.bind_some]; rfl⟩
  | .divQ .., ht, _ | .divR .., ht, _ | .load .., ht, _ => by simp [SymExpr.isTotal] at ht

theorem SymExpr.eval_subst {ρ₁ ρ₀ : Env} {ctx : Word} {snaps : MemSnaps} {f : VReg → SymExpr}
    (hsub : ∀ x v, ρ₁[x]? = some v → (f x).eval ρ₀ ctx snaps = some v) :
    ∀ {e : SymExpr} {v : Word}, e.eval ρ₁ ctx snaps = some v →
      (e.subst f).eval ρ₀ ctx snaps = some v
  | .reg x, v, h => hsub x v h
  | .imm _, _, h => h
  | .ctx, _, h => h
  | .bin o w a b, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, ho⟩ := h
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind,
        eval_subst hsub ha, eval_subst hsub hb, Option.bind_some, ho]
  | .select c w a b t e, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, vt, ht, ve, he, hres⟩ := h
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind,
        eval_subst hsub ha, eval_subst hsub hb, eval_subst hsub ht, eval_subst hsub he,
        Option.bind_some, hres]
  | .test c w a b, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, hres⟩ := h
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind,
        eval_subst hsub ha, eval_subst hsub hb, Option.bind_some, hres]
  | .bsr64 a, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, hres⟩ := h
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind,
        eval_subst hsub ha, Option.bind_some, hres]
  | .mulHi a b, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, hres⟩ := h
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind,
        eval_subst hsub ha, eval_subst hsub hb, Option.bind_some, hres]
  | .divQ a b c, v, h | .divR a b c, v, h | .addCLo a b c, v, h | .addCHi a b c, v, h
  | .subBLo a b c, v, h | .subBHi a b c, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, vc, hc, hres⟩ := h
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind,
        eval_subst hsub ha, eval_subst hsub hb, eval_subst hsub hc, Option.bind_some, hres]
  | .load s w e a, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, hld⟩ := h
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind,
        eval_subst hsub ha, Option.bind_some, hld]

theorem SymExpr.eval_subst_vars {ρ₁ ρ₀ : Env} {ctx : Word} {snaps : MemSnaps} {f : VReg → SymExpr} :
    ∀ {e : SymExpr} {v : Word},
      (∀ x ∈ e.vars, ∀ vx, ρ₁[x]? = some vx → (f x).eval ρ₀ ctx snaps = some vx) →
      e.eval ρ₁ ctx snaps = some v → (e.subst f).eval ρ₀ ctx snaps = some v
  | .reg x, v, hsub, h => hsub x (by simp [SymExpr.vars]) v h
  | .imm _, _, _, h => h
  | .ctx, _, _, h => h
  | .bin o w a b, v, hsub, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, ho⟩ := h
      have ha' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) ha
      have hb' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) hb
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind, ha', hb', Option.bind_some, ho]
  | .select c w a b t e, v, hsub, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, vt, ht, ve, he, hres⟩ := h
      have ha' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) ha
      have hb' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) hb
      have ht' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) ht
      have he' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) he
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind, ha', hb', ht', he', Option.bind_some, hres]
  | .test c w a b, v, hsub, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, hres⟩ := h
      have ha' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) ha
      have hb' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) hb
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind, ha', hb', Option.bind_some, hres]
  | .bsr64 a, v, hsub, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, hres⟩ := h
      have ha' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) ha
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind, ha', Option.bind_some, hres]
  | .mulHi a b, v, hsub, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, hres⟩ := h
      have ha' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) ha
      have hb' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) hb
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind, ha', hb', Option.bind_some, hres]
  | .divQ a b c, v, hsub, h | .divR a b c, v, hsub, h | .addCLo a b c, v, hsub, h
  | .addCHi a b c, v, hsub, h | .subBLo a b c, v, hsub, h | .subBHi a b c, v, hsub, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, vc, hc, hres⟩ := h
      have ha' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) ha
      have hb' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) hb
      have hc' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) hc
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind, ha', hb', hc', Option.bind_some, hres]
  | .load s w e a, v, hsub, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, hld⟩ := h
      have ha' := eval_subst_vars (fun x hx => hsub x (by simp [SymExpr.vars, hx])) ha
      simp only [SymExpr.subst, SymExpr.eval, Option.bind_eq_bind, ha', Option.bind_some, hld]

/-! ## `snapsLt` preservation across `mkBin` and `SymExpr.norm` -/

theorem matchAddShlSelf_snapsLt {bound : Nat} {a b r : SymExpr}
    (hm : matchAddShlSelf a b = some r)
    (ha : a.snapsLt bound) (hb : b.snapsLt bound) : r.snapsLt bound := by
  unfold matchAddShlSelf at hm
  split at hm
  · split at hm <;> (try cases hm); exact ⟨ha, trivial⟩
  · split at hm <;> (try cases hm); exact ⟨hb, trivial⟩
  · split at hm <;> (try cases hm); exact ⟨ha, trivial⟩
  · split at hm <;> (try cases hm); exact ⟨hb, trivial⟩
  · split at hm <;> (try cases hm); exact ⟨ha, trivial⟩
  · split at hm <;> (try cases hm); exact ⟨hb, trivial⟩
  · cases hm

theorem mkAdd64Core_snapsLt {bound : Nat} {a b : SymExpr}
    (ha : a.snapsLt bound) (hb : b.snapsLt bound) : (mkAdd64Core a b).snapsLt bound := by
  unfold mkAdd64Core
  split
  · exact ⟨ha, trivial⟩
  · cases hm : matchAddShlSelf a b with
    | some r => dsimp only; exact matchAddShlSelf_snapsLt hm ha hb
    | none => dsimp only; split <;> first | exact ⟨hb, ha⟩ | exact ⟨ha, hb⟩

theorem mkAdd64_snapsLt {bound : Nat} {a b : SymExpr}
    (ha : a.snapsLt bound) (hb : b.snapsLt bound) : (mkAdd64 a b).snapsLt bound := by
  unfold mkAdd64
  split
  · trivial
  · exact ha
  · exact hb
  · dsimp only; split
    · exact ha.1
    · exact ⟨ha.1, trivial⟩
  · dsimp only; split
    · exact hb.1
    · exact ⟨hb.1, trivial⟩
  · dsimp only; split
    · exact mkAdd64Core_snapsLt ha.1 hb.1
    · exact ⟨mkAdd64Core_snapsLt ha.1 hb.1, trivial⟩
  · exact ⟨mkAdd64Core_snapsLt ha.1 hb, trivial⟩
  · exact ⟨mkAdd64Core_snapsLt ha hb.1, trivial⟩
  · exact mkAdd64Core_snapsLt ha hb

theorem matchRotateShrShl_snapsLt {bound : Nat} {w rw : Width} {s1 s2 x : SymExpr} {r : Word}
    (hm : matchRotateShrShl w s1 s2 = some (rw, x, r))
    (h1 : s1.snapsLt bound) (h2 : s2.snapsLt bound) : x.snapsLt bound := by
  unfold matchRotateShrShl at hm
  split at hm
  · split at hm
    · dsimp only at hm; split at hm
      · cases hm; exact h1.1
      · cases hm
    · split at hm
      · dsimp only at hm; split at hm
        · cases hm; exact h1.1
        · cases hm
      · cases hm
  · split at hm
    · dsimp only at hm; split at hm
      · cases hm; exact h1.1.1
      · cases hm
    · cases hm
  · cases hm

theorem matchRotateOr_snapsLt {bound : Nat} {w rw : Width} {a b x : SymExpr} {r : Word}
    (hm : matchRotateOr w a b = some (rw, x, r))
    (ha : a.snapsLt bound) (hb : b.snapsLt bound) : x.snapsLt bound := by
  unfold matchRotateOr at hm
  cases h1 : matchRotateShrShl w a b with
  | some res => rw [h1] at hm; cases hm; exact matchRotateShrShl_snapsLt h1 ha hb
  | none => rw [h1] at hm; exact matchRotateShrShl_snapsLt hm hb ha

theorem matchRotateMasked32Pair_snapsLt {bound : Nat} {s1 s2 x : SymExpr} {r : Word}
    (hm : matchRotateMasked32Pair s1 s2 = some (x, r))
    (h1 : s1.snapsLt bound) (h2 : s2.snapsLt bound) : x.snapsLt bound := by
  unfold matchRotateMasked32Pair at hm
  split at hm
  · split at hm
    · dsimp only at hm; split at hm
      · cases hm; exact h1.1.1
      · cases hm
    · cases hm
  · cases hm

theorem matchRotateMasked32_snapsLt {bound : Nat} {a x : SymExpr} {r : Word}
    (hm : matchRotateMasked32 a = some (x, r))
    (ha : a.snapsLt bound) : x.snapsLt bound := by
  unfold matchRotateMasked32 at hm
  split at hm
  · cases h1 : matchRotateMasked32Pair _ _ with
    | some res => rw [h1] at hm; cases hm; exact matchRotateMasked32Pair_snapsLt h1 ha.1 ha.2
    | none => rw [h1] at hm; exact matchRotateMasked32Pair_snapsLt hm ha.2 ha.1
  · cases hm

theorem mkBinOrdered_snapsLt {bound : Nat} {o : BinOp} {w : Width} {a b : SymExpr}
    (ha : a.snapsLt bound) (hb : b.snapsLt bound) : (mkBinOrdered o w a b).snapsLt bound := by
  unfold mkBinOrdered
  split
  · split
    · trivial
    · exact ⟨ha, hb⟩
  · cases o with
    | add =>
        dsimp only
        cases w with
        | w64 => exact mkAdd64_snapsLt ha hb
        | w8 | w16 | w32 => dsimp only; split <;> exact ⟨ha, by first | trivial | exact hb⟩
    | sub =>
        dsimp only; split
        · trivial
        · split
          · split
            · exact ha
            · exact mkAdd64_snapsLt ha trivial
          · exact ⟨ha, hb⟩
    | mul =>
        dsimp only; split
        · trivial
        · split
          · exact ha
          · exact ⟨ha, trivial⟩
        · split
          · exact ⟨ha, trivial⟩
          · exact ⟨ha, trivial⟩
        · exact ⟨ha, hb⟩
    | and =>
        dsimp only; split
        · trivial
        · split
          · exact ha
          · split
            · cases hm : matchRotateMasked32 a with
              | none => exact ⟨ha, trivial⟩
              | some xr => exact ⟨matchRotateMasked32_snapsLt hm ha, trivial⟩
            · exact ⟨ha, trivial⟩
        · split
          · exact ha
          · exact ⟨ha, hb⟩
    | or =>
        dsimp only; split
        · split
          · exact ha
          · exact ⟨ha, trivial⟩
        · split
          · trivial
          · split
            · split
              · split
                · exact mkAdd64_snapsLt ha trivial
                · exact ⟨ha, trivial⟩
              · exact ⟨ha, trivial⟩
            · exact ⟨ha, trivial⟩
        · split
          · exact ha
          · cases hm : matchRotateOr w a b with
            | none => exact ⟨ha, hb⟩
            | some res => exact ⟨matchRotateOr_snapsLt hm ha hb, trivial⟩
    | xor =>
        dsimp only; split
        · trivial
        · split
          · exact ha
          · exact ⟨ha, hb⟩
    | shl | shr | sar | rol | ror =>
        dsimp only; split
        · trivial
        · split
          · exact ha
          · exact ⟨ha, trivial⟩
        · exact ⟨ha, hb⟩
    | udiv =>
        dsimp only; split
        · split
          · split
            · exact ha
            · exact ⟨ha, trivial⟩
          · split
            · exact ⟨ha, trivial⟩
            · exact ⟨ha, trivial⟩
        · exact ⟨ha, hb⟩
    | urem =>
        dsimp only; split
        · split
          · trivial
          · split
            · exact ⟨ha, trivial⟩
            · exact ⟨ha, trivial⟩
        · exact ⟨ha, hb⟩

theorem mkBin_snapsLt {bound : Nat} {o : BinOp} {w : Width} {a b : SymExpr}
    (ha : a.snapsLt bound) (hb : b.snapsLt bound) : (mkBin o w a b).snapsLt bound := by
  unfold mkBin
  split
  · exact mkBinOrdered_snapsLt hb ha
  · exact mkBinOrdered_snapsLt ha hb

theorem SymExpr.norm_snapsLt {bound : Nat} :
    ∀ {e : SymExpr}, e.snapsLt bound → e.norm.snapsLt bound
  | .reg _, h | .imm _, h | .ctx, h => h
  | .bin _ _ a b, ⟨ha, hb⟩ => mkBin_snapsLt (norm_snapsLt ha) (norm_snapsLt hb)
  | .select c w a b t f, ⟨ha, hb, ht, hf⟩ => by
      have ha' := norm_snapsLt ha; have hb' := norm_snapsLt hb
      have ht' := norm_snapsLt ht; have hf' := norm_snapsLt hf
      simp only [SymExpr.norm]
      have hbody : ∀ (c1 : Cond) (a1 b1 : SymExpr), a1.snapsLt bound → b1.snapsLt bound →
          (if t.norm == f.norm then t.norm
           else match condStatic c1 w a1 b1 with
           | some true => t.norm | some false => f.norm
           | none => .select c1 w a1 b1 t.norm f.norm).snapsLt bound := by
        intro c1 a1 b1 h1 h2
        split
        · exact ht'
        · split
          · exact ht'
          · exact hf'
          · exact ⟨h1, h2, ht', hf'⟩
      by_cases hcmp : (b.norm.cmp a.norm == .lt) = true
      · simp only [hcmp, ↓reduceIte]; exact hbody _ _ _ hb' ha'
      · simp only [hcmp, Bool.false_eq_true, ↓reduceIte]; exact hbody _ _ _ ha' hb'
  | .test c w a b, ⟨ha, hb⟩ => by
      have ha' := norm_snapsLt ha; have hb' := norm_snapsLt hb
      simp only [SymExpr.norm]
      have hbody : ∀ (c1 : Cond) (a1 b1 : SymExpr), a1.snapsLt bound → b1.snapsLt bound →
          (match condStatic c1 w a1 b1 with
           | some true => SymExpr.imm 1 | some false => .imm 0
           | none => .test c1 w a1 b1).snapsLt bound := by
        intro c1 a1 b1 h1 h2
        split
        · trivial
        · trivial
        · exact ⟨h1, h2⟩
      by_cases hcmp : (b.norm.cmp a.norm == .lt) = true
      · simp only [hcmp, ↓reduceIte]; exact hbody _ _ _ hb' ha'
      · simp only [hcmp, Bool.false_eq_true, ↓reduceIte]; exact hbody _ _ _ ha' hb'
  | .bsr64 a, ha => by
      have ha' := norm_snapsLt (e := a) ha
      simp only [SymExpr.norm]
      split
      · split <;> trivial
      · exact ha'
  | .mulHi a b, ⟨ha, hb⟩ => by
      have ha' := norm_snapsLt ha; have hb' := norm_snapsLt hb
      simp only [SymExpr.norm]
      have hbody : ∀ (a1 b1 : SymExpr), a1.snapsLt bound → b1.snapsLt bound →
          (match a1, b1 with
           | .imm xa, .imm xb => SymExpr.imm (UInt64.ofNat ((xa.toNat * xb.toNat) / 2 ^ 64))
           | _, .imm 0 => .imm 0 | _, .imm 1 => .imm 0
           | _, _ => .mulHi a1 b1).snapsLt bound := by
        intro a1 b1 h1 h2
        split <;> first | trivial | exact ⟨h1, h2⟩
      by_cases hcmp : (b.norm.cmp a.norm == .lt) = true
      · simp only [hcmp, ↓reduceIte]; exact hbody _ _ hb' ha'
      · simp only [hcmp, Bool.false_eq_true, ↓reduceIte]; exact hbody _ _ ha' hb'
  | .divQ a b c, ⟨ha, hb, hc⟩ => by
      have ha' := norm_snapsLt ha; have hb' := norm_snapsLt hb; have hc' := norm_snapsLt hc
      simp only [SymExpr.norm]
      split
      · split
        · exact ⟨ha', hb', hc'⟩
        · trivial
      · exact ⟨ha', hb', hc'⟩
  | .divR a b c, ⟨ha, hb, hc⟩ => by
      have ha' := norm_snapsLt ha; have hb' := norm_snapsLt hb; have hc' := norm_snapsLt hc
      simp only [SymExpr.norm]
      split
      · split
        · exact ⟨ha', hb', hc'⟩
        · trivial
      · exact ⟨ha', hb', hc'⟩
  | .addCLo a b c, ⟨ha, hb, hc⟩ | .addCHi a b c, ⟨ha, hb, hc⟩
  | .subBLo a b c, ⟨ha, hb, hc⟩ | .subBHi a b c, ⟨ha, hb, hc⟩ => by
      have ha' := norm_snapsLt ha; have hb' := norm_snapsLt hb; have hc' := norm_snapsLt hc
      simp only [SymExpr.norm]
      split
      · trivial
      · exact ⟨ha', hb', hc'⟩
  | .load snap w e a, ⟨hs, ha⟩ => ⟨hs, norm_snapsLt ha⟩

/-! ## `NatMap`, `NatSet`, and `bindParams` helper lemmas -/

/-- Pointwise relation on equal-length lists (avoiding non-core `List.Forall₂`). -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel R [] []
  | cons {a b as bs} : R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

theorem ListRel.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, ListRel R as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length_eq]

theorem natMap_ofList_inv {α : Type} {P : Nat → α → Prop} :
    ∀ (xs : List (Nat × α)) (m : Src.NatMap α),
      (∀ k v, m.get? k = some v → P k v) →
      (∀ p ∈ xs, P p.1 p.2) →
      ∀ k v, (xs.foldl (fun acc (k, x) => acc.insert k x) m).get? k = some v → P k v
  | [], m, hm, _, k, v, hg => hm k v hg
  | (k0, v0) :: rest, m, hm, hxs, k, v, hg => by
      simp only [List.foldl_cons] at hg
      apply natMap_ofList_inv rest (m.insert k0 v0) ?_ (fun p hp => hxs p (by simp [hp])) k v hg
      intro k' v' hg'
      rw [Src.NatMap.get?_insert] at hg'
      split at hg'
      · rename_i heq; subst heq; cases hg'; exact hxs (k', v0) (by simp)
      · exact hm k' v' hg'

theorem natMap_ofList_holds {α : Type} {P : Nat → α → Prop} {xs : List (Nat × α)}
    (hxs : ∀ p ∈ xs, P p.1 p.2) {k : Nat} {v : α}
    (hg : (Src.NatMap.ofList xs).get? k = some v) : P k v :=
  natMap_ofList_inv xs .leaf (fun _ _ h => by simp [Src.NatMap.get?] at h) hxs k v hg

theorem natSet_contains_insert (s : Src.NatSet) (k k' : Nat) :
    (s.insert k).contains k' = (k' == k || s.contains k') := by
  simp only [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert]
  by_cases h : k' = k <;> simp [h]

theorem natSet_contains_ofList {xs : List Nat} {k : Nat}
    (h : (Src.NatSet.ofList xs).contains k = true) : k ∈ xs := by
  simp only [Src.NatSet.ofList, Src.NatMap.contains, Option.isSome_iff_exists] at h
  obtain ⟨u, hu⟩ := h
  have hmem : k ∈ xs := natMap_ofList_holds (P := fun n _ => n ∈ xs)
    (fun p hp => by simp only [List.mem_map] at hp; obtain ⟨x, hx, rfl⟩ := hp; exact hx) hu
  exact hmem

theorem bindParams_exists :
    ∀ {ρ : Env} {ps : List VReg} {vs : List Word}, ps.length = vs.length → ∃ ρ', bindParams ρ ps vs = some ρ'
  | ρ, [], [], _ => ⟨ρ, rfl⟩
  | ρ, x :: ps, v :: vs, hlen => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [bindParams]
      exact bindParams_exists (ρ := ρ.insert x v) hlen
  | _, [], _ :: _, hlen | _, _ :: _, [], hlen => by simp at hlen

theorem bindParams_src_inv {ρ₀ : Env} {ctx : Word} {snaps : MemSnaps} :
    ∀ {ps : List VReg} {vs : List Word} {es : List SymExpr}
      {ρ ρ' : Env} {m : Src.NatMap SymExpr} {s : Src.NatSet},
      bindParams ρ ps vs = some ρ' →
      ListRel (fun e v => e.eval ρ₀ ctx snaps = some v) es vs →
      (∀ x v, ρ[x]? = some v → (srcLookup m x).eval ρ₀ ctx snaps = some v) →
      (∀ x, s.contains x = true → ρ[x]?.isSome = true) →
      (∀ x v, ρ'[x]? = some v → (srcLookup (bindNatMap m ps es) x).eval ρ₀ ctx snaps = some v) ∧
      (∀ x, (insertDefs s ps).contains x = true → ρ'[x]?.isSome = true)
  | [], [], [], ρ, ρ', m, s, hbp, _, hm, hs => by
      simp only [bindParams, Option.some.injEq] at hbp; subst hbp
      exact ⟨hm, hs⟩
  | p :: ps, v :: vs, e :: es, ρ, ρ', m, s, hbp, hfa, hm, hs => by
      simp only [bindParams] at hbp
      cases hfa with
      | cons he hrest =>
          simp only [bindNatMap, insertDefs]
          apply bindParams_src_inv hbp hrest
          · intro x vx hx
            rw [env_insert_get] at hx
            unfold srcLookup Src.NatMap.getD
            rw [Src.NatMap.get?_insert]
            by_cases hxp : x = p
            · subst hxp; simp only [↓reduceIte, Option.some.injEq] at hx; subst hx
              simp only [↓reduceIte, Option.getD_some]; exact he
            · have hpx : p ≠ x := Ne.symm hxp
              simp only [hpx, ↓reduceIte] at hx
              simp only [hxp, ↓reduceIte]
              exact hm x vx hx
          · intro x hx
            rw [natSet_contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
            rw [env_insert_get]
            rcases hx with rfl | hx
            · simp
            · split
              · rfl
              · exact hs x hx
  | [], [], _ :: _, _, _, _, _, _, hfa, _, _ | [], _ :: _, _, _, _, _, _, hbp, _, _, _
  | _ :: _, [], _, _, _, _, _, hbp, _, _, _ | _ :: _, _ :: _, [], _, _, _, _, _, hfa, _, _ => by
      first | cases hbp | cases hfa

theorem bindParams_tgt_inv {ρ₀ : Env} {ctx : Word} {snaps : MemSnaps} :
    ∀ {ps : List VReg} {vs : List Word} {es : List SymExpr}
      {ρ₂ ρ₂' : Env} {m : Src.NatMap SymExpr},
      bindParams ρ₂ ps vs = some ρ₂' →
      ListRel (fun e v => e.eval ρ₀ ctx snaps = some v) es vs →
      (∀ y ey, m.get? y = some ey → ∃ vy, ρ₂[y]? = some vy ∧ ey.eval ρ₀ ctx snaps = some vy) →
      (∀ y ey, (bindNatMap m ps es).get? y = some ey →
        ∃ vy, ρ₂'[y]? = some vy ∧ ey.eval ρ₀ ctx snaps = some vy)
  | [], [], [], ρ₂, ρ₂', m, hbp, _, hm => by
      simp only [bindParams, Option.some.injEq] at hbp; subst hbp; exact hm
  | p :: ps, v :: vs, e :: es, ρ₂, ρ₂', m, hbp, hfa, hm => by
      simp only [bindParams] at hbp
      cases hfa with
      | cons he hrest =>
          simp only [bindNatMap]
          apply bindParams_tgt_inv hbp hrest
          intro y ey hy
          rw [Src.NatMap.get?_insert] at hy
          rw [env_insert_get]
          by_cases hyp : y = p
          · subst hyp; simp only [↓reduceIte, Option.some.injEq] at hy; subst hy
            exact ⟨v, by simp, he⟩
          · simp only [hyp, ↓reduceIte] at hy
            have hpy : p ≠ y := Ne.symm hyp
            simp only [hpy, ↓reduceIte]
            exact hm y ey hy
  | [], [], _ :: _, _, _, _, _, hfa, _ | [], _ :: _, _, _, _, _, hbp, _, _
  | _ :: _, [], _, _, _, _, hbp, _, _ | _ :: _, _ :: _, [], _, _, _, _, hfa, _ => by
      first | cases hbp | cases hfa

theorem bindParams_not_mem :
    ∀ {ρ ρ' : Env} {ps : List VReg} {vs : List Word},
      bindParams ρ ps vs = some ρ' →
      ∀ x, x ∉ ps → ρ'[x]? = ρ[x]?
  | _, _, [], [], hbp, x, _ => by simp only [bindParams, Option.some.injEq] at hbp; subst hbp; rfl
  | ρ, _, p :: ps, v :: vs, hbp, x, hnot => by
      simp only [List.mem_cons, not_or] at hnot
      simp only [bindParams] at hbp
      rw [bindParams_not_mem (ρ := ρ.insert p v) hbp x hnot.2, env_insert_ne _ _ (Ne.symm hnot.1)]
  | _, _, [], _ :: _, hbp, _, _ | _, _, _ :: _, [], hbp, _, _ => by cases hbp

theorem bindParams_mem_eq :
    ∀ {ρ₁ ρ₂ ρ₁' ρ₂' : Env} {ps : List VReg} {vs : List Word},
      bindParams ρ₁ ps vs = some ρ₁' →
      bindParams ρ₂ ps vs = some ρ₂' →
      ∀ x ∈ ps, ∃ v, ρ₁'[x]? = some v ∧ ρ₂'[x]? = some v
  | _, _, _, _, [], [], _, _, _, hx => by cases hx
  | ρ₁, ρ₂, _, _, p :: ps, v :: vs, h1, h2, x, hx => by
      simp only [bindParams] at h1 h2
      by_cases htail : x ∈ ps
      · exact bindParams_mem_eq h1 h2 x htail
      · simp only [List.mem_cons] at hx
        rcases hx with rfl | hmem
        · rw [bindParams_not_mem h1 x htail, bindParams_not_mem h2 x htail,
            env_insert_self, env_insert_self]
          exact ⟨v, rfl, rfl⟩
        · exact absurd hmem htail
  | _, _, _, _, [], _ :: _, h1, _, _, _ | _, _, _, _, _ :: _, [], h1, _, _, _ => by cases h1

/-! ## `argToSym`, `addrToSym`, `ovfToSym`, `evalTgtArg`, `evalTgtAddr` -/

theorem argToSym_eval {ρ₁ ρ₀ : Env} {ctx : Word} {snaps : MemSnaps} {lookup : VReg → SymExpr}
    (hlk : ∀ x v, ρ₁[x]? = some v → (lookup x).eval ρ₀ ctx snaps = some v)
    {a : Arg} {v : Word} (ha : a.eval ρ₁ = some v) :
    (argToSym lookup a).eval ρ₀ ctx snaps = some v := by
  cases a with
  | v x => exact hlk x v ha
  | imm w => exact ha

theorem argToSym_snapsLt {bound : Nat} {lookup : VReg → SymExpr}
    (hlk : ∀ x, (lookup x).snapsLt bound) (a : Arg) : (argToSym lookup a).snapsLt bound := by
  cases a with
  | v x => exact hlk x
  | imm _ => trivial

theorem addrToSym_eval {ρ₁ ρ₀ : Env} {ctx : Word} {snaps : MemSnaps} {lookup : VReg → SymExpr}
    (hlk : ∀ x v, ρ₁[x]? = some v → (lookup x).eval ρ₀ ctx snaps = some v)
    {m : Addr} {va : Word} (hm : m.eval ρ₁ ctx = some va) :
    (addrToSym lookup m).eval ρ₀ ctx snaps = some va := by
  rcases m with ⟨mb, mi, disp⟩
  unfold Addr.eval at hm
  unfold addrToSym
  have finish : ∀ (be ie : SymExpr) (vb vi : Word),
      be.eval ρ₀ ctx snaps = some vb → ie.eval ρ₀ ctx snaps = some vi →
      vb + vi + dispWord disp = va →
      (mkBin .add .w64 (mkBin .add .w64 be ie) (.imm (dispWord disp))).eval ρ₀ ctx snaps = some va := by
    intro be ie vb vi hbe hie hsum
    rw [← hsum]
    exact mkBin_sound (mkBin_sound hbe hie (o := .add) (w := .w64) (v := vb + vi) (by simp [BinOp.eval, X86.Encode.truncate64]))
      (b := .imm (dispWord disp)) (vb := dispWord disp) rfl (o := .add) (w := .w64) (v := vb + vi + dispWord disp)
      (by simp [BinOp.eval, X86.Encode.truncate64])
  cases mb with
  | none =>
      cases mi with
      | none =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hm
          exact finish (.imm 0) (.imm 0) 0 0 rfl rfl hm
      | some xs =>
          obtain ⟨x, s⟩ := xs
          simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
            Option.map_eq_map, Option.map_eq_some_iff, Option.some.injEq] at hm
          obtain ⟨vi, ⟨vx, hvx, rfl⟩, hsum⟩ := hm
          exact finish (.imm 0) _ 0 (vx * s.word) rfl
            (mkBin_sound (hlk x vx hvx) (b := .imm s.word) (vb := s.word) rfl (o := .mul) (w := .w64) (v := vx * s.word)
              (by simp [BinOp.eval, X86.Encode.truncate64])) hsum
  | some b => cases b with
    | ctx =>
        cases mi with
        | none =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hm
            exact finish .ctx (.imm 0) ctx 0 rfl rfl hm
        | some xs =>
            obtain ⟨x, s⟩ := xs
            simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
              Option.map_eq_map, Option.map_eq_some_iff, Option.some.injEq] at hm
            obtain ⟨vi, ⟨vx, hvx, rfl⟩, hsum⟩ := hm
            exact finish .ctx _ ctx (vx * s.word) rfl
              (mkBin_sound (hlk x vx hvx) (b := .imm s.word) (vb := s.word) rfl (o := .mul) (w := .w64) (v := vx * s.word)
                (by simp [BinOp.eval, X86.Encode.truncate64])) hsum
    | v bx =>
        cases mi with
        | none =>
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_some, Option.some.injEq] at hm
            obtain ⟨vb, hvb, hsum⟩ := hm
            exact finish (lookup bx) (.imm 0) vb 0 (hlk bx vb hvb) rfl hsum
        | some xs =>
            obtain ⟨x, s⟩ := xs
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.map_eq_map, Option.map_eq_some_iff, Option.some.injEq] at hm
            obtain ⟨vb, hvb, vi, ⟨vx, hvx, rfl⟩, hsum⟩ := hm
            exact finish (lookup bx) _ vb (vx * s.word) (hlk bx vb hvb)
              (mkBin_sound (hlk x vx hvx) (b := .imm s.word) (vb := s.word) rfl (o := .mul) (w := .w64) (v := vx * s.word)
                (by simp [BinOp.eval, X86.Encode.truncate64])) hsum

theorem addrToSym_snapsLt {bound : Nat} {lookup : VReg → SymExpr}
    (hlk : ∀ x, (lookup x).snapsLt bound) (m : Addr) : (addrToSym lookup m).snapsLt bound := by
  unfold addrToSym
  have hb : (match m.base with | none => SymExpr.imm 0 | some (.v x) => lookup x | some .ctx => .ctx).snapsLt bound := by
    cases m.base with
    | none => trivial
    | some b => cases b with | v x => exact hlk x | ctx => trivial
  have hi : (match m.index with | none => SymExpr.imm 0 | some (x, s) => mkBin .mul .w64 (lookup x) (.imm s.word)).snapsLt bound := by
    cases m.index with
    | none => trivial
    | some xs => exact mkBin_snapsLt (hlk xs.1) trivial
  exact mkBin_snapsLt (mkBin_snapsLt hb hi) trivial

theorem toConstAddr_eval_src {ρ₁ ρ₀ : Env} {ctx : Word} {snaps : MemSnaps} {lookup : VReg → SymExpr}
    (hlk : ∀ x v, ρ₁[x]? = some v → (lookup x).eval ρ₀ ctx snaps = some v)
    {m : Addr} {va : Word} (hm : m.eval ρ₁ ctx = some va)
    {ca : ConstAddr} (hca : toConstAddr lookup m = some ca) :
    ca.eval ρ₀ ctx snaps = some va := by
  unfold toConstAddr at hca
  split at hca
  · cases hca
  · rename_i hok
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hok
    have hidx_none : m.index = none := by cases hi : m.index with | none => rfl | some _ => simp [hi] at hok
    simp only [Option.some.injEq] at hca; subst hca
    unfold Addr.eval at hm; rw [hidx_none] at hm
    cases hb : m.base with
    | none =>
        rw [hb] at hm; simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hm
        subst hm; rw [UInt64.add_zero]; simp [ConstAddr.eval, MemBase.eval]
    | some b => cases b with
      | ctx =>
          rw [hb] at hm; simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hm
          subst hm; rw [UInt64.add_zero]; simp [ConstAddr.eval, MemBase.eval]
      | v x =>
          rw [hb] at hm; simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_some, Option.some.injEq] at hm
          obtain ⟨vb, hvb, rfl⟩ := hm
          rw [UInt64.add_zero]
          have hx := SymExpr.norm_sound (hlk x vb hvb)
          simp [ConstAddr.eval, MemBase.eval, hx]

theorem ovfToSym_eval {ρ₀ : Env} {ctx : Word} {snaps : MemSnaps} {o : Ovf} {a b : SymExpr} {va vb : Word}
    (ha : a.eval ρ₀ ctx snaps = some va) (hb : b.eval ρ₀ ctx snaps = some vb) :
    (ovfToSym o a b).eval ρ₀ ctx snaps = some (o.eval va vb).1 := by
  cases o <;> exact mkBin_sound ha hb (by simp [BinOp.eval, Ovf.eval, X86.Encode.truncate64])

theorem evalTgtArg_sound {ρ₀ ρ₂ : Env} {ctx : Word} {snaps : MemSnaps} {tgtEnv : Src.NatMap SymExpr}
    (htgt : ∀ y ey, tgtEnv.get? y = some ey → ∃ vy, ρ₂[y]? = some vy ∧ ey.eval ρ₀ ctx snaps = some vy)
    {a : Arg} {e : SymExpr} (h : evalTgtArg tgtEnv a = some e) :
    ∃ v, a.eval ρ₂ = some v ∧ e.eval ρ₀ ctx snaps = some v := by
  cases a with
  | imm w => simp only [evalTgtArg, Option.some.injEq] at h; subst h; exact ⟨w, rfl, rfl⟩
  | v y => exact htgt y e h

theorem evalTgtArg_snapsLt {bound : Nat} {tgtEnv : Src.NatMap SymExpr}
    (hlt : ∀ y ey, tgtEnv.get? y = some ey → ey.snapsLt bound)
    {a : Arg} {e : SymExpr} (h : evalTgtArg tgtEnv a = some e) : e.snapsLt bound := by
  cases a with
  | imm _ => simp only [evalTgtArg, Option.some.injEq] at h; subst h; trivial
  | v y => exact hlt y e h

theorem evalTgtArgs_sound {ρ₀ ρ₂ : Env} {ctx : Word} {snaps : MemSnaps} {tgtEnv : Src.NatMap SymExpr}
    (htgt : ∀ y ey, tgtEnv.get? y = some ey → ∃ vy, ρ₂[y]? = some vy ∧ ey.eval ρ₀ ctx snaps = some vy) :
    ∀ {as : List Arg} {es : List SymExpr}, evalTgtArgs tgtEnv as = some es →
      ∃ vs, evalArgs ρ₂ as = some vs ∧ ListRel (fun e v => e.eval ρ₀ ctx snaps = some v) es vs
  | [], _, h => by simp only [evalTgtArgs, Option.some.injEq] at h; subst h; exact ⟨[], rfl, .nil⟩
  | a :: rest, _, h => by
      simp only [evalTgtArgs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨e, he, es', hes', rfl⟩ := h
      obtain ⟨v, hv, hev⟩ := evalTgtArg_sound htgt he
      obtain ⟨vs, hvs, hfa⟩ := evalTgtArgs_sound htgt hes'
      rw [evalArgs] at hvs
      exact ⟨v :: vs, by simp only [evalArgs, List.mapM_cons, Option.bind_eq_bind, hv, hvs, Option.bind_some, Option.pure_def], .cons hev hfa⟩

theorem evalTgtAddr_sound {ρ₀ ρ₂ : Env} {ctx : Word} {snaps : MemSnaps} {tgtEnv : Src.NatMap SymExpr}
    (htgt : ∀ y ey, tgtEnv.get? y = some ey → ∃ vy, ρ₂[y]? = some vy ∧ ey.eval ρ₀ ctx snaps = some vy)
    {m : Addr} {addr : SymExpr} {ca : Option ConstAddr}
    (h : evalTgtAddr tgtEnv m = some (addr, ca)) :
    ∃ va, m.eval ρ₂ ctx = some va ∧ addr.eval ρ₀ ctx snaps = some va ∧
      (∀ c, ca = some c → c.eval ρ₀ ctx snaps = some va) := by
  rcases m with ⟨mb, mi, disp⟩
  unfold evalTgtAddr at h
  revert h
  have finish : ∀ (be ie : SymExpr) (vb vi : Word),
      (match mb with | none => some 0 | some (.v x) => ρ₂[x]? | some .ctx => some ctx) = some vb →
      (match mi with | none => some 0 | some (x, s) => (· * s.word) <$> ρ₂[x]?) = some vi →
      be.eval ρ₀ ctx snaps = some vb → ie.eval ρ₀ ctx snaps = some vi →
      (match mb with | none => MemBase.zero | some .ctx => .ctx | some (.v _) => .expr be.norm).eval ρ₀ ctx snaps = some vb →
      (mi = none → vi = 0) →
      addr = (mkBin .add .w64 (mkBin .add .w64 be ie) (.imm (dispWord disp))).norm →
      ca = (if mi.isSome || !decide (-2147483648 ≤ disp ∧ disp < 2147483648) then none
            else some ⟨match mb with | none => .zero | some .ctx => .ctx | some (.v _) => .expr be.norm, disp⟩) →
      ∃ va, Addr.eval ρ₂ ctx ⟨mb, mi, disp⟩ = some va ∧ addr.eval ρ₀ ctx snaps = some va ∧
        (∀ c, ca = some c → c.eval ρ₀ ctx snaps = some va) := by
    intro be ie vb vi hbv hiv hbe hie hmbe hvi0 rfl hca_eq
    have hsum := mkBin_sound hbe hie (o := .add) (w := .w64) (v := vb + vi)
      (by simp [BinOp.eval, X86.Encode.truncate64])
    have haddr := SymExpr.norm_sound (mkBin_sound hsum (b := .imm (dispWord disp)) (vb := dispWord disp) rfl
      (o := .add) (w := .w64) (v := vb + vi + dispWord disp)
      (by simp [BinOp.eval, X86.Encode.truncate64]))
    refine ⟨vb + vi + dispWord disp, ?_, haddr, ?_⟩
    · cases mb with
      | none =>
          cases hbv; cases mi with
          | none => cases hiv; rfl
          | some xs => simp only [Addr.eval, Option.bind_eq_bind, Option.bind_some, hiv]
      | some b => cases b with
        | ctx =>
            cases hbv; cases mi with
            | none => cases hiv; rfl
            | some xs => simp only [Addr.eval, Option.bind_eq_bind, Option.bind_some, hiv]
        | v bx =>
            cases mi with
            | none => cases hiv; simp only [Addr.eval, Option.bind_eq_bind, hbv, Option.bind_some]
            | some xs => simp only [Addr.eval, Option.bind_eq_bind, hbv, hiv, Option.bind_some]
    · intro c hc
      rw [hca_eq] at hc
      cases mi with
      | some _ => simp at hc
      | none =>
          have hvi := hvi0 rfl; subst hvi
          rw [UInt64.add_zero]
          split at hc
          · cases hc
          · simp only [Option.some.injEq] at hc; subst hc
            simp only [ConstAddr.eval, Option.bind_eq_bind, hmbe, Option.bind_some]
  intro h
  cases mb with
  | none =>
      cases mi with
      | none =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          exact finish (.imm 0) (.imm 0) 0 0 rfl rfl rfl rfl rfl (fun _ => rfl) h.1.symm h.2.symm
      | some xs =>
          obtain ⟨y, s⟩ := xs
          simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨ey, hey, ha, hc⟩ := h
          obtain ⟨vy, hvy, heyv⟩ := htgt y ey hey
          exact finish (.imm 0) (mkBin .mul .w64 ey (.imm s.word)) 0 (vy * s.word) rfl (by simp [hvy]) rfl
            (mkBin_sound heyv (b := .imm s.word) (vb := s.word) rfl (o := .mul) (w := .w64) (v := vy * s.word)
              (by simp [BinOp.eval, X86.Encode.truncate64]))
            rfl (fun h => by cases h) ha.symm hc.symm
  | some b => cases b with
    | ctx =>
        cases mi with
        | none =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
            exact finish .ctx (.imm 0) ctx 0 rfl rfl rfl rfl rfl (fun _ => rfl) h.1.symm h.2.symm
        | some xs =>
            obtain ⟨y, s⟩ := xs
            simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨ey, hey, ha, hc⟩ := h
            obtain ⟨vy, hvy, heyv⟩ := htgt y ey hey
            exact finish .ctx (mkBin .mul .w64 ey (.imm s.word)) ctx (vy * s.word) rfl (by simp [hvy]) rfl
              (mkBin_sound heyv (b := .imm s.word) (vb := s.word) rfl (o := .mul) (w := .w64) (v := vy * s.word)
                (by simp [BinOp.eval, X86.Encode.truncate64]))
              rfl (fun h => by cases h) ha.symm hc.symm
    | v bx =>
        cases mi with
        | none =>
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨be, hbe, ha, hc⟩ := h
            obtain ⟨vb, hvb, hbev⟩ := htgt bx be hbe
            exact finish be (.imm 0) vb 0 hvb rfl hbev rfl (SymExpr.norm_sound hbev) (fun _ => rfl) ha.symm hc.symm
        | some xs =>
            obtain ⟨y, s⟩ := xs
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨be, hbe, ey, hey, ha, hc⟩ := h
            obtain ⟨vb, hvb, hbev⟩ := htgt bx be hbe
            obtain ⟨vy, hvy, heyv⟩ := htgt y ey hey
            exact finish be (mkBin .mul .w64 ey (.imm s.word)) vb (vy * s.word) hvb (by simp [hvy]) hbev
              (mkBin_sound heyv (b := .imm s.word) (vb := s.word) rfl (o := .mul) (w := .w64) (v := vy * s.word)
                (by simp [BinOp.eval, X86.Encode.truncate64]))
              (SymExpr.norm_sound hbev) (fun h => by cases h) ha.symm hc.symm

theorem evalTgtAddr_snapsLt {bound : Nat} {tgtEnv : Src.NatMap SymExpr}
    (hlt : ∀ y ey, tgtEnv.get? y = some ey → ey.snapsLt bound)
    {m : Addr} {addr : SymExpr} {ca : Option ConstAddr}
    (h : evalTgtAddr tgtEnv m = some (addr, ca)) :
    addr.snapsLt bound ∧
    (∀ c, ca = some c → match c.base with | .expr e => e.snapsLt bound | _ => True) := by
  rcases m with ⟨mb, mi, disp⟩
  unfold evalTgtAddr at h
  revert h
  have finish : ∀ (be ie : SymExpr), be.snapsLt bound → ie.snapsLt bound →
      addr = (mkBin .add .w64 (mkBin .add .w64 be ie) (.imm (dispWord disp))).norm →
      ca = (if mi.isSome || !decide (-2147483648 ≤ disp ∧ disp < 2147483648) then none
            else some ⟨match mb with | none => .zero | some .ctx => .ctx | some (.v _) => .expr be.norm, disp⟩) →
      addr.snapsLt bound ∧
      (∀ c, ca = some c → match c.base with | .expr e => e.snapsLt bound | _ => True) := by
    intro be ie hblt hilt rfl hca_eq
    refine ⟨SymExpr.norm_snapsLt (mkBin_snapsLt (mkBin_snapsLt hblt hilt) trivial), ?_⟩
    intro c hc
    rw [hca_eq] at hc
    split at hc
    · cases hc
    · simp only [Option.some.injEq] at hc; subst hc
      cases mb with
      | none => trivial
      | some b => cases b with | ctx => trivial | v _ => exact SymExpr.norm_snapsLt hblt
  intro h
  cases mb with
  | none =>
      cases mi with
      | none =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          exact finish (.imm 0) (.imm 0) trivial trivial h.1.symm h.2.symm
      | some xs =>
          obtain ⟨y, s⟩ := xs
          simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨ey, hey, ha, hc⟩ := h
          exact finish (.imm 0) (mkBin .mul .w64 ey (.imm s.word)) trivial (mkBin_snapsLt (hlt y ey hey) trivial) ha.symm hc.symm
  | some b => cases b with
    | ctx =>
        cases mi with
        | none =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
            exact finish .ctx (.imm 0) trivial trivial h.1.symm h.2.symm
        | some xs =>
            obtain ⟨y, s⟩ := xs
            simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨ey, hey, ha, hc⟩ := h
            exact finish .ctx (mkBin .mul .w64 ey (.imm s.word)) trivial (mkBin_snapsLt (hlt y ey hey) trivial) ha.symm hc.symm
    | v bx =>
        cases mi with
        | none =>
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨be, hbe, ha, hc⟩ := h
            exact finish be (.imm 0) (hlt bx be hbe) trivial ha.symm hc.symm
        | some xs =>
            obtain ⟨y, s⟩ := xs
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨be, hbe, ey, hey, ha, hc⟩ := h
            exact finish be (mkBin .mul .w64 ey (.imm s.word)) (hlt bx be hbe) (mkBin_snapsLt (hlt y ey hey) trivial) ha.symm hc.symm

/-! ## `MemWrite` snapshot bounds and `BlockInv.Holds` -/

def ConstAddr.snapsLt (bound : Nat) (ca : ConstAddr) : Prop :=
  match ca.base with | .expr e => e.snapsLt bound | _ => True

def MemWrite.snapsLt (bound : Nat) (wr : MemWrite) : Prop :=
  wr.addr.snapsLt bound ∧ wr.val.snapsLt bound ∧ (∀ ca, wr.caddr = some ca → ca.snapsLt bound)

theorem ConstAddr.snapsLt_mono {b1 b2 : Nat} (hle : b1 ≤ b2) {ca : ConstAddr}
    (h : ca.snapsLt b1) : ca.snapsLt b2 := by
  cases hb : ca.base with
  | zero | ctx => simp [ConstAddr.snapsLt, hb]
  | expr e => simp only [ConstAddr.snapsLt, hb] at h ⊢; exact SymExpr.snapsLt_mono hle h

theorem MemWrite.snapsLt_mono {b1 b2 : Nat} (hle : b1 ≤ b2) {wr : MemWrite}
    (h : wr.snapsLt b1) : wr.snapsLt b2 :=
  ⟨SymExpr.snapsLt_mono hle h.1, SymExpr.snapsLt_mono hle h.2.1,
   fun ca hca => ConstAddr.snapsLt_mono hle (h.2.2 ca hca)⟩

theorem MemWrite.valid_snaps_congr {ρ : Env} {ctx : Word} {snaps1 snaps2 : MemSnaps} {bound : Nat}
    (hagree : ∀ id < bound, snaps1 id = snaps2 id) {wr : MemWrite}
    (hlt : wr.snapsLt bound) (hv : wr.Valid ρ ctx snaps1) : wr.Valid ρ ctx snaps2 := by
  obtain ⟨va, vv, ha, hval, hca⟩ := hv
  refine ⟨va, vv, ?_, ?_, ?_⟩
  · rw [← SymExpr.eval_snaps_congr hagree hlt.1]; exact ha
  · rw [← SymExpr.eval_snaps_congr hagree hlt.2.1]; exact hval
  · intro ca hceq
    have hc := hca ca hceq
    have hclt := hlt.2.2 ca hceq
    cases hb : ca.base with
    | zero | ctx => simpa [ConstAddr.eval, MemBase.eval, hb] using hc
    | expr e =>
        simp only [ConstAddr.snapsLt, hb] at hclt
        simpa [ConstAddr.eval, MemBase.eval, hb, SymExpr.eval_snaps_congr hagree hclt] using hc

theorem dropShadowed_snapsLt {bound : Nat} {w : Width} {ca : Option ConstAddr} :
    ∀ {ws : List MemWrite}, (∀ wr ∈ ws, wr.snapsLt bound) →
      ∀ wr ∈ dropShadowed w ca ws, wr.snapsLt bound
  | [], _, _, h => by simp [dropShadowed] at h
  | u :: rest, hlt, wr, hmem => by
      unfold dropShadowed at hmem
      split at hmem
      · exact hlt wr (by simp [hmem])
      · split at hmem
        · simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hlt _ (by simp)
          · exact dropShadowed_snapsLt (fun x hx => hlt x (by simp [hx])) wr hmem
        · exact hlt wr hmem

theorem readAux_suffix_snapsLt {bound : Nat} {w : Width} {e : Ext} {ca : Option ConstAddr} :
    ∀ {ws : List MemWrite}, (∀ wr ∈ ws, wr.snapsLt bound) →
      match SymMem.readAux w e ca ws with
      | .inl fe => fe.snapsLt bound
      | .inr ws' => ∀ wr ∈ ws', wr.snapsLt bound
  | [], _ => fun _ h => by cases h
  | wr :: rest, hlt => by
      unfold SymMem.readAux
      have hwr := hlt wr (by simp)
      by_cases hsame : constAddrSame w ca wr.width wr.caddr = true
      · simp only [hsame, ↓reduceIte]
        cases hfw : forwardVal w e wr.val with
        | none => exact hlt
        | some fe =>
            unfold forwardVal at hfw
            cases w with
            | w64 => simp only [Option.some.injEq] at hfw; subst hfw; exact hwr.2.1
            | w8 | w16 | w32 =>
                cases e with
                | zero =>
                    simp only [Option.some.injEq] at hfw; subst hfw
                    exact mkBin_snapsLt hwr.2.1 (b := .imm _) trivial
                | sign =>
                    cases hv : wr.val with
                    | imm k => rw [hv] at hfw; simp only [Option.some.injEq] at hfw; subst hfw; trivial
                    | _ => rw [hv] at hfw; cases hfw
      · simp only [hsame, Bool.false_eq_true, ↓reduceIte]
        by_cases hdisj : constAddrDisjoint w ca wr.width wr.caddr = true
        · simp only [hdisj, ↓reduceIte]
          exact readAux_suffix_snapsLt (fun x hx => hlt x (by simp [hx]))
        · simp only [hdisj, Bool.false_eq_true, ↓reduceIte]
          exact hlt

/-- Dummy memory used for memory-free expressions in `BlockInv.Holds`. -/
def emptyMem : X86.Memory :=
  { bytes := fun _ => 0, readable := fun _ => false, writable := fun _ => false }

/-- Semantic meaning of a block-entry (or post-call) relational invariant `inv`. -/
def BlockInv.Holds (inv : BlockInv) (ρ₁ ρ₂ : Env) (ctx : Word) : Prop :=
  inv.isMemFree = true ∧
  (∀ x ∈ inv.srcDef, ρ₁[x]?.isSome = true) ∧
  (∀ p ∈ inv.tgtOf, ∃ v, ρ₂[p.1]? = some v ∧ p.2.eval ρ₁ ctx (fun _ => emptyMem) = some v) ∧
  (∀ p ∈ inv.srcEq, ∃ v, ρ₁[p.1]? = some v ∧ p.2.eval ρ₁ ctx (fun _ => emptyMem) = some v) ∧
  FactsHold ρ₁ ctx (fun _ => emptyMem) inv.facts

/-! ## Segment symbolic invariants (`SegInv`) -/

/-- Full relational invariant connecting segment-entry `(ρ₁₀, mem₀)` with current
source `(ρ₁, mem₁)`, target `(ρ₂, mem₂)`, symbolic state `st`, and concrete `snaps`. -/
structure SegInv (st : SegState) (ρ₁₀ : Env) (mem₀ : X86.Memory)
    (ρ₁ : Env) (mem₁ : X86.Memory) (ρ₂ : Env) (mem₂ : X86.Memory)
    (ctx : Word) (snaps : MemSnaps) : Prop where
  snapsCons : SnapsConsistent ρ₁₀ ctx mem₀ st.snaps snaps
  snapsLtTab : ∀ (id : Nat) (u : List MemWrite), st.snaps[id]? = some u →
      ∀ wr ∈ u, wr.addr.snapsLt st.snaps.size ∧ wr.val.snapsLt st.snaps.size
  srcEnvEval : ∀ x v, ρ₁[x]? = some v → (srcLookup st.srcEnv x).eval ρ₁₀ ctx snaps = some v
  srcEnvLt : ∀ x, (srcLookup st.srcEnv x).snapsLt st.snaps.size
  srcDefOk : ∀ x, st.srcDef.contains x = true → ρ₁[x]?.isSome = true
  tgtEnvEval : ∀ y ey, st.tgtEnv.get? y = some ey →
      ∃ v, ρ₂[y]? = some v ∧ ey.eval ρ₁₀ ctx snaps = some v
  tgtEnvLt : ∀ y ey, st.tgtEnv.get? y = some ey → ey.snapsLt st.snaps.size
  factsHold : FactsHold ρ₁₀ ctx snaps st.facts
  factsMemFree : ∀ f ∈ st.facts, f.isMemFree = true
  smem1Ok : applyWrites ρ₁₀ ctx snaps mem₀ st.smem1 = some mem₁
  smem1Valid : ∀ wr ∈ st.smem1, wr.Valid ρ₁₀ ctx snaps
  smem1Lt : ∀ wr ∈ st.smem1, wr.snapsLt st.snaps.size
  smem2Ok : applyWrites ρ₁₀ ctx snaps mem₀ st.smem2 = some mem₂
  smem2Valid : ∀ wr ∈ st.smem2, wr.Valid ρ₁₀ ctx snaps
  smem2Lt : ∀ wr ∈ st.smem2, wr.snapsLt st.snaps.size
  safeReadsOk : ∀ p ∈ st.safeReads, ∃ va, p.2.eval ρ₁₀ ctx snaps = some va ∧
      p.2.snapsLt st.snaps.size ∧ X86.Memory.rangeAllowed mem₀.readable va p.1.bytes = true
  safeWritesOk : ∀ p ∈ st.safeWrites, ∃ va, p.2.eval ρ₁₀ ctx snaps = some va ∧
      p.2.snapsLt st.snaps.size ∧ X86.Memory.rangeAllowed mem₀.writable va p.1.bytes = true
  safeDivsOk : ∀ p ∈ st.safeDivs, ∃ vd, p.2.eval ρ₁₀ ctx snaps = some vd ∧
      p.2.snapsLt st.snaps.size ∧ p.1.truncate vd ≠ 0
  safeBsrsOk : ∀ a ∈ st.safeBsrs, ∃ va, a.eval ρ₁₀ ctx snaps = some va ∧
      a.snapsLt st.snaps.size ∧ va ≠ 0
  safeDivWidesOk : ∀ p ∈ st.safeDivWides, ∃ vhi vd,
      p.1.eval ρ₁₀ ctx snaps = some vhi ∧ p.2.eval ρ₁₀ ctx snaps = some vd ∧
      p.1.snapsLt st.snaps.size ∧ p.2.snapsLt st.snaps.size ∧
      vd.toNat ≠ 0 ∧ vhi.toNat < vd.toNat

/-- Extending `snaps` via `SnapTable.intern` preserves every field of `SegInv`. -/
theorem SegInv.liftSnaps {st : SegState} {ρ₁₀ ρ₁ ρ₂ : Env} {mem₀ mem₁ mem₂ : X86.Memory}
    {ctx : Word} {snaps snaps' : MemSnaps} {snapsTab' : SnapTable}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hle : st.snaps.size ≤ snapsTab'.size)
    (hagree : ∀ k < st.snaps.size, snaps' k = snaps k)
    (hcons' : SnapsConsistent ρ₁₀ ctx mem₀ snapsTab' snaps')
    (hltTab' : ∀ (id : Nat) (u : List MemWrite), snapsTab'[id]? = some u →
      ∀ wr ∈ u, wr.addr.snapsLt snapsTab'.size ∧ wr.val.snapsLt snapsTab'.size) :
    SegInv { st with snaps := snapsTab' } ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps' where
  snapsCons := hcons'
  snapsLtTab := hltTab'
  srcEnvEval x v hx := by
    rw [SymExpr.eval_snaps_congr hagree (h.srcEnvLt x)]; exact h.srcEnvEval x v hx
  srcEnvLt x := SymExpr.snapsLt_mono hle (h.srcEnvLt x)
  srcDefOk := h.srcDefOk
  tgtEnvEval y ey hy := by
    obtain ⟨v, hv, hev⟩ := h.tgtEnvEval y ey hy
    exact ⟨v, hv, by rw [SymExpr.eval_snaps_congr hagree (h.tgtEnvLt y ey hy)]; exact hev⟩
  tgtEnvLt y ey hy := SymExpr.snapsLt_mono hle (h.tgtEnvLt y ey hy)
  factsHold f hf := PFact.holds_snaps_congr (h.factsMemFree f hf) (h.factsHold f hf)
  factsMemFree := h.factsMemFree
  smem1Ok := by
    rw [applyWrites_snaps_congr hagree (fun wr hwr => ⟨(h.smem1Lt wr hwr).1, (h.smem1Lt wr hwr).2.1⟩)]
    exact h.smem1Ok
  smem1Valid wr hwr := MemWrite.valid_snaps_congr (fun k hk => (hagree k hk).symm) (h.smem1Lt wr hwr) (h.smem1Valid wr hwr)
  smem1Lt wr hwr := MemWrite.snapsLt_mono hle (h.smem1Lt wr hwr)
  smem2Ok := by
    rw [applyWrites_snaps_congr hagree (fun wr hwr => ⟨(h.smem2Lt wr hwr).1, (h.smem2Lt wr hwr).2.1⟩)]
    exact h.smem2Ok
  smem2Valid wr hwr := MemWrite.valid_snaps_congr (fun k hk => (hagree k hk).symm) (h.smem2Lt wr hwr) (h.smem2Valid wr hwr)
  smem2Lt wr hwr := MemWrite.snapsLt_mono hle (h.smem2Lt wr hwr)
  safeReadsOk p hp := by
    obtain ⟨va, hva, hlt, hr⟩ := h.safeReadsOk p hp
    exact ⟨va, by rw [SymExpr.eval_snaps_congr hagree hlt]; exact hva, SymExpr.snapsLt_mono hle hlt, hr⟩
  safeWritesOk p hp := by
    obtain ⟨va, hva, hlt, hw⟩ := h.safeWritesOk p hp
    exact ⟨va, by rw [SymExpr.eval_snaps_congr hagree hlt]; exact hva, SymExpr.snapsLt_mono hle hlt, hw⟩
  safeDivsOk p hp := by
    obtain ⟨vd, hvd, hlt, hnz⟩ := h.safeDivsOk p hp
    exact ⟨vd, by rw [SymExpr.eval_snaps_congr hagree hlt]; exact hvd, SymExpr.snapsLt_mono hle hlt, hnz⟩
  safeBsrsOk a ha := by
    obtain ⟨va, hva, hlt, hnz⟩ := h.safeBsrsOk a ha
    exact ⟨va, by rw [SymExpr.eval_snaps_congr hagree hlt]; exact hva, SymExpr.snapsLt_mono hle hlt, hnz⟩
  safeDivWidesOk p hp := by
    obtain ⟨vhi, vd, hhi, hd, hlt1, hlt2, hnz, hlt⟩ := h.safeDivWidesOk p hp
    exact ⟨vhi, vd,
      by rw [SymExpr.eval_snaps_congr hagree hlt1]; exact hhi,
      by rw [SymExpr.eval_snaps_congr hagree hlt2]; exact hd,
      SymExpr.snapsLt_mono hle hlt1, SymExpr.snapsLt_mono hle hlt2, hnz, hlt⟩

theorem SymExpr.isMemFree_of_snapsLt_zero :
    ∀ {e : SymExpr}, e.snapsLt 0 → e.isMemFree = true
  | .reg _, _ | .imm _, _ | .ctx, _ => rfl
  | .bin _ _ a b, ⟨ha, hb⟩ | .test _ _ a b, ⟨ha, hb⟩ | .mulHi a b, ⟨ha, hb⟩ => by
      simp [SymExpr.isMemFree, isMemFree_of_snapsLt_zero ha, isMemFree_of_snapsLt_zero hb]
  | .select _ _ a b t f, ⟨ha, hb, ht, hf⟩ => by
      simp [SymExpr.isMemFree, isMemFree_of_snapsLt_zero ha, isMemFree_of_snapsLt_zero hb,
        isMemFree_of_snapsLt_zero ht, isMemFree_of_snapsLt_zero hf]
  | .bsr64 a, ha => by simp [SymExpr.isMemFree, isMemFree_of_snapsLt_zero (e := a) ha]
  | .divQ a b c, ⟨ha, hb, hc⟩ | .divR a b c, ⟨ha, hb, hc⟩ | .addCLo a b c, ⟨ha, hb, hc⟩
  | .addCHi a b c, ⟨ha, hb, hc⟩ | .subBLo a b c, ⟨ha, hb, hc⟩ | .subBHi a b c, ⟨ha, hb, hc⟩ => by
      simp [SymExpr.isMemFree, isMemFree_of_snapsLt_zero ha, isMemFree_of_snapsLt_zero hb,
        isMemFree_of_snapsLt_zero hc]
  | .load snap _ _ _, ⟨hs, _⟩ => absurd hs (Nat.not_lt_zero snap)

theorem SymExpr.isMemFree_subst {f : VReg → SymExpr}
    (hf : ∀ x, (f x).isMemFree = true) :
    ∀ {e : SymExpr}, e.isMemFree = true → (e.subst f).isMemFree = true
  | .reg x, _ => hf x
  | .imm _, _ | .ctx, _ => rfl
  | .bin _ _ a b, h | .test _ _ a b, h | .mulHi a b, h => by
      simp only [SymExpr.isMemFree, Bool.and_eq_true] at h
      simp [SymExpr.subst, SymExpr.isMemFree, isMemFree_subst hf h.1, isMemFree_subst hf h.2]
  | .select _ _ a b t e, h => by
      simp only [SymExpr.isMemFree, Bool.and_eq_true] at h
      simp [SymExpr.subst, SymExpr.isMemFree, isMemFree_subst hf h.1.1.1, isMemFree_subst hf h.1.1.2,
        isMemFree_subst hf h.1.2, isMemFree_subst hf h.2]
  | .bsr64 a, h => by simp [SymExpr.subst, SymExpr.isMemFree, isMemFree_subst hf (e := a) h]
  | .divQ a b c, h | .divR a b c, h | .addCLo a b c, h | .addCHi a b c, h
  | .subBLo a b c, h | .subBHi a b c, h => by
      simp only [SymExpr.isMemFree, Bool.and_eq_true] at h
      simp [SymExpr.subst, SymExpr.isMemFree, isMemFree_subst hf h.1.1, isMemFree_subst hf h.1.2,
        isMemFree_subst hf h.2]
  | .load .., h => by simp [SymExpr.isMemFree] at h

theorem SymExpr.eval_subst_eq {ρ : Env} {ctx : Word} {snaps : MemSnaps} {f : VReg → SymExpr}
    (hsub : ∀ x, (f x).eval ρ ctx snaps = ρ[x]?) :
    ∀ (e : SymExpr), (e.subst f).eval ρ ctx snaps = e.eval ρ ctx snaps
  | .reg x => hsub x
  | .imm _ | .ctx => rfl
  | .bin o w a b => by simp only [SymExpr.subst, SymExpr.eval, eval_subst_eq hsub a, eval_subst_eq hsub b]
  | .select c w a b t e => by
      simp only [SymExpr.subst, SymExpr.eval, eval_subst_eq hsub a, eval_subst_eq hsub b,
        eval_subst_eq hsub t, eval_subst_eq hsub e]
  | .test c w a b => by simp only [SymExpr.subst, SymExpr.eval, eval_subst_eq hsub a, eval_subst_eq hsub b]
  | .bsr64 a => by simp only [SymExpr.subst, SymExpr.eval, eval_subst_eq hsub a]
  | .mulHi a b => by simp only [SymExpr.subst, SymExpr.eval, eval_subst_eq hsub a, eval_subst_eq hsub b]
  | .divQ a b c | .divR a b c | .addCLo a b c | .addCHi a b c | .subBLo a b c | .subBHi a b c => by
      simp only [SymExpr.subst, SymExpr.eval, eval_subst_eq hsub a, eval_subst_eq hsub b, eval_subst_eq hsub c]
  | .load s w e a => by simp only [SymExpr.subst, SymExpr.eval, eval_subst_eq hsub a]

/-- Initialization of `SegInv` from `BlockInv.Holds`. -/
theorem segInv_ofInv {inv : BlockInv} {ρ₁₀ ρ₂₀ : Env} {mem₀ : X86.Memory} {ctx : Word}
    (hinv : inv.Holds ρ₁₀ ρ₂₀ ctx) :
    SegInv (SegState.ofInv inv) ρ₁₀ mem₀ ρ₁₀ mem₀ ρ₂₀ mem₀ ctx (fun _ => mem₀) := by
  obtain ⟨hmf, hdef, htgt, hseq, hfacts⟩ := hinv
  simp only [BlockInv.isMemFree, Bool.and_eq_true, List.all_eq_true] at hmf
  obtain ⟨⟨hmfTgt, hmfSrc⟩, hmfFacts⟩ := hmf
  let srcEnv0 := Src.NatMap.ofList (inv.srcEq.map fun (x, e) => (x, e.norm))
  have hsub_exact : ∀ x, (srcLookup srcEnv0 x).eval ρ₁₀ ctx (fun _ => mem₀) = ρ₁₀[x]? := by
    intro x
    unfold srcLookup Src.NatMap.getD
    cases hg : srcEnv0.get? x with
    | none => rfl
    | some e =>
        have hp : ∃ e0, (x, e0) ∈ inv.srcEq ∧ e = e0.norm :=
          natMap_ofList_holds (P := fun k val => ∃ e0, (k, e0) ∈ inv.srcEq ∧ val = e0.norm)
            (fun p hp => by
              simp only [List.mem_map] at hp
              obtain ⟨⟨k0, e0⟩, hmem, rfl⟩ := hp
              exact ⟨e0, hmem, rfl⟩) hg
        obtain ⟨e0, hmem, rfl⟩ := hp
        obtain ⟨v0, hv0, he0⟩ := hseq (x, e0) hmem
        rw [SymExpr.eval_isMemFree (snaps2 := fun _ => mem₀) (hmfSrc (x, e0) hmem)] at he0
        simp only [Option.getD_some]
        rw [SymExpr.norm_sound he0, hv0]
  have hsub_mf : ∀ x, (srcLookup srcEnv0 x).isMemFree = true := by
    intro x
    unfold srcLookup Src.NatMap.getD
    cases hg : srcEnv0.get? x with
    | none => rfl
    | some e =>
        have hp : ∃ e0, (x, e0) ∈ inv.srcEq ∧ e = e0.norm :=
          natMap_ofList_holds (P := fun k val => ∃ e0, (k, e0) ∈ inv.srcEq ∧ val = e0.norm)
            (fun p hp => by
              simp only [List.mem_map] at hp
              obtain ⟨⟨k0, e0⟩, hmem, rfl⟩ := hp
              exact ⟨e0, hmem, rfl⟩) hg
        obtain ⟨e0, hmem, rfl⟩ := hp
        exact SymExpr.isMemFree_of_snapsLt_zero
          (SymExpr.norm_snapsLt (SymExpr.snapsLt_of_isMemFree (hmfSrc (x, e0) hmem) 0))
  refine
    { snapsCons := fun id ws hget => by
        cases id with
        | zero => simp [SegState.ofInv, SnapTable.init] at hget; subst hget; rfl
        | succ _ => simp [SegState.ofInv, SnapTable.init] at hget
      snapsLtTab := fun id u hget wr hwr => by
        cases id with
        | zero => simp [SegState.ofInv, SnapTable.init] at hget; subst hget; cases hwr
        | succ _ => simp [SegState.ofInv, SnapTable.init] at hget
      srcEnvEval := fun x v hx => by
        change (srcLookup srcEnv0 x).eval ρ₁₀ ctx (fun _ => mem₀) = some v
        rw [hsub_exact x, hx]
      srcEnvLt := fun x =>
        SymExpr.snapsLt_of_isMemFree (hsub_mf x) _
      srcDefOk := fun x hx => hdef x (natSet_contains_ofList hx)
      tgtEnvEval := fun y ey hy => by
        have hp : ∃ e0, (y, e0) ∈ inv.tgtOf ∧ ey = (e0.subst (srcLookup srcEnv0)).norm :=
          natMap_ofList_holds
            (P := fun k val => ∃ e0, (k, e0) ∈ inv.tgtOf ∧ val = (e0.subst (srcLookup srcEnv0)).norm)
            (fun p hp => by
              simp only [List.mem_map] at hp
              obtain ⟨⟨k0, e0⟩, hmem, rfl⟩ := hp
              exact ⟨e0, hmem, rfl⟩) hy
        obtain ⟨e0, hmem, rfl⟩ := hp
        obtain ⟨v, hv, he0⟩ := htgt (y, e0) hmem
        rw [SymExpr.eval_isMemFree (snaps2 := fun _ => mem₀) (hmfTgt (y, e0) hmem)] at he0
        have he1 : (e0.subst (srcLookup srcEnv0)).eval ρ₁₀ ctx (fun _ => mem₀) = some v := by
          rw [SymExpr.eval_subst_eq hsub_exact]; exact he0
        exact ⟨v, hv, SymExpr.norm_sound he1⟩
      tgtEnvLt := fun y ey hy => by
        have hp : ∃ e0, (y, e0) ∈ inv.tgtOf ∧ ey = (e0.subst (srcLookup srcEnv0)).norm :=
          natMap_ofList_holds
            (P := fun k val => ∃ e0, (k, e0) ∈ inv.tgtOf ∧ val = (e0.subst (srcLookup srcEnv0)).norm)
            (fun p hp => by
              simp only [List.mem_map] at hp
              obtain ⟨⟨k0, e0⟩, hmem, rfl⟩ := hp
              exact ⟨e0, hmem, rfl⟩) hy
        obtain ⟨e0, hmem, rfl⟩ := hp
        exact SymExpr.norm_snapsLt
          (SymExpr.snapsLt_of_isMemFree (SymExpr.isMemFree_subst hsub_mf (hmfTgt (y, e0) hmem)) _)
      factsHold := fun f hf => by
        simp only [SegState.ofInv, List.mem_map] at hf
        obtain ⟨f0, hf0, rfl⟩ := hf
        obtain ⟨v1, v2, h1, h2, hc⟩ := PFact.holds_snaps_congr (hmfFacts f0 hf0) (hfacts f0 hf0)
        exact ⟨v1, v2, by rw [SymExpr.eval_subst_eq hsub_exact]; exact h1,
          by rw [SymExpr.eval_subst_eq hsub_exact]; exact h2, hc⟩
      factsMemFree := fun f hf => by
        simp only [SegState.ofInv, List.mem_map] at hf
        obtain ⟨f0, hf0, rfl⟩ := hf
        have hmf0 := hmfFacts f0 hf0
        simp only [PFact.isMemFree, Bool.and_eq_true] at hmf0 ⊢
        exact ⟨SymExpr.isMemFree_subst hsub_mf hmf0.1, SymExpr.isMemFree_subst hsub_mf hmf0.2⟩
      smem1Ok := rfl
      smem1Valid := fun _ h => by cases h
      smem1Lt := fun _ h => by cases h
      smem2Ok := rfl
      smem2Valid := fun _ h => by cases h
      smem2Lt := fun _ h => by cases h
      safeReadsOk := fun _ h => by cases h
      safeWritesOk := fun _ h => by cases h
      safeDivsOk := fun _ h => by cases h
      safeBsrsOk := fun _ h => by cases h
      safeDivWidesOk := fun _ h => by cases h }

/-! ## Stepping source statements (`stepSrcStmt_sound`, `stepSrcList_sound`) -/

private theorem toConstAddr_snapsLt {bound : Nat} {lookup : VReg → SymExpr}
    (hlk : ∀ x, (lookup x).snapsLt bound) (m : Addr) {ca : ConstAddr}
    (hca : toConstAddr lookup m = some ca) : ca.snapsLt bound := by
  unfold toConstAddr at hca
  split at hca
  · cases hca
  · simp only [Option.some.injEq] at hca; subst hca
    cases m.base with
    | none => trivial
    | some b => cases b with
      | ctx => trivial
      | v x => exact SymExpr.norm_snapsLt (hlk x)

theorem stepSrcRhs_sound {st : SegState} {ρ₁₀ ρ₁ ρ₂ : Env} {mem₀ mem₁ mem₂ : X86.Memory}
    {ctx : Word} {snaps : MemSnaps} {r : Rhs} {v : Word}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hr : r.eval ρ₁ mem₁ ctx = some v) :
    let (e, st') := stepSrcRhs st r
    ∃ snaps',
      SegInv st' ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps' ∧
      e.eval ρ₁₀ ctx snaps' = some v ∧
      e.snapsLt st'.snaps.size := by
  cases r with
  | arg a =>
      simp only [Rhs.eval] at hr
      have he := SymExpr.norm_sound (argToSym_eval h.srcEnvEval hr)
      have hlt := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt a)
      exact ⟨snaps, h, he, hlt⟩
  | bin o w a b =>
      simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
      obtain ⟨va, ha, vb, hb, ho⟩ := hr
      have hea := SymExpr.norm_sound (argToSym_eval h.srcEnvEval ha)
      have heb := SymExpr.norm_sound (argToSym_eval h.srcEnvEval hb)
      have hlta := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt a)
      have hltb := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt b)
      refine ⟨snaps, ?_, mkBin_sound hea heb ho, mkBin_snapsLt hlta hltb⟩
      refine { h with safeDivsOk := fun p hp => ?_ }
      dsimp only at hp
      split at hp
      · rename_i hdiv
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · refine ⟨vb, heb, hltb, ?_⟩
          rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hdiv
          rcases hdiv with rfl | rfl <;>
          · simp only [BinOp.eval] at ho
            split at ho
            · cases ho
            · rename_i hnz; simpa using hnz
        · exact h.safeDivsOk p hp
      · exact h.safeDivsOk p hp
  | load w ext m =>
      simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
      obtain ⟨va, hm, hld⟩ := hr
      have haddr := SymExpr.norm_sound (addrToSym_eval h.srcEnvEval hm)
      have haddr_lt := SymExpr.norm_snapsLt (addrToSym_snapsLt h.srcEnvLt m)
      have hca : ∀ c, toConstAddr (srcLookup st.srcEnv) m = some c → c.eval ρ₁₀ ctx snaps = some va :=
        fun c hc => toConstAddr_eval_src h.srcEnvEval hm hc
      have hread_ok : X86.Memory.rangeAllowed mem₀.readable va w.bytes = true := by
        have hperms := applyWrites_perms h.smem1Ok
        unfold loadWord X86.Memory.read? at hld
        by_cases hra : X86.Memory.rangeAllowed mem₁.readable va w.bytes = true
        · rw [← hperms.1]; exact hra
        · simp [hra] at hld
      have haux := SymMem.readAux_sound hca h.smem1Valid h.smem1Ok hld
      have haux_lt := readAux_suffix_snapsLt (w := w) (e := ext) (ca := toConstAddr (srcLookup st.srcEnv) m) h.smem1Lt
      simp only [stepSrcRhs, SymMem.read]
      cases hraw : SymMem.readAux w ext (toConstAddr (srcLookup st.srcEnv) m) st.smem1 with
      | inl fe =>
          rw [hraw] at haux haux_lt
          refine ⟨snaps, { h with safeReadsOk := fun p hp => ?_ }, SymExpr.norm_sound haux, SymExpr.norm_snapsLt haux_lt⟩
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨va, haddr, haddr_lt, hread_ok⟩
          · exact h.safeReadsOk p hp
      | inr ws =>
          rw [hraw] at haux haux_lt
          dsimp only
          obtain ⟨mws, hmws, hld_ws⟩ := haux
          have hin := SnapTable.intern_sound h.snapsCons h.snapsLtTab
            (fun wr hwr => ⟨(haux_lt wr hwr).1, (haux_lt wr hwr).2.1⟩) hmws
          generalize hint_eq : st.snaps.intern ws = pair at hin ⊢
          obtain ⟨id, snapsTab'⟩ := pair
          dsimp only at hin ⊢
          obtain ⟨snaps', hid, hle, hagree, hsid, hcons', hltTab'⟩ := hin
          have hlift := h.liftSnaps hle hagree hcons' hltTab'
          have haddr' : (addrToSym (srcLookup st.srcEnv) m).norm.eval ρ₁₀ ctx snaps' = some va := by
            rw [SymExpr.eval_snaps_congr hagree haddr_lt]; exact haddr
          have heval : (SymExpr.load id w ext (addrToSym (srcLookup st.srcEnv) m).norm.norm).eval ρ₁₀ ctx snaps' = some v := by
            simp only [SymExpr.eval, Option.bind_eq_bind, SymExpr.norm_sound haddr', Option.bind_some, hsid, hld_ws]
          refine ⟨snaps', { hlift with safeReadsOk := fun p hp => ?_ },
            SymExpr.norm_sound heval,
            SymExpr.norm_snapsLt ⟨hid, SymExpr.norm_snapsLt (SymExpr.snapsLt_mono hle haddr_lt)⟩⟩
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨va, haddr', SymExpr.snapsLt_mono hle haddr_lt, hread_ok⟩
          · exact hlift.safeReadsOk p hp
  | addr m =>
      simp only [Rhs.eval] at hr
      have he := SymExpr.norm_sound (addrToSym_eval h.srcEnvEval hr)
      have hlt := SymExpr.norm_snapsLt (addrToSym_snapsLt h.srcEnvLt m)
      exact ⟨snaps, h, he, hlt⟩
  | select c w a b t f =>
      simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      obtain ⟨va, ha, vb, hb, vt, ht, vf, hf, rfl⟩ := hr
      have he : (SymExpr.select c w (argToSym (srcLookup st.srcEnv) a) (argToSym (srcLookup st.srcEnv) b)
          (argToSym (srcLookup st.srcEnv) t) (argToSym (srcLookup st.srcEnv) f)).eval ρ₁₀ ctx snaps =
          some (if c.holds w va vb then vt else vf) := by
        simp only [SymExpr.eval, Option.bind_eq_bind, argToSym_eval h.srcEnvEval ha,
          argToSym_eval h.srcEnvEval hb, argToSym_eval h.srcEnvEval ht,
          argToSym_eval h.srcEnvEval hf, Option.bind_some]
      exact ⟨snaps, h, SymExpr.norm_sound he, SymExpr.norm_snapsLt
        ⟨argToSym_snapsLt h.srcEnvLt a, argToSym_snapsLt h.srcEnvLt b,
         argToSym_snapsLt h.srcEnvLt t, argToSym_snapsLt h.srcEnvLt f⟩⟩
  | test c w a b =>
      simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      obtain ⟨va, ha, vb, hb, rfl⟩ := hr
      have he : (SymExpr.test c w (argToSym (srcLookup st.srcEnv) a) (argToSym (srcLookup st.srcEnv) b)).eval ρ₁₀ ctx snaps =
          some (if c.holds w va vb then 1 else 0) := by
        simp only [SymExpr.eval, Option.bind_eq_bind, argToSym_eval h.srcEnvEval ha,
          argToSym_eval h.srcEnvEval hb, Option.bind_some]
      exact ⟨snaps, h, SymExpr.norm_sound he, SymExpr.norm_snapsLt
        ⟨argToSym_snapsLt h.srcEnvLt a, argToSym_snapsLt h.srcEnvLt b⟩⟩
  | bsr64 a =>
      simp only [Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
      obtain ⟨va, ha, hres⟩ := hr
      have hea := SymExpr.norm_sound (argToSym_eval h.srcEnvEval ha)
      have hlta := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt a)
      have hnz : va ≠ 0 := by
        split at hres
        · cases hres
        · rename_i hne; simpa using hne
      have he : (SymExpr.bsr64 (argToSym (srcLookup st.srcEnv) a).norm).eval ρ₁₀ ctx snaps = some v := by
        simp only [SymExpr.eval, Option.bind_eq_bind, hea, Option.bind_some, hres]
      refine ⟨snaps, { h with safeBsrsOk := fun e' he' => ?_ }, SymExpr.norm_sound he, SymExpr.norm_snapsLt hlta⟩
      simp only [List.mem_cons] at he'
      rcases he' with rfl | he'
      · exact ⟨va, hea, hlta, hnz⟩
      · exact h.safeBsrsOk e' he'

theorem stepSrcLimb_sound {st : SegState} {ρ₁₀ ρ₁ ρ₂ : Env} {mem₀ mem₁ mem₂ : X86.Memory}
    {ctx : Word} {snaps : MemSnaps} {op : LimbOp} {v1 v2 : Word}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hop : op.eval ρ₁ = some (v1, v2)) :
    let (e1, e2, st') := stepSrcLimb st op
    SegInv st' ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps ∧
    e1.eval ρ₁₀ ctx snaps = some v1 ∧ e2.eval ρ₁₀ ctx snaps = some v2 ∧
    e1.snapsLt st'.snaps.size ∧ e2.snapsLt st'.snaps.size := by
  cases op with
  | mulWide64 a b =>
      simp only [LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨va, ha, vb, hb, rfl, rfl⟩ := hop
      have hea := SymExpr.norm_sound (argToSym_eval h.srcEnvEval ha)
      have heb := SymExpr.norm_sound (argToSym_eval h.srcEnvEval hb)
      have hlta := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt a)
      have hltb := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt b)
      exact ⟨h,
        mkBin_sound hea heb (by simp [BinOp.eval, X86.Encode.truncate64]),
        SymExpr.norm_sound (by simp [SymExpr.eval, hea, heb]),
        mkBin_snapsLt hlta hltb, SymExpr.norm_snapsLt ⟨hlta, hltb⟩⟩
  | divWide64 hi lo d =>
      simp only [LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hop
      obtain ⟨vhi, hhi, vlo, hlo, vd, hd, hres⟩ := hop
      split at hres
      · cases hres
      · rename_i hok
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hok
        simp only [Option.some.injEq, Prod.mk.injEq] at hres
        obtain ⟨rfl, rfl⟩ := hres
        have hehi := SymExpr.norm_sound (argToSym_eval h.srcEnvEval hhi)
        have helo := SymExpr.norm_sound (argToSym_eval h.srcEnvEval hlo)
        have hed := SymExpr.norm_sound (argToSym_eval h.srcEnvEval hd)
        have hlthi := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt hi)
        have hltlo := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt lo)
        have hltd := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt d)
        have hlt_ok : vhi.toNat < vd.toNat := Nat.lt_of_not_le hok.2
        refine ⟨{ h with safeDivWidesOk := fun p hp => ?_ },
          SymExpr.norm_sound (by simp [SymExpr.eval, hehi, helo, hed]; exact ⟨hok.1, hlt_ok⟩),
          SymExpr.norm_sound (by simp [SymExpr.eval, hehi, helo, hed]; exact ⟨hok.1, hlt_ok⟩),
          SymExpr.norm_snapsLt ⟨hlthi, hltlo, hltd⟩, SymExpr.norm_snapsLt ⟨hlthi, hltlo, hltd⟩⟩
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨vhi, vd, hehi, hed, hlthi, hltd, hok.1, hlt_ok⟩
        · exact h.safeDivWidesOk p hp
  | addCarry64 a b c =>
      simp only [LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨va, ha, vb, hb, vc, hc, rfl, rfl⟩ := hop
      have hea := SymExpr.norm_sound (argToSym_eval h.srcEnvEval ha)
      have heb := SymExpr.norm_sound (argToSym_eval h.srcEnvEval hb)
      have hec := SymExpr.norm_sound (argToSym_eval h.srcEnvEval hc)
      have hlta := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt a)
      have hltb := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt b)
      have hltc := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt c)
      exact ⟨h,
        SymExpr.norm_sound (by simp [SymExpr.eval, hea, heb, hec]),
        SymExpr.norm_sound (by simp [SymExpr.eval, hea, heb, hec]),
        SymExpr.norm_snapsLt ⟨hlta, hltb, hltc⟩, SymExpr.norm_snapsLt ⟨hlta, hltb, hltc⟩⟩
  | subBorrow64 a b c =>
      simp only [LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨va, ha, vb, hb, vc, hc, rfl, rfl⟩ := hop
      have hea := SymExpr.norm_sound (argToSym_eval h.srcEnvEval ha)
      have heb := SymExpr.norm_sound (argToSym_eval h.srcEnvEval hb)
      have hec := SymExpr.norm_sound (argToSym_eval h.srcEnvEval hc)
      have hlta := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt a)
      have hltb := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt b)
      have hltc := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt c)
      exact ⟨h,
        SymExpr.norm_sound (by simp [SymExpr.eval, hea, heb, hec]),
        SymExpr.norm_sound (by simp [SymExpr.eval, hea, heb, hec]),
        SymExpr.norm_snapsLt ⟨hlta, hltb, hltc⟩, SymExpr.norm_snapsLt ⟨hlta, hltb, hltc⟩⟩

theorem stepSrcStmt_sound {st : SegState} {ρ₁₀ ρ₁ ρ₁' ρ₂ : Env} {mem₀ mem₁ mem₁' mem₂ : X86.Memory}
    {ctx : Word} {snaps : MemSnaps} {s : Stmt}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hx : s.exec ρ₁ mem₁ ctx = some (ρ₁', mem₁')) :
    ∃ snaps', SegInv (stepSrcStmt st s) ρ₁₀ mem₀ ρ₁' mem₁' ρ₂ mem₂ ctx snaps' := by
  cases s with
  | assign x r =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨v, hr, rfl, rfl⟩ := hx
      have hstep := stepSrcRhs_sound h hr
      simp only [stepSrcStmt]
      generalize hsr : stepSrcRhs st r = pair at hstep ⊢
      obtain ⟨e, st'⟩ := pair
      obtain ⟨snaps', hinv', he, hlt⟩ := hstep
      refine ⟨snaps', { hinv' with
        srcEnvEval := fun y vy hy => by
          rw [env_insert_get] at hy
          unfold srcLookup Src.NatMap.getD
          rw [Src.NatMap.get?_insert]
          by_cases hyx : y = x
          · subst hyx; simp only [↓reduceIte, Option.some.injEq] at hy; subst hy
            simp only [↓reduceIte, Option.getD_some]; exact he
          · have hxy : x ≠ y := Ne.symm hyx
            simp only [hxy, ↓reduceIte] at hy
            simp only [hyx, ↓reduceIte]
            exact hinv'.srcEnvEval y vy hy
        srcEnvLt := fun y => by
          unfold srcLookup Src.NatMap.getD
          rw [Src.NatMap.get?_insert]
          by_cases hyx : y = x
          · subst hyx; simpa using hlt
          · simp only [hyx, ↓reduceIte]; exact hinv'.srcEnvLt y
        srcDefOk := fun y hy => by
          rw [natSet_contains_insert, Bool.or_eq_true, beq_iff_eq] at hy
          rw [env_insert_get]
          rcases hy with rfl | hy
          · simp
          · split
            · rfl
            · exact hinv'.srcDefOk y hy }⟩
  | limb r1 r2 op =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨⟨v1, v2⟩, hop, rfl, rfl⟩ := hx
      have hstep := stepSrcLimb_sound h hop
      simp only [stepSrcStmt]
      generalize hsl : stepSrcLimb st op = triple at hstep ⊢
      obtain ⟨e1, e2, st'⟩ := triple
      obtain ⟨hinv', he1, he2, hlt1, hlt2⟩ := hstep
      refine ⟨snaps, { hinv' with
        srcEnvEval := fun y vy hy => by
          rw [env_insert_get] at hy
          unfold srcLookup Src.NatMap.getD
          rw [Src.NatMap.get?_insert]
          by_cases hy2 : y = r2
          · subst hy2; simp only [↓reduceIte, Option.some.injEq] at hy; subst hy
            simp only [↓reduceIte, Option.getD_some]; exact he2
          · have h2y : r2 ≠ y := Ne.symm hy2
            simp only [h2y, ↓reduceIte] at hy
            simp only [hy2, ↓reduceIte]
            rw [env_insert_get] at hy
            rw [Src.NatMap.get?_insert]
            by_cases hy1 : y = r1
            · subst hy1; simp only [↓reduceIte, Option.some.injEq] at hy; subst hy
              simp only [↓reduceIte, Option.getD_some]; exact he1
            · have h1y : r1 ≠ y := Ne.symm hy1
              simp only [h1y, ↓reduceIte] at hy
              simp only [hy1, ↓reduceIte]
              exact hinv'.srcEnvEval y vy hy
        srcEnvLt := fun y => by
          unfold srcLookup Src.NatMap.getD
          rw [Src.NatMap.get?_insert]
          by_cases hy2 : y = r2
          · subst hy2; simpa using hlt2
          · simp only [hy2, ↓reduceIte]
            rw [Src.NatMap.get?_insert]
            by_cases hy1 : y = r1
            · subst hy1; simpa using hlt1
            · simp only [hy1, ↓reduceIte]; exact hinv'.srcEnvLt y
        srcDefOk := fun y hy => by
          rw [natSet_contains_insert, natSet_contains_insert, Bool.or_eq_true, Bool.or_eq_true,
            beq_iff_eq, beq_iff_eq] at hy
          rw [env_insert_get, env_insert_get]
          rcases hy with rfl | rfl | hy
          · simp
          · split <;> simp
          · split
            · rfl
            · split
              · rfl
              · exact hinv'.srcDefOk y hy }⟩
  | store w m a =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
      obtain ⟨va, hm, vv, ha, hwr⟩ := hx
      by_cases hwa : X86.Memory.rangeAllowed mem₁.writable va w.bytes = true
      · simp only [X86.Memory.write?, hwa, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hwr
        obtain ⟨rfl, rfl⟩ := hwr
        have hperms := applyWrites_perms h.smem1Ok
        have hwa0 : X86.Memory.rangeAllowed mem₀.writable va w.bytes = true := by
          rw [← hperms.2]; exact hwa
        have haddr := SymExpr.norm_sound (addrToSym_eval h.srcEnvEval hm)
        have haddr_lt := SymExpr.norm_snapsLt (addrToSym_snapsLt h.srcEnvLt m)
        have hval := SymExpr.norm_sound (argToSym_eval h.srcEnvEval ha)
        have hval_lt := SymExpr.norm_snapsLt (argToSym_snapsLt h.srcEnvLt a)
        have hca : ∀ c, toConstAddr (srcLookup st.srcEnv) m = some c → c.eval ρ₁₀ ctx snaps = some va :=
          fun c hc => toConstAddr_eval_src h.srcEnvEval hm hc
        obtain ⟨m', hm', hweq⟩ := dropShadowed_sound (w := w) (vv := vv) hca h.smem1Valid h.smem1Ok
        refine ⟨snaps, { h with
          smem1Ok := by
            simp only [stepSrcStmt, SymMem.write, applyWrites, Option.bind_eq_bind, hm',
              SymExpr.norm_sound haddr, SymExpr.norm_sound hval, Option.bind_some, hweq]
          smem1Valid := fun wr hmem => by
            simp only [stepSrcStmt, SymMem.write, List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact ⟨va, vv, SymExpr.norm_sound haddr, SymExpr.norm_sound hval, hca⟩
            · exact dropShadowed_valid h.smem1Valid wr hmem
          smem1Lt := fun wr hmem => by
            simp only [stepSrcStmt, SymMem.write, List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact ⟨SymExpr.norm_snapsLt haddr_lt, SymExpr.norm_snapsLt hval_lt,
                fun c hc => toConstAddr_snapsLt h.srcEnvLt m hc⟩
            · exact dropShadowed_snapsLt h.smem1Lt wr hmem
          safeWritesOk := fun p hp => by
            simp only [stepSrcStmt, List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact ⟨va, haddr, haddr_lt, hwa0⟩
            · exact h.safeWritesOk p hp }⟩
      · simp [X86.Memory.write?, hwa] at hwr
  | call _ _ _ => simp [Stmt.exec] at hx

theorem stepSrcList_sound {ρ₁₀ ρ₂ : Env} {mem₀ mem₂ : X86.Memory} {ctx : Word}
    {seg : List Stmt} {st : SegState} {ρ₁ ρ₁' : Env} {mem₁ mem₁' : X86.Memory} {snaps : MemSnaps}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hx : execList ρ₁ mem₁ ctx seg = some (ρ₁', mem₁')) :
    ∃ snaps', SegInv (stepSrcList st seg) ρ₁₀ mem₀ ρ₁' mem₁' ρ₂ mem₂ ctx snaps' := by
  induction seg generalizing st ρ₁ mem₁ snaps with
  | nil =>
      simp only [execList, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx; exact ⟨snaps, h⟩
  | cons s rest ih =>
      simp only [execList] at hx
      cases hs : s.exec ρ₁ mem₁ ctx with
      | none => rw [hs] at hx; cases hx
      | some p =>
          rw [hs] at hx
          obtain ⟨snaps1, h1⟩ := stepSrcStmt_sound h hs
          exact ih h1 hx

/-! ## Stepping target statements (`stepTgtStmt_sound`, `stepTgtList_sound`, `stepTotalTgtList_sound`) -/

private theorem isSafeDiv_sound {st : SegState} {ρ₁₀ ρ₁ ρ₂ : Env} {mem₀ mem₁ mem₂ : X86.Memory}
    {ctx : Word} {snaps : MemSnaps} {w : Width} {eb : SymExpr} {vb : Word}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hsafe : isSafeDiv st w eb = true) (heb : eb.eval ρ₁₀ ctx snaps = some vb) :
    w.truncate vb ≠ 0 := by
  unfold isSafeDiv at hsafe
  rw [Bool.or_eq_true, Bool.or_eq_true] at hsafe
  rcases hsafe with (himm | hlist) | hrng
  · cases eb with
    | imm k =>
        simp only [SymExpr.eval, Option.some.injEq] at heb; subst heb
        simpa [bne] using himm
    | _ => cases himm
  · rw [List.any_eq_true] at hlist
    obtain ⟨⟨w', d'⟩, hmem, hchk⟩ := hlist
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    obtain ⟨hw, heq⟩ := hchk
    obtain ⟨vd, hvd, _, hnz⟩ := h.safeDivsOk (w', d') hmem
    rw [hw] at hnz
    have := exprEquiv_sound heq hvd heb
    rw [← this]; exact hnz
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrng
    obtain ⟨rfl, hpos⟩ := hrng
    have hr := rangeOf_sound h.factsHold heb
    simp only [URange.Contains] at hr
    rw [X86.Encode.truncate64]
    intro h0; have := congrArg UInt64.toNat h0; simp at this; omega

private theorem isSafeBsr_sound {st : SegState} {ρ₁₀ ρ₁ ρ₂ : Env} {mem₀ mem₁ mem₂ : X86.Memory}
    {ctx : Word} {snaps : MemSnaps} {ea : SymExpr} {va : Word}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hsafe : isSafeBsr st ea = true) (hea : ea.eval ρ₁₀ ctx snaps = some va) :
    va ≠ 0 := by
  unfold isSafeBsr at hsafe
  rw [Bool.or_eq_true, Bool.or_eq_true] at hsafe
  rcases hsafe with (himm | hlist) | hrng
  · cases ea with
    | imm k =>
        simp only [SymExpr.eval, Option.some.injEq] at hea; subst hea
        simpa [bne] using himm
    | _ => cases himm
  · rw [List.any_eq_true] at hlist
    obtain ⟨a', hmem, heq⟩ := hlist
    obtain ⟨va', hva', _, hnz⟩ := h.safeBsrsOk a' hmem
    have := exprEquiv_sound heq hva' hea
    rw [← this]; exact hnz
  · simp only [decide_eq_true_eq] at hrng
    have hr := rangeOf_sound h.factsHold hea
    simp only [URange.Contains] at hr
    intro h0; have := congrArg UInt64.toNat h0; simp at this; omega

private theorem isSafeDivWide_sound {st : SegState} {ρ₁₀ ρ₁ ρ₂ : Env} {mem₀ mem₁ mem₂ : X86.Memory}
    {ctx : Word} {snaps : MemSnaps} {ehi ed : SymExpr} {vhi vd : Word}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hsafe : isSafeDivWide st ehi ed = true)
    (hhi : ehi.eval ρ₁₀ ctx snaps = some vhi) (hd : ed.eval ρ₁₀ ctx snaps = some vd) :
    vd.toNat ≠ 0 ∧ vhi.toNat < vd.toNat := by
  unfold isSafeDivWide at hsafe
  rw [Bool.or_eq_true] at hsafe
  rcases hsafe with himm | hlist
  · cases ehi with
    | imm k1 =>
        cases ed with
        | imm k2 =>
            simp only [SymExpr.eval, Option.some.injEq] at hhi hd; subst hhi hd
            simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at himm
            exact himm
        | _ => cases himm
    | _ => cases himm
  · rw [List.any_eq_true] at hlist
    obtain ⟨⟨hi', d'⟩, hmem, hchk⟩ := hlist
    simp only [Bool.and_eq_true] at hchk
    obtain ⟨vhi', vd', hhi', hd', _, _, hnz, hlt⟩ := h.safeDivWidesOk (hi', d') hmem
    rw [← exprEquiv_sound hchk.1 hhi' hhi, ← exprEquiv_sound hchk.2 hd' hd]
    exact ⟨hnz, hlt⟩

private theorem isSafeLoad_sound {st : SegState} {ρ₁₀ ρ₁ ρ₂ : Env} {mem₀ mem₁ mem₂ : X86.Memory}
    {ctx : Word} {snaps : MemSnaps} {w : Width} {addr : SymExpr} {va : Word}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hsafe : isSafeLoad st w addr = true) (haddr : addr.eval ρ₁₀ ctx snaps = some va) :
    X86.Memory.rangeAllowed mem₂.readable va w.bytes = true := by
  unfold isSafeLoad at hsafe
  rw [List.any_eq_true] at hsafe
  obtain ⟨⟨w', a'⟩, hmem, hchk⟩ := hsafe
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨hw, heq⟩ := hchk
  obtain ⟨va', hva', _, hok⟩ := h.safeReadsOk (w', a') hmem
  rw [hw] at hok
  have hveq := exprEquiv_sound heq hva' haddr
  have hperms := applyWrites_perms h.smem2Ok
  rw [hperms.1, ← hveq]; exact hok

private theorem isSafeStore_sound {st : SegState} {ρ₁₀ ρ₁ ρ₂ : Env} {mem₀ mem₁ mem₂ : X86.Memory}
    {ctx : Word} {snaps : MemSnaps} {w : Width} {addr : SymExpr} {va : Word}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hsafe : isSafeStore st w addr = true) (haddr : addr.eval ρ₁₀ ctx snaps = some va) :
    X86.Memory.rangeAllowed mem₂.writable va w.bytes = true := by
  unfold isSafeStore at hsafe
  rw [List.any_eq_true] at hsafe
  obtain ⟨⟨w', a'⟩, hmem, hchk⟩ := hsafe
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨hw, heq⟩ := hchk
  obtain ⟨va', hva', _, hok⟩ := h.safeWritesOk (w', a') hmem
  rw [hw] at hok
  have hveq := exprEquiv_sound heq hva' haddr
  have hperms := applyWrites_perms h.smem2Ok
  rw [hperms.2, ← hveq]; exact hok

private theorem segInv_insert_tgt {st : SegState} {ρ₁₀ ρ₁ ρ₂ : Env} {mem₀ mem₁ mem₂ : X86.Memory}
    {ctx : Word} {snaps : MemSnaps} {y : VReg} {v : Word} {e : SymExpr}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (he : e.eval ρ₁₀ ctx snaps = some v) (hlt : e.snapsLt st.snaps.size) :
    SegInv { st with tgtEnv := st.tgtEnv.insert y e } ρ₁₀ mem₀ ρ₁ mem₁ (ρ₂.insert y v) mem₂ ctx snaps :=
  { h with
    tgtEnvEval := fun z ez hz => by
      rw [Src.NatMap.get?_insert] at hz
      rw [env_insert_get]
      by_cases hzy : z = y
      · subst hzy; simp only [↓reduceIte, Option.some.injEq] at hz; subst hz; exact ⟨v, by simp, he⟩
      · simp only [hzy, ↓reduceIte] at hz
        have hyz : y ≠ z := Ne.symm hzy
        simp only [hyz, ↓reduceIte]
        exact h.tgtEnvEval z ez hz
    tgtEnvLt := fun z ez hz => by
      rw [Src.NatMap.get?_insert] at hz
      by_cases hzy : z = y
      · subst hzy; simp only [↓reduceIte, Option.some.injEq] at hz; subst hz; exact hlt
      · simp only [hzy, ↓reduceIte] at hz; exact h.tgtEnvLt z ez hz }

theorem stepTgtStmt_sound {st st' : SegState} {ρ₁₀ ρ₁ ρ₂ : Env} {mem₀ mem₁ mem₂ : X86.Memory}
    {ctx : Word} {snaps : MemSnaps} {s : Stmt}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hstep : stepTgtStmt st s = some st') :
    ∃ ρ₂' mem₂' snaps',
      s.exec ρ₂ mem₂ ctx = some (ρ₂', mem₂') ∧
      SegInv st' ρ₁₀ mem₀ ρ₁ mem₁ ρ₂' mem₂' ctx snaps' := by
  cases s with
  | assign y r =>
      cases r with
      | arg a =>
          simp only [stepTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨ea, hea, rfl⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound h.tgtEnvEval hea
          have hlta := evalTgtArg_snapsLt h.tgtEnvLt hea
          exact ⟨ρ₂.insert y va, mem₂, snaps, by simp [Stmt.exec, Rhs.eval, hva],
            segInv_insert_tgt h (SymExpr.norm_sound heva) (SymExpr.norm_snapsLt hlta)⟩
      | bin o w a b =>
          simp only [stepTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
          obtain ⟨ea, hea, eb, heb, hrest⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound h.tgtEnvEval hea
          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound h.tgtEnvEval heb
          have hlta := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt hea)
          have hltb := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt heb)
          split at hrest
          · cases hrest
          · rename_i hok
            simp only [Option.some.injEq] at hrest; subst hrest
            have heval_bin : ∃ v, o.eval w va vb = some v := by
              cases o with
              | udiv | urem =>
                  cases hsafe : isSafeDiv st w eb.norm with
                  | false => simp [hsafe] at hok
                  | true =>
                      have hnz := isSafeDiv_sound h hsafe (SymExpr.norm_sound hevb)
                      have hnzb : (w.truncate vb == 0) = false := beq_false_of_ne hnz
                      exact ⟨_, by simp [BinOp.eval, hnzb]; rfl⟩
              | add | sub | and | or | xor | mul | shl | shr | sar | rol | ror =>
                  exact ⟨_, by simp [BinOp.eval]; rfl⟩
            obtain ⟨v, hv⟩ := heval_bin
            exact ⟨ρ₂.insert y v, mem₂, snaps, by simp [Stmt.exec, Rhs.eval, hva, hvb, hv],
              segInv_insert_tgt h (mkBin_sound (SymExpr.norm_sound heva) (SymExpr.norm_sound hevb) hv)
                (mkBin_snapsLt hlta hltb)⟩
      | load w ext m =>
          simp only [stepTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
          obtain ⟨⟨addr, ca⟩, haddr_eq, hrest⟩ := hstep
          obtain ⟨va, hm, haddr_ev, hca⟩ := evalTgtAddr_sound h.tgtEnvEval haddr_eq
          obtain ⟨haddr_lt, _⟩ := evalTgtAddr_snapsLt h.tgtEnvLt haddr_eq
          split at hrest
          · cases hrest
          · rename_i hnsafe
            have hsafe : isSafeLoad st w addr = true := by simpa using hnsafe
            have hra := isSafeLoad_sound h hsafe haddr_ev
            obtain ⟨v, hld⟩ : ∃ v, loadWord mem₂ w ext va = some v := by
              cases ext <;> exact ⟨_, by simp [loadWord, X86.Memory.read?, hra]; rfl⟩
            have haux := SymMem.readAux_sound hca h.smem2Valid h.smem2Ok hld
            have haux_lt := readAux_suffix_snapsLt (w := w) (e := ext) (ca := ca) h.smem2Lt
            simp only [SymMem.read] at hrest
            cases hraw : SymMem.readAux w ext ca st.smem2 with
            | inl fe =>
                rw [hraw] at haux haux_lt hrest
                simp only [Option.some.injEq] at hrest; subst hrest
                exact ⟨ρ₂.insert y v, mem₂, snaps, by simp [Stmt.exec, Rhs.eval, hm, hld],
                  segInv_insert_tgt h (SymExpr.norm_sound haux) (SymExpr.norm_snapsLt haux_lt)⟩
            | inr ws =>
                rw [hraw] at haux haux_lt hrest
                dsimp only at hrest
                obtain ⟨mws, hmws, hld_ws⟩ := haux
                have hin := SnapTable.intern_sound h.snapsCons h.snapsLtTab
                  (fun wr hwr => ⟨(haux_lt wr hwr).1, (haux_lt wr hwr).2.1⟩) hmws
                generalize hint_eq : st.snaps.intern ws = pair at hin hrest
                obtain ⟨id, snapsTab'⟩ := pair
                dsimp only at hin hrest
                obtain ⟨snaps', hid, hle, hagree, hsid, hcons', hltTab'⟩ := hin
                simp only [Option.some.injEq] at hrest; subst hrest
                have hlift := h.liftSnaps hle hagree hcons' hltTab'
                have haddr' : addr.eval ρ₁₀ ctx snaps' = some va := by
                  rw [SymExpr.eval_snaps_congr hagree haddr_lt]; exact haddr_ev
                have heval : (SymExpr.load id w ext addr.norm).eval ρ₁₀ ctx snaps' = some v := by
                  simp only [SymExpr.eval, Option.bind_eq_bind, SymExpr.norm_sound haddr', Option.bind_some, hsid, hld_ws]
                exact ⟨ρ₂.insert y v, mem₂, snaps', by simp [Stmt.exec, Rhs.eval, hm, hld],
                  segInv_insert_tgt hlift (SymExpr.norm_sound heval)
                    (SymExpr.norm_snapsLt ⟨hid, SymExpr.norm_snapsLt (SymExpr.snapsLt_mono hle haddr_lt)⟩)⟩
      | addr m =>
          simp only [stepTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨⟨addr, ca⟩, haddr_eq, rfl⟩ := hstep
          obtain ⟨va, hm, haddr_ev, _⟩ := evalTgtAddr_sound h.tgtEnvEval haddr_eq
          obtain ⟨haddr_lt, _⟩ := evalTgtAddr_snapsLt h.tgtEnvLt haddr_eq
          exact ⟨ρ₂.insert y va, mem₂, snaps, by simp [Stmt.exec, Rhs.eval, hm],
            segInv_insert_tgt h haddr_ev haddr_lt⟩
      | select c w a b t f =>
          simp only [stepTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨ea, hea, eb, heb, et, het, ef, hef, rfl⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound h.tgtEnvEval hea
          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound h.tgtEnvEval heb
          obtain ⟨vt, hvt, hevt⟩ := evalTgtArg_sound h.tgtEnvEval het
          obtain ⟨vf, hvf, hevf⟩ := evalTgtArg_sound h.tgtEnvEval hef
          have he : (SymExpr.select c w ea eb et ef).eval ρ₁₀ ctx snaps = some (if c.holds w va vb then vt else vf) := by
            simp [SymExpr.eval, heva, hevb, hevt, hevf]
          exact ⟨ρ₂.insert y (if c.holds w va vb then vt else vf), mem₂, snaps,
            by simp [Stmt.exec, Rhs.eval, hva, hvb, hvt, hvf],
            segInv_insert_tgt h (SymExpr.norm_sound he)
              (SymExpr.norm_snapsLt ⟨evalTgtArg_snapsLt h.tgtEnvLt hea, evalTgtArg_snapsLt h.tgtEnvLt heb,
                evalTgtArg_snapsLt h.tgtEnvLt het, evalTgtArg_snapsLt h.tgtEnvLt hef⟩)⟩
      | test c w a b =>
          simp only [stepTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨ea, hea, eb, heb, rfl⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound h.tgtEnvEval hea
          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound h.tgtEnvEval heb
          have he : (SymExpr.test c w ea eb).eval ρ₁₀ ctx snaps = some (if c.holds w va vb then 1 else 0) := by
            simp [SymExpr.eval, heva, hevb]
          exact ⟨ρ₂.insert y (if c.holds w va vb then 1 else 0), mem₂, snaps,
            by simp [Stmt.exec, Rhs.eval, hva, hvb],
            segInv_insert_tgt h (SymExpr.norm_sound he)
              (SymExpr.norm_snapsLt ⟨evalTgtArg_snapsLt h.tgtEnvLt hea, evalTgtArg_snapsLt h.tgtEnvLt heb⟩)⟩
      | bsr64 a =>
          simp only [stepTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
          obtain ⟨ea, hea, hrest⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound h.tgtEnvEval hea
          have hlta := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt hea)
          split at hrest
          · cases hrest
          · rename_i hnsafe
            have hsafe : isSafeBsr st ea.norm = true := by simpa using hnsafe
            simp only [Option.some.injEq] at hrest; subst hrest
            have hnz := isSafeBsr_sound h hsafe (SymExpr.norm_sound heva)
            have he : (SymExpr.bsr64 ea.norm).eval ρ₁₀ ctx snaps = some (UInt64.ofNat va.toNat.log2) := by
              simp [SymExpr.eval, SymExpr.norm_sound heva, hnz]
            exact ⟨ρ₂.insert y (UInt64.ofNat va.toNat.log2), mem₂, snaps,
              by simp [Stmt.exec, Rhs.eval, hva, hnz],
              segInv_insert_tgt h (SymExpr.norm_sound he) (SymExpr.norm_snapsLt hlta)⟩
  | limb r1 r2 op =>
      cases op with
      | mulWide64 a b =>
          simp only [stepTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨ea, hea, eb, heb, rfl⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound h.tgtEnvEval hea
          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound h.tgtEnvEval heb
          have hlta := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt hea)
          have hltb := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt heb)
          have h1 := segInv_insert_tgt (y := r1) (v := va * vb) h
            (mkBin_sound (o := .mul) (w := .w64) (SymExpr.norm_sound heva) (SymExpr.norm_sound hevb)
              (by simp [BinOp.eval, X86.Encode.truncate64]))
            (mkBin_snapsLt hlta hltb)
          have h2 := segInv_insert_tgt (y := r2) (v := UInt64.ofNat ((va.toNat * vb.toNat) / 2 ^ 64)) h1
            (SymExpr.norm_sound (e := .mulHi ea.norm eb.norm)
              (by simp [SymExpr.eval, SymExpr.norm_sound heva, SymExpr.norm_sound hevb]))
            (SymExpr.norm_snapsLt ⟨hlta, hltb⟩)
          exact ⟨_, mem₂, snaps, by simp [Stmt.exec, LimbOp.eval, hva, hvb], h2⟩
      | divWide64 hi lo d =>
          simp only [stepTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
          obtain ⟨ehi, hhi, elo, hlo, ed, hd, hrest⟩ := hstep
          obtain ⟨vhi, hvhi, hevhi⟩ := evalTgtArg_sound h.tgtEnvEval hhi
          obtain ⟨vlo, hvlo, hevlo⟩ := evalTgtArg_sound h.tgtEnvEval hlo
          obtain ⟨vd, hvd, hevd⟩ := evalTgtArg_sound h.tgtEnvEval hd
          have hlthi := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt hhi)
          have hltlo := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt hlo)
          have hltd := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt hd)
          split at hrest
          · cases hrest
          · rename_i hnsafe
            have hsafe : isSafeDivWide st ehi.norm ed.norm = true := by simpa using hnsafe
            simp only [Option.some.injEq] at hrest; subst hrest
            obtain ⟨hnz, hlt⟩ := isSafeDivWide_sound h hsafe (SymExpr.norm_sound hevhi) (SymExpr.norm_sound hevd)
            let qv := UInt64.ofNat ((vhi.toNat * 2 ^ 64 + vlo.toNat) / vd.toNat)
            let rv := UInt64.ofNat ((vhi.toNat * 2 ^ 64 + vlo.toNat) % vd.toNat)
            have h1 := segInv_insert_tgt (y := r1) (v := qv) h
              (SymExpr.norm_sound (e := .divQ ehi.norm elo.norm ed.norm)
                (by simp [SymExpr.eval, SymExpr.norm_sound hevhi, SymExpr.norm_sound hevlo, SymExpr.norm_sound hevd, qv]; exact ⟨hnz, hlt⟩))
              (SymExpr.norm_snapsLt ⟨hlthi, hltlo, hltd⟩)
            have h2 := segInv_insert_tgt (y := r2) (v := rv) h1
              (SymExpr.norm_sound (e := .divR ehi.norm elo.norm ed.norm)
                (by simp [SymExpr.eval, SymExpr.norm_sound hevhi, SymExpr.norm_sound hevlo, SymExpr.norm_sound hevd, rv]; exact ⟨hnz, hlt⟩))
              (SymExpr.norm_snapsLt ⟨hlthi, hltlo, hltd⟩)
            have hexec : Stmt.exec ρ₂ mem₂ ctx (.limb r1 r2 (.divWide64 hi lo d)) = some ((ρ₂.insert r1 qv).insert r2 rv, mem₂) := by
              simp [Stmt.exec, LimbOp.eval, hvhi, hvlo, hvd, qv, rv, hnz, Nat.not_le.mpr hlt]
            exact ⟨_, mem₂, snaps, hexec, h2⟩
      | addCarry64 a b c =>
          simp only [stepTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨ea, hea, eb, heb, ec, hec, rfl⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound h.tgtEnvEval hea
          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound h.tgtEnvEval heb
          obtain ⟨vc, hvc, hevc⟩ := evalTgtArg_sound h.tgtEnvEval hec
          have hlta := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt hea)
          have hltb := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt heb)
          have hltc := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt hec)
          let cin : Nat := if vc == 0 then 0 else 1
          have h1 := segInv_insert_tgt (y := r1) (v := va + vb + UInt64.ofNat cin) h
            (SymExpr.norm_sound (e := .addCLo ea.norm eb.norm ec.norm)
              (by simp [SymExpr.eval, SymExpr.norm_sound heva, SymExpr.norm_sound hevb, SymExpr.norm_sound hevc, cin]))
            (SymExpr.norm_snapsLt ⟨hlta, hltb, hltc⟩)
          have h2 := segInv_insert_tgt (y := r2) (v := if 2 ^ 64 ≤ va.toNat + vb.toNat + cin then 1 else 0) h1
            (SymExpr.norm_sound (e := .addCHi ea.norm eb.norm ec.norm)
              (by simp [SymExpr.eval, SymExpr.norm_sound heva, SymExpr.norm_sound hevb, SymExpr.norm_sound hevc, cin]))
            (SymExpr.norm_snapsLt ⟨hlta, hltb, hltc⟩)
          exact ⟨_, mem₂, snaps, by simp [Stmt.exec, LimbOp.eval, hva, hvb, hvc, cin], h2⟩
      | subBorrow64 a b c =>
          simp only [stepTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨ea, hea, eb, heb, ec, hec, rfl⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound h.tgtEnvEval hea
          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound h.tgtEnvEval heb
          obtain ⟨vc, hvc, hevc⟩ := evalTgtArg_sound h.tgtEnvEval hec
          have hlta := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt hea)
          have hltb := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt heb)
          have hltc := SymExpr.norm_snapsLt (evalTgtArg_snapsLt h.tgtEnvLt hec)
          let bin : Nat := if vc == 0 then 0 else 1
          have h1 := segInv_insert_tgt (y := r1) (v := va - vb - UInt64.ofNat bin) h
            (SymExpr.norm_sound (e := .subBLo ea.norm eb.norm ec.norm)
              (by simp [SymExpr.eval, SymExpr.norm_sound heva, SymExpr.norm_sound hevb, SymExpr.norm_sound hevc, bin]))
            (SymExpr.norm_snapsLt ⟨hlta, hltb, hltc⟩)
          have h2 := segInv_insert_tgt (y := r2) (v := if va.toNat < vb.toNat + bin then 1 else 0) h1
            (SymExpr.norm_sound (e := .subBHi ea.norm eb.norm ec.norm)
              (by simp [SymExpr.eval, SymExpr.norm_sound heva, SymExpr.norm_sound hevb, SymExpr.norm_sound hevc, bin]))
            (SymExpr.norm_snapsLt ⟨hlta, hltb, hltc⟩)
          exact ⟨_, mem₂, snaps, by simp [Stmt.exec, LimbOp.eval, hva, hvb, hvc, bin], h2⟩
  | store w m a =>
      simp only [stepTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
      obtain ⟨⟨addr, ca⟩, haddr_eq, val, hval_eq, hrest⟩ := hstep
      obtain ⟨va, hm, haddr_ev, hca⟩ := evalTgtAddr_sound h.tgtEnvEval haddr_eq
      obtain ⟨haddr_lt, hca_lt⟩ := evalTgtAddr_snapsLt h.tgtEnvLt haddr_eq
      obtain ⟨vv, ha, hval_ev⟩ := evalTgtArg_sound h.tgtEnvEval hval_eq
      have hval_lt := evalTgtArg_snapsLt h.tgtEnvLt hval_eq
      split at hrest
      · cases hrest
      · rename_i hnsafe
        have hsafe : isSafeStore st w addr = true := by simpa using hnsafe
        simp only [Option.some.injEq] at hrest; subst hrest
        have hwa := isSafeStore_sound h hsafe haddr_ev
        obtain ⟨m', hm', hweq⟩ := dropShadowed_sound (w := w) (vv := vv) hca h.smem2Valid h.smem2Ok
        refine ⟨ρ₂, mem₂.write w va vv, snaps, by simp [Stmt.exec, hm, ha, X86.Memory.write?, hwa],
          { h with
            smem2Ok := by
              simp only [SymMem.write, applyWrites, Option.bind_eq_bind, hm',
                SymExpr.norm_sound haddr_ev, SymExpr.norm_sound (SymExpr.norm_sound hval_ev),
                Option.bind_some, hweq]
            smem2Valid := fun wr hmem => by
              simp only [SymMem.write, List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact ⟨va, vv, SymExpr.norm_sound haddr_ev, SymExpr.norm_sound (SymExpr.norm_sound hval_ev), hca⟩
              · exact dropShadowed_valid h.smem2Valid wr hmem
            smem2Lt := fun wr hmem => by
              simp only [SymMem.write, List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact ⟨SymExpr.norm_snapsLt haddr_lt, SymExpr.norm_snapsLt (SymExpr.norm_snapsLt hval_lt), hca_lt⟩
              · exact dropShadowed_snapsLt h.smem2Lt wr hmem }⟩
  | call _ _ _ => simp [stepTgtStmt] at hstep

theorem stepTgtList_sound {ρ₁₀ ρ₁ : Env} {mem₀ mem₁ : X86.Memory} {ctx : Word} :
    ∀ {seg : List Stmt} {st st' : SegState} {ρ₂ : Env} {mem₂ : X86.Memory} {snaps : MemSnaps},
      SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps →
      stepTgtList st seg = some st' →
      ∃ ρ₂' mem₂' snaps',
        execList ρ₂ mem₂ ctx seg = some (ρ₂', mem₂') ∧
        SegInv st' ρ₁₀ mem₀ ρ₁ mem₁ ρ₂' mem₂' ctx snaps'
  | [], st, st', ρ₂, mem₂, snaps, h, hstep => by
      simp only [stepTgtList, Option.some.injEq] at hstep; subst hstep
      exact ⟨ρ₂, mem₂, snaps, rfl, h⟩
  | s :: rest, st, st', ρ₂, mem₂, snaps, h, hstep => by
      simp only [stepTgtList, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
      obtain ⟨st1, h1, h2⟩ := hstep
      obtain ⟨ρ₂1, mem₂1, snaps1, hx1, hinv1⟩ := stepTgtStmt_sound h h1
      obtain ⟨ρ₂', mem₂', snaps', hx2, hinv'⟩ := stepTgtList_sound hinv1 h2
      exact ⟨ρ₂', mem₂', snaps', by simp [execList, hx1, hx2], hinv'⟩

/-- Stepping a pure total preheader statement succeeds without modifying memory. -/
theorem stepTotalTgtStmt_sound {ρ₁₀ ρ₂ : Env} {mem : X86.Memory} {ctx : Word} {snaps : MemSnaps}
    {tgtEnv tgtEnv' : Src.NatMap SymExpr} {s : Stmt}
    (htgt : ∀ y ey, tgtEnv.get? y = some ey → ∃ v, ρ₂[y]? = some v ∧ ey.eval ρ₁₀ ctx snaps = some v)
    (hstep : stepTotalTgtStmt tgtEnv s = some tgtEnv') :
    s.isCall = false ∧
    ∃ ρ₂', s.exec ρ₂ mem ctx = some (ρ₂', mem) ∧
      ∀ y ey, tgtEnv'.get? y = some ey → ∃ v, ρ₂'[y]? = some v ∧ ey.eval ρ₁₀ ctx snaps = some v := by
  have hins : ∀ (m : Src.NatMap SymExpr) (ρ : Env) (z : VReg) (v : Word) (e : SymExpr),
      (∀ y ey, m.get? y = some ey → ∃ vy, ρ[y]? = some vy ∧ ey.eval ρ₁₀ ctx snaps = some vy) →
      e.eval ρ₁₀ ctx snaps = some v →
      ∀ y ey, (m.insert z e).get? y = some ey →
        ∃ vy, (ρ.insert z v)[y]? = some vy ∧ ey.eval ρ₁₀ ctx snaps = some vy := by
    intro m ρ z v e hm he y ey hy
    rw [Src.NatMap.get?_insert] at hy
    rw [env_insert_get]
    by_cases hyz : y = z
    · subst hyz; simp only [↓reduceIte, Option.some.injEq] at hy; subst hy; exact ⟨v, by simp, he⟩
    · simp only [hyz, ↓reduceIte] at hy
      have hzy : z ≠ y := Ne.symm hyz
      simp only [hzy, ↓reduceIte]
      exact hm y ey hy
  cases s with
  | assign y r =>
      refine ⟨rfl, ?_⟩
      cases r with
      | arg a =>
          simp only [stepTotalTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨ea, hea, rfl⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound htgt hea
          exact ⟨ρ₂.insert y va, by simp [Stmt.exec, Rhs.eval, hva], hins _ _ _ _ _ htgt (SymExpr.norm_sound heva)⟩
      | bin o w a b =>
          simp only [stepTotalTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
          obtain ⟨ea, hea, eb, heb, hrest⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound htgt hea
          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound htgt heb
          have hbin_ok : (∃ v, o.eval w va vb = some v) ∧ tgtEnv.insert y (mkBin o w ea.norm eb.norm) = tgtEnv' := by
            cases hnb : eb.norm with
            | imm k =>
                rw [hnb] at hrest; dsimp only at hrest
                cases hok : (binOpIsTotal o || w.truncate k != 0) with
                | false => rw [hok] at hrest; cases hrest
                | true =>
                    rw [hok] at hrest
                    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hrest
                    refine ⟨?_, hrest⟩
                    rw [Bool.or_eq_true] at hok
                    rcases hok with htot | hnz
                    · cases o <;> simp [binOpIsTotal] at htot <;> simp [BinOp.eval]
                    · have heb' := SymExpr.norm_sound hevb
                      rw [hnb] at heb'; simp only [SymExpr.eval, Option.some.injEq] at heb'; subst heb'
                      have hne : w.truncate k ≠ 0 := by simpa [bne] using hnz
                      cases o <;> simp [BinOp.eval, hne]
            | _ =>
                rw [hnb] at hrest; dsimp only at hrest
                cases hok : binOpIsTotal o with
                | false => rw [hok] at hrest; cases hrest
                | true =>
                    rw [hok] at hrest
                    simp only [Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hrest
                    refine ⟨?_, hrest⟩
                    cases o <;> simp [binOpIsTotal] at hok <;> simp [BinOp.eval]
          obtain ⟨⟨v, hv⟩, rfl⟩ := hbin_ok
          exact ⟨ρ₂.insert y v, by simp [Stmt.exec, Rhs.eval, hva, hvb, hv],
            hins _ _ _ _ _ htgt (mkBin_sound (SymExpr.norm_sound heva) (SymExpr.norm_sound hevb) hv)⟩
      | addr m =>
          simp only [stepTotalTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨⟨addr, _⟩, haddr_eq, rfl⟩ := hstep
          obtain ⟨va, hm, haddr_ev, _⟩ := evalTgtAddr_sound htgt haddr_eq
          exact ⟨ρ₂.insert y va, by simp [Stmt.exec, Rhs.eval, hm], hins _ _ _ _ _ htgt haddr_ev⟩
      | select c w a b t f =>
          simp only [stepTotalTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨ea, hea, eb, heb, et, het, ef, hef, rfl⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound htgt hea
          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound htgt heb
          obtain ⟨vt, hvt, hevt⟩ := evalTgtArg_sound htgt het
          obtain ⟨vf, hvf, hevf⟩ := evalTgtArg_sound htgt hef
          exact ⟨ρ₂.insert y (if c.holds w va vb then vt else vf),
            by simp [Stmt.exec, Rhs.eval, hva, hvb, hvt, hvf],
            hins _ _ _ _ _ htgt (SymExpr.norm_sound (by simp [SymExpr.eval, heva, hevb, hevt, hevf]))⟩
      | test c w a b =>
          simp only [stepTotalTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨ea, hea, eb, heb, rfl⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound htgt hea
          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound htgt heb
          exact ⟨ρ₂.insert y (if c.holds w va vb then 1 else 0),
            by simp [Stmt.exec, Rhs.eval, hva, hvb],
            hins _ _ _ _ _ htgt (SymExpr.norm_sound (by simp [SymExpr.eval, heva, hevb]))⟩
      | bsr64 a =>
          simp only [stepTotalTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
          obtain ⟨ea, hea, hrest⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound htgt hea
          cases hna : ea.norm with
          | imm k =>
              rw [hna] at hrest; dsimp only at hrest
              have hea' := SymExpr.norm_sound heva
              rw [hna] at hea'; simp only [SymExpr.eval, Option.some.injEq] at hea'; subst hea'
              cases hnz : (k != 0) with
              | false => rw [hnz] at hrest; cases hrest
              | true =>
                  rw [hnz] at hrest; simp only [↓reduceIte, Option.some.injEq] at hrest; subst hrest
                  have hne : k ≠ 0 := by simpa [bne] using hnz
                  exact ⟨ρ₂.insert y (UInt64.ofNat k.toNat.log2),
                    by simp [Stmt.exec, Rhs.eval, hva, hne],
                    hins _ _ _ _ _ htgt rfl⟩
          | _ => rw [hna] at hrest; cases hrest
      | load _ _ _ => simp [stepTotalTgtStmt] at hstep
  | limb r1 r2 op =>
      refine ⟨rfl, ?_⟩
      cases op with
      | mulWide64 a b =>
          simp only [stepTotalTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨ea, hea, eb, heb, rfl⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound htgt hea
          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound htgt heb
          have h1 := hins _ _ r1 (va * vb) _ htgt
            (mkBin_sound (o := .mul) (w := .w64) (SymExpr.norm_sound heva) (SymExpr.norm_sound hevb)
              (by simp [BinOp.eval, X86.Encode.truncate64]))
          have h2 := hins _ _ r2 (UInt64.ofNat ((va.toNat * vb.toNat) / 2 ^ 64)) _ h1
            (SymExpr.norm_sound (e := .mulHi ea.norm eb.norm)
              (by simp [SymExpr.eval, SymExpr.norm_sound heva, SymExpr.norm_sound hevb]))
          exact ⟨_, by simp [Stmt.exec, LimbOp.eval, hva, hvb], h2⟩
      | addCarry64 a b c =>
          simp only [stepTotalTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨ea, hea, eb, heb, ec, hec, rfl⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound htgt hea
          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound htgt heb
          obtain ⟨vc, hvc, hevc⟩ := evalTgtArg_sound htgt hec
          let cin : Nat := if vc == 0 then 0 else 1
          have h1 := hins _ _ r1 (va + vb + UInt64.ofNat cin) _ htgt
            (SymExpr.norm_sound (e := .addCLo ea.norm eb.norm ec.norm)
              (by simp [SymExpr.eval, SymExpr.norm_sound heva, SymExpr.norm_sound hevb, SymExpr.norm_sound hevc, cin]))
          have h2 := hins _ _ r2 (if 2 ^ 64 ≤ va.toNat + vb.toNat + cin then 1 else 0) _ h1
            (SymExpr.norm_sound (e := .addCHi ea.norm eb.norm ec.norm)
              (by simp [SymExpr.eval, SymExpr.norm_sound heva, SymExpr.norm_sound hevb, SymExpr.norm_sound hevc, cin]))
          exact ⟨_, by simp [Stmt.exec, LimbOp.eval, hva, hvb, hvc, cin], h2⟩
      | subBorrow64 a b c =>
          simp only [stepTotalTgtStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstep
          obtain ⟨ea, hea, eb, heb, ec, hec, rfl⟩ := hstep
          obtain ⟨va, hva, heva⟩ := evalTgtArg_sound htgt hea
          obtain ⟨vb, hvb, hevb⟩ := evalTgtArg_sound htgt heb
          obtain ⟨vc, hvc, hevc⟩ := evalTgtArg_sound htgt hec
          let bin : Nat := if vc == 0 then 0 else 1
          have h1 := hins _ _ r1 (va - vb - UInt64.ofNat bin) _ htgt
            (SymExpr.norm_sound (e := .subBLo ea.norm eb.norm ec.norm)
              (by simp [SymExpr.eval, SymExpr.norm_sound heva, SymExpr.norm_sound hevb, SymExpr.norm_sound hevc, bin]))
          have h2 := hins _ _ r2 (if va.toNat < vb.toNat + bin then 1 else 0) _ h1
            (SymExpr.norm_sound (e := .subBHi ea.norm eb.norm ec.norm)
              (by simp [SymExpr.eval, SymExpr.norm_sound heva, SymExpr.norm_sound hevb, SymExpr.norm_sound hevc, bin]))
          exact ⟨_, by simp [Stmt.exec, LimbOp.eval, hva, hvb, hvc, bin], h2⟩
      | divWide64 _ _ _ => simp [stepTotalTgtStmt] at hstep
  | store _ _ _ => simp [stepTotalTgtStmt] at hstep
  | call _ _ _ => simp [stepTotalTgtStmt] at hstep

theorem stepTotalTgtList_sound {ρ₁₀ : Env} {mem : X86.Memory} {ctx : Word} {snaps : MemSnaps} :
    ∀ {ss : List Stmt} {tgtEnv tgtEnv' : Src.NatMap SymExpr} {ρ₂ : Env},
      (∀ y ey, tgtEnv.get? y = some ey → ∃ v, ρ₂[y]? = some v ∧ ey.eval ρ₁₀ ctx snaps = some v) →
      stepTotalTgtList tgtEnv ss = some tgtEnv' →
      (∀ s ∈ ss, s.isCall = false) ∧
      ∃ ρ₂', execList ρ₂ mem ctx ss = some (ρ₂', mem) ∧
        ∀ y ey, tgtEnv'.get? y = some ey → ∃ v, ρ₂'[y]? = some v ∧ ey.eval ρ₁₀ ctx snaps = some v
  | [], tgtEnv, tgtEnv', ρ₂, htgt, hstep => by
      simp only [stepTotalTgtList, Option.some.injEq] at hstep; subst hstep
      exact ⟨(fun _ h => by cases h), ρ₂, rfl, htgt⟩
  | s :: rest, tgtEnv, tgtEnv', ρ₂, htgt, hstep => by
      simp only [stepTotalTgtList, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
      obtain ⟨t1, h1, h2⟩ := hstep
      obtain ⟨hnc1, ρ₂1, hx1, htgt1⟩ := stepTotalTgtStmt_sound (mem := mem) htgt h1
      obtain ⟨hnc2, ρ₂', hx2, htgt'⟩ := stepTotalTgtList_sound (mem := mem) htgt1 h2
      refine ⟨fun s' hs' => ?_, ρ₂', by simp [execList, hx1, hx2], htgt'⟩
      simp only [List.mem_cons] at hs'
      rcases hs' with rfl | hs'
      · exact hnc1
      · exact hnc2 s' hs'

/-! ## Master segment theorem (`checkSeg_sound`) -/

/-- **Segment soundness:** if `checkSeg inv seg1 seg2 = some st` and `seg1` runs from
`(ρ₁₀, mem₀)` to `(ρ₁', mem₁)`, then `seg2` runs from `(ρ₂₀, mem₀)` to `(ρ₂', mem₁)`
with the **exact same final memory `mem₁`** and satisfies `SegInv`. -/
theorem checkSeg_sound {inv : BlockInv} {seg1 seg2 : List Stmt} {st : SegState}
    {ρ₁₀ ρ₁' ρ₂₀ : Env} {mem₀ mem₁ : X86.Memory} {ctx : Word}
    (hinv : inv.Holds ρ₁₀ ρ₂₀ ctx)
    (hchk : checkSeg inv seg1 seg2 = some st)
    (hx1 : execList ρ₁₀ mem₀ ctx seg1 = some (ρ₁', mem₁)) :
    ∃ ρ₂' snaps,
      execList ρ₂₀ mem₀ ctx seg2 = some (ρ₂', mem₁) ∧
      SegInv st ρ₁₀ mem₀ ρ₁' mem₁ ρ₂' mem₁ ctx snaps := by
  unfold checkSeg at hchk
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hchk
  obtain ⟨st2, htgt, hmem⟩ := hchk
  split at hmem
  · rename_i hmeq
    simp only [Option.some.injEq] at hmem; subst hmem
    have h0 := segInv_ofInv (mem₀ := mem₀) hinv
    obtain ⟨snaps1, h1⟩ := stepSrcList_sound h0 hx1
    obtain ⟨ρ₂', mem₂', snaps2, hx2, h2⟩ := stepTgtList_sound h1 htgt
    have heq_mem : mem₁ = mem₂' := writesEquiv_sound hmeq h2.smem1Ok h2.smem2Ok
    subst heq_mem
    exact ⟨ρ₂', snaps2, hx2, h2⟩
  · cases hmem

/-! ## Arguments, entailment, post-call, and entry invariant soundness -/

theorem checkArgEquiv_sound {st : SegState} {ρ₁₀ ρ₁ ρ₂ : Env} {mem₀ mem₁ mem₂ : X86.Memory}
    {ctx : Word} {snaps : MemSnaps} {a1 a2 : Arg} {v : Word}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hchk : checkArgEquiv st a1 a2 = true) (ha1 : a1.eval ρ₁ = some v) :
    a2.eval ρ₂ = some v := by
  unfold checkArgEquiv at hchk
  cases hg : evalTgtArg st.tgtEnv a2 with
  | none => rw [hg] at hchk; cases hchk
  | some e2 =>
      rw [hg] at hchk
      obtain ⟨v2, hv2, hev2⟩ := evalTgtArg_sound h.tgtEnvEval hg
      have hev1 := argToSym_eval h.srcEnvEval ha1
      have heq := exprEquivFacts_sound h.factsHold hchk hev1 hev2
      rw [← heq] at hv2; exact hv2

theorem checkArgsEquiv_sound {st : SegState} {ρ₁₀ ρ₁ ρ₂ : Env} {mem₀ mem₁ mem₂ : X86.Memory}
    {ctx : Word} {snaps : MemSnaps} (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps) :
    ∀ {as1 as2 : List Arg} {vs : List Word},
      checkArgsEquiv st as1 as2 = true → evalArgs ρ₁ as1 = some vs → evalArgs ρ₂ as2 = some vs
  | [], [], _, _, h1 => by simp only [evalArgs_nil, Option.some.injEq] at h1; subst h1; rfl
  | a1 :: r1, a2 :: r2, _, hchk, h1 => by
      simp only [checkArgsEquiv, Bool.and_eq_true] at hchk
      simp only [evalArgs_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h1
      obtain ⟨v, hv, vs, hvs, rfl⟩ := h1
      have hv2 := checkArgEquiv_sound h hchk.1 hv
      have hvs2 := checkArgsEquiv_sound h hchk.2 hvs
      simp [evalArgs_cons, hv2, hvs2]
  | [], _ :: _, _, hchk, _ | _ :: _, [], _, hchk, _ => by cases hchk

theorem checkEntails_sound {ρ₁₀ ρ₁ ρ₂ : Env} {ctx : Word} {snaps : MemSnaps}
    {srcEnv1 tgtEnv1 : Src.NatMap SymExpr} {srcDef1 : Src.NatSet}
    {allFacts : List PFact} {tgtInv : BlockInv}
    (hsrc : ∀ x v, ρ₁[x]? = some v → (srcLookup srcEnv1 x).eval ρ₁₀ ctx snaps = some v)
    (hdef : ∀ x, srcDef1.contains x = true → ρ₁[x]?.isSome = true)
    (htgt : ∀ y ey, tgtEnv1.get? y = some ey → ∃ v, ρ₂[y]? = some v ∧ ey.eval ρ₁₀ ctx snaps = some v)
    (hfacts : FactsHold ρ₁₀ ctx snaps allFacts)
    (hent : checkEntails srcEnv1 srcDef1 tgtEnv1 allFacts tgtInv = true) :
    tgtInv.Holds ρ₁ ρ₂ ctx := by
  unfold checkEntails at hent
  simp only [Bool.and_eq_true, List.all_eq_true] at hent
  obtain ⟨⟨⟨⟨hmf, hdefChk⟩, htgtChk⟩, hsrcChk⟩, hfactsChk⟩ := hent
  have hmf' := hmf
  simp only [BlockInv.isMemFree, Bool.and_eq_true, List.all_eq_true] at hmf'
  obtain ⟨⟨hmfTgt, hmfSrc⟩, hmfFacts⟩ := hmf'
  refine ⟨hmf, fun x hx => hdef x (hdefChk x hx), ?_, ?_, ?_⟩
  · intro ⟨y, expr⟩ hmem
    have hck := htgtChk (y, expr) hmem
    obtain ⟨⟨htot, hvars⟩, hmatch⟩ := hck
    cases hg : tgtEnv1.get? y with
    | none => rw [hg] at hmatch; cases hmatch
    | some ty =>
        rw [hg] at hmatch
        obtain ⟨v2, hv2, hty⟩ := htgt y ty hg
        obtain ⟨v1, hv1⟩ := SymExpr.eval_isTotal (snaps := snaps) htot (fun v hv => hdef v (hvars v hv))
        have hsub := SymExpr.eval_subst hsrc hv1
        have heq := exprEquivFacts_sound hfacts hmatch hsub hty
        rw [SymExpr.eval_isMemFree (snaps2 := fun _ => emptyMem) (hmfTgt (y, expr) hmem)] at hv1
        exact ⟨v2, hv2, by rw [← heq]; exact hv1⟩
  · intro ⟨x, expr⟩ hmem
    have hck := hsrcChk (x, expr) hmem
    obtain ⟨⟨⟨htot, hxdef⟩, hvars⟩, heqChk⟩ := hck
    have hx_is : ρ₁[x]?.isSome = true := hdef x hxdef
    cases hrx : ρ₁[x]? with
    | none => simp [hrx] at hx_is
    | some vx =>
        obtain ⟨v1, hv1⟩ := SymExpr.eval_isTotal (snaps := snaps) htot (fun v hv => hdef v (hvars v hv))
        have hsub := SymExpr.eval_subst hsrc hv1
        have heq := exprEquivFacts_sound hfacts heqChk (hsrc x vx hrx) hsub
        rw [SymExpr.eval_isMemFree (snaps2 := fun _ => emptyMem) (hmfSrc (x, expr) hmem)] at hv1
        exact ⟨vx, rfl, by rw [heq]; exact hv1⟩
  · intro f hf
    have hck := hfactsChk f hf
    obtain ⟨⟨⟨⟨hl_tot, hr_tot⟩, hl_vars⟩, hr_vars⟩, hcf⟩ := hck
    rw [beq_iff_eq] at hcf
    have hmf_f := hmfFacts f hf
    simp only [PFact.isMemFree, Bool.and_eq_true] at hmf_f
    obtain ⟨v1, hl⟩ := SymExpr.eval_isTotal (snaps := snaps) hl_tot (fun v hv => hdef v (hl_vars v hv))
    obtain ⟨v2, hr⟩ := SymExpr.eval_isTotal (snaps := snaps) hr_tot (fun v hv => hdef v (hr_vars v hv))
    have hc := condFromFacts_sound hfacts hcf (SymExpr.eval_subst hsrc hl) (SymExpr.eval_subst hsrc hr)
    rw [SymExpr.eval_isMemFree (snaps2 := fun _ => emptyMem) hmf_f.1] at hl
    rw [SymExpr.eval_isMemFree (snaps2 := fun _ => emptyMem) hmf_f.2] at hr
    exact ⟨v1, v2, hl, hr, hc⟩

theorem checkAfterCall_sound {st : SegState} {ρ₁₀ ρ₁ ρ₂ ρ₁' ρ₂' : Env}
    {mem₀ mem₁ mem₂ : X86.Memory} {ctx : Word} {snaps : MemSnaps}
    {rs : List VReg} {vals : List Word} {postInv : BlockInv}
    (h : SegInv st ρ₁₀ mem₀ ρ₁ mem₁ ρ₂ mem₂ ctx snaps)
    (hchk : checkAfterCall st rs postInv = true)
    (hb1 : bindParams ρ₁ rs vals = some ρ₁')
    (hb2 : bindParams ρ₂ rs vals = some ρ₂') :
    postInv.Holds ρ₁' ρ₂' ctx := by
  unfold checkAfterCall at hchk
  simp only [Bool.and_eq_true, List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨hmf, hdefChk⟩, htgtChk⟩, hsrcChk⟩, hfactsChk⟩ := hchk
  have hmf' := hmf
  simp only [BlockInv.isMemFree, Bool.and_eq_true, List.all_eq_true] at hmf'
  obtain ⟨⟨hmfTgt, hmfSrc⟩, hmfFacts⟩ := hmf'
  have hdef' : ∀ x, x ∉ rs → st.srcDef.contains x = true → ρ₁'[x]?.isSome = true := fun x hnr hd => by
    rw [bindParams_not_mem hb1 x hnr]; exact h.srcDefOk x hd
  refine ⟨hmf, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hc := hdefChk x hx
    rw [Bool.or_eq_true] at hc
    rcases hc with hmem | hsd
    · obtain ⟨v, hv1, _⟩ := bindParams_mem_eq hb1 hb2 x (by simpa using hmem)
      simp [hv1]
    · by_cases hmem : x ∈ rs
      · obtain ⟨v, hv1, _⟩ := bindParams_mem_eq hb1 hb2 x hmem; simp [hv1]
      · exact hdef' x hmem hsd
  · intro ⟨y, expr⟩ hmem
    have hck := htgtChk (y, expr) hmem
    split at hck
    · rename_i hself
      simp only [beq_iff_eq] at hself
      obtain ⟨rfl, hyr⟩ := hself
      obtain ⟨v, hv1, hv2⟩ := bindParams_mem_eq hb1 hb2 y (by simpa using hyr)
      exact ⟨v, hv2, hv1⟩
    · simp only [Bool.and_eq_true, List.all_eq_true] at hck
      obtain ⟨⟨⟨hynr, htot⟩, hvars⟩, hmatch⟩ := hck
      have hynr' : y ∉ rs := by simpa using hynr
      cases hg : st.tgtEnv.get? y with
      | none => rw [hg] at hmatch; cases hmatch
      | some ty =>
          rw [hg] at hmatch
          obtain ⟨v2, hv2, hty⟩ := h.tgtEnvEval y ty hg
          have hvars_def : ∀ v ∈ expr.vars, ρ₁'[v]?.isSome = true := fun v hv => by
            have hc := hvars v hv
            exact hdef' v (by simpa using hc.1) hc.2
          obtain ⟨v1, hv1⟩ := SymExpr.eval_isTotal (snaps := snaps) htot hvars_def
          have hsub : (expr.subst (srcLookup st.srcEnv)).eval ρ₁₀ ctx snaps = some v1 :=
            SymExpr.eval_subst_vars (fun v hv vv hvv => by
              have hc := hvars v hv
              rw [bindParams_not_mem hb1 v (by simpa using hc.1)] at hvv
              exact h.srcEnvEval v vv hvv) hv1
          have heq := exprEquivFacts_sound h.factsHold hmatch hsub hty
          rw [SymExpr.eval_isMemFree (snaps2 := fun _ => emptyMem) (hmfTgt (y, expr) hmem)] at hv1
          rw [bindParams_not_mem hb2 y hynr']
          exact ⟨v2, hv2, by rw [← heq]; exact hv1⟩
  · intro ⟨x, expr⟩ hmem
    have hck := hsrcChk (x, expr) hmem
    obtain ⟨⟨⟨⟨hxnr, htot⟩, hxdef⟩, hvars⟩, heqChk⟩ := hck
    have hxnr' : x ∉ rs := by simpa using hxnr
    have hx_is : ρ₁[x]?.isSome = true := h.srcDefOk x hxdef
    cases hrx : ρ₁[x]? with
    | none => simp [hrx] at hx_is
    | some vx =>
        have hvars_def : ∀ v ∈ expr.vars, ρ₁'[v]?.isSome = true := fun v hv => by
          have hc := hvars v hv
          exact hdef' v (by simpa using hc.1) hc.2
        obtain ⟨v1, hv1⟩ := SymExpr.eval_isTotal (snaps := snaps) htot hvars_def
        have hsub : (expr.subst (srcLookup st.srcEnv)).eval ρ₁₀ ctx snaps = some v1 :=
          SymExpr.eval_subst_vars (fun v hv vv hvv => by
            have hc := hvars v hv
            rw [bindParams_not_mem hb1 v (by simpa using hc.1)] at hvv
            exact h.srcEnvEval v vv hvv) hv1
        have heq := exprEquivFacts_sound h.factsHold heqChk (h.srcEnvEval x vx hrx) hsub
        rw [SymExpr.eval_isMemFree (snaps2 := fun _ => emptyMem) (hmfSrc (x, expr) hmem)] at hv1
        rw [bindParams_not_mem hb1 x hxnr']
        exact ⟨vx, hrx, by rw [heq]; exact hv1⟩
  · intro f hf
    have hck := hfactsChk f hf
    obtain ⟨⟨⟨hl_tot, hr_tot⟩, hvnr⟩, hcf⟩ := hck
    rw [beq_iff_eq] at hcf
    have hmf_f := hmfFacts f hf
    simp only [PFact.isMemFree, Bool.and_eq_true] at hmf_f
    obtain ⟨v1, hl⟩ := SymExpr.eval_isTotal (snaps := snaps) hl_tot (fun v hv => by
      have hc := hvnr v (by simp [PFact.vars, hv])
      exact hdef' v (by simpa using hc.1) hc.2)
    obtain ⟨v2, hr⟩ := SymExpr.eval_isTotal (snaps := snaps) hr_tot (fun v hv => by
      have hc := hvnr v (by simp [PFact.vars, hv])
      exact hdef' v (by simpa using hc.1) hc.2)
    have hl' : (f.lhs.subst (srcLookup st.srcEnv)).eval ρ₁₀ ctx snaps = some v1 :=
      SymExpr.eval_subst_vars (fun v hv vv hvv => by
        have hc := hvnr v (by simp [PFact.vars, hv])
        rw [bindParams_not_mem hb1 v (by simpa using hc.1)] at hvv
        exact h.srcEnvEval v vv hvv) hl
    have hr' : (f.rhs.subst (srcLookup st.srcEnv)).eval ρ₁₀ ctx snaps = some v2 :=
      SymExpr.eval_subst_vars (fun v hv vv hvv => by
        have hc := hvnr v (by simp [PFact.vars, hv])
        rw [bindParams_not_mem hb1 v (by simpa using hc.1)] at hvv
        exact h.srcEnvEval v vv hvv) hr
    have hc := condFromFacts_sound h.factsHold hcf hl' hr'
    rw [SymExpr.eval_isMemFree (snaps2 := fun _ => emptyMem) hmf_f.1] at hl
    rw [SymExpr.eval_isMemFree (snaps2 := fun _ => emptyMem) hmf_f.2] at hr
    exact ⟨v1, v2, hl, hr, hc⟩

theorem checkEntryInv_sound {params : List VReg} {vals : List Word} {ρ : Env} {ctx : Word}
    {inv : BlockInv}
    (hchk : checkEntryInv params inv = true)
    (hbp : bindParams {} params vals = some ρ) :
    inv.Holds ρ ρ ctx := by
  unfold checkEntryInv at hchk
  simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at hchk
  obtain ⟨⟨⟨⟨hmf, hseq⟩, hfacts⟩, hdef⟩, htgt⟩ := hchk
  refine ⟨hmf, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, hv, _⟩ := bindParams_mem_eq hbp hbp x (by simpa using hdef x hx)
    simp [hv]
  · intro ⟨y, e⟩ hmem
    have hck := htgt (y, e) hmem
    simp only [beq_iff_eq] at hck
    obtain ⟨rfl, hy⟩ := hck
    obtain ⟨v, hv, _⟩ := bindParams_mem_eq hbp hbp y (by simpa using hy)
    exact ⟨v, hv, hv⟩
  · intro p hp; rw [hseq] at hp; cases hp
  · intro f hf; rw [hfacts] at hf; cases hf

end IxCC.Lir.Opt
