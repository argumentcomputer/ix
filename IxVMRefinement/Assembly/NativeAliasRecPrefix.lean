import IxVMRefinement.Assembly.NativeAliasTeleWalk
import IxC.Kernel.Model.Inductives.NativeAtRecLate

/-! # A recursor depends on the former's binders, not its residual

The block's `former_tele_at` inserts the computed sort after the requested binders, whereas
`nat_former_tele` keeps the residual expression. Their complete outputs need not be identical.
`PrefixEq` of the parameter and index binders suffices for equality of the generated recursor
type and rules, and hence transports `NativeRecRunJ` and `NativeRecJ` without changing the
stored recursor or the registered family's telescope. The operational producer of this prefix
relation is separate: these lemmas do not infer it from definitional equality.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel
open Ix.Kernel.Semantics
open IxVM.Refinement.Core

/-- Expose one pair of equal telescope binders. -/
theorem PrefixEq.succ_view {n : Nat} {E R : KExpr} (h : PrefixEq (n + 1) E R) :
    ∃ T B B' bm, E = .forallE T B bm ∧ R = .forallE T B' bm ∧ PrefixEq n B B' := by
  cases E <;> cases R <;> simp only [PrefixEq] at h
  all_goals try contradiction
  rename_i T B bm T' B' bm'
  obtain ⟨rfl, rfl, hr⟩ := h
  exact ⟨T, B, B', bm, rfl, rfl, hr⟩

/-- Forget a suffix of the common binder prefix. -/
theorem PrefixEq.take : ∀ (n m : Nat) {E R : KExpr},
    PrefixEq (n + m) E R → PrefixEq n E R
  | 0, _, _, _, _ => trivial
  | n + 1, m, E, R, h => by
    have h' : PrefixEq ((n + m) + 1) E R := by simpa only [Nat.succ_add, Nat.add_succ] using h
    obtain ⟨T, B, B', bm, rfl, rfl, hr⟩ := h'.succ_view
    exact ⟨rfl, rfl, PrefixEq.take n m hr⟩

/-- Stripping a common prefix keeps the same binders and the remaining common prefix. -/
theorem PrefixEq.strip : ∀ (n m : Nat) {E R : KExpr}, PrefixEq (n + m) E R →
    ∃ bs B B', E.stripPis n = some (bs, B) ∧ R.stripPis n = some (bs, B') ∧ PrefixEq m B B'
  | 0, _, E, R, h => ⟨[], E, R, rfl, rfl, by simpa only [Nat.zero_add] using h⟩
  | n + 1, m, E, R, h => by
    have h' : PrefixEq ((n + m) + 1) E R := by simpa only [Nat.succ_add, Nat.add_succ] using h
    obtain ⟨T, B, B', bm, rfl, rfl, hr⟩ := h'.succ_view
    obtain ⟨bs, C, C', hc, hc', heq⟩ := PrefixEq.strip n m hr
    exact ⟨(T, bm) :: bs, C, C', by simp [Expr.stripPis, hc],
      by simp [Expr.stripPis, hc'], heq⟩

/-- Lifting de Bruijn indices preserves equality of the binder prefix. -/
theorem PrefixEq.lift : ∀ (n : Nat) {E R : KExpr} (amount cutoff : Nat), PrefixEq n E R →
    PrefixEq n (E.liftLooseBVars amount cutoff) (R.liftLooseBVars amount cutoff)
  | 0, _, _, _, _, _ => trivial
  | n + 1, E, R, amount, cutoff, h => by
    obtain ⟨T, B, B', bm, rfl, rfl, hr⟩ := h.succ_view
    exact ⟨rfl, rfl, PrefixEq.lift n amount (cutoff + 1) hr⟩

/-- Replacing the residual depends only on the consumed binder prefix. -/
theorem PrefixEq.replacePisPw : ∀ {n : Nat} {E R : KExpr}, PrefixEq n E R →
    ∀ (pw : PropWhen) (body : KExpr), E.replacePisPw pw n body = R.replacePisPw pw n body
  | 0, _, _, _, _, _ => rfl
  | n + 1, E, R, h, pw, body => by
    obtain ⟨T, B, B', bm, rfl, rfl, hr⟩ := h.succ_view
    simp only [Expr.replacePisPw, hr.replacePisPw pw body]

/-- The rule's lambda prefix likewise ignores the residual expression. -/
theorem PrefixEq.pisToLamsPw : ∀ {n : Nat} {E R : KExpr}, PrefixEq n E R →
    ∀ (pw : PropWhen) (body : KExpr), E.pisToLamsPw pw n body = R.pisToLamsPw pw n body
  | 0, _, _, _, _, _ => rfl
  | n + 1, E, R, h, pw, body => by
    obtain ⟨T, B, B', bm, rfl, rfl, hr⟩ := h.succ_view
    simp only [Expr.pisToLamsPw, hr.pisToLamsPw pw body]

/-- Equal parameter and index binders give the same generated recursor type. -/
theorem PrefixEq.structRecTyR {nP nIdx : Nat} {E R : KExpr} (h : PrefixEq (nP + nIdx) E R)
    (T : Key .anon) (lps : List LevelParam) (elim : LevelParam) (large : Bool)
    (ctors : List (Key .anon × Nat × KExpr × List Nat)) :
    Ix.Kernel.structRecTyR T lps elim large nP nIdx E ctors =
      Ix.Kernel.structRecTyR T lps elim large nP nIdx R ctors := by
  obtain ⟨bs, B, B', hb, hb', hi⟩ := h.strip nP nIdx
  have hp := h.take nP nIdx
  unfold Ix.Kernel.structRecTyR
  rw [hb, hb']
  simp only [Option.bind_some, structMotiveTyI]
  simp_rw [hi.replacePisPw, (hi.lift nIdx (ctors.length + 1) 0).replacePisPw,
    hp.replacePisPw]

/-- Equal parameter and index binders give the same generated rule. -/
theorem PrefixEq.structRecRhsR {nP nIdx : Nat} {E R : KExpr} (h : PrefixEq (nP + nIdx) E R)
    (T : Key .anon) (lps : List LevelParam) (elim : LevelParam) (large : Bool)
    (ctors : List (Key .anon × Nat × KExpr × List Nat))
    (recC : Key .anon) (rlvls : List Level) (j : Nat) :
    Ix.Kernel.structRecRhsR T lps elim large nP nIdx E ctors recC rlvls j =
      Ix.Kernel.structRecRhsR T lps elim large nP nIdx R ctors recC rlvls j := by
  obtain ⟨bs, B, B', hb, hb', hi⟩ := h.strip nP nIdx
  have hp := h.take nP nIdx
  unfold Ix.Kernel.structRecRhsR
  split
  · rfl
  · rw [hb, hb']
    simp only [Option.bind_some, structMotiveTyI]
    simp_rw [hi.replacePisPw, hp.pisToLamsPw]

/-- Rule scoping checks are identical when the former binder prefixes agree. -/
theorem PrefixEq.checkNativeRules {nP nIdx : Nat} {E R : KExpr}
    (h : PrefixEq (nP + nIdx) E R) (envR : Env .anon) (rlps : List LevelParam)
    (T : Key .anon) (lps : List LevelParam) (elim : LevelParam) (large : Bool)
    (ctors : List (Key .anon × Nat × KExpr × List Nat)) (recC : Key .anon)
    (rlvls : List Level) : ∀ k j,
    Ix.Kernel.checkNativeRules (m := CheckM .anon) envR rlps T lps elim large nP nIdx E ctors recC rlvls k j =
      Ix.Kernel.checkNativeRules (m := CheckM .anon) envR rlps T lps elim large nP nIdx R ctors recC rlvls k j
  | 0, _ => rfl
  | k + 1, j => by
    simp only [Ix.Kernel.checkNativeRules, h.structRecRhsR, h.checkNativeRules envR rlps T lps elim large
      ctors recC rlvls k (j + 1)]

/-- Transfer the actual generated-type/rule check to the registered telescope using only
binder-prefix agreement. No equality of the residuals is required. -/
theorem NativeRecRunJ.of_prefix {J : Judgements .anon} {env : Env .anon}
    {p : NativeParts .anon} {cvTa cvTb cvRa : ConstantVal .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {rhss : List KExpr}
    (hprefix : PrefixEq (p.nP + p.nIdx) cvTa.type cvTb.type)
    (hrun : NativeRecRunJ J env p cvTa ctorsA cvRa rhss) :
    NativeRecRunJ J env p cvTb ctorsA cvRa rhss := by
  simpa only [NativeRecRunJ, hprefix.structRecTyR, hprefix.checkNativeRules] using hrun

/-- The stored-recursion relation has the same transport, preserving the stored record. -/
theorem NativeRecJ.of_prefix {J : Judgements .anon} {env : Env .anon}
    {p : NativeParts .anon} {cvTa cvTb cvRa : ConstantVal .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {rhss : List KExpr}
    (hprefix : PrefixEq (p.nP + p.nIdx) cvTa.type cvTb.type)
    (hrun : NativeRecJ J env p cvTa ctorsA cvRa rhss) :
    NativeRecJ J env p cvTb ctorsA cvRa rhss := by
  obtain ⟨cvRg, rhsG, hg, hs⟩ := hrun
  exact ⟨cvRg, rhsG, NativeRecRunJ.of_prefix hprefix hg, hs⟩

/-- The terminal expressions really may differ: no binders are inspected at depth zero. -/
example : PrefixEq 0 (.sort .zero) (.sort (.succ .zero)) := trivial

end IxVM.Refinement.Decl
