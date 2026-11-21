import IxVMRefinement.Core.Specs.Whnf
import IxC.Kernel.Rules.Inversion

/-! # Telescope certificates up to reduction are certificates on a telescope

`certs_all` head-normalizes a telescope that is not syntactically a `∀` before reading the next
slot, so the walks' specs conclude `CertsR` (`Specs/Whnf.lean`): the rules' `Certs` with a `Red`
step allowed before any slot. On a telescope with a binder for every argument the extra steps
are identities, since a `∀` reduces only to itself (`Red.rigid`), and with no argument left the
walk is `Certs.nil`; so `CertsR` is `Certs` there (`CertsR.toCerts`). The rules that read a
walk (`Red.iota`, `Red.rescueK`, `Red.rescueEta`) walk stored telescopes, which have that many
binders by the environment's arity facts. -/

namespace IxVM.Refinement.Core.Specs.Whnf

open Ix.Kernel.Rules (Red Certs)

/-- Instantiating a bound variable keeps a telescope's leading `∀`s. -/
theorem stripPis_isSome_instantiate1 (v : KExpr) :
    ∀ (n : Nat) (e : KExpr) (k : Nat), (e.stripPis n).isSome = true →
      ((e.instantiate1 v k).stripPis n).isSome = true := by
  intro n
  induction n with
  | zero => intro e k _; simp [Ix.Kernel.Expr.stripPis]
  | succ n ih =>
    intro e k he
    cases e with
    | forallE ty b m =>
      simp only [Ix.Kernel.Expr.stripPis, Option.isSome_map] at he
      simp only [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.stripPis, Option.isSome_map]
      exact ih b (k + 1) he
    | _ => simp [Ix.Kernel.Expr.stripPis] at he

/-- Instantiating level parameters keeps a telescope's leading `∀`s. -/
theorem stripPis_isSome_instantiateLevelParams (ks : List Ix.Kernel.LevelParam) (us : List KLevel) :
    ∀ (n : Nat) (e : KExpr), (e.stripPis n).isSome = true →
      ((e.instantiateLevelParams ks us).stripPis n).isSome = true := by
  intro n
  induction n with
  | zero => intro e _; simp [Ix.Kernel.Expr.stripPis]
  | succ n ih =>
    intro e he
    cases e with
    | forallE ty b m =>
      simp only [Ix.Kernel.Expr.stripPis, Option.isSome_map] at he
      simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.stripPis,
        Option.isSome_map]
      exact ih b he
    | _ => simp [Ix.Kernel.Expr.stripPis] at he

/-- A telescope with `n` leading `∀`s has every fewer number of them. -/
theorem stripPis_isSome_of_le :
    ∀ {m n : Nat} {e : KExpr}, m ≤ n → (e.stripPis n).isSome = true →
      (e.stripPis m).isSome = true := by
  intro m
  induction m with
  | zero => intro n e _ _; simp [Ix.Kernel.Expr.stripPis]
  | succ m ih =>
    intro n e hmn he
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    cases e with
    | forallE ty b mb =>
      simp only [Ix.Kernel.Expr.stripPis, Option.isSome_map] at he ⊢
      exact ih (by omega) he
    | _ => simp [Ix.Kernel.Expr.stripPis] at he

/-- A telescope with a binder for one more argument is a `∀`. -/
theorem isSortOrPi_of_stripPis_succ {T : KExpr} {n : Nat}
    (h : (T.stripPis (n + 1)).isSome = true) : Ix.Kernel.Rules.isSortOrPi T = true := by
  cases T with
  | forallE => rfl
  | _ => simp [Ix.Kernel.Expr.stripPis] at h

/-- **A certificate up to reduction on a telescope with a binder for every argument is a
certificate**: a reduction step on a `∀` is the identity (`Red.rigid`), and with no argument left
the walk is `Certs.nil`. -/
theorem CertsR.toCerts {env : Ix.Kernel.Env .anon} {d : Nat} {lic : Bool} {T : KExpr}
    {zs : List KExpr} (hc : CertsR env d lic T zs) :
    (T.stripPis zs.length).isSome = true → Certs env d lic T zs := by
  induction hc with
  | nil => intro _; exact .nil
  | @skip ty body arg mb rest hl hn _ ih =>
    intro hs
    simp only [List.length_cons, Ix.Kernel.Expr.stripPis, Option.isSome_map] at hs
    exact .skip hl hn (ih (stripPis_isSome_instantiate1 arg _ body 0 hs))
  | @cert ty body arg ta mb rest hi hd _ ih =>
    intro hs
    simp only [List.length_cons, Ix.Kernel.Expr.stripPis, Option.isSome_map] at hs
    exact .cert hi hd (ih (stripPis_isSome_instantiate1 arg _ body 0 hs))
  | @red T T' zs hr _ ih =>
    intro hs
    cases zs with
    | nil => exact .nil
    | cons z zs =>
      have e := Red.rigid hr (isSortOrPi_of_stripPis_succ hs)
      subst e
      exact ih hs

end IxVM.Refinement.Core.Specs.Whnf
