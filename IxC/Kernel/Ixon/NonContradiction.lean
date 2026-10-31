import IxC.Kernel.Ixon.Values
import IxC.Kernel.Verify.Rename.UnionJoin

/-!
# Non-contradiction, the IxC half (ALPHA-COLLAPSE §8.1, S1)

A refutation Source accepts and a proof a certificate's closure installs
cannot meet: there is no proposition `P` with a constant of type `¬P` in an
environment Source accepts and a constant of type `P` (renamed) in one the
certificate's closure installs, wherever the two lists can be joined.

**The route.**
1. The renaming walk (`Cached.AcceptsRef.rename`, step 7.3) takes Source's
   acceptance to its renaming by `f` (injective on Source's ids), an
   environment that answers each good key's lookup renamed.
2. The union (`Cached.AcceptsRef.union`, S1) joins the renamed Source list
   with the certificate's, both the prelude's front followed by units: one
   accepted list, whose environment answers every lookup either environment
   answers, as it does.
3. The union's environment has a model (`Cached.AcceptsRef.strongModel`,
   relative to a model of the set theory). In it the refutation, a member of
   what `P → False` denotes, applied to the proof, a member of what `P`
   denotes, is a member of what `False` denotes, the empty set
   (`Model.not_refuted_and_proved`).

`IsNegationOf` is syntactic: `T` is `.forallE P (.const falseName []) m`.
The theorem is general in `f`. Its union hypotheses (`UnitsOk`,
`UnitsAgree`, `Closed`, the operations) are the union's; among them,
`UnitsAgree` carries the agreement of a mutual or nested block's generated
records on the two sides.
-/

namespace Ix.Kernel

open SetTheory Ix.Kernel.SetModel

universe w

variable {md : Mode}

/-- **`T` is the negation of `P`**: `P → False`, syntactically. -/
def Expr.IsNegationOf (T P : Expr md) : Prop :=
  ∃ m : BinderMeta, T = .forallE P (.const falseName []) m

/-- **No model holds a refutation and a proof of one proposition**: a stored
constant of type `P → False` and a stored constant of type `P` cannot both be
members of what their types denote. -/
theorem Model.not_refuted_and_proved {V : Type w} [SetTheory V] {env : Env md}
    (M : Model V env) {r t : ConstantInfo md} (hr : r ∈ env.consts) (ht : t ∈ env.consts)
    {P : Expr md} (hneg : r.toConstantVal.type.IsNegationOf P)
    (htype : t.toConstantVal.type = P) : False := by
  obtain ⟨m, hm⟩ := hneg
  let φ : LevelParam → Nat := fun _ => 0
  let ρ : BVarIdx → V := fun _ => empty
  obtain ⟨T, hT, hrT⟩ := M.mem r hr φ ρ
  obtain ⟨A', hA', htA⟩ := M.mem t ht φ ρ
  rw [hm] at hT
  rw [htype] at hA'
  cases hT with
  | pi hA hB hP =>
    rename_i A B
    have hAA : A' = A := Denotes_functional hA' hA
    rw [hAA] at htA
    have hBe : ∀ x, x ∈ˢ A → B x = empty := fun x hx =>
      M.false_empty φ (push x ρ) (B x) (hB x hx)
    have happ := app_mem_piR hrT htA fun h0 x hx => by
      rw [← univ_zero]; exact hP h0 x hx
    rw [hBe _ htA] at happ
    exact not_mem_empty _ happ

/-- **Non-contradiction (IxC level).** Source's list `dsS`, accepted under
its evidence, renamed by `f` (injective on its ids), is the prelude's front
followed by units `usS`; the certificate's list is the same front followed by
units `usA`, accepted under its evidence; the two lists' units agree where
they share a base, both are closed in order, and the renamed Source list's
operations are the certificate's. Then no constant Source installs refutes
a proposition `P` whose renaming the type of a constant the certificate
installs is (relative to a model of the set theory `V`). -/
theorem nonContradiction (V : Type w) [SetTheory V] {f : Mode.Id .source → Mode.Id .anon}
    {S : Mode.Id .source → Prop} (hf : InjOn f S)
    {evS : Evidences .source} {dsS : List (Declaration .source)} {envS : Env .source}
    (hS : Cached.AcceptsRef .verified evS dsS envS)
    (hevS : evS.Good (KeyScope.ofId S)) (hdsS : ∀ d ∈ dsS, d.Good (KeyScope.ofId S))
    {evA : Evidences .anon} {front : List (Declaration .anon)}
    {usA usS : List (List (Declaration .anon))} {envA : Env .anon}
    (hA : Cached.AcceptsRef .verified evA (front ++ usA.flatten) envA)
    (hsplit : dsS.map (Declaration.mapKeys f) = front ++ usS.flatten)
    (huA : UnitsOk front usA) (huS : UnitsOk front usS) (hagree : UnitsAgree usA usS)
    (hcA : Closed (front ++ usA.flatten)) (hcS : Closed (front ++ usS.flatten))
    (hops : ∀ u ∈ usS, (∃ d ∈ u, ¬ d.NoOp) → u ∈ usA)
    {kr : Key .source} {r : ConstantInfo .source} (hr : envS.find? kr = some r)
    (hkr : kr.Good (KeyScope.ofId S)) {P : Expr .source}
    (hneg : r.toConstantVal.type.IsNegationOf P)
    {kt : Key .anon} {t : ConstantInfo .anon} (ht : envA.find? kt = some t)
    (htype : t.toConstantVal.type = P.mapKeys f) : False := by
  obtain ⟨envS', hS', hrel⟩ := Cached.AcceptsRef.rename .verified hf hevS hdsS hS
  rw [hsplit] at hS'
  obtain ⟨U, hU, hAU, hSU⟩ :=
    Cached.AcceptsRef.union hA hS' huA huS hagree hcA hcS hops
  obtain ⟨M⟩ := hU.strongModel V
  have hr' : envS'.find? (kr.map f) = some (r.mapKeys f) := by
    rw [hrel.find kr hkr, hr]; rfl
  have hrU := List.mem_of_find?_eq_some (hSU _ _ hr')
  have htU := List.mem_of_find?_eq_some (hAU _ _ ht)
  obtain ⟨m, hm⟩ := hneg
  refine Model.not_refuted_and_proved M.model hrU htU (P := P.mapKeys f) ⟨m, ?_⟩ htype
  rw [ConstantInfo.mapKeys_toConstantVal, ConstantVal.mapKeys_type, hm]
  rfl

end Ix.Kernel
