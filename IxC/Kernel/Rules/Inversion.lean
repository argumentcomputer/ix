module

public import IxC.Kernel.Rules.Rel

@[expose] public section

/-!
# Inversions of the rules tier

What a derivation says about its subject's shape:

* **a sort or a `∀` reduces only to itself** (`Red.rigid`). Every reduction rule
  but `refl` and `trans` has an application, a constant, a literal or a projection
  on its left, or a constant head (`delta`, `deltaThm`, `eqProof`, `iota`), except
  the three rescues, whose subject is arbitrary. A rescue at a sort or a `∀` would
  need the subject's type, itself a sort, to reduce to a constant-headed
  application, which the same fact excludes; so the recursion runs through the
  rescues' type reduction.
* the inference rules inverted at a sort, a `∀`, a constant and an application at
  the full grade (`Infer.sort_inv`, `Infer.forallE_inv`, `Infer.const_inv`,
  `Infer.app_inv`).

They are what the pinned axioms' bit lemmas read over derivations
(`Model/JudgeRules.lean`, `axiomBits_rulesJ`).
-/

namespace Ix.Kernel.Rules

/-- A sort or a `∀`: the subjects no rule rewrites. -/
def isSortOrPi : Expr md → Bool
  | .sort _ | .forallE .. => true
  | _ => false

theorem isSortOrPi_getAppFn {e : Expr md} (h : isSortOrPi e = true) : e.getAppFn = e := by
  cases e <;> first | rfl | exact nomatch h

theorem isSortOrPi_false_of_head {e : Expr md} {c : Key md} {us : List Level}
    (h : e.getAppFn = .const c us) : isSortOrPi e = false := by
  cases e with
  | sort | forallE => exact nomatch h
  | _ => rfl

theorem unfoldDefinition_sortOrPi {env : Env md} {e : Expr md} (h : isSortOrPi e = true) :
    unfoldDefinition env e = none := by
  unfold unfoldDefinition
  rw [isSortOrPi_getAppFn h]
  cases e <;> first | rfl | exact nomatch h

/-- A sort or a `∀` infers a sort. -/
theorem Infer.sort_of_sortOrPi {env : Env md} {g : Grade} {d : Nat} {e t : Expr md}
    (h : Infer env g d e t) (he : isSortOrPi e = true) : ∃ u, t = .sort u := by
  cases h with
  | sort => exact ⟨_, rfl⟩
  | forallE => exact ⟨_, rfl⟩
  | _ => exact nomatch he

mutual

/-- **A sort or a `∀` reduces only to itself.** -/
theorem Red.rigid {env : Env md} :
    ∀ {d : Nat} {e e' : Expr md}, Red env d e e' → isSortOrPi e = true → e' = e
  | _, _, _, .refl, _ => rfl
  | _, _, _, .trans h₁ h₂, he => by
    have h1 := Red.rigid h₁ he
    exact (Red.rigid h₂ (h1 ▸ he)).trans h1
  | _, _, _, .appFn _, he => nomatch he
  | _, _, _, .projArg _, he => nomatch he
  | _, _, _, .appArg _, he => nomatch he
  | _, _, _, .betaGate _, he => nomatch he
  | _, _, _, .beta _ _, he => nomatch he
  | _, _, _, .delta hu, he => by
    rw [unfoldDefinition_sortOrPi he] at hu
    exact nomatch hu
  | _, _, _, .deltaThm .., he => nomatch he
  | _, _, _, .eqProof hhead .., he => by
    rw [isSortOrPi_false_of_head hhead] at he
    exact nomatch he
  | _, _, _, .natLit _, he => nomatch he
  | _, _, _, .natZeroLit _, he => nomatch he
  | _, _, _, .strLit _, he => nomatch he
  | _, _, _, .natSucc .., he => nomatch he
  | _, _, _, .natOp .., he => nomatch he
  | _, _, _, .natAddSucc .., he => nomatch he
  | _, _, _, .natAddZero .., he => nomatch he
  | _, _, _, .proj .., he => nomatch he
  | _, _, _, .iota hhead .., he => by
    rw [isSortOrPi_false_of_head hhead] at he
    exact nomatch he
  | _, _, _, .rescueK _ _ _ _ _ htm htmaj hthead .., he => by
    obtain ⟨u, hu⟩ := Infer.sort_of_sortOrPi htm he
    have h := Red.rigid htmaj (by cases hu; rfl)
    rw [h, hu] at hthead
    exact nomatch hthead
  | _, _, _, .rescueEta _ _ _ _ _ htm htmaj hthead .., he => by
    obtain ⟨u, hu⟩ := Infer.sort_of_sortOrPi htm he
    have h := Red.rigid htmaj (by cases hu; rfl)
    rw [h, hu] at hthead
    exact nomatch hthead
  | _, _, _, .rescueAnd _ _ _ _ htm htmaj hthead .., he => by
    obtain ⟨u, hu⟩ := Infer.sort_of_sortOrPi htm he
    have h := Red.rigid htmaj (by cases hu; rfl)
    rw [h, hu] at hthead
    exact nomatch hthead

theorem Red.rigid_defEq {env : Env md} :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → True
  | _, _, _, _ => trivial

theorem Red.rigid_infer {env : Env md} :
    ∀ {g : Grade} {d : Nat} {e t : Expr md}, Infer env g d e t → True
  | _, _, _, _, _ => trivial

theorem Red.rigid_certs {env : Env md} :
    ∀ {d : Nat} {lic : Bool} {ty : Expr md} {args : List (Expr md)},
      Certs env d lic ty args → True
  | _, _, _, _, _ => trivial

theorem Red.rigid_defEqList {env : Env md} :
    ∀ {d : Nat} {as bs : List (Expr md)}, DefEqList env d as bs → True
  | _, _, _, _ => trivial

theorem Red.rigid_etaProjCerts {env : Env md} :
    ∀ {d : Nat} {T : Key md} {us' : List Level} {targs : List (Expr md)} {b : Expr md}
      {lpsT : List LevelParam} {idxs : List Nat},
      EtaProjCerts env d T us' targs b lpsT idxs → True
  | _, _, _, _, _, _, _, _ => trivial

end

/-- A sort reduces only to itself. -/
theorem Red.sort_eq {env : Env md} {d : Nat} {u v : Level}
    (h : Red env d (.sort u) (.sort v)) : v = u :=
  Expr.sort.inj (Red.rigid h rfl)

/-! ## Inference, inverted -/

theorem Infer.sort_inv {env : Env md} {g : Grade} {d : Nat} {u : Level} {t : Expr md}
    (h : Infer env g d (.sort u) t) : t = .sort (.succ u) := by
  cases h
  rfl

theorem Infer.fvar_inv {env : Env md} {g : Grade} {d i : Nat} {ty t : Expr md}
    (h : Infer env g d (.fvar i ty) t) : t = ty := by
  cases h
  rfl

theorem Infer.const_inv {env : Env md} {g : Grade} {d : Nat} {n : Key md} {us : List Level}
    {t : Expr md} (h : Infer env g d (.const n us) t) :
    ∃ ci, env.find? n = some ci ∧ ci.isTowerEntry = false ∧
      us.length = ci.toConstantVal.levelParams.length ∧
      t = ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us := by
  cases h with
  | const hf ht hus => exact ⟨_, hf, ht, hus, rfl⟩

theorem Infer.forallE_inv {env : Env md} {g : Grade} {d : Nat} {ty body t : Expr md}
    {mb : BinderMeta} (h : Infer env g d (.forallE ty body mb) t) :
    ∃ s u bs v, Infer env g d ty s ∧ Red env d s (.sort u) ∧
      Infer env g (d + 1) (body.instantiate1 (.fvar d ty)) bs ∧
      Red env (d + 1) bs (.sort v) ∧ Level.zeronessOf v = mb.pw ∧
      t = .sort (.imax u v) := by
  cases h with
  | forallE hs hu hbs hv hz => exact ⟨_, _, _, _, hs, hu, hbs, hv, hz, rfl⟩

/-- An application at the full grade is the certified rule (`appSkip` is io only). -/
theorem Infer.app_inv {env : Env md} {d : Nat} {f a t : Expr md}
    (h : Infer env .full d (.app f a) t) :
    ∃ tf ty body mt ta, Infer env .full d f tf ∧ Red env d tf (.forallE ty body mt) ∧
      Infer env .full d a ta ∧ DefEq env d ta ty ∧ t = body.instantiate1 a := by
  cases h with
  | app htf hw hta hd => exact ⟨_, _, _, _, _, htf, hw, hta, hd, rfl⟩

end Ix.Kernel.Rules
