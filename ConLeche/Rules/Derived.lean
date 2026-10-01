module

public import ConLeche.Rules.Rel

@[expose] public section

/-!
# The derived rules (task #305)

Theorems, not constructors: the shapes the bridge lands on at the
checker sites the constructors cover only up to `symm`, `refl` and
`trans` — the right-hand-side variants of the one-sided rules, the
spine congruence from the per-node one, the `Bool.true` shortcut, the
δ continuations, the string-literal arms.  Each names its checker site;
each is proved here, so a proof lane never re-derives one.
-/

namespace ConLeche.Rules

variable {env : Env}

/-! ## Spine algebra (local copies: the `Verify` tier's twins sit above
the fueled entry points, which this module does not import) -/

theorem Expr.mkAppN_append_one' (f : Expr) (l : List Expr) (a : Expr) :
    Expr.mkAppN f (l ++ [a]) = .app (Expr.mkAppN f l) a := by
  induction l generalizing f with
  | nil => rfl
  | cons x xs ih => simp [Expr.mkAppN, ih]

/-- An expression is its head applied to its spine. -/
theorem Expr.mkAppN_getApp' : ∀ (e : Expr),
    Expr.mkAppN e.getAppFn e.getAppArgs = e
  | .app f a => by
    simp only [Expr.getAppFn, Expr.getAppArgs, Expr.mkAppN_append_one']
    rw [Expr.mkAppN_getApp' f]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _
  | .forallE _ _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ => rfl

/-! ## `DefEqList` kit -/

theorem DefEqList.length {d : Nat} : ∀ {as bs : List Expr},
    DefEqList env d as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [DefEqList.length h]

theorem DefEqList.refl {d : Nat} : ∀ (as : List Expr), DefEqList env d as as
  | [] => .nil
  | _ :: as => .cons .refl (DefEqList.refl as)

theorem DefEqList.symm {d : Nat} : ∀ {as bs : List Expr},
    DefEqList env d as bs → DefEqList env d bs as
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h.symm hs.symm

/-! ## `Red` derived rules -/

/-- A string literal expands and re-reduces (`litMajorToCtor`'s and
`projLitToCtor`'s string arms, `Core.lean:736-738`, `:752-754`: `whnf
(strLitToConstructor s)`). -/
theorem Red.strLitWhnf {d : Nat} {s : String} {e' : Expr}
    (hsup : strLitSupported env = true)
    (h : Red env d (strLitToConstructor s) e') :
    Red env d (.lit (.strVal s)) e' :=
  .trans (.strLit hsup) h

/-- `litToCtorIfNat` on a whole term (`litMajorToCtor`'s non-string
arm, `Core.lean:739`): a reduction, the identity off a supported
`Nat` literal. -/
theorem Red.litToCtorIfNat {d : Nat} (e : Expr) :
    Red env d e (litToCtorIfNat env e) := by
  match e with
  | .lit (.natVal n) =>
    simp only [ConLeche.litToCtorIfNat]
    split
    · exact .natLit ‹_›
    · exact .refl
  | .lit (.strVal _) | .bvar _ | .fvar _ _ | .sort _ | .const _ _
  | .app _ _ | .lam _ _ _ | .forallE _ _ _ | .letE _ _ _ | .proj _ _ _ =>
    exact .refl

/-! ## `DefEq` derived rules -/

/-- A reduction is an equation (`refl` after the reduction). -/
theorem DefEq.ofRed {d : Nat} {a b : Expr} (h : Red env d a b) :
    DefEq env d a b :=
  .redL h .refl

/-- Reduce the right side, then continue (`whnfCore b`, `Core.lean:1467`;
the right-side literal and δ continuations). -/
theorem DefEq.redR {d : Nat} {a b b' : Expr}
    (h : Red env d b b') (h' : DefEq env d a b') : DefEq env d a b :=
  .symm (.redL h h'.symm)

/-- Head-normalise both sides, then continue (`Core.lean:1466-1467`). -/
theorem DefEq.redBoth {d : Nat} {a a' b b' : Expr}
    (ha : Red env d a a') (hb : Red env d b b') (h : DefEq env d a' b') :
    DefEq env d a b :=
  .redL ha (.redR hb h)

/-- **Unfold the left head, then continue** (the maintainer's example
of ruling 1; `defeqStep`'s one-sided and hint-guided unfoldings,
`Core.lean:1537-1545`, `:1551-1554`). -/
theorem DefEq.deltaL {d : Nat} {a a' b : Expr}
    (h : unfoldDefinition env a = some a') (h' : DefEq env d a' b) :
    DefEq env d a b :=
  .redL (.delta h) h'

/-- Unfold the right head, then continue (`Core.lean:1546-1549`,
`:1555-1558`). -/
theorem DefEq.deltaR {d : Nat} {a b b' : Expr}
    (h : unfoldDefinition env b = some b') (h' : DefEq env d a b') :
    DefEq env d a b :=
  .redR (.delta h) h'

/-- Unfold both heads, then continue (`Core.lean:1570-1577`). -/
theorem DefEq.deltaBoth {d : Nat} {a a' b b' : Expr}
    (ha : unfoldDefinition env a = some a') (hb : unfoldDefinition env b = some b')
    (h : DefEq env d a' b') : DefEq env d a b :=
  .deltaL ha (.deltaR hb h)

/-- **The `Bool.true` shortcut** (`boolTrueShortcut`, `Core.lean:1415-1424`,
at `defeqStep`'s entry `:1468-1471`): the left side reduces to the
constant `Bool.true` — `refl` after the reduction. -/
theorem DefEq.boolTrue {d : Nat} {a w : Expr}
    (h : Red env d a w) (hw : w.isBoolTrue = true) :
    DefEq env d a (.const boolTrueName []) := by
  have : w = .const boolTrueName [] := by
    match w, hw with
    | .const c [], hw =>
      simp only [Expr.isBoolTrue, beq_iff_eq] at hw
      rw [hw]
  subst this
  exact .ofRed h

/-- Two equal literals (`Core.lean:1582`). -/
theorem DefEq.lit {d : Nat} {l : Literal} : DefEq env d (.lit l) (.lit l) :=
  .refl

/-- `Nat.zero` against the packed zero (`Core.lean:1589-1591`). -/
theorem DefEq.natZeroR {d : Nat} :
    DefEq env d (.const natZeroName []) (.lit (.natVal 0)) :=
  .symm .natZero

/-- `Nat.succ x` against a packed successor (`Core.lean:1598-1603`):
unpack one layer and continue, with the checker's argument order. -/
theorem DefEq.natSuccR {d : Nat} {k : Nat} {x : Expr}
    (h : DefEq env d x (.lit (.natVal k))) :
    DefEq env d (.app (.const natSuccName []) x) (.lit (.natVal (k + 1))) :=
  .symm (.natSucc h.symm)

/-- A string literal on the left against a `String.ofList` application
(`Core.lean:1610-1613`): expand and continue. -/
theorem DefEq.strLitL {d : Nat} {s : String} {b : Expr}
    (hsup : strLitSupported env = true)
    (h : DefEq env d (strLitToConstructor s) b) :
    DefEq env d (.lit (.strVal s)) b :=
  .redL (.strLit hsup) h

/-- The mirror (`Core.lean:1614-1617`). -/
theorem DefEq.strLitR {d : Nat} {s : String} {a : Expr}
    (hsup : strLitSupported env = true)
    (h : DefEq env d a (strLitToConstructor s)) :
    DefEq env d a (.lit (.strVal s)) :=
  .redR (.strLit hsup) h

/-- η with the λ on the right (`Core.lean:1693-1696`: `etaCert ty₂ body₂
m₂ a₁`). -/
theorem DefEq.etaR {d : Nat} {a ta ty₁ B ty₂ body₂ : Expr} {m₁ m₂ : BinderMeta}
    (hi : Infer env .io d a ta) (hr : Red env d ta (.forallE ty₁ B m₁))
    (hty : DefEq env d ty₁ ty₂)
    (hbody : DefEq env (d + 1) (body₂.instantiate1 (.fvar d ty₂))
      (.app a (.fvar d ty₂)))
    (hpw : m₂.pw = m₁.pw) :
    DefEq env d a (.lam ty₂ body₂ m₂) :=
  .symm (.eta hi hr hty hbody hpw)

/-- Congruence along a spine: the head and the arguments pairwise. -/
theorem DefEq.mkAppN {d : Nat} : ∀ {as bs : List Expr} {f g : Expr},
    DefEq env d f g → DefEqList env d as bs →
    DefEq env d (Expr.mkAppN f as) (Expr.mkAppN g bs)
  | _, _, _, _, hfg, .nil => hfg
  | _, _, _, _, hfg, .cons hab hs => by
    simp only [Expr.mkAppN]
    exact DefEq.mkAppN (.app hfg hab) hs

/-- **The spine-wise application congruence** (`defeqStep`'s stuck
application arm, `Core.lean:1652-1678`; official `is_def_eq_app`):
equal spine lengths (implied), one head comparison, the argument lists
pairwise. -/
theorem DefEq.spine {d : Nat} {a b : Expr}
    (hf : DefEq env d a.getAppFn b.getAppFn)
    (hargs : DefEqList env d a.getAppArgs b.getAppArgs) :
    DefEq env d a b := by
  have h := DefEq.mkAppN hf hargs
  rwa [Expr.mkAppN_getApp', Expr.mkAppN_getApp'] at h

/-- **The same-head short-circuit** (`defeqSpine`, `Core.lean:1426-1458`, at `:1570`;
official `try_eq_const_app`): both heads the same constant at
equivalent levels, the spines pairwise. -/
theorem DefEq.constSpine {d : Nat} {a b : Expr} {n : Name} {us us' : List Level}
    (ha : a.getAppFn = .const n us) (hb : b.getAppFn = .const n us')
    (hus : Level.isEquivList us us' = some true)
    (hargs : DefEqList env d a.getAppArgs b.getAppArgs) :
    DefEq env d a b :=
  .spine (by rw [ha, hb]; exact .const hus) hargs

/-- Structure η with the constructor on the right (`stuckIrrel`'s
second arm, `Core.lean:539`: `structEtaCert b a`). -/
theorem DefEq.structEtaR {d : Nat} {a b : Expr} (h : DefEq env d b a) :
    DefEq env d a b :=
  h.symm

/-! ## Shape facts read off a derivation's conclusion -/

/-- The inferred type of a λ is a ∀ at the λ's own annotation
(`infer_lam_meta_copy`'s twin); the λ clause's chain case consumes it. -/
theorem Infer.lam_shape {g : Grade} {d : Nat} {ty body t : Expr}
    {mb : BinderMeta} (h : Infer env g d (.lam ty body mb) t) :
    ∃ bt, t = .forallE ty bt mb := by
  cases h with
  | lam _ _ _ _ _ _ _ => exact ⟨_, rfl⟩

end ConLeche.Rules
