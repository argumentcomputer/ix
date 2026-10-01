module

public import ConLeche.Verify.Knot

public section

/-!
# `defeqStep`, inverted (task #305, lane B3)

`Model/Steps/DefEq.lean`'s `defeqStep_claim` (`:514`) and
`defeqStuck_claim` (`:873`) invert `defeqStep` INLINE, against their
own continuation contract; nothing in `ConLeche/Verify/` did, so the
defeq bridge would have had to invert it a third time.  This module is
the inversion on its own: the checker's case tree, read back as a
disjunction of the runs each exit made, with no model in sight.

Two statements.  `DefeqStuckExit` is the seventeen exits of the
**stuck tree** (`Core.lean:1580-1700`, the `match a', b'` that runs
once neither head unfolds) — sixteen shape-directed certificates and
the `stuckIrrel` fallback every non-firing arm takes, on the *same*
pair, which is why one disjunct covers them all.  `defeqStep_inv` is
the body's prefix: the syntactic fast path, the `Bool.true` shortcut,
the two `whnfCore` reducts, and then the nine ways the step can end —
proof irrelevance, the two literal accelerations, the three δ
materialisations, the same-head short-circuit, and the stuck tree.

The continuation `k` is opaque: an exit that calls it hands back the
call's own `.ok true`, which is what a fuel induction consumes.
-/

namespace ConLeche.Rules

variable {env : Env} {fuel : Nat}

/-- **The stuck tree's exits** (`defeqStep`, `Core.lean:1580-1700`, the
`match a', b'` that runs once neither head unfolds).  `fallback` is the
exit of every arm whose shape guard fails: they all call `stuckIrrel`
on the *same* pair, so one constructor stands for all of them.  The
other sixteen are the certificates the arms run, each at the shapes its
pattern pinned. -/
inductive DefeqStuckExit (env : Env) (fuel d : Nat) : Expr → Expr → Prop where
  /-- Every non-firing arm's fallback. -/
  | fallback {a b : Expr} :
      stuckIrrelFueled .verified env fuel d a b = .ok true →
      DefeqStuckExit env fuel d a b
  /-- `Core.lean:1581`: two sorts. -/
  | sort {u v : Level} :
      Level.isEquiv u v = some true →
      DefeqStuckExit env fuel d (.sort u) (.sort v)
  /-- `:1582`: two equal literals. -/
  | lit {l : Literal} : DefeqStuckExit env fuel d (.lit l) (.lit l)
  /-- `:1586-1588`: the packed zero against `Nat.zero`. -/
  | natZeroL : DefeqStuckExit env fuel d (.lit (.natVal 0)) (.const natZeroName [])
  /-- `:1589-1591`: the mirror. -/
  | natZeroR : DefeqStuckExit env fuel d (.const natZeroName []) (.lit (.natVal 0))
  /-- `:1592-1597`: a packed successor against `Nat.succ x`. -/
  | natSuccL {n : Nat} {x : Expr} :
      isDefEqCore .verified env fuel d (.lit (.natVal n)) x = .ok true →
      DefeqStuckExit env fuel d (.lit (.natVal (n + 1)))
        (.app (.const natSuccName []) x)
  /-- `:1598-1603`: the mirror (the checker's argument order). -/
  | natSuccR {n : Nat} {x : Expr} :
      isDefEqCore .verified env fuel d x (.lit (.natVal n)) = .ok true →
      DefeqStuckExit env fuel d (.app (.const natSuccName []) x)
        (.lit (.natVal (n + 1)))
  /-- `:1610-1613`: a string literal against a `String.ofList` application. -/
  | strLitL {s : String} {x : Expr} :
      strLitSupported env = true →
      isDefEqCore .verified env fuel d (strLitToConstructor s)
        (.app (.const stringOfListName []) x) = .ok true →
      DefeqStuckExit env fuel d (.lit (.strVal s))
        (.app (.const stringOfListName []) x)
  /-- `:1614-1617`: the mirror. -/
  | strLitR {s : String} {x : Expr} :
      strLitSupported env = true →
      isDefEqCore .verified env fuel d (.app (.const stringOfListName []) x)
        (strLitToConstructor s) = .ok true →
      DefeqStuckExit env fuel d (.app (.const stringOfListName []) x)
        (.lit (.strVal s))
  /-- `:1618-1620`: two free variables of the same index. -/
  | fvar {i : Nat} {ty₁ ty₂ : Expr} :
      DefeqStuckExit env fuel d (.fvar i ty₁) (.fvar i ty₂)
  /-- `:1621-1626`: the same constant at equivalent levels. -/
  | const {n : Name} {us us' : List Level} :
      Level.isEquivList us us' = some true →
      DefeqStuckExit env fuel d (.const n us) (.const n us')
  /-- `:1627-1643`: ∀-congruence, the bodies opened at the RIGHT domain,
  the annotations equal (the `.verified` validation). -/
  | forallE {ty₁ bd₁ ty₂ bd₂ : Expr} {m₁ m₂ : BinderMeta} :
      isDefEqCore .verified env fuel d ty₁ ty₂ = .ok true →
      isDefEqCore .verified env fuel (d + 1) (bd₁.instantiate1 (.fvar d ty₂))
        (bd₂.instantiate1 (.fvar d ty₂)) = .ok true →
      m₁.pw = m₂.pw →
      DefeqStuckExit env fuel d (.forallE ty₁ bd₁ m₁) (.forallE ty₂ bd₂ m₂)
  /-- `:1644-1651`: λ-congruence, likewise. -/
  | lam {ty₁ bd₁ ty₂ bd₂ : Expr} {m₁ m₂ : BinderMeta} :
      isDefEqCore .verified env fuel d ty₁ ty₂ = .ok true →
      isDefEqCore .verified env fuel (d + 1) (bd₁.instantiate1 (.fvar d ty₂))
        (bd₂.instantiate1 (.fvar d ty₂)) = .ok true →
      m₁.pw = m₂.pw →
      DefeqStuckExit env fuel d (.lam ty₁ bd₁ m₁) (.lam ty₂ bd₂ m₂)
  /-- `:1652-1678`: the stuck spine congruence (the equal-length guard is
  `defEqList`'s own). -/
  | spine {a b : Expr} :
      isDefEqCore .verified env fuel d a.getAppFn b.getAppFn = .ok true →
      defEqListFueled .verified env fuel d a.getAppArgs b.getAppArgs = .ok true →
      DefeqStuckExit env fuel d a b
  /-- `:1679-1689`: the stuck projection congruence, same table slot. -/
  | proj {sn : Name} {i : Nat} {e₁ e₂ : Expr} :
      isDefEqCore .verified env fuel d e₁ e₂ = .ok true →
      DefeqStuckExit env fuel d (.proj sn i e₁) (.proj sn i e₂)
  /-- `:1690-1692`: a one-sided λ on the left — η. -/
  | etaL {ty bd : Expr} {mb : BinderMeta} {b : Expr} :
      etaCertFueled .verified env fuel d ty bd mb b = .ok true →
      DefeqStuckExit env fuel d (.lam ty bd mb) b
  /-- `:1693-1696`: a one-sided λ on the right. -/
  | etaR {ty bd : Expr} {mb : BinderMeta} {a : Expr} :
      etaCertFueled .verified env fuel d ty bd mb a = .ok true →
      DefeqStuckExit env fuel d a (.lam ty bd mb)

/-- `Expr.isBoolTrue` reads exactly the constant `Bool.true`
(`Model/Steps/DefEq.lean:510`'s private twin). -/
theorem isBoolTrue_iff {e : Expr} : e.isBoolTrue = true ↔ e = .const boolTrueName [] := by
  cases e <;> (try cases ‹List Level›) <;> simp [Expr.isBoolTrue]

/-- **The inversion of `defeqStep`** (`Core.lean:1460-1700`): the
prefix's three exits and, under the two `whnfCore` reducts, the nine
ways the step can end. -/
theorem defeqStep_inv {d : Nat} {k : Bool → Expr → Expr → CheckM Bool}
    {pi : Bool} {a b : Expr}
    (h : defeqStep .verified (pureFns .verified env fuel) env d k pi a b
      = .ok true) :
    a = b ∨
    (b = .const boolTrueName [] ∧
      boolTrueShortcutFueled .verified env fuel d a = .ok true) ∨
    ∃ a' b', whnfCore .verified env fuel d a = .ok a' ∧
      whnfCore .verified env fuel d b = .ok b' ∧
      (a' = b' ∨
       propIrrelFueled .verified env fuel d a' b' = .ok true ∨
       (∃ a₂, reduceNatFueled .verified env fuel d a' = .ok (some a₂) ∧
          k true a₂ b' = .ok true) ∨
       (∃ b₂, reduceNatFueled .verified env fuel d b' = .ok (some b₂) ∧
          k true a' b₂ = .ok true) ∨
       (∃ a₂, unfoldDefinition env a' = some a₂ ∧ k false a₂ b' = .ok true) ∨
       (∃ b₂, unfoldDefinition env b' = some b₂ ∧ k false a' b₂ = .ok true) ∨
       (∃ a₂ b₂, unfoldDefinition env a' = some a₂ ∧
          unfoldDefinition env b' = some b₂ ∧ k false a₂ b₂ = .ok true) ∨
       defeqSpineFueled .verified env fuel d a' b' = .ok true ∨
       DefeqStuckExit env fuel d a' b') := by
  simp only [defeqStep, Bind.bind, Except.bind, whnfCore_def,
    propIrrel_fold, reduceNat_fold, boolTrueShortcut_fold,
    defeqSpine_fold, stuckIrrel_fold, defeq_def,
    defEqList_fold, etaCert_fold] at h
  split at h
  · next hab => exact Or.inl (eq_of_beq hab)
  · cases hbt : (if pi && b.isBoolTrue && !a.hasFvar then
        boolTrueShortcutFueled .verified env fuel d a else pure false) with
    | error err => rw [hbt] at h; exact nomatch h
    | ok rbt =>
    rw [hbt] at h
    dsimp only at h
    cases rbt with
    | true =>
      have hbt' : boolTrueShortcutFueled .verified env fuel d a = .ok true ∧
          b.isBoolTrue = true := by
        split at hbt
        · next hc =>
          simp only [Bool.and_eq_true] at hc
          exact ⟨hbt, hc.1.2⟩
        · exact nomatch hbt
      exact Or.inr (Or.inl ⟨isBoolTrue_iff.mp hbt'.2, hbt'.1⟩)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases hwca : whnfCore .verified env fuel d a with
    | error err => rw [hwca] at h; exact nomatch h
    | ok a' =>
    rw [hwca] at h
    dsimp only at h
    cases hwcb : whnfCore .verified env fuel d b with
    | error err => rw [hwcb] at h; exact nomatch h
    | ok b' =>
    rw [hwcb] at h
    dsimp only at h
    refine Or.inr (Or.inr ⟨a', b', rfl, rfl, ?_⟩)
    split at h
    · next hab' => exact Or.inl (eq_of_beq hab')
    · cases hir : (if pi && !a'.quickPair b' then
          propIrrelFueled .verified env fuel d a' b' else pure false) with
      | error err => rw [hir] at h; exact nomatch h
      | ok r =>
      rw [hir] at h
      dsimp only at h
      cases r with
      | true =>
        refine Or.inr (Or.inl ?_)
        split at hir
        · exact hir
        · exact nomatch hir
      | false =>
      cases hna : (if !a'.hasFvar && !b'.hasFvar then
          reduceNatFueled .verified env fuel d a' else pure none) with
      | error err => rw [hna] at h; exact nomatch h
      | ok o₁ =>
      rw [hna] at h
      dsimp only at h
      match o₁, hna, h with
      | some a₂, hna, h =>
        refine Or.inr (Or.inr (Or.inl ⟨a₂, ?_, h⟩))
        split at hna
        · exact hna
        · exact nomatch hna
      | none, hna, h =>
      dsimp only at h
      cases hnb : (if !a'.hasFvar && !b'.hasFvar then
          reduceNatFueled .verified env fuel d b' else pure none) with
      | error err => rw [hnb] at h; exact nomatch h
      | ok o₂ =>
      rw [hnb] at h
      dsimp only at h
      match o₂, hnb, h with
      | some b₂, hnb, h =>
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨b₂, ?_, h⟩)))
        split at hnb
        · exact hnb
        · exact nomatch hnb
      | none, hnb, h =>
      cases hha : unfoldableHead env a' <;> cases hhb : unfoldableHead env b' <;>
        rw [hha, hhb] at h <;> dsimp only at h
      · -- neither head unfolds: the stuck tree (`Core.lean:1580-1700`)
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ?_)))))))
        have hfall : stuckIrrelFueled .verified env fuel d a' b' = .ok true →
            DefeqStuckExit env fuel d a' b' := DefeqStuckExit.fallback
        -- the tree's `split` substitutes `a'`/`b'`, so every hypothesis
        -- that mentions them is reverted and re-introduced after the
        -- pattern variables: clear them, so `rename_i` names the shapes
        rename_i x₁ x₂ x₃ x₄ x₅ x₆
        clear x₁ x₂ x₃ x₄ x₅ x₆ hbt hwca hwcb hir hna hnb hha hhb o₁ o₂
        simp only [Bool.false_eq_true, if_false] at h
        split at h
        · -- 1: two sorts
          rename_i u v
          cases hle : Level.isEquiv u v with
          | none => rw [hle] at h; exact nomatch h
          | some r =>
            rw [hle] at h
            dsimp only [liftFueled] at h
            cases r with
            | false => exact nomatch h
            | true => exact .sort hle
        · -- 2: two literals
          rename_i l₁ l₂
          simp only [pure, Except.pure, Except.ok.injEq] at h
          obtain rfl : l₁ = l₂ := eq_of_beq h
          exact .lit
        · -- 3: the packed zero against `Nat.zero`
          rename_i n c us
          split at h
          · next hcond =>
            obtain ⟨rfl, rfl⟩ := hcond
            simp only [pure, Except.pure, Except.ok.injEq] at h
            obtain rfl : n = 0 := by simpa using h.symm
            exact .natZeroL
          · exact hfall h
        · -- 4: `Nat.zero` against the packed zero
          rename_i c us n
          split at h
          · next hcond =>
            obtain ⟨rfl, rfl⟩ := hcond
            simp only [pure, Except.pure, Except.ok.injEq] at h
            obtain rfl : n = 0 := by simpa using h.symm
            exact .natZeroR
          · exact hfall h
        · -- 5: a packed successor against a `Nat.succ` application
          split at h
          · split at h
            · next hc => subst hc; exact .natSuccL h
            · exact hfall h
          · exact hfall h
        · -- 6: a `Nat.succ` application against a packed successor
          split at h
          · split at h
            · next hc => subst hc; exact .natSuccR h
            · exact hfall h
          · exact hfall h
        · -- 7: a string literal against a `String.ofList` application
          split at h
          · next hcond =>
            obtain ⟨rfl, rfl, hg⟩ := hcond
            exact .strLitL hg h
          · exact hfall h
        · -- 8: a `String.ofList` application against a string literal
          split at h
          · next hcond =>
            obtain ⟨rfl, rfl, hg⟩ := hcond
            exact .strLitR hg h
          · exact hfall h
        · -- 9: two free variables of the same index
          rename_i i t₁ j t₂
          split at h
          · next hij =>
            obtain rfl : i = j := eq_of_beq hij
            exact .fvar
          · exact hfall h
        · -- 10: the same constant at equivalent levels
          rename_i n us n' us'
          split at h
          · next hnn =>
            subst hnn
            cases hle : Level.isEquivList us us' with
            | none => rw [hle] at h; exact nomatch h
            | some r =>
              rw [hle] at h
              dsimp only [liftFueled] at h
              cases r with
              | false => exact hfall h
              | true => exact .const hle
          · exact hfall h
        · -- 11: ∀-congruence
          rename_i ty₁ bd₁ mb₁ ty₂ bd₂ mb₂
          cases hdt : isDefEqCore .verified env fuel d ty₁ ty₂ with
          | error err => rw [hdt] at h; exact nomatch h
          | ok r =>
          rw [hdt] at h
          cases r with
          | false => exact nomatch h
          | true =>
            dsimp only at h
            have hbd : isDefEqCore .verified env fuel (d + 1)
                (bd₁.instantiate1 (.fvar d ty₂))
                (bd₂.instantiate1 (.fvar d ty₂)) = .ok true := by
              revert h
              cases hbd0 : isDefEqCore .verified env fuel (d + 1)
                  (bd₁.instantiate1 (.fvar d ty₂))
                  (bd₂.instantiate1 (.fvar d ty₂)) with
              | error err => intro h; exact nomatch h
              | ok rb =>
                intro h
                dsimp only at h
                cases rb with
                | false => simp [pure, Except.pure] at h
                | true => rfl
            have hq : (mb₁.pw == mb₂.pw) = true := by
              by_cases hq0 : (mb₁.pw == mb₂.pw) = true
              · exact hq0
              · exfalso
                have hq1 : (mb₁.pw == mb₂.pw) = false := by simpa using hq0
                rw [hbd] at h
                dsimp only at h
                rw [hq1] at h
                simp [throw, throwThe, MonadExceptOf.throw] at h
            exact .forallE hdt hbd (eq_of_beq hq)
        · -- 12: λ-congruence
          rename_i ty₁ bd₁ mb₁ ty₂ bd₂ mb₂
          cases hdt : isDefEqCore .verified env fuel d ty₁ ty₂ with
          | error err => rw [hdt] at h; exact nomatch h
          | ok r =>
          rw [hdt] at h
          cases r with
          | false => exact nomatch h
          | true =>
            dsimp only at h
            have hbd : isDefEqCore .verified env fuel (d + 1)
                (bd₁.instantiate1 (.fvar d ty₂))
                (bd₂.instantiate1 (.fvar d ty₂)) = .ok true := by
              revert h
              cases hbd0 : isDefEqCore .verified env fuel (d + 1)
                  (bd₁.instantiate1 (.fvar d ty₂))
                  (bd₂.instantiate1 (.fvar d ty₂)) with
              | error err => intro h; exact nomatch h
              | ok rb =>
                intro h
                dsimp only at h
                cases rb with
                | false => simp [pure, Except.pure] at h
                | true => rfl
            have hq : (mb₁.pw == mb₂.pw) = true := by
              by_cases hq0 : (mb₁.pw == mb₂.pw) = true
              · exact hq0
              · exfalso
                have hq1 : (mb₁.pw == mb₂.pw) = false := by simpa using hq0
                rw [hbd] at h
                dsimp only at h
                rw [hq1] at h
                simp [throw, throwThe, MonadExceptOf.throw] at h
            exact .lam hdt hbd (eq_of_beq hq)
        · -- 13: the stuck spine congruence
          rename_i f₁ a₁ f₂ a₂
          split at h
          · next hlen =>
            cases hhd : isDefEqCore .verified env fuel d
                (Expr.app f₁ a₁).getAppFn (Expr.app f₂ a₂).getAppFn with
            | error err => rw [hhd] at h; exact nomatch h
            | ok r =>
            rw [hhd] at h
            dsimp only at h
            cases r with
            | false => exact hfall h
            | true =>
              cases hls : defEqListFueled .verified env fuel d
                  (Expr.app f₁ a₁).getAppArgs (Expr.app f₂ a₂).getAppArgs with
              | error err => rw [hls] at h; exact nomatch h
              | ok r' =>
              rw [hls] at h
              dsimp only at h
              cases r' with
              | false => exact hfall h
              | true => exact .spine hhd hls
          · exact hfall h
        · -- 14: the stuck projection congruence
          rename_i s₁ i₁ e₁ s₂ i₂ e₂
          split at h
          · next hii =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hii
            obtain ⟨rfl, rfl⟩ := hii
            cases hde : isDefEqCore .verified env fuel d e₁ e₂ with
            | error err => rw [hde] at h; exact nomatch h
            | ok r =>
            rw [hde] at h
            dsimp only at h
            cases r with
            | false => exact hfall h
            | true => exact .proj hde
          · exact hfall h
        · -- 15: a one-sided λ on the left
          rename_i ty₁ bd₁ mb₁ _hnl
          cases he : etaCertFueled .verified env fuel d ty₁ bd₁ mb₁ b' with
          | error err => rw [he] at h; exact nomatch h
          | ok r =>
          rw [he] at h
          dsimp only at h
          cases r with
          | true => exact .etaL he
          | false => exact hfall h
        · -- 16: a one-sided λ on the right
          rename_i ty₂ bd₂ mb₂ _hnl
          cases he : etaCertFueled .verified env fuel d ty₂ bd₂ mb₂ a' with
          | error err => rw [he] at h; exact nomatch h
          | ok r =>
          rw [he] at h
          dsimp only at h
          cases r with
          | true => exact .etaR he
          | false => exact hfall h
        · -- 17: distinct stuck head symbols
          exact hfall h
      · cases hub : unfoldDefinition env b' with
        | none => rw [hub] at h; exact nomatch h
        | some b₂ =>
          rw [hub] at h
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b₂, rfl, h⟩)))))
      · cases hua : unfoldDefinition env a' with
        | none => rw [hua] at h; exact nomatch h
        | some a₂ =>
          rw [hua] at h
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a₂, rfl, h⟩))))
      · have hboth : ∀ {x : CheckM Bool},
            (match unfoldDefinition env a', unfoldDefinition env b' with
              | some a₂, some b₂ => k false a₂ b₂
              | _, _ => (pure false : CheckM Bool)) = .ok true →
            (∃ a₂ b₂, unfoldDefinition env a' = some a₂ ∧
              unfoldDefinition env b' = some b₂ ∧ k false a₂ b₂ = .ok true) := by
          intro x hbb2
          cases hua : unfoldDefinition env a' with
          | none => rw [hua] at hbb2; exact nomatch hbb2
          | some a₂ =>
          cases hub : unfoldDefinition env b' with
          | none => rw [hua, hub] at hbb2; exact nomatch hbb2
          | some b₂ =>
            rw [hua, hub] at hbb2
            exact ⟨a₂, b₂, rfl, rfl, hbb2⟩
        cases hlt1 : ReducibilityHint.lt (headHint env b') (headHint env a') <;>
          rw [hlt1] at h
        · cases hlt2 : ReducibilityHint.lt (headHint env a') (headHint env b') <;>
            rw [hlt2] at h
          · cases hsr : (ReducibilityHint.sameRegular (headHint env a')
                  (headHint env b') && sameConstHeads a' b') <;> rw [hsr] at h
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl (hboth (x := pure false) h)))))))
            · cases hsp : defeqSpineFueled .verified env fuel d a' b' with
              | error err => rw [hsp] at h; exact nomatch h
              | ok r' =>
              rw [hsp] at h
              dsimp only at h
              cases r' with
              | true =>
                -- `cases hsp : _` rewrote the run in the goal too
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inl rfl)))))))
              | false =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl (hboth (x := pure false) h)))))))
          · cases hub : unfoldDefinition env b' with
            | none => rw [hub] at h; exact nomatch h
            | some b₂ =>
              rw [hub] at h
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨b₂, rfl, h⟩)))))
        · cases hua : unfoldDefinition env a' with
          | none => rw [hua] at h; exact nomatch h
          | some a₂ =>
            rw [hua] at h
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a₂, rfl, h⟩))))

end ConLeche.Rules
