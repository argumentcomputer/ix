module

public import ConLeche.Kernel.PropRead
public import ConLeche.Verify.Shift
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import ConLeche.Kernel.PropWhen
import all ConLeche.Kernel.PropWhen

public section

/-!
# The head-symbol prop-ness readers under the verification walks
(task #168)

The readers (`ConLeche/Kernel/PropRead.lean`) look only at head symbols,
arities and binder data, none of which a free-variable shift touches —
so every reader commutes with `shiftFrom`, which is all the
deep-embedding lemma family (`ConLeche/Verify/Deep.lean`) needs of them.
-/

namespace ConLeche

open Expr

theorem Expr.numArgs_shiftFrom {p : Nat} :
    ∀ (e : Expr), (shiftFrom p e).numArgs = e.numArgs := by
  intro e
  induction e <;> simp_all [shiftFrom, numArgs]
  case fvar => split <;> rfl

theorem residualPW_peelNeverPis_shiftFrom {p : Nat} :
    ∀ (k : Nat) (e : Expr),
      residualPW ((shiftFrom p e).peelNeverPis k) =
        residualPW (e.peelNeverPis k) := by
  intro k
  induction k with
  | zero =>
    intro e
    cases e <;> try rfl
    case fvar => simp only [shiftFrom]; split <;> rfl
  | succ k ih =>
    intro e
    cases e <;> try rfl
    case fvar => simp only [shiftFrom]; split <;> rfl
    case forallE ty b m =>
      simp only [shiftFrom, peelNeverPis]
      split
      · exact ih b
      · rfl

theorem headTypePW_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (h : Expr) (n : Nat) :
    headTypePW find? (shiftFrom p h) n = headTypePW find? h n := by
  cases h <;> try rfl
  case fvar =>
    simp only [shiftFrom]
    split <;> simp only [headTypePW, residualPW_peelNeverPis_shiftFrom]

theorem typeSortPW_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (T : Expr) :
    typeSortPW find? (shiftFrom p T) = typeSortPW find? T := by
  cases T <;> try rfl
  case fvar =>
    simp only [shiftFrom]
    split <;> simp only [typeSortPW, getAppFn, numArgs, headTypePW,
      residualPW_peelNeverPis_shiftFrom]
  case app f x =>
    have h1 := getAppFn_shiftFrom (p := p) (.app f x)
    have h2 := numArgs_shiftFrom (p := p) (.app f x)
    simp only [shiftFrom] at h1 h2 ⊢
    simp only [typeSortPW, h1, h2, headTypePW_shiftFrom]

theorem headProofPW_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (h : Expr) :
    headProofPW find? (shiftFrom p h) = headProofPW find? h := by
  cases h <;> try rfl
  case fvar =>
    simp only [shiftFrom]
    split <;> simp only [headProofPW, typeSortPW_shiftFrom]

/-- `proofPW` through the total `lamPw` reader (the shape the walks
rewrite). -/
theorem proofPW_eq (find? : Name → Option ConstantInfo) (a : Expr) :
    proofPW find? a =
      match a.lamPw with
      | some pw => some pw
      | none => headProofPW find? a.getAppFn := by
  cases a <;> rfl

theorem proofPW_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (a : Expr) :
    proofPW find? (shiftFrom p a) = proofPW find? a := by
  rw [proofPW_eq, proofPW_eq, lamPw_shiftFrom, getAppFn_shiftFrom,
    headProofPW_shiftFrom]

theorem notProofFast_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (a : Expr) :
    notProofFast find? (shiftFrom p a) = notProofFast find? a := by
  simp only [notProofFast, proofPW_shiftFrom]

theorem isProofFast_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (a : Expr) :
    isProofFast find? (shiftFrom p a) = isProofFast find? a := by
  simp only [isProofFast, proofPW_shiftFrom]

/-! ## Inversions — what a reader's answer says about the term

The "yes" arm's licence (`ConLeche/Model/Steps/IrrelFast.lean`) consumes
the readers through these: each `some` verdict is one of finitely many
head shapes with the datum spelled out. -/

theorem Expr.numArgs_eq_length : ∀ (e : Expr), e.numArgs = e.getAppArgs.length := by
  intro e
  induction e <;> simp_all [numArgs, getAppArgs]

theorem Expr.lamPw_some_inv {a : Expr} {pw : PropWhen} (h : a.lamPw = some pw) :
    ∃ ty bd mb, a = .lam ty bd mb ∧ pw = mb.pw := by
  cases a <;> simp only [lamPw, reduceCtorEq, Option.some.injEq] at h
  exact ⟨_, _, _, rfl, h.symm⟩

theorem Expr.peelNeverPis_zero_inv {T R : Expr} (h : T.peelNeverPis 0 = some R) :
    T = R := Option.some.inj h

theorem Expr.peelNeverPis_succ_inv {k : Nat} {T R : Expr}
    (h : T.peelNeverPis (k + 1) = some R) :
    ∃ ty b m, T = .forallE ty b m ∧ m.pw.isNever = true ∧
      b.peelNeverPis k = some R := by
  cases T <;> simp only [peelNeverPis, reduceCtorEq] at h
  case forallE ty b m =>
    split at h
    · exact ⟨ty, b, m, rfl, ‹_›, h⟩
    · exact nomatch h

/-- Peeling commutes with term instantiation at any offset: the
binders and their data are untouched, a `Sort` residual stays. -/
theorem Expr.peelNeverPis_instantiate1 : ∀ (k : Nat) {T : Expr} {u : Level}
    (v : Expr) (off : Nat), T.peelNeverPis k = some (.sort u) →
    (T.instantiate1 v off).peelNeverPis k = some (.sort u) := by
  intro k
  induction k with
  | zero =>
    intro T u v off h
    obtain rfl := Expr.peelNeverPis_zero_inv h
    rfl
  | succ k ih =>
    intro T u v off h
    obtain ⟨ty, b, m, rfl, hnev, hb⟩ := Expr.peelNeverPis_succ_inv h
    simp only [instantiate1, peelNeverPis, hnev, if_true]
    exact ih v (off + 1) hb

/-- Peeling commutes with level instantiation: a `.never` datum
instantiates to `.never`, a `Sort` residual to its instance. -/
theorem Expr.peelNeverPis_instantiateLevelParams : ∀ (k : Nat) {T : Expr}
    {u : Level} (ks : List Name) (vs : List Level),
    T.peelNeverPis k = some (.sort u) →
    (T.instantiateLevelParams ks vs).peelNeverPis k =
      some (.sort (Level.subst ks vs u)) := by
  intro k
  induction k with
  | zero =>
    intro T u ks vs h
    obtain rfl := Expr.peelNeverPis_zero_inv h
    rfl
  | succ k ih =>
    intro T u ks vs h
    obtain ⟨ty, b, m, rfl, hnev, hb⟩ := Expr.peelNeverPis_succ_inv h
    have hnev' : (Level.substPW ks vs m.pw).isNever = true := by
      cases hpw : m.pw with
      | never => rfl
      | ifAllZero ps => rw [hpw] at hnev; simp at hnev
    show (if (Level.substPW ks vs m.pw).isNever then
        (b.instantiateLevelParams ks vs).peelNeverPis k else none) = _
    rw [hnev']
    exact ih ks vs hb

/-- A successful peel is a successful `stripPis` with the same
residual. -/
theorem Expr.stripPis_of_peelNeverPis : ∀ (k : Nat) {T R : Expr},
    T.peelNeverPis k = some R → ∃ bs, T.stripPis k = some (bs, R) := by
  intro k
  induction k with
  | zero =>
    intro T R h
    obtain rfl := Expr.peelNeverPis_zero_inv h
    exact ⟨[], rfl⟩
  | succ k ih =>
    intro T R h
    obtain ⟨ty, b, m, rfl, -, hb⟩ := Expr.peelNeverPis_succ_inv h
    obtain ⟨bs, hbs⟩ := ih hb
    exact ⟨(ty, m) :: bs, by simp [stripPis, hbs]⟩

theorem Expr.hasFvar_of_getAppFn_fvar : ∀ {e : Expr} {idx : Nat}
    {ty : Expr}, e.getAppFn = .fvar idx ty → e.hasFvar = true := by
  intro e
  induction e <;> intro idx ty h <;> simp_all [getAppFn, hasFvar]

theorem residualPW_some_inv {o : Option Expr} {pw : PropWhen}
    (h : residualPW o = some pw) :
    ∃ u, o = some (.sort u) ∧ pw = Level.zeronessOf u := by
  match o, h with
  | some (.sort u), h => exact ⟨u, rfl, (Option.some.inj h).symm⟩
  | none, h => exact nomatch h
  | some (.bvar _), h | some (.fvar _ _), h | some (.const _ _), h
  | some (.app _ _), h | some (.lam _ _ _), h | some (.forallE _ _ _), h
  | some (.letE _ _ _), h | some (.lit _), h | some (.proj _ _ _), h =>
    exact nomatch h

theorem headTypePW_some_inv (find? : Name → Option ConstantInfo) {hd : Expr}
    {k : Nat} {pw : PropWhen} (h : headTypePW find? hd k = some pw) :
    (∃ I us ci u, hd = .const I us ∧ find? I = some ci ∧
        ci.isTowerEntry = false ∧
        us.length = ci.toConstantVal.levelParams.length ∧
        ci.toConstantVal.type.peelNeverPis k = some (.sort u) ∧
        pw = Level.substPW ci.toConstantVal.levelParams us
          (Level.zeronessOf u)) ∨
    (∃ idx ty u, hd = .fvar idx ty ∧
        ty.peelNeverPis k = some (.sort u) ∧ pw = Level.zeronessOf u) := by
  cases hd <;> simp only [headTypePW, reduceCtorEq] at h
  case const I us =>
    cases hf : find? I with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      dsimp only at h
      split at h
      · exact nomatch h
      · next hnt =>
        split at h
        · next hlen =>
          cases hr : residualPW (ci.toConstantVal.type.peelNeverPis k) with
          | none => rw [hr] at h; exact nomatch h
          | some pw0 =>
            rw [hr] at h
            obtain ⟨u, hu, rfl⟩ := residualPW_some_inv hr
            exact Or.inl ⟨I, us, ci, u, rfl, hf, Bool.eq_false_iff.mpr hnt, hlen,
              hu, (Option.some.inj h).symm⟩
        · exact nomatch h
  case fvar idx ty =>
    obtain ⟨u, hu, rfl⟩ := residualPW_some_inv h
    exact Or.inr ⟨idx, ty, u, rfl, hu, rfl⟩

/-- `typeSortPW` through the two special cases (the shape the
inversion rewrites). -/
theorem typeSortPW_eq (find? : Name → Option ConstantInfo) (T : Expr) :
    typeSortPW find? T =
      match T with
      | .forallE _ _ m => some m.pw
      | .sort _ => some .never
      | T => headTypePW find? T.getAppFn T.getAppArgs.length := by
  cases T <;> simp [typeSortPW, Expr.numArgs_eq_length]

theorem typeSortPW_some_inv (find? : Name → Option ConstantInfo) {T : Expr}
    {pw : PropWhen} (h : typeSortPW find? T = some pw) :
    (∃ A B mb, T = .forallE A B mb ∧ pw = mb.pw) ∨
    pw = .never ∨
    (∃ I us ci u, T.getAppFn = .const I us ∧ find? I = some ci ∧
        ci.isTowerEntry = false ∧
        us.length = ci.toConstantVal.levelParams.length ∧
        ci.toConstantVal.type.peelNeverPis T.getAppArgs.length =
          some (.sort u) ∧
        pw = Level.substPW ci.toConstantVal.levelParams us
          (Level.zeronessOf u)) ∨
    (∃ idx ty u, T.getAppFn = .fvar idx ty ∧
        ty.peelNeverPis T.getAppArgs.length = some (.sort u) ∧
        pw = Level.zeronessOf u) := by
  rw [typeSortPW_eq] at h
  cases T <;> simp only [Option.some.injEq] at h
  case forallE A B mb => exact Or.inl ⟨A, B, mb, rfl, h.symm⟩
  case sort u => exact Or.inr (Or.inl h.symm)
  all_goals
    rcases headTypePW_some_inv find? h with
      ⟨I, us, ci, u, hfn, hf, hnt, hlen, hpeel, rfl⟩ |
      ⟨idx, ty, u, hfn, hpeel, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨I, us, ci, u, hfn, hf, hnt, hlen, hpeel, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨idx, ty, u, hfn, hpeel, rfl⟩))

theorem headProofPW_some_inv (find? : Name → Option ConstantInfo) {hd : Expr}
    {pw : PropWhen} (h : headProofPW find? hd = some pw) :
    (∃ c us ci, hd = .const c us ∧ find? c = some ci ∧
        ci.isTowerEntry = false ∧
        us.length = ci.toConstantVal.levelParams.length ∧
        ∃ pw0, typeSortPW find? ci.toConstantVal.type = some pw0 ∧
          pw = Level.substPW ci.toConstantVal.levelParams us pw0) ∨
    (∃ idx ty, hd = .fvar idx ty ∧ typeSortPW find? ty = some pw) ∨
    pw = .never := by
  cases hd <;> simp only [headProofPW, reduceCtorEq, Option.some.injEq] at h
  case const c us =>
    cases hf : find? c with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      dsimp only at h
      split at h
      · exact nomatch h
      · next hnt =>
        split at h
        · next hlen =>
          cases hr : typeSortPW find? ci.toConstantVal.type with
          | none => rw [hr] at h; exact nomatch h
          | some pw0 =>
            rw [hr] at h
            exact Or.inl ⟨c, us, ci, rfl, hf, Bool.eq_false_iff.mpr hnt, hlen,
              pw0, hr, (Option.some.inj h).symm⟩
        · exact nomatch h
  case fvar idx ty => exact Or.inr (Or.inl ⟨idx, ty, rfl, h⟩)
  all_goals exact Or.inr (Or.inr h.symm)

theorem proofPW_some_inv (find? : Name → Option ConstantInfo) {a : Expr}
    {pw : PropWhen} (h : proofPW find? a = some pw) :
    (∃ ty bd mb, a = .lam ty bd mb ∧ pw = mb.pw) ∨
    (a.lamPw = none ∧ headProofPW find? a.getAppFn = some pw) := by
  rw [proofPW_eq] at h
  cases hl : a.lamPw with
  | some p =>
    rw [hl] at h
    obtain ⟨ty, bd, mb, rfl, rfl⟩ := Expr.lamPw_some_inv hl
    exact Or.inl ⟨ty, bd, mb, rfl, (Option.some.inj h).symm⟩
  | none => rw [hl] at h; exact Or.inr ⟨rfl, h⟩

theorem isProofFast_inv (find? : Name → Option ConstantInfo) {a : Expr}
    (h : isProofFast find? a = true) :
    ∃ pw, proofPW find? a = some pw ∧ pw.isProp = true := by
  unfold isProofFast at h
  cases hp : proofPW find? a with
  | none => rw [hp] at h; exact nomatch h
  | some pw => rw [hp] at h; exact ⟨pw, rfl, h⟩

@[simp] theorem PropWhen.isProp_never : PropWhen.isProp .never = false := by rfl

@[simp] theorem Level.substPW_never (ks : List Name) (vs : List Level) :
    Level.substPW ks vs .never = .never := by rfl

end ConLeche
