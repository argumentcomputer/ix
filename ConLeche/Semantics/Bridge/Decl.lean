module

public import ConLeche.Semantics.Decl
public import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.IotaWalkInv

@[expose] public section

/-!
# The declaration-level RUN inversions (task #148 T6; the derivation
half removed 2026-09-05)

Three inversions from `checkDecl`'s own steps into the V-free run
records of `SetBase/Decl.lean`: `certifyNatEqs` into `NatEqsRun`, and
the pinned basis fold into `BasisInstallRun`/`DeclBasisRun`.  Each inverts a statement
about the checker into a statement about the checker; no valuation, no
relation and no model appears in any of them.

**What this file used to be.**  2 755 lines: the six per-kind
declaration bridges (`declDefnR`, `declThmR`, `declOpaqueR`,
`declAxiomR`, the `indDecl` walk packs, the four pin bridges) that took
`checkDecl`'s run and produced a `DeclR` *derivation* — the collapsed
model's front door, premised throughout on `checkBridge`
(`SetBase/Bridge/Main.lean`) and hence on `mode.betaGate = false`.  The
SetR removal's Stage C deleted the relation family those derivations
inhabited, so the bridges went with it; a proof-term probe had already
put every one of them outside both surviving capstones' closures and
outside the run route the graded fold calls.

The four survivors are here, and not in the grave, because each has a
live consumer: `SetBase/Bridge/DeclRun.lean` for the walks' runs and
the template fold, and `checkDeclRun_of`'s basis arm for the pair
below.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

variable {pins : List NatOpPinSet}

/-- **`certifyNatEqs`, exposed as runs** (task #161 P4 H1 at the
literal tier): the verdict is one `isDefEqCore` success per equation,
and the recorded form is the checker's literal call —
`fueledOps_isDefEq` at fuel `F`, depth `2`.  The P tier's
`NatOps` establishment consumes these through `DefEqClaim`
instead of the relational `NatEqsR` below (whose `DefEq` only has
collapse-currency soundness). -/
theorem natEqsRun_of_certs {μ : CheckMode} {F : Nat} {env : Env} :
    ∀ (eqs : List (Expr × Expr)),
      certifyNatEqs (m := CheckM) (fueledOps μ F) env eqs = .ok true →
      NatEqsRun μ F env eqs := by
  intro eqs
  induction eqs with
  | nil => intro _ eq heq; exact nomatch heq
  | cons e rest ih =>
    intro h eq heq
    simp only [certifyNatEqs, fueledOps_isDefEq, Bind.bind,
      Except.bind] at h
    cases hx : isDefEqCore μ env F 2 e.1 e.2 with
    | error err => rw [hx] at h; exact nomatch h
    | ok b =>
      cases b with
      | false =>
        rw [hx] at h
        simp only [Bool.false_eq_true, if_false, pure, Except.pure,
          Except.ok.injEq] at h
      | true =>
        rw [hx] at h
        simp only [if_true] at h
        rcases List.mem_cons.mp heq with rfl | heq'
        · exact hx
        · exact ih h eq heq'

/-! ## `basisDecl`

The simplest branch: a guard on the pinned `Eq` former, then a fold of
duplicate checks.  `BasisInstallRun` records exactly the fold's output —
each constant fresh, then consed — so the inversion is one induction
over `installBasisDecl_inv`. -/

/-- **The pinned-block fold, inverted** into `BasisInstallRun`. -/
theorem foldlM_installBasisDecl_invR :
    ∀ (l : List ConstantInfo) {env env₁ : Env},
      l.foldlM (installBasisDecl (m := CheckM)) env = .ok env₁ →
      BasisInstallRun env l env₁
  | [], env, env₁, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  | ci :: l, env, env₁, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hi : installBasisDecl (m := CheckM) env ci with
    | error e => intro h; exact nomatch h
    | ok env' =>
      intro h
      obtain ⟨hfresh, rfl⟩ := installBasisDecl_inv hi
      exact ⟨Option.isNone_iff_eq_none.mpr hfresh,
        foldlM_installBasisDecl_invR l h⟩

/-- **The pinned-block install, bridged.**  Stated over
`checkBasisDecl` and not over `checkDecl`'s `.basisDecl` arm, because
since task #293 three arms share that body: the fold's own
`basisDecl` kind, a stream block `basisPinHit` recognises, and the
first quotient record `quotPinHit` recognises. -/
theorem declBasisRunOf {env env₂ : Env} {kind : BasisKind}
    (h : checkBasisDecl (m := CheckM) env kind = .ok env₂) :
    DeclBasisRun env kind env₂ := by
  simp only [checkBasisDecl, Bind.bind, Except.bind] at h
  by_cases hk : kind = .quotK
  · subst hk
    by_cases hEq : env.find? eqName = some eqA
    · simp only [hEq, if_true] at h
      exact ⟨fun _ => hEq, foldlM_installBasisDecl_invR _ h⟩
    · simp [hEq] at h
  · simp only [if_neg hk] at h
    exact ⟨fun hh => absurd hh hk, foldlM_installBasisDecl_invR _ h⟩

/-- **`basisDecl`, bridged.** -/
theorem declBasisRun {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {kind : BasisKind}
    (h : checkDecl μ (fueledOps μ F) pins env (.basisDecl kind) = .ok env₂) :
    DeclBasisRun env kind env₂ := declBasisRunOf h

end ConLeche.Semantics
