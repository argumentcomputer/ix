module

import IxC.Kernel.Checker
public import IxC.Kernel.Verify.Fueled
import IxC.Kernel.Verify.Leaves
public import IxC.Kernel.Verify.Extend.Inversions

public section

/-!
# `V`-free inversions of the `Nat.div`/`Nat.mod` evidence gate (task #123)

`checkDivModEvidence` and `checkDivModCerts` are checker walks over
`Env`/`Expr`; unpacking a successful run into the annotate/infer/defeq
triple it performed, and reading the guards it passed, mentions no
valuation.  All of it was written in `IxC/Kernel/Model/DivModCert.lean`
under that module's `variable (V) [SetTheory V]`, and is relocated here
verbatim under the criterion #123 established: **V-free checker
inversion belongs in `IxC/Kernel/Verify`**, so both verification paths can
consume it instead of restating it.

`IxC/Kernel/Model/DivModCert.lean` imports this file; the valuation-carrying
half of that module (the frame's `EqSideOk` machinery and
`divmod_certs_sound`) stays where it is.
-/

namespace Ix.Kernel

variable {mode : CheckMode}
variable {ev : Evidences md}

variable {env : Env md}

/-- Pairwise facts over the certificate statement/proof lists. -/
inductive CertRuns (P : (List (Expr md) × Expr md) → Expr md → Prop) :
    List (List (Expr md) × Expr md) → List (Expr md) → Prop
  | nil : CertRuns P [] []
  | cons {st : List (Expr md) × Expr md} {proof : Expr md}
      {srest : List (List (Expr md) × Expr md)} {prest : List (Expr md)} :
      P st proof → CertRuns P srest prest →
      CertRuns P (st :: srest) (proof :: prest)

/-- The per-certificate content of a successful run. -/
@[expose] def CertRunFacts (mode : CheckMode) (env : Env md) (F : Nat) (c : Key md) (annVal : Expr md)
    (st : List (Expr md) × Expr md) (proof : Expr md) : Prop :=
  divModCertGuard env c annVal st.1 st.2 proof = true ∧
  ∃ appliedA tp,
    annotateCore mode env F 4 (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))) = .ok appliedA ∧
    inferTypeCore mode env F 4 appliedA = .ok tp ∧
    isDefEqCore mode env F 4 tp (Expr.substConst0 c annVal st.2) = .ok true

/-- Unpack a successful `checkDivModCerts` run, per certificate. -/
theorem checkDivModCerts_inv {env : Env md} {F : Nat} {c : Key md}
    {annVal : Expr md} :
    ∀ {stmts : List (List (Expr md) × Expr md)} {proofs : List (Expr md)},
      checkDivModCerts (fueledOps mode F) env c annVal stmts proofs = .ok true →
      CertRuns (CertRunFacts mode env F c annVal) stmts proofs
  | [], [], _ => CertRuns.nil
  | [], _ :: _, h => by
    simp [checkDivModCerts, pure, Except.pure] at h
  | _ :: _, [], h => by
    simp [checkDivModCerts, pure, Except.pure] at h
  | (hyps, eqE) :: srest, proof :: prest, h => by
    simp only [checkDivModCerts, fueledOps_annotate, fueledOps_inferType,
      fueledOps_isDefEq, Bind.bind, Except.bind] at h
    revert h
    split
    case isFalse => intro h; simp [pure, Except.pure] at h
    case isTrue hg =>
      cases hann : annotateCore mode env F 4 (divModCertApplied
          (Expr.substConstAll c annVal proof)
          (hyps.map (Expr.substConst0 c annVal))) with
      | error e => intro h; exact nomatch h
      | ok appliedA =>
        intro h
        dsimp only at h
        revert h
        cases hinf : inferTypeCore mode env F 4 appliedA with
        | error e => intro h; exact nomatch h
        | ok tp =>
          intro h
          dsimp only at h
          revert h
          cases hde : isDefEqCore mode env F 4 tp
              (Expr.substConst0 c annVal eqE) with
          | error e => intro h; exact nomatch h
          | ok b =>
            cases b with
            | false => intro h; simp [pure, Except.pure] at h
            | true =>
              intro h
              simp only [↓reduceIte] at h
              exact CertRuns.cons ⟨hg, appliedA, tp, hann, hinf, hde⟩
                (checkDivModCerts_inv h)

/-- `natOpStoredOk`, split. -/
theorem natOpStoredOk_tyPinned {n : Key md}
    (h : natOpStoredOk env n = true) :
    ∃ cv v hint, env.find? n = some (.defnInfo cv v hint) ∧
      natOpTyPinned env n cv.type = true := by
  unfold natOpStoredOk at h
  revert h
  split
  · next cv v hint heq =>
    intro h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨cv, v, hint, heq, h.2⟩
  · intro h; exact nomatch h

/-- Unpack a successful `checkDivModEvidence` run: the environment guard,
the stored definition, and the operation's evidence — one proof per
certificate statement, past the syntactic guards and the closure
condition, with its certificates checked. -/
theorem checkDivModEvidence_inv {env env2 : Env md} {F : Nat} {c : Key md} {u : Unit}
    (h : checkDivModEvidence (fueledOps mode F) ev env env2 c = .ok u) :
    divModEnvGuard env2 c = true ∧
    ∃ cv' value' hint',
      env2.find? c = some (.defnInfo cv' value' hint') ∧
      ∃ proofs, evidenceProofs ev c = some proofs ∧
        divModCertsGuard proofs env c value' = true ∧
        evidenceLocal env.find? c value' proofs = true ∧
        checkDivModCerts (fueledOps mode F) env c value'
          (divModCertStmts c) proofs = .ok true := by
  unfold checkDivModEvidence at h
  revert h
  split
  case isFalse => intro h; exact nomatch h
  case isTrue hg =>
    refine fun h => ⟨hg, ?_⟩
    revert h
    cases hfind : env2.find? c with
    | none => intro h; exact nomatch h
    | some ci =>
      cases ci with
      | axiomInfo cv' => intro h; exact nomatch h
      | thmInfo cv' v' => intro h; exact nomatch h
      | indInfo cv' caps => intro h; exact nomatch h
      | ctorInfo cv' nP nF => intro h; exact nomatch h
      | recInfo cv' mI rP rules => intro h; exact nomatch h
      | projInfo _ => intro h; exact nomatch h
      | defnInfo cv' value' hint' =>
        dsimp only
        cases hev : evidenceProofs ev c with
        | none => intro h; exact nomatch h
        | some proofs =>
          dsimp only
          split
          case isFalse => intro h; exact nomatch h
          case isTrue hguards =>
            rw [fueledOps_orElse]
            intro h
            simp only [Bool.and_eq_true] at hguards
            refine ⟨cv', value', hint', rfl, proofs, rfl, hguards.1, hguards.2, ?_⟩
            revert h
            cases hx : checkDivModCerts (fueledOps mode F) env c value'
                (divModCertStmts c) proofs with
            | ok b =>
              cases b with
              | true => intro _; rfl
              | false => intro h; exact nomatch h
            | error e => intro h; exact nomatch h


/-- The pin names are distinct from every constant the install path
transports (the `Nat`/`Bool` pins, the pinned equality, and the
already-certified dependencies). -/
theorem natDivModNames_ne_env {c : Key md} (hc : c ∈ natDivModNames) :
    c ≠ natName ∧ c ≠ natZeroName ∧ c ≠ natSuccName ∧ c ≠ boolName ∧
    c ≠ boolTrueName ∧ c ≠ boolFalseName ∧ c ≠ eqName ∧
    c ≠ natBleName ∧ c ≠ natSubName ∧ c ≠ natPredName ∧
    c ≠ natBeqName := by
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by (cases md <;> decide), by (cases md <;> decide), by (cases md <;> decide), by (cases md <;> decide), by (cases md <;> decide),
      by (cases md <;> decide), by (cases md <;> decide), by (cases md <;> decide), by (cases md <;> decide), by (cases md <;> decide), by (cases md <;> decide)⟩

/-- `divModEnvGuard`, split into facts. -/
theorem divModEnvGuard_inv {env2 : Env md} {c : Key md}
    (h : divModEnvGuard env2 c = true) :
    natOpGuard env2 c = true ∧
    (natOpDeps c).all (natOpStoredOk env2) = true ∧
    env2.find? eqName = some eqA ∧
    (∃ ci, env2.find? boolTrueName = some ci ∧
      ci.toConstantVal.type = .const boolName []) ∧
    (∃ ci, env2.find? boolFalseName = some ci ∧
      ci.toConstantVal.type = .const boolName []) := by
  unfold divModEnvGuard at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hg, hdeps⟩, heq⟩, hbT⟩, hbF⟩ := h
  refine ⟨hg, hdeps, by simpa using heq, ?_, ?_⟩
  · revert hbT
    split
    · next ci hfind =>
      intro hbT
      exact ⟨ci, hfind, by simpa using hbT⟩
    · intro hbT; exact nomatch hbT
  · revert hbF
    split
    · next ci hfind =>
      intro hbF
      exact ⟨ci, hfind, by simpa using hbF⟩
    · intro hbF; exact nomatch hbF

end Ix.Kernel
