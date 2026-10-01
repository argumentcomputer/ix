module

import ConLeche.Kernel.Checker
public import ConLeche.Verify.Fueled
import ConLeche.Verify.Leaves
public import ConLeche.Verify.Extend.Inversions

public section

/-!
# `V`-free inversions of the `Nat.div`/`Nat.mod` pin (task #123)

`checkDivModPin` and `checkDivModCerts` are checker walks over
`Env`/`Expr`; unpacking a successful run into the annotate/infer/defeq
triple it performed, and reading the guards it passed, mentions no
valuation.  All of it was written in `ConLeche/Model/DivModCert.lean`
under that module's `variable (V) [SetTheory V]`, and is relocated here
verbatim under the criterion #123 established: **V-free checker
inversion belongs in `ConLeche/Verify`**, so both verification paths can
consume it instead of restating it.

`ConLeche/Model/DivModCert.lean` imports this file; the valuation-carrying
half of that module (the frame's `EqSideOk` machinery and
`divmod_certs_sound`) stays where it is.
-/

namespace ConLeche

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

variable {env : Env}

/-- Pairwise facts over the certificate statement/proof lists. -/
inductive CertRuns (P : (List Expr × Expr) → Expr → Prop) :
    List (List Expr × Expr) → List Expr → Prop
  | nil : CertRuns P [] []
  | cons {st : List Expr × Expr} {proof : Expr}
      {srest : List (List Expr × Expr)} {prest : List Expr} :
      P st proof → CertRuns P srest prest →
      CertRuns P (st :: srest) (proof :: prest)

/-- The per-certificate content of a successful run. -/
@[expose] def CertRunFacts (mode : CheckMode) (env : Env) (F : Nat) (c : Name) (annVal : Expr)
    (st : List Expr × Expr) (proof : Expr) : Prop :=
  divModCertGuard env c annVal st.1 st.2 proof = true ∧
  ∃ appliedA tp,
    annotateCore mode env F 4 (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))) = .ok appliedA ∧
    inferTypeCore mode env F 4 appliedA = .ok tp ∧
    isDefEqCore mode env F 4 tp (Expr.substConst0 c annVal st.2) = .ok true

/-- Unpack a successful `checkDivModCerts` run, per certificate. -/
theorem checkDivModCerts_inv {env : Env} {F : Nat} {c : Name}
    {annVal : Expr} :
    ∀ {stmts : List (List Expr × Expr)} {proofs : List Expr},
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
theorem natOpStoredOk_tyPinned {n : Name}
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

/-- One variant's successful attempt, unpacked: the variant's pin
annotated and definitionally equal to the stored value, and the
variant's certificates checked (task #273). -/
theorem checkDivModPinAt_inv {env : Env} {F : Nat} {c : Name}
    {value' : Expr} {ps : NatOpPinSet}
    (h : checkDivModPinAt (fueledOps mode F) env c value' ps = .ok true) :
    (∃ pinA, annotateCore mode env F 0 (divModDeclPin ps c) = .ok pinA ∧
      isDefEqCore mode env F 0 value' pinA = .ok true) ∧
    checkDivModCerts (fueledOps mode F) env c value'
      (divModCertStmts c) (divModCertProofs ps c) = .ok true := by
  unfold checkDivModPinAt at h
  simp only [fueledOps_annotate, fueledOps_isDefEq, Bind.bind,
    Except.bind] at h
  revert h
  cases hann : annotateCore mode env F 0 (divModDeclPin ps c) with
  | error e => intro h; exact nomatch h
  | ok pinA =>
    intro h
    dsimp only at h
    revert h
    cases hde : isDefEqCore mode env F 0 value' pinA with
    | error e => intro h; exact nomatch h
    | ok b =>
      cases b with
      | false => intro h; simp [pure, Except.pure] at h
      | true =>
        intro h
        simp only [↓reduceIte] at h
        exact ⟨⟨pinA, rfl, hde⟩, h⟩

/-- The variant loop's success: some listed variant passed its guards
and its attempt. -/
theorem checkDivModPinLoop_inv {env : Env} {F : Nat} {c : Name}
    {value' : Expr} {u : Unit} :
    ∀ {pss : List NatOpPinSet} {tried : List String},
      checkDivModPinLoop (fueledOps mode F) env c value' pss tried = .ok u →
      ∃ ps ∈ pss,
        (divModPinGuard ps env c && divModCertsGuard ps env c value') = true ∧
        checkDivModPinAt (fueledOps mode F) env c value' ps = .ok true
  | [], _, h => nomatch h
  | ps :: rest, tried, h => by
    unfold checkDivModPinLoop at h
    revert h
    split
    case isTrue hg =>
      rw [fueledOps_orElse]
      cases hx : checkDivModPinAt (fueledOps mode F) env c value' ps with
      | ok b =>
        cases b with
        | true => intro _; exact ⟨ps, List.mem_cons_self .., hg, hx⟩
        | false =>
          intro h
          obtain ⟨ps', hm, hrest⟩ := checkDivModPinLoop_inv h
          exact ⟨ps', List.mem_cons_of_mem _ hm, hrest⟩
      | error e =>
        intro h
        obtain ⟨ps', hm, hrest⟩ := checkDivModPinLoop_inv h
        exact ⟨ps', List.mem_cons_of_mem _ hm, hrest⟩
    case isFalse =>
      intro h
      obtain ⟨ps', hm, hrest⟩ := checkDivModPinLoop_inv h
      exact ⟨ps', List.mem_cons_of_mem _ hm, hrest⟩

/-- Unpack a successful `checkDivModPin` run: the environment guard,
the stored definition, and the pin variant that matched — its guards,
its pin definitionally equal to the stored value, its certificates
checked. -/
theorem checkDivModPin_inv {env env2 : Env} {F : Nat} {c : Name} {u : Unit}
    (h : checkDivModPin (fueledOps mode F) pins env env2 c = .ok u) :
    divModEnvGuard env2 c = true ∧
    ∃ cv' value' hint',
      env2.find? c = some (.defnInfo cv' value' hint') ∧
      ∃ ps ∈ pins,
        (divModPinGuard ps env c && divModCertsGuard ps env c value') = true ∧
        (∃ pinA, annotateCore mode env F 0 (divModDeclPin ps c) = .ok pinA ∧
          isDefEqCore mode env F 0 value' pinA = .ok true) ∧
        checkDivModCerts (fueledOps mode F) env c value'
          (divModCertStmts c) (divModCertProofs ps c) = .ok true := by
  unfold checkDivModPin at h
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
        intro h
        obtain ⟨ps, hm, hg', hat⟩ := checkDivModPinLoop_inv h
        exact ⟨cv', value', hint', rfl, ps, hm, hg',
          checkDivModPinAt_inv hat⟩


/-- The pin names are distinct from every constant the install path
transports (the `Nat`/`Bool` pins, the pinned equality, and the
already-certified dependencies). -/
theorem natDivModNames_ne_env {c : Name} (hc : c ∈ natDivModNames) :
    c ≠ natName ∧ c ≠ natZeroName ∧ c ≠ natSuccName ∧ c ≠ boolName ∧
    c ≠ boolTrueName ∧ c ≠ boolFalseName ∧ c ≠ eqName ∧
    c ≠ natBleName ∧ c ≠ natSubName ∧ c ≠ natPredName ∧
    c ≠ natBeqName := by
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `divModEnvGuard`, split into facts. -/
theorem divModEnvGuard_inv {env2 : Env} {c : Name}
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

end ConLeche
