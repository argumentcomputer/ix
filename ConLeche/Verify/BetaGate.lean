module

public import ConLeche.Kernel.Core

public section

/-!
# The β gate's dead-branch collapse (task #161, S13a)

`betaGateFires` (`ConLeche/Kernel/Core.lean`) is the *one* β-certificate
gate predicate, shared by every β-cert lane (the pure body, the cached
`whnfAppI`/`betaPeelI` twins, and the pure mirror in
`Verify/BetaSpine.lean`).  This module is its whole proof
interface, and it is deliberately small:

* **`betaGateFires_off` — THE DEAD-BRANCH COLLAPSE.**  At a mode whose
  gate is off the predicate is `false`, so the gated `if` takes its
  `else` arm — which is the pre-gate clause *byte-for-byte*.  Every
  pre-gate proof of every non-gated mode is therefore one `simp only`
  from its old form, and that rewrite is the same lemma at every site.
  This is the *whole* reason the gate is a pure early return rather
  than a wrapper around the certificate's `Bool`;
* **`isNever_of_betaGateFires`** — a fired gate's datum is `.never`,
  which is what the P tier's licensing composition
  (`WellDenotedV_beta_gate`, `Model/Steps/Gate.lean`, via
  `pwBit_ne_zero_of_isNever`) consumes.  No certificate appears in it;
* **`verified_isNever_of_betaGateFires`** — a fired gate is a verified
  mode's gate, which is the pair the P tier's licensing theorem is
  stated against.  (The mode-level coverage certificates that used to
  sit here retired with the mode set they partitioned; see below.);
* **the mode functions' values at the two constructors** (task #185)
  — the `rfl` table that replaced the configuration-record bridge, and the
  conditional forms the cached simulation tower reads through.

The module imports `Kernel.Core` and nothing else: it is base-tier.
-/

namespace ConLeche

variable {mode : CheckMode} {pw : PropWhen}

/-- **THE DEAD-BRANCH COLLAPSE.**  At `betaGate = false` the gate never
fires, so the gated `if`'s `else` arm — the pre-gate clause, verbatim
— is the one taken. -/
@[simp] theorem betaGateFires_off (h : mode.betaGate = false) :
    betaGateFires mode pw = false := by
  simp [betaGateFires, h]

/-- The gate is off at `.trusted`. -/
@[simp] theorem betaGate_off_trusted :
    CheckMode.betaGate .trusted = false := rfl

/-- The gate is on at `.verified` — the one verified mode. -/
@[simp] theorem betaGate_on_verified :
    CheckMode.betaGate .verified = true := rfl

/-! ## The coverage certificates, RETIRED (2026-09-05)

`CheckMode.verified_of_betaGate` (a gated mode is a verified mode) and
`CheckMode.betaGate_off_or_verified` (every mode is ungated or
verified) were a **partition of the capstone families**: ungated modes
were the R letters', verified modes the P letters'.  With one verified
mode and one unverified one there is no partition to certify — the
statements would be true and empty.  The user's ruling at the SetR
removal is that they go, not that they be restated one-sided:
*coverage certificates were the pathology.*  What the fence actually
needs is stated where it is consumed (`WellDenotedV_beta_gate`,
`Model/Steps/Gate.lean`), against the datum, not against the mode
set. -/

/-- A fired gate's datum is `.never`. -/
theorem isNever_of_betaGateFires (h : betaGateFires mode pw = true) :
    pw.isNever = true :=
  (Bool.and_eq_true .. |>.mp h).2

/-- A fired gate is a verified mode's gate: the pair the P tier's
licensing theorem (`WellDenotedV_beta_gate`) is stated against. -/
theorem verified_isNever_of_betaGateFires
    (h : betaGateFires mode pw = true) :
    (mode.verifiedChecks && pw.isNever) = true := by
  rcases Bool.and_eq_true .. |>.mp h with ⟨hg, hn⟩
  cases mode <;> simp_all [CheckMode.betaGate, CheckMode.verifiedChecks]

/-! ## The mode functions at the two constructors (task #185)

`CheckMode`'s functions (`ConLeche/Kernel/Env.lean`) are the cores'
whole configuration since the configuration record retired: every read a
shipped core makes is one of `verifiedChecks`, `betaGate`, `ioGate`,
`certs`, `betaSkip`, `ioSkip`, `ttChecks`, each a `match` on the enum.
These are their values at the two constructors — all `rfl`, which is
the record's old `rfl`-eliminability requirement (*"every field
computes away by `rfl` at each named core"*) stated at the enum
itself — plus the three conditional forms the mode-parametric
simulation tower (`ConLeche/Verify/Cached/*`) consumes under its
`hμ : mode.verifiedChecks = true`: at such a mode the certificate
families are on, the β read is the spec's gate predicate and the io
read is the datum alone. -/

@[simp] theorem verifiedChecks_verified :
    CheckMode.verifiedChecks .verified = true := rfl
@[simp] theorem verifiedChecks_trusted :
    CheckMode.verifiedChecks .trusted = false := rfl
@[simp] theorem certs_verified : CheckMode.certs .verified = true := rfl
@[simp] theorem certs_trusted : CheckMode.certs .trusted = false := rfl
/-- The TT-lane residue is off at every mode (task #148 T7b). -/
theorem ttChecks_eq_false : mode.ttChecks = false := rfl

/-- The two certification-only switches agree at both constructors;
they stay two functions because they gate different work (see
`CheckMode.certs`). -/
theorem certs_eq_verifiedChecks : mode.certs = mode.verifiedChecks := by
  cases mode <;> rfl

/-- **A mode running the verified checks is `.verified`** — the enum has
two constructors and the other one does not.  This is the simulation
tower's way through a cached body's certificate switches: after
`obtain rfl := CheckMode.eq_verified hμ` every `certAtI`/`betaSkip`/
`ioSkip` read is at the literal `.verified` and reduces by `rfl`, so a
proof written when the switches were literals
resumes verbatim (the record's era: task #172 B2 to #185). -/
theorem CheckMode.eq_verified (h : mode.verifiedChecks = true) :
    mode = .verified := by
  cases mode <;> simp_all [CheckMode.verifiedChecks]

/-- A mode running the verified checks runs the certificate families. -/
@[simp] theorem certs_of_verifiedChecks (h : mode.verifiedChecks = true) :
    mode.certs = true := by
  rw [certs_eq_verifiedChecks, h]

/-- A mode running the verified checks has the β gate on. -/
theorem betaGate_of_verifiedChecks (h : mode.verifiedChecks = true) :
    mode.betaGate = true := by
  cases mode <;> simp_all [CheckMode.betaGate, CheckMode.verifiedChecks]

/-- **The β site's read at a verified mode is the spec's gate
predicate**: the certificate families are on, so the skip is exactly
`betaGateFires`. -/
@[simp] theorem betaSkip_of_verifiedChecks (h : mode.verifiedChecks = true) :
    mode.betaSkip pw = betaGateFires mode pw := by
  simp [CheckMode.betaSkip, betaGateFires, certs_of_verifiedChecks h]

/-- The io licence at a verified mode reads the datum alone. -/
@[simp] theorem ioSkip_of_verifiedChecks (h : mode.verifiedChecks = true) :
    mode.ioSkip pw = pw.isNever := by
  simp [CheckMode.ioSkip, certs_of_verifiedChecks h]

/-- **The P core's β branch reads the datum, not a flag**: at
`.verified` the skip predicate is the redex's own validated
annotation. -/
@[simp] theorem betaSkip_verified :
    CheckMode.betaSkip .verified pw = pw.isNever := rfl
/-- The β certificate is a certificate family: skipped at every redex
in the trusted mode, licence or not. -/
@[simp] theorem betaSkip_trusted : CheckMode.betaSkip .trusted pw = true := rfl
@[simp] theorem ioSkip_verified :
    CheckMode.ioSkip .verified pw = pw.isNever := rfl
@[simp] theorem ioSkip_trusted : CheckMode.ioSkip .trusted pw = true := rfl

/-- The β read at `.verified` **is** `betaGateFires .verified` — the
identity the cached core's P instantiation rests on. -/
theorem betaSkip_verified_eq_gate (pw : PropWhen) :
    CheckMode.betaSkip .verified pw = betaGateFires .verified pw := rfl

end ConLeche
