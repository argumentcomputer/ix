import IxCC.Recheck.Err
import IxCC.Recheck.Cert
import IxCC.Recheck.Run
import IxCC.Recheck.Produce
import IxCC.Recheck.Json
import IxCC.Own.Plain.Certificate

/-! # The compiler: `produce` and `Recheck.run` (D17)

Decision D17 (`docs/compiler-design.md`, "Design decisions"), as built for
Phase 1:


* `Recheck.Cert` (`Recheck.Cert`): the untrusted certificate: the table in
  proposal form, the relevance annotation, the middle end's oracle, the
  allocation outputs, the frame layouts and the block order;
* `Recheck.produce` (`Recheck.Produce`): ingress's output to a certificate,
  natively, with every search and oracle;
* `Recheck.run` (`Recheck.Run`): a `Src.Program` and a certificate to an
  ELF object, re-running the P-style passes on the certificate's decisions
  and validating the rest, in kernel-evaluable style as far as the stages
  allow;
* `Recheck.compile`: ingress, `produce`, `run`;
* `Recheck.Json`: the certificate's serialisation (`ixcc/cert/1`);
* `Recheck.Err`: every decline or rejection as `stage: code: message`.

`Recheck.sound` (the per-artifact theorem, from which `compile_sound` and
`compile_safe` follow) is proved in `Recheck.Proof.Soundness`. The
command-line compiler is
`IxCC.Cli`. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

theorem checkPlainMap_implies_checkContractPlainMap {F : Fir.Program} {candidate : Src.NatMap Code}
    (h : checkPlainMap F candidate = true) :
    checkContractPlainMap F candidate = true := by
  simp only [checkPlainMap, checkContractPlainMap, Bool.and_eq_true, and_assoc] at h ⊢
  exact ⟨programDomain_implies_contractProgramDomain h.1, h.2.1, h.2.2⟩

/-- Unannotated plain-RC candidate map check. -/
def Program.check (F : Fir.Program) (candidate : Src.NatMap Code) : Bool :=
  checkPlainMap F candidate

/-- Contract-aware plain-RC candidate map check (`0`, `1`, `&`, `*`, `!`, `~`, `let borrow`). -/
def Program.checkWithContracts (F : Fir.Program) (candidate : Src.NatMap Code) : Bool :=
  checkContractPlainMap F candidate

theorem Program.check_implies_checkWithContracts {F : Fir.Program} {candidate : Src.NatMap Code}
    (h : Program.check F candidate = true) :
    Program.checkWithContracts F candidate = true :=
  checkPlainMap_implies_checkContractPlainMap h

theorem Program.check_or_checkWithContracts_iff (F : Fir.Program) (candidate : Src.NatMap Code) :
    (Program.check F candidate || Program.checkWithContracts F candidate) = true ↔
      checkContractPlainMap F candidate = true := by
  constructor
  · intro h
    rcases Bool.or_eq_true_iff.mp h with h1 | h2
    · exact checkPlainMap_implies_checkContractPlainMap h1
    · exact h2
  · intro h
    exact Bool.or_eq_true_iff.mpr (.inr h)

/-- Decode and admit a plain-RC certificate under the contract-aware `Own.Plain`
domain check (which subsumes `Program.check` by `Program.check_implies_checkWithContracts`). -/
def Certificate.admitWithContracts (F : Fir.Program) (j : Lean.Json) : Except String Program := do
  let bodies ← Certificate.decode F j
  if Program.checkWithContracts F bodies then
    return { source := F, bodies }
  else
    throw "own.cert.check: ownership proposal or source domain refused"

theorem Certificate.admitWithContracts_parts {F : Fir.Program} {j : Lean.Json} {P : Program}
    (accepted : Certificate.admitWithContracts F j = .ok P) :
    P.source = F ∧ checkContractPlainMap F P.bodies = true := by
  unfold Certificate.admitWithContracts at accepted
  cases hd : Certificate.decode F j with
  | error e =>
    simp only [hd, bind, Except.bind] at accepted
    cases accepted
  | ok bodies =>
    simp only [hd, bind, Except.bind] at accepted
    split at accepted
    · next checked =>
      cases accepted
      exact ⟨rfl, checked⟩
    · cases accepted

theorem Certificate.admit_implies_admitWithContracts {F : Fir.Program} {j : Lean.Json} {P : Program}
    (accepted : Certificate.admit F j = .ok P) :
    Certificate.admitWithContracts F j = .ok P := by
  unfold Certificate.admit at accepted
  unfold Certificate.admitWithContracts
  cases hd : Certificate.decode F j with
  | error e =>
    simp only [hd, bind, Except.bind] at accepted
    cases accepted
  | ok bodies =>
    simp only [hd, bind, Except.bind] at accepted ⊢
    split at accepted
    · next checked =>
      cases accepted
      have hc : Program.checkWithContracts F bodies = true :=
        Program.check_implies_checkWithContracts checked
      simp [hc, pure, Except.pure]
    · cases accepted

end IxCC.Own.Plain

namespace IxCC.Recheck

/-- Verify that a lowered `Fir.Program` qualifies for `.zeroRc` and passes
`Own.Plain` contract-aware canonical verification. -/
def checkZeroRcContracts (F : Fir.Program) : Bool :=
  (Own.Plain.selectRcPolicy F == .zeroRc) &&
    Own.Plain.Program.checkWithContracts F (Own.Plain.Program.canonical F).bodies

theorem checkZeroRcContracts_parts {F : Fir.Program} (h : checkZeroRcContracts F = true) :
    Own.Plain.selectRcPolicy F = .zeroRc ∧
      Own.Plain.checkContractPlainMap F (Own.Plain.Program.canonical F).bodies = true := by
  simp only [checkZeroRcContracts, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2⟩

/-- The `Own.Plain.RcPolicy` selected for a rechecked artifact's lowered `Fir.Program`. -/
def Artifact.rcPolicy (a : Artifact) : Own.Plain.RcPolicy :=
  Own.Plain.selectRcPolicy a.fir

/-- Contract-aware `Own.Plain` canonical check on a rechecked artifact's lowered `Fir.Program`. -/
def Artifact.checkContractOwn (a : Artifact) : Bool :=
  Own.Plain.Program.checkWithContracts a.fir (Own.Plain.Program.canonical a.fir).bodies

theorem Artifact.checkContractOwn_iff (a : Artifact) :
    a.checkContractOwn = true ↔
      Own.Plain.checkContractPlainMap a.fir (Own.Plain.Program.canonical a.fir).bodies = true :=
  Iff.rfl

/-- Run `Recheck.run` and additionally verify that the lowered `Fir.Program`
passes contract-aware `Own.Plain` canonical verification (`Artifact.checkContractOwn`). -/
def runWithContracts (cfg : Config) (P : Src.Program) (c : Cert) : Except Err Artifact := do
  let a ← run cfg P c
  if a.checkContractOwn then
    pure a
  else
    throw { stage := .cert, code := "own.plain", message := "contract ownership domain check failed" }

/-- Produce a certificate and recheck it with contract-aware `Own.Plain` verification. -/
def compileInputWithContracts (cfg : Config) (inp : Input) : Except Err (Cert × Artifact) := do
  let cfg := cfg.forInput inp
  let c ← produce cfg inp
  let a ← runWithContracts cfg inp.program c
  pure (c, a)

/-- Ingress, `produce`, and contract-aware `runWithContracts`. -/
def compileWithContracts (cfg : Config) (bytes : ByteArray) (equations : Lean.Json)
    (roots : List String := []) (typecheck : Bool := true) : Except Err (Cert × Artifact) := do
  compileInputWithContracts cfg (← ingress bytes equations roots typecheck)

end IxCC.Recheck

