import IxCCCorrect.Tiers

/-!
# The two routes to `Correct` (`IxCCCorrect.Routes`)

Both routes establish the same proposition. Neither is proved; these are the
statements a proof lane has to meet, as predicates on the function that is
evaluated inside the argument.

* `CertifiedRoute compile`: the compiler itself is the function. Proved once, for
  every environment and target.
* `CertifyingRoute check`: a checker is the function, and the certificate is
  quantified existentially in the hypothesis: what a zero-knowledge argument of
  "I know a certificate the checker accepts" gives a verifier.

In both, the function takes the bytes of the environment and (for the checker) of
the file, so the proposition it yields is about those bytes. An argument system
proves that statement with the bytes as witnesses under the claim's digests; the
conclusion a holder of the claim alone draws is `Claim.Holds`.

`claim.checker` is the digest of the function's arithmetization. No Lean statement
here relates a Lean function to that digest: that is the exporter's faithfulness,
part of the proof system's trusted base.
-/

set_option autoImplicit false

namespace IxCC.Correct

/-- **The certified route.** `compile` maps the committed environment's bytes, a
target address and options to a claim and a file. Whenever it succeeds, the claim
is about that target and that file, and `Correct` holds. -/
def CertifiedRoute.{w} {ε Options : Type}
    (compile : ByteArray → Ixon.Address → Options → Except ε (Claim × ByteArray)) : Prop :=
  ∀ envBytes target options claim exe,
    compile envBytes target options = .ok (claim, exe) →
    claim.target = target ∧ claim.Binds exe ∧ Correct.{w} claim envBytes exe

/-- **The certifying route.** `check` decides, from the claim, the committed
environment's bytes, the file's bytes and a certificate, whether to accept. If
some certificate is accepted, the claim names the file and `Correct` holds. The
certificate does not occur in the conclusion. -/
def CertifyingRoute.{w} {Cert : Type}
    (check : Claim → ByteArray → ByteArray → Cert → Bool) : Prop :=
  ∀ claim envBytes exe,
    (∃ cert, check claim envBytes exe cert = true) →
    claim.Binds exe ∧ Correct.{w} claim envBytes exe

/-- A certifying route gives every accepted claim `Claim.Holds`. -/
theorem CertifyingRoute.holds.{w} {Cert : Type}
    {check : Claim → ByteArray → ByteArray → Cert → Bool}
    (h : CertifyingRoute.{w} check) {claim : Claim} {envBytes exe : ByteArray} {cert : Cert}
    (hc : check claim envBytes exe cert = true) : Claim.Holds.{w} claim :=
  ⟨envBytes, exe, h claim envBytes exe ⟨cert, hc⟩⟩

/-- A certified route gives every claim it produces `Claim.Holds`. -/
theorem CertifiedRoute.holds.{w} {ε Options : Type}
    {compile : ByteArray → Ixon.Address → Options → Except ε (Claim × ByteArray)}
    (h : CertifiedRoute.{w} compile) {envBytes : ByteArray} {target : Ixon.Address}
    {options : Options} {claim : Claim} {exe : ByteArray}
    (hc : compile envBytes target options = .ok (claim, exe)) : Claim.Holds.{w} claim :=
  ⟨envBytes, exe, (h envBytes target options claim exe hc).2⟩

end IxCC.Correct
