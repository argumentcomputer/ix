/-! # Lean source of the guard-certificate check

An ordinary Lean declaration, checked by Lean's kernel, that `ixvm-guard-certificate`
(`Tests.Ix.IxVM.GuardCertificate`) reads from the test binary's environment and compiles with
Ix's compiler. -/

namespace Tests.Ix.IxVM.GuardCertificateDefs

/-- A proposition with a quantified field and a second field. -/
structure P : Prop where
  h : ∀ n : Nat, n = n
  k : True

end Tests.Ix.IxVM.GuardCertificateDefs
