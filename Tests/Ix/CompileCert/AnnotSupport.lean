import Ix.CompileCert.AnnotSupport

namespace Tests.Ix.CompileCert.AnnotSupport
open _root_.Ix.CompileCert

private def absent : Ix.Kernel.Env := .empty
private def extraNat : Ix.Kernel.Env := {
  consts := [Ix.Kernel.pinnedInfo Ix.Kernel.natName,
    Ix.Kernel.pinnedInfo Ix.Kernel.natZeroName,
    Ix.Kernel.pinnedInfo Ix.Kernel.natSuccName] }

-- These compare actual supported declaration shapes, not mock flag inputs.
#guard !Ix.Kernel.natLitSupported absent
#guard Ix.Kernel.natLitSupported extraNat
#guard !checkLiteralSupport absent extraNat
#guard checkExprLiteralSupport absent extraNat (.sort .zero)
#guard checkInstalledExpr absent extraNat id UniverseImage.identity (.sort .zero) (.sort .zero) == some true
#guard checkExprLiteralSupport absent extraNat (.lam (.sort .zero) (.bvar 0) ⟨.never⟩)
#guard !checkExprLiteralSupport absent extraNat (.lit (.natVal 0))
#guard !checkExprLiteralSupport absent extraNat (.app (.sort .zero) (.lit (.natVal 3)))
#guard !checkExprLiteralSupport absent extraNat (.forallE (.sort .zero) (.lit (.natVal 2)) ⟨.never⟩)
#guard !checkExprLiteralSupport absent extraNat (.proj Ix.Kernel.natName 0 (.lit (.natVal 1)))
#guard checkExprLiteralSupport extraNat extraNat (.lit (.natVal 7))
#guard checkExprLiteralSupport absent extraNat (.lit (.strVal "unchanged unsupported string"))
#guard checkInstalledExpr absent extraNat id UniverseImage.identity
  (.lit (.strVal "unsupported")) (.lit (.strVal "unsupported")) != some true

end Tests.Ix.CompileCert.AnnotSupport
