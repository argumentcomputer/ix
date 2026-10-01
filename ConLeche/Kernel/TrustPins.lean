module
public import ConLeche.Kernel.Basis.Builder

@[expose] public section

/-!
# Pinned compiler-trust opaque values (task #95; hand-written since task #273)

The pinned defining expressions of the toolchain's `Lean.reduceNat` /
`Lean.reduceBool` opaques: the plain identity functions, written with
the same builder (`ConLeche/Kernel/Basis/Builder.lean`) that
`ConLeche/Kernel/TrustAxioms.lean` writes the family's axiom shapes,
`Lean.trustCompiler` and the types with.  At install (`checkReducePin`
in `ConLeche/Kernel/Checker.lean`) the stream's stored opaque value is
compared against the pin by definitional equality — drift declines,
never silently — and the identity certificate `value x ≡ x` is what
the model consumes (`EnvModel.reduce_ops`).

**Nothing here reads the compiling environment.**  Until task #273
these two pins were GENERATED at elaboration time (`#gen_trust_pins`,
reading `Lean.reduceBool`/`reduceNat` out of the COMPILING toolchain's
`Init`), which made the binary's behaviour depend on the toolchain
that compiled it — the one such dependency left once the Nat-op pins
became committed files — and lean4 master has removed the two opaques
(with `Lean.trustCompiler` and the `ofReduce*` axioms) from `Init`
altogether, so there was nothing to read there.  The user's ruling:
*"the host toolchain of the binary is irrelevant for our purposes; if
not, there is a design flaw."*  The pin has been the same on every
toolchain that had the opaques —
`opaque reduceBool (b : Bool) : Bool := have := trustCompiler; b`,
whose `have` the conversion zeta-expanded away, leaving `fun b => b` —
so it is written down here once.  Should a toolchain ever respell the
opaques, the install-time comparison declines its streams and the
toolchain matrix (`scripts/natop-matrix.sh`) shows it; no
generator-side assertion is kept.
-/

namespace ConLeche

open BasisDSL

/-- `Lean.reduceBool`'s pinned value: `fun (b : Bool) => b`. -/
def reduceBoolDeclPin : Expr := lm "b" (cnst (bn "Bool")) (bv 0)

/-- `Lean.reduceNat`'s pinned value: `fun (n : Nat) => n`. -/
def reduceNatDeclPin : Expr := lm "n" (cnst (bn "Nat")) (bv 0)

end ConLeche
