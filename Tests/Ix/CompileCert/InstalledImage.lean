import Ix.CompileCert.Entry

/-! Executable image-comparison controls. Synthetic environments exercise
only the comparison boundary; they do not stand in for admitted models. -/
namespace Tests.Ix.CompileCert.InstalledImage

open _root_.Ix.CompileCert
open _root_.Ix.Kernel

def identity : UniverseImage := ⟨Level.param⟩
def compare := checkInstalledExpr Env.empty Env.empty id identity

example : compare (.bvar 0) (.bvar 0) = some true := by decide
example : compare (.bvar 0) (.bvar 1) = some false := by decide
example : compare (.sort (.max .zero (.succ .zero))) (.sort (.succ .zero)) = some true := by decide
-- The certified level decision has an opaque executable backend on this path.
#eval (do
  unless compare (.sort .zero) (.sort (.succ .zero)) == some false do
    throw (IO.userError "unequal universe sorts were not rejected") : IO Unit)
example : compare (.lam (.sort .zero) (.bvar 0) ⟨.never⟩)
    (.lam (.sort .zero) (.bvar 0) ⟨.never⟩) = some true := by decide
example : compare (.lam (.sort .zero) (.bvar 0) ⟨.never⟩)
    (.lam (.sort .zero) (.bvar 0) ⟨.ifAllZero []⟩) = some false := by decide
example : compare (.letE (.sort .zero) (.sort .zero) (.bvar 0)) (.sort .zero) = none := by decide
example : compare (.sort .zero) (.fvar 0 (.sort .zero)) = none := by decide

def entry (name parameter : Lean.Name) : ConstantInfo :=
  .axiomInfo ⟨sourceName name, [sourceName parameter], .sort .zero⟩
def aliases : Env := ⟨[entry `first `u, entry `second `v]⟩
def target : Env := ⟨[entry `shared `x]⟩
def aliasCompare := checkInstalledExpr aliases target (fun _ => sourceName `shared) identity
example : aliasCompare (.const (sourceName `first) [.zero])
    (.const (sourceName `shared) [.max .zero .zero]) = some true := by decide
example : aliasCompare (.const (sourceName `second) [.zero])
    (.const (sourceName `shared) [.zero]) = some true := by decide
example : aliasCompare (.const (sourceName `first) [])
    (.const (sourceName `shared) []) = some false := by decide
example : aliasCompare (.const (sourceName `first) [.zero])
    (.const (sourceName `missing) [.zero]) = some false := by decide

def pins : Env := ⟨stringImagePins.map fun (name, levels) =>
  .axiomInfo ⟨name, levels.map fun _ => sourceName `u, .sort .zero⟩⟩
def pinCompare := checkInstalledExpr pins pins id identity
-- Large literals are compared through pin obligations, without unary expansion.
example : pinCompare (.lit (.natVal 1000000000000)) (.lit (.natVal 1000000000000)) = some true := by decide
example : pinCompare (.lit (.natVal 1)) (.lit (.natVal 2)) = some false := by decide
example : compare (.lit (.natVal 0)) (.lit (.natVal 0)) = some false := by decide
example : pinCompare (.lit (.strVal "λ")) (.lit (.strVal "λ")) = some true := by decide
example : checkInstalledExpr pins pins (fun _ => sourceName `wrong) identity
    (.lit (.natVal 0)) (.lit (.natVal 0)) = some false := by decide

def table (offset : Nat) : Env := ⟨[.projInfo {
  structName := sourceName `Pair, levelParams := [], numParams := 0,
  ctor := sourceName `Pair.mk, numFields := 2, structSort := .zero,
  bodies := #[.sort .zero, .sort .zero], guards := [.zero, .zero], off := offset }]⟩

example : checkInstalledProjection (table 1) (table 0) id
    (sourceName `Pair) (sourceName `Pair) 0 1 = true := by decide
example : checkInstalledProjection (table 1) (table 0) id
    (sourceName `Pair) (sourceName `Pair) 0 0 = false := by decide
example : checkInstalledProjection (table 0) Env.empty id
    (sourceName `Pair) (sourceName `Pair) 0 0 = false := by decide
example : checkInstalledProjection Env.empty Env.empty id
    (sourceName `Pair) (sourceName `Pair) 1 1 = true := by decide
example : checkInstalledProjection Env.empty Env.empty id
    (sourceName `Pair) (sourceName `Pair) 2 2 = false := by decide

end Tests.Ix.CompileCert.InstalledImage
