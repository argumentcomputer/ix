module

public import IxC.Kernel.RoleEquations
public import Ix.IxVM.RoleSpecGen

/-! # Render the shared role specifications for the Rust checker

This renderer reads `Role.spec`, the canonical group order, and the same
telescope-closing functions as the Lean equation checker. Rust receives
closed syntax over bound role addresses, never a second handwritten set of
equations. The generated code only constructs specifications; admission must
check the carried declarations and evidence before enabling their reductions.
-/

@[expose] public section

namespace Ix.RoleBinding.RustSpecGen

open Ix.Kernel

def role (r : Role) : String := s!"Role::ALL[{IxVM.RoleSpecGen.roleIdx r}]"

def roleKey : Key .anon → Except String String
  | .role r => pure (role r)
  | _ => throw "a Rust role specification mentions a non-role key"

def level (parameters : List LevelParam) : Level → Except String String
  | .zero => pure "U::zero()"
  | .succ u => return s!"U::succ({← level parameters u})"
  | .max u v => return s!"U::max({← level parameters u}, {← level parameters v})"
  | .imax u v => return s!"U::imax({← level parameters u}, {← level parameters v})"
  | .param n =>
    if parameters.contains n then pure s!"param({parameters.idxOf n})"
    else throw s!"undeclared universe parameter {n} in a Rust role specification"

def expr (parameters : List LevelParam) : Expr .anon → Except String String
  | .bvar n => pure s!"var({n})"
  | .fvar .. => throw "an open variable in a Rust role specification"
  | .sort u => return s!"sort({← level parameters u})"
  | .const key universes => do
    let us ← universes.mapM (level parameters)
    return s!"reference(source, {← roleKey key}, &[{", ".intercalate us}])?"
  | .app f a => return s!"app({← expr parameters f}, {← expr parameters a})"
  | .lam t b _ => return s!"lam({← expr parameters t}, {← expr parameters b})"
  | .forallE t b _ => return s!"pi({← expr parameters t}, {← expr parameters b})"
  | .letE t v b _ =>
    return s!"E::let_((), {← expr parameters t}, {← expr parameters v}, {← expr parameters b}, false)"
  | .lit _ => throw "a literal in a Rust role specification"
  | .proj key field value =>
    return s!"E::prj(KId::new(source.required_role({← roleKey key}).map_err(|e| e.to_string())?.clone(), ()), {field}, {← expr parameters value})"

def closedExpr (parameters : List LevelParam) (term : Expr .anon) : Except String String := do
  unless term.looseBVarsBounded 0 && !term.hasFvar && term.allLevelParamsDefined parameters do
    throw "an open or undeclared term in a Rust role specification"
  expr parameters term

def equation (parameters : List LevelParam) (eq : Equation .anon) : Except String String := do
  let statement ← closedExpr parameters eq.statement
  let sides ← if eq.hyps.isEmpty then do
      let lhs ← closedExpr parameters (eq.closedSide eq.lhs)
      let rhs ← closedExpr parameters (eq.closedSide eq.rhs)
      pure s!"Some(({lhs}, {rhs}))"
    else pure "None"
  return s!"Equation \{ statement: {statement}, definitional_sides: {sides} }"

def specification (r : Role) : Except String (Option String) := do
  match r.spec (md := .anon) with
  | .anchor levels type =>
    return some s!"Specification::Anchor \{ levels: {levels}, typ: {← closedExpr (List.range levels) type} }"
  | .eqns levels type equations =>
    let typ ← closedExpr (List.range levels) type
    let equations ← equations.mapM (equation (List.range levels))
    return some s!"Specification::Definition \{ levels: {levels}, typ: {typ}, equations: vec![{", ".intercalate equations}] }"
  | _ => pure none

def header : String := "// Generated from IxC's Role.spec by Ix/RoleBinding/RustSpecGen.lean.
// Run scripts/RustRoleSpecs.lean to regenerate or check this file.
// These terms describe candidates; only checked admission enables reductions.

use super::equations::{Equation, SpecGroup, Specification, reference};
use super::*;

"

def render : Except String String := do
  IxVM.RoleSpecGen.checkGroups
  let digest ← Ix.SpecDigest.specDigest
  let mut out := header ++ s!"// Specification version {specVersion}; digest {digest}.\n\n"
  out := out ++ "#[rustfmt::skip]\npub(super) const GROUPS: &[SpecGroup] = &[\n"
  for group in IxVM.RoleSpecGen.groups do
    let roles := ", ".intercalate (group.map role)
    let needs := ", ".intercalate ((IxVM.RoleSpecGen.groupNeeds group).map role)
    out := out ++ s!"  SpecGroup \{ roles: &[{roles}], needs: &[{needs}] },\n"
  out := out ++ "];\n\n#[rustfmt::skip]\npub(super) fn specification(role: Role, source: &ArtifactSource) -> Result<Option<Specification>, String> {\n  Ok(Some(match role.index() {\n"
  let mut arms : Array (List Nat × String) := #[]
  for r in Role.all do
    if let some spec ← specification r then
      let index := IxVM.RoleSpecGen.roleIdx r
      if let some slot := arms.findIdx? (fun arm => arm.2 == spec) then
        arms := arms.modify slot fun (indices, body) => (indices ++ [index], body)
      else arms := arms.push ([index], spec)
  for (indices, spec) in arms do
    out := out ++ s!"    {" | ".intercalate (indices.map toString)} => {spec},\n"
  out := out ++ "    _ => return Ok(None),\n  }))\n}\n"
  return out

/-- An independent wire-shape fixture for Rust's candidate checks. -/
def shape : String := Id.run do
  let indices (roles : List Role) :=
    ",".intercalate (roles.map fun r => toString (IxVM.RoleSpecGen.roleIdx r))
  let kind : Option Bool → String
    | some true => "defeq"
    | some false => "proof"
    | none => "either"
  let mut out := s!"# Role.block/deps and Spec.evidenceAllowed, version{specVersion}\n"
  for r in Role.all do
    let kinds := ",".intercalate ((r.spec (md := .anon)).evidenceAllowed.map kind)
    out := out ++ s!"{IxVM.RoleSpecGen.roleIdx r}\t{indices r.block}\t{indices r.deps}\t{kinds}\n"
  return out

end Ix.RoleBinding.RustSpecGen
