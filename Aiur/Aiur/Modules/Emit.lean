import Aiur.Modules.Function

/-! Kernel-checked emission of a resolved Aiur program. Function bodies are
quoted as Lean expressions; the program contains references to their named
constants, so execution and proofs share the same definitions. -/

namespace Aiur.Modules
open Lean Elab Command

/-- Quote canonically natural-valued elements of a type with `NatCast` using
ordinary numeral instances. Preserve the public type and numeral form so that
unfolding the emitted AST works with ordinary simplification lemmas. `toNat`
must represent each value faithfully through that type's natural-number cast. -/
def numeralQuoter {α : Type} (type : Lean.Expr) (toNat : α → Nat) : Term.TermElabM (ToExpr α) := do
  let zero ← Meta.mkNumeral type 0
  let one ← Meta.mkNumeral type 1
  let cast ← Meta.synthInstance (mkApp (mkConst ``NatCast [0]) type)
  return {
    toTypeExpr := type
    toExpr := fun x =>
      let n := toNat x
      if n == 0 then zero else if n == 1 then one else
      let atLeastTwo := mkApp2 (mkConst ``Nat.instAtLeastTwoHAddOfNat) (toExpr (n - 1))
        (mkApp (mkConst ``Nat.instNeZeroSucc) (toExpr (n - 2)))
      let inst := mkApp4 (mkConst ``instOfNatAtLeastTwo [0]) type (mkRawNatLit n) cast atLeastTwo
      mkApp3 (mkConst ``OfNat.ofNat [0]) type (mkRawNatLit n) inst }

private def emit (name : Name) (type value : Lean.Expr) : CommandElabM Unit := do
  liftCoreM <| addAndCompile (.defnDecl {
    name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  liftCoreM <| enableRealizationsForConst name

/-- Emit each resolved function once and assemble the program from those
constants. Static tables may be supplied by a shared generator rather than
quoting every row. All emitted definitions are checked by Lean's kernel. -/
def emitProgram {F : Type} [ToExpr F] (fieldType : Lean.Expr)
    (namespaceName : Name) (functionName : String → Name)
    (program : Generic.Program F) (tables : Lean.Expr) : CommandElabM Unit := do
  let functionType := mkApp (mkConst ``Generic.Function) fieldType
  let mut functions : List Lean.Expr := []
  for func in program.functions do
    let name := functionName func.name
    emit name functionType (toExpr func)
    functions := functions ++ [mkConst name]
  let functionList := functions.foldr (fun f tail => mkApp3 (mkConst ``List.cons [0]) functionType f tail)
    (mkApp (mkConst ``List.nil [0]) functionType)
  let sections := [
    ("functions", mkApp (mkConst ``List [0]) functionType, functionList),
    ("enums", toTypeExpr (List Generic.EnumDecl), toExpr program.enums),
    ("structs", toTypeExpr (List Generic.StructDecl), toExpr program.structs),
    ("maps", toTypeExpr (List Generic.MapDecl), toExpr program.maps),
    ("aliases", toTypeExpr (List Generic.AliasDecl), toExpr program.aliases),
    ("consts", mkApp (mkConst ``List [0]) (mkApp (mkConst ``Generic.ConstDecl) fieldType),
      toExpr program.consts)]
  for (name, type, value) in sections do
    emit (namespaceName.str name) type value
  let value := mkAppN (mkConst ``Generic.Program.mk) #[fieldType,
    mkConst (namespaceName.str "functions"), mkConst (namespaceName.str "enums"),
    mkConst (namespaceName.str "structs"), tables, mkConst (namespaceName.str "maps"),
    mkConst (namespaceName.str "aliases"), mkConst (namespaceName.str "consts")]
  emit (namespaceName.str "program") (mkApp (mkConst ``Generic.Program) fieldType) value

end Aiur.Modules
