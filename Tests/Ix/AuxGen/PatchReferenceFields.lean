import Ix.AuxGen.Types
import Lean.Elab.Command

/-! A manually encoded record must not silently acquire an omitted field.
Constructor matches already cover the Name/Level/Expr/patch sum types;
raw mdata explicitly refuses. Check every encoded structure and parent list. -/

run_cmd do
  let env ← Lean.getEnv
  let records : Array (Lean.Name × Array Lean.Name) := #[
    (``ByteArray, #[`data]), (``Address, #[`hash]),
    (``Ix.ConstantVal, #[`name, `levelParams, `type]),
    (``Ix.RecursorRule, #[`ctor, `nfields, `rhs]),
    (``Ix.RecursorVal, #[`cnst, `all, `numParams, `numIndices, `numMotives, `numMinors, `rules, `k, `isUnsafe]),
    (``Ix.InductiveVal, #[`cnst, `numParams, `numIndices, `all, `ctors, `numNested, `isRec, `isUnsafe, `isReflexive]),
    (``Ix.ConstructorVal, #[`cnst, `induct, `cidx, `numParams, `numFields, `isUnsafe]),
    (``Ix.AuxGen.AuxDef, #[`name, `levelParams, `typ, `value, `isUnsafe]),
    (``Ix.AuxGen.BelowDef, #[`name, `levelParams, `typ, `value, `isUnsafe]),
    (``Ix.AuxGen.BelowCtor, #[`name, `typ, `nParams, `nFields]),
    (``Ix.AuxGen.BelowIndc, #[`name, `levelParams, `nParams, `nIndices, `isReflexive, `isUnsafe, `typ, `ctors]),
    (``Ix.AuxGen.BRecOnDef, #[`name, `levelParams, `typ, `value, `isUnsafe, `isProp]),
    (``Ix.AuxGen.AuxPatchesOutput, #[`patches, `aliases, `perm, `evaporated, `nCanonicalAux, `canonicalRecs])]
  unless records.size == 13 do throwError "patch reference field census coverage differs"
  for (decl, expected) in records do
    let some info := Lean.getStructureInfo? env decl | throwError "encoded structure missing: {decl}"
    unless info.fieldNames == expected && info.parentInfo.isEmpty do
      throwError "encoded structure changed: {decl}; fields={info.fieldNames}, parents={info.parentInfo.map (·.structName)}"
