/-
  Ix.AuxGen.RecOn: `.recOn` generation — reorders `.rec` arguments.

  Port of `crates/compile/src/compile/aux_gen/rec_on.rs`.

  `.rec` binder order:   params, motives, minors, indices, major
  `.recOn` binder order: params, motives, indices, major, minors

  Uses FVar-based construction: open all rec binders into FVars, reorder
  the FVar/declaration arrays, then close back with `mkForall`/`mkLambda`.
  Follows `refs/lean4/src/Lean/Meta/Constructions/RecOn.lean`.

  PARITY RULE: every constructed node goes through the hash-maintaining
  smart constructors in `Ix.Environment` (`Expr.mkApp`, `Level.mkParam`,
  ...) so the embedded blake3 hashes stay bit-identical with the Rust
  compiler.
-/
module
public import Ix.Environment
public import Ix.AuxGen.Types
public import Ix.AuxGen.ExprUtils
public section

namespace Ix.AuxGen

/-- Mirrors Rust `generate_rec_on` (aux_gen/rec_on.rs:20).

    Generate a `.recOn` definition from a canonical `.rec`.
    Returns `none` if the recursor type cannot be decomposed.

    (Deviation: the Rust `num_*.to_u64()?` big-nat conversions cannot fail
    here — `Ix.RecursorVal` carries native `Nat` counts, so the four
    early-`None` conversion exits vanish.) -/
def generateRecOn (name : Name) (recVal : RecursorVal) : Option AuxDef :=
  let nParams := recVal.numParams
  let nMotives := recVal.numMotives
  let nMinors := recVal.numMinors
  let nIndices := recVal.numIndices

  let acSize := nParams + nMotives -- params + motives (kept in place)
  let total := acSize + nMinors + nIndices + 1

  -- Open all foralls into FVars (equivalent to Lean's forallTelescope).
  let (fvars, decls, body) := forallTelescope recVal.cnst.type total "ro" 0
  if fvars.size < total then
    none
  else
    -- Build rec application: rec fvar[0] fvar[1] ... fvar[n-1] (original
    -- order).
    let recUnivs : Array Level := recVal.cnst.levelParams.map Level.mkParam
    let recApp := mkAppN (mkConst recVal.cnst.name recUnivs) fvars

    -- Reorder declarations and FVars:
    --   before: [params, motives, minors, indices, major]
    --   after:  [params, motives, indices, major, minors]
    --
    -- This matches RecOn.lean lines 25-29:
    --   vs = xs[*...AC_size]
    --     ++ xs[(AC_size + numMinors) ... (AC_size + numMinors + 1 + numIndices)]
    --     ++ xs[AC_size ... (AC_size + numMinors)]
    let reordered : Array LocalDecl :=
      decls.extract 0 acSize
        ++ decls.extract (acSize + nMinors) total
        ++ decls.extract acSize (acSize + nMinors)

    -- Close back into BVar form with reordered binders.
    -- mkForall/mkLambda handle all de Bruijn index calculation
    -- automatically.
    let recOnType := mkForall body reordered
    let recOnValue := mkLambda recApp reordered

    some {
      name
      levelParams := recVal.cnst.levelParams
      typ := recOnType
      value := recOnValue
      -- `.recOn` mirrors the recursor's safety — Lean builds it via
      -- `mkDefinitionValInferringUnsafe`
      -- (`Lean/Meta/Constructions/RecOn.lean:32`) and the inferred safety
      -- matches the parent inductive since the value references the
      -- inductive's `.rec`.
      isUnsafe := recVal.isUnsafe }

end Ix.AuxGen

end
