module

public import Lean
public import Ix.Compile.CircuitContract.Basic
public meta import Ix.Compile.CircuitContract.Basic

/-!
# Scoped `Ix.Circuit` attributes and `checked def` frontend (`Ix.Compile.CircuitContract.Attr`)

Activates strictly under `open scoped Ix.Circuit`.

## Zero `TokenTable` pollution & zero Ixon address mutation

* All new attribute names (`circuit_inline`, `circuit_noinline`, `circuit_group`,
  `circuit_unroll`, `circuit_lanes`, `circuit_budget`, `circuit_range_table`) and
  `checked def` keywords (`checked`, `hint`, `check`) use `nonReservedSymbol`,
  adding **zero** tokens to Lean's global `TokenTable`.
* Every `@[circuit_*]` attribute registers metadata exclusively in
  `Ix.Compile.CircuitContract.circuitAttrExtension` (`SimplePersistentEnvExtension`)
  without touching the elaborated `Lean.ConstantInfo`. Consequently, annotating a
  definition with `@[circuit_*]` never mutates its Ixon content address.
* `checked def` desugars to ordinary Lean declarations (`def foo`, `def foo.check`,
  `theorem foo.check_unique`) plus a sidecar `CircuitCheckedMeta` record in
  `circuitAttrExtension` for Tier-2 non-deterministic `guess` witnesses.
-/

set_option autoImplicit false

public meta section

namespace Ix.Compile.CircuitContract.AttrSyntax

open Lean Parser

/-! ### Scoped `@[circuit_*]` attribute parsers (zero `TokenTable` entries) -/

@[expose] def ix_circuit_inline := leading_parser
  nonReservedSymbol "circuit_inline"

@[expose] def ix_circuit_noinline := leading_parser
  nonReservedSymbol "circuit_noinline"

@[expose] def ix_circuit_group := leading_parser
  nonReservedSymbol "circuit_group" >> ppSpace >> strLit

@[expose] def ix_circuit_unroll := leading_parser
  nonReservedSymbol "circuit_unroll" >> ppSpace >> numLit

@[expose] def ix_circuit_lanes := leading_parser
  nonReservedSymbol "circuit_lanes" >> ppSpace >> numLit

/-- One ceiling in `@[circuit_budget ...]`: either a natural number literal or `_` (unchecked). -/
@[expose] def circuitBudgetBound := leading_parser
  numLit <|> Term.hole

/-- `@[circuit_budget maxChips maxCols maxCalls maxMem]` with optional 5th `maxTotalCols`.
Any position may be `_` to leave that ceiling unchecked. -/
@[expose] def ix_circuit_budget := leading_parser
  nonReservedSymbol "circuit_budget" >>
  ppSpace >> circuitBudgetBound >>
  ppSpace >> circuitBudgetBound >>
  ppSpace >> circuitBudgetBound >>
  ppSpace >> circuitBudgetBound >>
  optional (ppSpace >> circuitBudgetBound)

/-- Mode token for `@[circuit_range_table small|pair|auto]`. -/
@[expose] def circuitRangeMode := leading_parser
  nonReservedSymbol "small" <|> nonReservedSymbol "pair" <|> nonReservedSymbol "auto"

@[expose] def ix_circuit_range_table := leading_parser
  nonReservedSymbol "circuit_range_table" >> ppSpace >> circuitRangeMode

/-! ### Scoped `checked def` command parser for Tier-2 `guess` witnesses -/

/-- Scoped syntax for Tier-2 verified non-deterministic witness definitions:
```lean
checked def isqrt (x : Nat) : Nat :=
  hint Nat.sqrt x
  where check fun r => r * r ≤ x && x < (r + 1) * (r + 1)
  by
    intro r hr
    ...
```
Desugars to:
1. `def isqrt (x : Nat) : Nat := Nat.sqrt x` (ordinary Lean `def`; unchanged Ixon address),
2. `def isqrt.check (x : Nat) : Nat → Bool := fun r => ...`,
3. `theorem isqrt.check_unique (x : Nat) : ∀ (res : Nat), isqrt.check x res = true → res = isqrt x := by ...`,
plus a sidecar `CircuitCheckedMeta` registration in `circuitAttrExtension`. -/
@[expose] def checkedDefCmd := leading_parser
  Command.declModifiers false >>
  atomic (nonReservedSymbol "checked" (includeIdent := true) >> "def ") >>
  ident >>
  many (ppSpace >> Term.explicitBinder) >>
  " : " >> termParser >>
  " := " >>
  nonReservedSymbol "hint" >> termParser >>
  " where " >> optional (nonReservedSymbol "check") >> termParser >>
  " by " >> Tactic.tacticSeq

-- Register syntax node kinds locally without exporting any global parser.
section
attribute [local attr_parser]
  ix_circuit_inline
  ix_circuit_noinline
  ix_circuit_group
  ix_circuit_unroll
  ix_circuit_lanes
  ix_circuit_budget
  ix_circuit_range_table
attribute [local command_parser] checkedDefCmd
end

end Ix.Compile.CircuitContract.AttrSyntax

end

public section

namespace Ix.Compile.CircuitContract.AttrElab

open Lean Elab Command Term

private meta def addAttrEntry (attrLabel : String) (declName : Lean.Name)
    (entry : CircuitAttrEntry) : AttrM Unit := do
  let env ← getEnv
  let some source := (env.setExporting false).find? declName
    | throwUnknownConstant declName
  match source with
  | .thmInfo _ =>
    throwError "@[{attrLabel}] cannot be applied to theorem '{declName}'"
  | _ => pure ()
  match registerCircuitAttr env entry with
  | .ok env' => setEnv env'
  | .error err => throwError "{err}"

private meta def parseBudgetBound (stx : Syntax) : AttrM (Option Nat) := do
  let inner := stx[0]
  if inner.isOfKind ``Parser.Term.hole then
    return none
  else if let some n := inner.isNatLit? then
    return some n
  else
    throwErrorAt stx "expected natural number literal or '_' in @[circuit_budget]"

private meta def parseRangeMode (stx : Syntax) : AttrM CircuitRangeCheckMode := do
  let atom := stx[0]
  if !atom.isAtom then
    throwErrorAt stx "expected 'small', 'pair', or 'auto' in @[circuit_range_table]"
  match atom.getAtomVal with
  | "small" => return .smallTable
  | "pair" => return .pairTable
  | "auto" => return .auto
  | other => throwErrorAt stx "invalid @[circuit_range_table] mode '{other}' (expected 'small', 'pair', or 'auto')"

meta initialize registerBuiltinAttribute {
  name := `ix_circuit_inline
  descr := "Mark a definition for mandatory circuit inlining (InlinePolicy.always)."
  add := fun decl _ kind => do
    unless kind == AttributeKind.global do
      throwError "@[circuit_inline] cannot be local or scoped"
    addAttrEntry "circuit_inline" decl { declName := decl, inline := some .always }
}

meta initialize registerBuiltinAttribute {
  name := `ix_circuit_noinline
  descr := "Keep a definition as a dedicated memoized chip (InlinePolicy.never)."
  add := fun decl _ kind => do
    unless kind == AttributeKind.global do
      throwError "@[circuit_noinline] cannot be local or scoped"
    addAttrEntry "circuit_noinline" decl { declName := decl, inline := some .never }
}

meta initialize registerBuiltinAttribute {
  name := `ix_circuit_group
  descr := "Assign a definition's compiled chip to a named co-packing group."
  add := fun decl stx kind => do
    unless kind == AttributeKind.global do
      throwError "@[circuit_group] cannot be local or scoped"
    let some groupName := stx[1].isStrLit?
      | throwErrorAt stx "expected string literal group name in @[circuit_group \"name\"]"
    addAttrEntry "circuit_group" decl { declName := decl, group := some groupName }
}

meta initialize registerBuiltinAttribute {
  name := `ix_circuit_unroll
  descr := "Set the compile-time loop unroll factor for a definition."
  add := fun decl stx kind => do
    unless kind == AttributeKind.global do
      throwError "@[circuit_unroll] cannot be local or scoped"
    let some n := stx[1].isNatLit?
      | throwErrorAt stx "expected positive natural number literal in @[circuit_unroll N]"
    addAttrEntry "circuit_unroll" decl { declName := decl, unroll := some n }
}

meta initialize registerBuiltinAttribute {
  name := `ix_circuit_lanes
  descr := "Set the horizontal vectorization lane width K for a definition."
  add := fun decl stx kind => do
    unless kind == AttributeKind.global do
      throwError "@[circuit_lanes] cannot be local or scoped"
    let some k := stx[1].isNatLit?
      | throwErrorAt stx "expected positive natural number literal in @[circuit_lanes K]"
    addAttrEntry "circuit_lanes" decl { declName := decl, lanes := some k }
}

meta initialize registerBuiltinAttribute {
  name := `ix_circuit_budget
  descr := "Attach fail-closed circuit compilation ceilings (maxChips maxCols maxCalls maxMem [maxTotalCols])."
  add := fun decl stx kind => do
    unless kind == AttributeKind.global do
      throwError "@[circuit_budget] cannot be local or scoped"
    let maxChips ← parseBudgetBound stx[1]
    let maxColumns ← parseBudgetBound stx[2]
    let maxCallsPerChip ← parseBudgetBound stx[3]
    let maxMemoryPerChip ← parseBudgetBound stx[4]
    let maxTotalColumns ←
      if stx[5].isNone then pure none
      else parseBudgetBound stx[5][0]
    let budget : CircuitBudget :=
      { maxChips, maxColumns, maxCallsPerChip, maxMemoryPerChip, maxTotalColumns }
    addAttrEntry "circuit_budget" decl { declName := decl, budget := some budget }
}

meta initialize registerBuiltinAttribute {
  name := `ix_circuit_range_table
  descr := "Select the range-check lookup table strategy (small | pair | auto)."
  add := fun decl stx kind => do
    unless kind == AttributeKind.global do
      throwError "@[circuit_range_table] cannot be local or scoped"
    let mode ← parseRangeMode stx[1]
    addAttrEntry "circuit_range_table" decl { declName := decl, rangeCheck := some mode }
}

/-! ### Elaborator for `checked def` -/

/-- Build a `declModifiers` keeping only visibility (e.g. `private`/`protected`) so
companion `.check` and `.check_unique` declarations inherit visibility without
duplicating docstrings or `@[circuit_*]` attributes. -/
private meta def visibilityOnlyModifiers (mods : Syntax) : TSyntax ``Parser.Command.declModifiers :=
  let empty := mkNullNode #[]
  let vis := if mods.getNumArgs >= 3 then mods[2] else empty
  ⟨mkNode ``Parser.Command.declModifiers #[empty, empty, vis, empty, empty, empty]⟩

/-- Collect argument identifier terms from an array of `Parser.Term.explicitBinder` nodes. -/
private meta def collectExplicitBinderArgs (binders : Array Syntax) :
    CommandElabM (Array (TSyntax `term)) := do
  let mut args : Array (TSyntax `term) := #[]
  for b in binders do
    let binderIdents := b[1].getArgs
    for bi in binderIdents do
      if bi.isIdent then
        args := args.push (mkIdentFrom bi bi.getId)
      else
        throwErrorAt bi "checked def parameters must be named identifiers (anonymous '_' binders are not supported)"
  return args

@[command_elab AttrSyntax.checkedDefCmd]
meta def elabCheckedDef : CommandElab := fun stx => do
  let mods : TSyntax ``Parser.Command.declModifiers := ⟨stx[0]⟩
  let visMods := visibilityOnlyModifiers stx[0]
  let nameId : Ident := ⟨stx[3]⟩
  let rawBinders := stx[4].getArgs
  let binders : Array (TSyntax ``Parser.Term.bracketedBinder) := rawBinders.map (⟨·⟩)
  let retTy : TSyntax `term := ⟨stx[6]⟩
  let hintTerm : TSyntax `term := ⟨stx[9]⟩
  let checkTerm : TSyntax `term := ⟨stx[12]⟩
  let tacticSeq : TSyntax ``Parser.Tactic.tacticSeq := ⟨stx[14]⟩
  let args ← collectExplicitBinderArgs rawBinders
  let checkId : Ident := mkIdentFrom nameId (nameId.getId ++ `check)
  let uniqueId : Ident := mkIdentFrom nameId (nameId.getId ++ `check_unique)
  -- 1. Ordinary Lean definition (unchanged ConstantInfo / Ixon content address)
  let defCmd ←
    `($mods:declModifiers def $nameId $binders:bracketedBinder* : $retTy := $hintTerm)
  -- 2. Companion Boolean checker predicate for Tier-2 prover witness verification
  let checkCmd ←
    `($visMods:declModifiers def $checkId $binders:bracketedBinder* : $retTy → Bool := $checkTerm)
  -- 3. Kernel-checked uniqueness theorem tying the checker back to the ordinary definition
  let fooApp : TSyntax `term ←
    if args.isEmpty then `($nameId)
    else `($nameId $args*)
  let checkApp : TSyntax `term ←
    if args.isEmpty then `($checkId)
    else `($checkId $args*)
  let uniqueCmd ←
    `($visMods:declModifiers theorem $uniqueId $binders:bracketedBinder* :
        ∀ (res : $retTy), $checkApp res = true → res = $fooApp := by $tacticSeq)
  elabCommand defCmd
  elabCommand checkCmd
  elabCommand uniqueCmd
  -- 4. Record sidecar linkage in `circuitAttrExtension` without mutating any ConstantInfo
  let fullFooName ← liftCoreM (realizeGlobalConstNoOverload nameId)
  let fullCheckName ← liftCoreM (realizeGlobalConstNoOverload checkId)
  let fullUniqueName ← liftCoreM (realizeGlobalConstNoOverload uniqueId)
  let env ← getEnv
  let entry : CircuitAttrEntry := {
    declName := fullFooName
    checked := some { checkDecl := fullCheckName, uniqueThm := fullUniqueName }
  }
  match registerCircuitAttr env entry with
  | .ok env' => setEnv env'
  | .error err => throwErrorAt stx "{err}"

end Ix.Compile.CircuitContract.AttrElab

/-! ### Scoped activation (`open scoped Ix.Circuit`) -/

namespace Ix.Circuit

attribute [scoped attr_parser 2000]
  Ix.Compile.CircuitContract.AttrSyntax.ix_circuit_inline
  Ix.Compile.CircuitContract.AttrSyntax.ix_circuit_noinline
  Ix.Compile.CircuitContract.AttrSyntax.ix_circuit_group
  Ix.Compile.CircuitContract.AttrSyntax.ix_circuit_unroll
  Ix.Compile.CircuitContract.AttrSyntax.ix_circuit_lanes
  Ix.Compile.CircuitContract.AttrSyntax.ix_circuit_budget
  Ix.Compile.CircuitContract.AttrSyntax.ix_circuit_range_table

attribute [scoped command_parser 2000]
  Ix.Compile.CircuitContract.AttrSyntax.checkedDefCmd

end Ix.Circuit

end
