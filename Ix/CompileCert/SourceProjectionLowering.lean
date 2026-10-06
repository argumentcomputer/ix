import Ix.CompileCert.SourceInstallation

/-! # The lowering receipt for source projection functions

A projection function `f : ∀ p⃗ (self : T p⃗), R` of a structure-like `T` that
the certified checker does not serve natively (a member of a mutual block, a
nested structure-like) has the Lean value `fun p⃗ self => .proj T i self`. The
checker's semantics gives `.proj` no meaning at such a `T` (no projection
table), so the original value has no denotation in the installed source model,
and no model-side statement can relate it to anything. The normalised source
route therefore installs the recursor form (`Kernel.Frontend.projRecValue`)

    fun p⃗ (self : T p⃗) => T.rec.{ℓ, u⃗} p⃗ motives… minors… self

and this module's receipt relates it to the original **in Lean's logic**:

* decidable syntactic checks: the replacement keeps the original header and
  hint; its `nP + 1` λ-domains are the declared type's Π-domains; it is
  exactly `projRecValue` of a recipe read only from the original recursor
  `T.rec`, at the universe `ℓ` its own recursor head carries;
* a Lean theorem `f._ix_projection_lowering`, built by the certifier and
  accepted by Lean's kernel at certification time, whose statement exports
  exactly to `∀ p⃗ (self : T p⃗), @Eq.{ℓ} R (f p⃗ self) (value p⃗ self)` over the
  declared type's own telescope, with the same `ℓ`. Lean's kernel accepting
  `@Eq.{ℓ} R …` means it inferred `R : Sort ℓ`: the elimination level is the
  sort of `R` by inference, not the modeller's `proj_i.iota` artifact.

What is *not* proved here: that the listed theorems were accepted by Lean's
kernel. The certifier submits each one with `Lean.Environment.addDeclCore`
(checking on) and lists only accepted ones; this is the same kind of trust as
the host `Lean.Environment` the source capture reads. -/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

/-- Lean theorems built by the certifier and accepted by Lean's kernel. -/
abbrev LoweringWitnesses := List Lean.TheoremVal

/-- The name of the Lean lowering equation of projection function `f`. -/
def loweringEquationName (projection : Lean.Name) : Lean.Name :=
  projection.str "_ix_projection_lowering"

/-- The `count` leading binders of a telescope as arguments, outermost first. -/
def loweringArguments (count : Nat) : List Kernel.Expr :=
  (List.range count).map (fun i => .bvar (count - 1 - i))

/-- `∀ D⃗, @Eq.{level} R (f.{u⃗} args) (value args)`, over the first `count`
binders `D⃗` of the declared type and its remaining body `R`. The right-hand
side applies `value` as it is installed; it is not β-reduced. -/
def loweringStatement (header : Kernel.ConstantVal) (count : Nat) (value : Kernel.Expr)
    (level : Kernel.Level) : Option Kernel.Expr := do
  let (binders, result) ← header.type.stripPis count
  let arguments := loweringArguments count
  let lhs := Kernel.Expr.mkAppN (.const header.name (header.levelParams.map Kernel.Level.param)) arguments
  let rhs := Kernel.Expr.mkAppN value arguments
  let equation := Kernel.Expr.mkAppN (.const Kernel.eqName [level]) [result, lhs, rhs]
  return binders.foldr (fun (type, binder) body => .forallE type body binder) equation

/-- The installed value named by a lowering statement: the head of its
right-hand side. Untrusted extraction; the receipt rebuilds the statement. -/
def loweringValueOf (count : Nat) (statement : Kernel.Expr) : Option Kernel.Expr := do
  let (_, equation) ← statement.stripPis count
  let rhs ← equation.getAppArgs.getLast?
  return rhs.getAppFn

/-- The universe at the recursor head of a lowered value: its elimination level. -/
def loweredLevel (count : Nat) (value : Kernel.Expr) : Option Kernel.Level :=
  match value.stripLams count with
  | some (_, body) =>
    match body.getAppFn with
    | .const _ (level :: _) => some level
    | _ => none
  | none => none

/-- The first `count` λ-domains. -/
def lambdaDomains (count : Nat) (value : Kernel.Expr) : Option (List Kernel.Expr) :=
  (value.stripLams count).map fun (binders, _) => binders.map (·.1)

/-- The first `count` Π-domains. -/
def piDomains (count : Nat) (type : Kernel.Expr) : Option (List Kernel.Expr) :=
  (type.stripPis count).map fun (binders, _) => binders.map (·.1)

/-- The rewrite's recipe, from the original recursor's export only. -/
def sourceProjectionRecipe (source : Source) (site : SourceProjectionSite source) :
    ExportM Kernel.Frontend.ProjRecOwner := do
  let some (.recInfo recursor) := source.find (site.ownerName.str "rec")
    | throw "source projection owner has no original recursor"
  unless recursor.numParams == site.owner.numParams && recursor.numIndices == 0 do
    throw "source projection recursor parameters or indices differ from original owner"
  let .recursor recHeader _ _ _ ← exportSourceEntry (.recInfo recursor)
    | throw "source projection recursor export has the wrong kind"
  return {
    T := sourceName site.ownerName, lps := site.owner.levelParams.map sourceName,
    nP := site.owner.numParams, ctor := sourceName site.ctorName, nF := site.ctor.numFields,
    recName := recHeader.name, recLps := recHeader.levelParams, recType := recHeader.type,
    numMotives := recursor.numMotives, numMinors := recursor.numMinors }

/-- The value of a source declaration that can be a projection function: a
definition, or a theorem (Lean makes the projection onto a proof field a
theorem). Read explicitly: `ConstantInfo.value?` omits theorems. -/
def projectionSourceValue : Lean.ConstantInfo → Option Lean.Expr
  | .defnInfo d => some d.value
  | .thmInfo t => some t.value
  | _ => none

/-- The declaration an exported definition or theorem entry installs as. -/
def entryDeclaration : DirectEntry → Option Kernel.Declaration
  | .defn header value hint => some (.defnDecl header value hint)
  | .thm header value => some (.thmDecl header value)
  | _ => none

/-- Header and value of a definition or theorem declaration. -/
def declarationParts : Kernel.Declaration → Option (Kernel.ConstantVal × Kernel.Expr)
  | .defnDecl header value _ => some (header, value)
  | .thmDecl header value => some (header, value)
  | _ => none

/-- The same declaration (kind, header and, for a definition, hint) with another value. -/
def replaceValue : Kernel.Declaration → Kernel.Expr → Kernel.Declaration
  | .defnDecl header _ hint, value => .defnDecl header value hint
  | .thmDecl header _, value => .thmDecl header value
  | declaration, _ => declaration

/-- The lowering receipt. Every field is decided by
`checkSourceProjectionLowering`; `faithful` states its content. -/
structure SourceProjectionLowering (source : Source) (witnesses : LoweringWitnesses)
    (original replacement : Kernel.Declaration) where
  ci : Lean.ConstantInfo
  original_lookup : source.find ci.name = some ci
  sourceValue : Lean.Expr
  source_value : projectionSourceValue ci = some sourceValue
  entry : DirectEntry
  exported : exportSourceEntry ci = .ok entry
  original_entry : entryDeclaration entry = some original
  header : Kernel.ConstantVal
  body : Kernel.Expr
  parts : declarationParts original = some (header, body)
  ownerName : Lean.Name
  field : Nat
  site : SourceProjectionSite source
  site_checked : sourceProjectionSite source ownerName field = .ok site
  raw_shape : sourceProjectionBody sourceValue = some (ownerName, field, site.owner.numParams + 1)
  value : Kernel.Expr
  replacement_decl : replacement = replaceValue original value
  closed : value.looseBVarsBounded 0 = true
  domains_present : (piDomains (site.owner.numParams + 1) header.type).isSome = true
  domains : lambdaDomains (site.owner.numParams + 1) value = piDomains (site.owner.numParams + 1) header.type
  recipe : Kernel.Frontend.ProjRecOwner
  recipe_checked : sourceProjectionRecipe source site = .ok recipe
  level : Kernel.Level
  level_read : loweredLevel (site.owner.numParams + 1) value = some level
  shape : Kernel.Frontend.projRecValue recipe level header.type body field = some value
  witness : Lean.TheoremVal
  witness_listed : witness ∈ witnesses
  witness_name : witness.name = loweringEquationName ci.name
  witness_levels : witness.levelParams = ci.levelParams
  statement : Kernel.Expr
  statement_built : loweringStatement header (site.owner.numParams + 1) value level = some statement
  witness_statement : exportSourceExpr ci.levelParams witness.type = .ok statement

/-- The decision procedure for `SourceProjectionLowering`. -/
def checkSourceProjectionLowering (source : Source) (witnesses : LoweringWitnesses)
    (original replacement : Kernel.Declaration) :
    ExportM (SourceProjectionLowering source witnesses original replacement) := do
  let some (originalHeader, _) := declarationParts original
    | throw "projection lowering original is not a definition or theorem"
  let some named := source.declarations.find?
      (fun ci => decide (sourceName ci.name = originalHeader.name))
    | throw "projection lowering original declaration is absent"
  match ho : source.find named.name with
  | none => throw "projection lowering does not identify the exact original declaration"
  | some ci =>
  if hn : ci.name = named.name then
  have originalLookup : source.find ci.name = some ci := by rw [hn]; exact ho
  match hv : projectionSourceValue ci with
  | none => throw "projection lowering original is not a definition or theorem of the source"
  | some sourceValue =>
  match he : exportSourceEntry ci with
  | .error why => throw s!"projection lowering source declaration could not be exported: {why}"
  | .ok entry =>
  if hd : entryDeclaration entry = some original then
  match hparts : declarationParts original with
  | none => throw "projection lowering original is not a definition or theorem"
  | some (header, body) =>
  match hb : sourceProjectionBody sourceValue with
  | none => throw "projection lowering original body is not a projection"
  | some (owner, field, binders) =>
  match hm : sourceProjectionSite source owner field with
  | .error why => throw why
  | .ok site =>
  if hs : binders = site.owner.numParams + 1 then
  let some (_, value) := declarationParts replacement
    | throw "projection lowering replacement is not a definition or theorem"
  if hr : replacement = replaceValue original value then
  if hc : value.looseBVarsBounded 0 = true then
  if hp : (piDomains (site.owner.numParams + 1) header.type).isSome = true then
  if hdom : lambdaDomains (site.owner.numParams + 1) value =
      piDomains (site.owner.numParams + 1) header.type then
  match hrec : sourceProjectionRecipe source site with
  | .error why => throw why
  | .ok recipe =>
  match hl : loweredLevel (site.owner.numParams + 1) value with
  | none => throw "projection lowering replacement has no recursor head"
  | some level =>
  if hshape : Kernel.Frontend.projRecValue recipe level header.type body field = some value then
  match hw : witnesses.find? (fun w => decide (w.name = loweringEquationName ci.name)) with
  | none => throw "projection lowering has no Lean-kernel-checked lowering equation"
  | some witness =>
  if hwl : witness.levelParams = ci.levelParams then
  match hst : loweringStatement header (site.owner.numParams + 1) value level with
  | none => throw "projection lowering statement cannot be formed over the declared type"
  | some statement =>
  match hx : exportSourceExpr ci.levelParams witness.type with
  | .error why => throw s!"projection lowering equation cannot be exported: {why}"
  | .ok exported =>
  if hsame : exported = statement then
    return ⟨ci, originalLookup, sourceValue, hv, entry, he, hd, header, body, hparts, owner, field,
      site, hm, by rw [hb, hs], value, hr, hc, hp, hdom, recipe, hrec, level, hl, hshape,
      witness, List.mem_of_find?_eq_some hw, by simpa using List.find?_some hw,
      hwl, statement, hst, hsame ▸ hx⟩
  else throw "projection lowering equation does not state the original function equal to the replacement"
  else throw "projection lowering equation has another universe telescope"
  else throw "projection lowering replacement is not the recursor form of the original field (spine, motive, minor or field index)"
  else throw "projection lowering binder domains differ from the declared type's domains"
  else throw "projection lowering declared type has too few binders"
  else throw "projection lowering replacement is not closed"
  else throw "projection lowering replacement changed the original kind, header or hint"
  else throw "projection lowering binder count differs from the original owner parameters"
  else throw "projection lowering original differs from its exact source export"
  else throw "projection lowering original identity is inconsistent"

/-- `replaceValue` keeps the kind, the header and (for a definition) the hint. -/
theorem declarationParts_replaceValue {original : Kernel.Declaration} {header : Kernel.ConstantVal}
    {body : Kernel.Expr} (parts : declarationParts original = some (header, body)) (value : Kernel.Expr) :
    declarationParts (replaceValue original value) = some (header, value) := by
  cases original <;> simp_all [declarationParts, replaceValue]

/-- **What a lowering receipt states.** The original declaration is the
installation form of the exact export of a definition or theorem `ci` of the
source; the replacement is the same declaration (kind, header, hint) with
another value; that value's `n` leading λ-domains are the declared type's `n`
leading Π-domains `D⃗` (with body `R`); and a listed Lean theorem, with `ci`'s
universe telescope, has a statement whose export is exactly
`∀ D⃗, @Eq.{ℓ} R (f.{u⃗} args) (value args)`, where `ℓ` is the elimination level
at the replacement's recursor head. With the listed theorems accepted by Lean's
kernel (the certifier's executable step), this says: in Lean's logic the
installed value is pointwise equal to the original function. -/
theorem SourceProjectionLowering.faithful {source : Source} {witnesses : LoweringWitnesses}
    {original replacement : Kernel.Declaration}
    (lowering : SourceProjectionLowering source witnesses original replacement) :
    ∃ (ci : Lean.ConstantInfo) (entry : DirectEntry) (header : Kernel.ConstantVal)
      (body value : Kernel.Expr) (count : Nat) (binders : List (Kernel.Expr × Kernel.BinderMeta))
      (result : Kernel.Expr) (level : Kernel.Level) (witness : Lean.TheoremVal),
      source.find ci.name = some ci ∧
      (projectionSourceValue ci).isSome ∧
      exportSourceEntry ci = .ok entry ∧
      entryDeclaration entry = some original ∧
      declarationParts original = some (header, body) ∧
      replacement = replaceValue original value ∧
      declarationParts replacement = some (header, value) ∧
      value.looseBVarsBounded 0 = true ∧
      header.type.stripPis count = some (binders, result) ∧
      lambdaDomains count value = some (binders.map (·.1)) ∧
      loweredLevel count value = some level ∧
      witness ∈ witnesses ∧
      witness.name = loweringEquationName ci.name ∧
      witness.levelParams = ci.levelParams ∧
      exportSourceExpr ci.levelParams witness.type = .ok
        (binders.foldr (fun (type, binder) body => .forallE type body binder)
          (Kernel.Expr.mkAppN (.const Kernel.eqName [level])
            [result,
             Kernel.Expr.mkAppN (.const header.name (header.levelParams.map Kernel.Level.param))
               (loweringArguments count),
             Kernel.Expr.mkAppN value (loweringArguments count)])) := by
  have built := lowering.statement_built
  cases hs : lowering.header.type.stripPis (lowering.site.owner.numParams + 1) with
  | none => simp [loweringStatement, hs] at built
  | some pair =>
    obtain ⟨binders, result⟩ := pair
    simp only [loweringStatement, hs, bind, Option.bind, pure, Option.some.injEq] at built
    have domains := lowering.domains
    simp only [piDomains, hs, Option.map_some] at domains
    have replaced : declarationParts replacement = some (lowering.header, lowering.value) := by
      have parts := declarationParts_replaceValue lowering.parts lowering.value
      rw [← lowering.replacement_decl] at parts
      exact parts
    refine ⟨lowering.ci, lowering.entry, lowering.header, lowering.body, lowering.value,
      lowering.site.owner.numParams + 1, binders, result, lowering.level, lowering.witness,
      lowering.original_lookup, by rw [lowering.source_value]; rfl, lowering.exported,
      lowering.original_entry, lowering.parts, lowering.replacement_decl,
      replaced,
      lowering.closed, hs, domains, lowering.level_read, lowering.witness_listed, lowering.witness_name,
      lowering.witness_levels, ?_⟩
    rw [lowering.witness_statement, ← built]

end Ix.CompileCert
