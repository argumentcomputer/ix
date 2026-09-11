import Ix.Compiler.Ixon.Work

/-!
# Structured local validation for decoded Ixon constants

The byte codec deliberately remains a small, proof-oriented parser.  This
module is the resource-bounded ingress layer: it turns syntax failures into a
structured error and rejects table indices that the evaluator would otherwise
interpret as missing or (for universe variables) silently default to zero.

Validation is local to one constant.  Foreign declaration arities and
cross-constant projection/member metadata still belong to store ingestion.
The raw `de` API remains available for codec laws and wire-format fixtures;
untrusted constant bytes should enter through `decodeChecked`.
-/

namespace Ix.Compiler.Ixon.DecodeCheck

/-- The authoritative expression slot currently being validated. -/
inductive Root where
  | definitionType
  | definitionValue
  | recursorType
  | recursorRule (index : Nat)
  | axiomType
  | quotientType
  | inductiveType
  | constructorType (index : Nat)
  deriving BEq, DecidableEq, Repr

/-- A root is either in a standalone declaration or in one member of a
mutual block. -/
structure Site where
  member : Option Nat
  root : Root
  deriving BEq, DecidableEq, Repr

/-- The four expression forms whose payload indexes the local refs table. -/
inductive RefKind where
  | constant
  | string
  | natural
  | projectionType
  deriving BEq, DecidableEq, Repr

/-- Counted regions whose declared length is checked before any loop or
allocation begins. -/
inductive Sequence where
  | universeArguments
  | applicationSpine
  | lambdaTelescope
  | forallTelescope
  | recursorRules
  | constructors
  | mutualMembers
  | sharingTable
  | references
  | universes
  | universeSuccessors
  deriving BEq, DecidableEq, Repr

/-- Resource policy for untrusted constant bytes.  The defaults are per
constant (not per environment) and deliberately configurable so a corpus can
record a tighter budget without changing the wire format. -/
structure Limits where
  maxObjectBytes : Nat := 64 * 1024 * 1024
  maxExpressionDepth : Nat := 512
  maxUniverseDepth : Nat := 512
  maxSequenceLength : Nat := 4096
  /-- Inclusive charge for the quadratic layer-1 sharing scan. -/
  maxLayer1NodeVisits : Nat := 16 * 1024 * 1024
  deriving BEq, DecidableEq, Repr

def defaultLimits : Limits := {}

/-- Structured failures produced at the checked-ingress boundary.  `syntax`
wraps the existing proof-oriented parser diagnostics; all post-decode
semantic failures have data-bearing constructors. -/
inductive Error where
  | syntax (message : String)
  | objectTooLarge (actual limit : Nat)
  | expressionDepth (limit : Nat)
  | universeDepth (limit : Nat)
  | sequenceTooLong (sequence : Sequence) (actual limit : Nat)
  | resource (exceeded : Work.Exceeded)
  | sharingInvariant
  | refIndex (site : Site) (kind : RefKind) (index bound : Nat)
  | universeIndex (site : Site) (index bound : Nat)
  | universeVariable (site : Site) (index levels : Nat)
  | recurIndex (site : Site) (index bound : Nat)
  | unresolvedShare (site : Site) (index : Nat)
  | recursorTypeArity (site : Site) (expected actual : Nat)
  | recursorRuleArity (site : Site) (expected actual : Nat)
  deriving BEq, DecidableEq, Repr

inductive EncodeError where
  | wireNotRepresentable
  | invalid (error : Error)
  deriving BEq, DecidableEq, Repr

abbrev CheckM := Except Error

/-! ## Executable encoder domain

The theorem-facing `wireWF` predicates live in `Prop`; these boolean mirrors
are the executable guard used by the checked writer below. -/

def wireExprWF : Expr → Bool
  | .sort _ | .var _ | .str _ | .nat _ | .share _ => true
  | .ref _ indices | .recur _ indices =>
    decide (indices.size < UInt64.size)
  | .prj _ _ value => wireExprWF value
  | .app fn arg =>
    wireExprWF fn && wireExprWF arg &&
      decide (fn.appCount + 1 < UInt64.size)
  | .lam _ type body =>
    wireExprWF type && wireExprWF body &&
      decide (body.lamCount + 1 < UInt64.size)
  | .all _ _ domain codomain =>
    wireExprWF domain && wireExprWF codomain &&
      decide (codomain.allCount + 1 < UInt64.size)
  | .letE _ type value body =>
    wireExprWF type && wireExprWF value && wireExprWF body

theorem wireExprWF_eq_true_iff (e : Expr) :
    wireExprWF e = true ↔ e.wireWF := by
  induction e <;> simp_all [wireExprWF, Expr.wireWF, and_assoc]

def wireDefinitionWF (d : Definition) : Bool :=
  wireExprWF d.typ && wireExprWF d.value

def wireRecursorRuleWF (r : RecursorRule) : Bool :=
  wireExprWF r.rhs

def wireRecursorWF (r : Recursor) : Bool :=
  wireExprWF r.typ && decide (r.rules.size < UInt64.size) &&
    r.rules.all wireRecursorRuleWF

def wireAxiomWF (a : Axiom) : Bool := wireExprWF a.typ

def wireQuotientWF (q : Quotient) : Bool := wireExprWF q.typ

def wireConstructorWF (c : Constructor) : Bool := wireExprWF c.typ

def wireInductiveWF (i : Inductive) : Bool :=
  wireExprWF i.typ && decide (i.ctors.size < UInt64.size) &&
    i.ctors.all wireConstructorWF

def wireMutConstWF : MutConst → Bool
  | .defn d => wireDefinitionWF d
  | .indc i => wireInductiveWF i
  | .recr r => wireRecursorWF r

def wireConstantInfoWF : ConstantInfo → Bool
  | .defn d => wireDefinitionWF d
  | .recr r => wireRecursorWF r
  | .axio a => wireAxiomWF a
  | .quot q => wireQuotientWF q
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => true
  | .muts members =>
    decide (members.size < UInt64.size) &&
      members.all wireMutConstWF

def wireConstantWF (c : Constant) : Bool :=
  wireConstantInfoWF c.info &&
    decide (c.sharing.size < UInt64.size) &&
    c.sharing.all wireExprWF &&
    decide (c.refs.size < UInt64.size) &&
    decide (c.univs.size < UInt64.size)

private theorem forall_getElem_iff_forall_mem [BEq α]
    (values : Array α) (property : α → Prop) :
    (∀ (index : Nat) (h : index < values.size),
      property values[index]) ↔
      ∀ value, value ∈ values → property value := by
  constructor
  · intro h value hmem
    rcases Array.mem_iff_getElem.mp hmem with ⟨index, hi, heq⟩
    subst value
    exact h index hi
  · intro h index hi
    exact h values[index] (Array.getElem_mem hi)

theorem wireDefinitionWF_eq_true_iff (d : Definition) :
    wireDefinitionWF d = true ↔ d.wireWF := by
  simp [wireDefinitionWF, Definition.wireWF, wireExprWF_eq_true_iff]

theorem wireRecursorRuleWF_eq_true_iff (r : RecursorRule) :
    wireRecursorRuleWF r = true ↔ r.wireWF := by
  simp [wireRecursorRuleWF, RecursorRule.wireWF, wireExprWF_eq_true_iff]

theorem wireRecursorWF_eq_true_iff (r : Recursor) :
    wireRecursorWF r = true ↔ r.wireWF := by
  simp [wireRecursorWF, Recursor.wireWF, wireExprWF_eq_true_iff,
    wireRecursorRuleWF_eq_true_iff, forall_getElem_iff_forall_mem,
    and_assoc]

theorem wireAxiomWF_eq_true_iff (a : Axiom) :
    wireAxiomWF a = true ↔ a.wireWF := by
  simp [wireAxiomWF, Axiom.wireWF, wireExprWF_eq_true_iff]

theorem wireQuotientWF_eq_true_iff (q : Quotient) :
    wireQuotientWF q = true ↔ q.wireWF := by
  simp [wireQuotientWF, Quotient.wireWF, wireExprWF_eq_true_iff]

theorem wireConstructorWF_eq_true_iff (c : Constructor) :
    wireConstructorWF c = true ↔ c.wireWF := by
  simp [wireConstructorWF, Constructor.wireWF, wireExprWF_eq_true_iff]

theorem wireInductiveWF_eq_true_iff (i : Inductive) :
    wireInductiveWF i = true ↔ i.wireWF := by
  simp [wireInductiveWF, Inductive.wireWF, wireExprWF_eq_true_iff,
    wireConstructorWF_eq_true_iff, forall_getElem_iff_forall_mem,
    and_assoc]

theorem wireMutConstWF_eq_true_iff (m : MutConst) :
    wireMutConstWF m = true ↔ m.wireWF := by
  cases m <;> simp [wireMutConstWF, MutConst.wireWF,
    wireDefinitionWF_eq_true_iff, wireInductiveWF_eq_true_iff,
    wireRecursorWF_eq_true_iff]

theorem wireConstantInfoWF_eq_true_iff (info : ConstantInfo) :
    wireConstantInfoWF info = true ↔ info.wireWF := by
  cases info <;> simp [wireConstantInfoWF, ConstantInfo.wireWF,
    wireDefinitionWF_eq_true_iff, wireRecursorWF_eq_true_iff,
    wireAxiomWF_eq_true_iff, wireQuotientWF_eq_true_iff,
    wireMutConstWF_eq_true_iff, forall_getElem_iff_forall_mem]

theorem wireConstantWF_eq_true_iff (c : Constant) :
    wireConstantWF c = true ↔ c.wireWF := by
  simp [wireConstantWF, Constant.wireWF,
    wireConstantInfoWF_eq_true_iff, wireExprWF_eq_true_iff,
    forall_getElem_iff_forall_mem, and_assoc]

/-! ## Resource-bounded syntax decoder

The law-facing codec in `Const` remains unchanged.  This ingress decoder uses
the same strict primitive readers, but makes recursion and every input-driven
loop explicit.  Arrays and flattened expression spines are accumulated by
iteration, so their input counts do not become native call-stack depth. -/

private abbrev DecodeM := StateT GetState (Except Error)

private def liftSyntax (get : GetM α) : DecodeM α := fun state =>
  match get.run state with
  | .ok result => .ok result
  | .error message => .error (.syntax message)

private def guardSequence (limits : Limits) (sequence : Sequence)
    (count : Nat) : DecodeM Unit :=
  if count ≤ limits.maxSequenceLength then pure ()
  else throw (.sequenceTooLong sequence count limits.maxSequenceLength)

private def getArrayBounded (limits : Limits) (sequence : Sequence)
    (getOne : DecodeM α) (count : Nat) : DecodeM (Array α) := do
  guardSequence limits sequence count
  let mut values := #[]
  for _ in [:count] do
    values := values.push (← getOne)
  return values

private def getCountedArrayBounded (limits : Limits) (sequence : Sequence)
    (getOne : DecodeM α) : DecodeM (Array α) := do
  let count := (← liftSyntax getTag0).size.toNat
  getArrayBounded limits sequence getOne count

private def getUniverseArguments (limits : Limits)
    (count : Nat) : DecodeM (Array UInt64) := do
  guardSequence limits .universeArguments count
  let mut indices := #[]
  for _ in [:count] do
    indices := indices.push (← liftSyntax getTag0).size
  return indices

private def getExprBounded (limits : Limits) : Nat → DecodeM Expr
  | 0 => throw (.expressionDepth limits.maxExpressionDepth)
  | depth + 1 => do
    let tag ← liftSyntax getTag4
    let recur := getExprBounded limits depth
    match tag.flag with
    | 0x0 => return .sort tag.size
    | 0x1 => return .var tag.size
    | 0x2 => do
      let refIndex := (← liftSyntax getTag0).size
      return .ref refIndex
        (← getUniverseArguments limits tag.size.toNat)
    | 0x3 => do
      let recurIndex := (← liftSyntax getTag0).size
      return .recur recurIndex
        (← getUniverseArguments limits tag.size.toNat)
    | 0x4 => do
      let typeRefIndex := (← liftSyntax getTag0).size
      return .prj typeRefIndex tag.size (← recur)
    | 0x5 => return .str tag.size
    | 0x6 => return .nat tag.size
    | 0x7 => do
      let count := tag.size.toNat
      if count == 0 then throw (.syntax "getExpr: empty app spine")
      guardSequence limits .applicationSpine count
      let base ← recur
      match base with
      | .app .. => throw (.syntax "getExpr: non-canonical app base")
      | _ =>
        let mut result := base
        for _ in [:count] do
          result := .app result (← recur)
        return result
    | 0x8 => do
      let count := tag.size.toNat
      if count == 0 then throw (.syntax "getExpr: empty lam telescope")
      guardSequence limits .lambdaTelescope count
      let mut binders : List (Uses × Expr) := []
      for _ in [:count] do
        let mode ← liftSyntax getLamMode
        let type ← recur
        binders := (mode, type) :: binders
      let body ← recur
      match body with
      | .lam .. => throw (.syntax "getExpr: non-canonical lam telescope")
      | _ =>
        let mut result := body
        for binder in binders do
          result := .lam binder.1 binder.2 result
        return result
    | 0x9 => do
      let count := tag.size.toNat
      if count == 0 then throw (.syntax "getExpr: empty all telescope")
      guardSequence limits .forallTelescope count
      let mut binders : List (Uses × Owned × Expr) := []
      for _ in [:count] do
        let mode ← liftSyntax getAllMode
        let type ← recur
        binders := (mode.1, mode.2, type) :: binders
      let body ← recur
      match body with
      | .all .. => throw (.syntax "getExpr: non-canonical all telescope")
      | _ =>
        let mut result := body
        for binder in binders do
          result := .all binder.1 binder.2.1 binder.2.2 result
        return result
    | 0xA => do
      if tag.size > 1 then
        throw (.syntax s!"getExpr: invalid letE nonDep {tag.size}")
      let type ← recur
      let value ← recur
      return .letE (tag.size == 1) type value (← recur)
    | 0xB => return .share tag.size
    | flag => throw (.syntax s!"getExpr: invalid flag {flag}")

private def getUnivBounded (limits : Limits) : Nat → DecodeM Univ
  | 0 => throw (.universeDepth limits.maxUniverseDepth)
  | depth + 1 => do
    let tag ← liftSyntax getTag2
    let recur := getUnivBounded limits depth
    match tag.flag with
    | 0 =>
      if tag.size == 0 then return .zero
      else do
        let count := tag.size.toNat
        if count > maxSuccExpansion then
          throw (.sequenceTooLong .universeSuccessors count maxSuccExpansion)
        let base ← recur
        match base with
        | .succ _ =>
          if count == maxSuccExpansion then
            return Univ.addSucc count base
          else
            throw (.syntax "getUniv: non-canonical short succ chunk")
        | _ => return Univ.addSucc count base
    | 1 => do
      if tag.size != 0 then
        throw (.syntax s!"getUniv: non-canonical max size {tag.size}")
      return .max (← recur) (← recur)
    | 2 => do
      if tag.size != 0 then
        throw (.syntax s!"getUniv: non-canonical imax size {tag.size}")
      return .imax (← recur) (← recur)
    | 3 => return .var tag.size
    | flag => throw (.syntax s!"getUniv: invalid flag {flag}")

private def getDefinitionBounded (limits : Limits) : DecodeM Definition := do
  let mode ← liftSyntax getDefinitionMode
  let levels := (← liftSyntax getTag0).size
  let type ← getExprBounded limits limits.maxExpressionDepth
  let value ← getExprBounded limits limits.maxExpressionDepth
  return ⟨mode.1, mode.2, levels, type, value⟩

private def getRecursorRuleBounded (limits : Limits) : DecodeM RecursorRule := do
  let fields := (← liftSyntax getTag0).size
  let rhs ← getExprBounded limits limits.maxExpressionDepth
  return ⟨fields, rhs⟩

private def getRecursorBounded (limits : Limits) : DecodeM Recursor := do
  let mode ← liftSyntax getRecursorMode
  let levels := (← liftSyntax getTag0).size
  let params := (← liftSyntax getTag0).size
  let indices := (← liftSyntax getTag0).size
  let motives := (← liftSyntax getTag0).size
  let minors := (← liftSyntax getTag0).size
  let type ← getExprBounded limits limits.maxExpressionDepth
  let rules ← getCountedArrayBounded limits .recursorRules
    (getRecursorRuleBounded limits)
  return ⟨mode.1, mode.2, levels, params, indices, motives, minors,
    type, rules⟩

private def getAxiomBounded (limits : Limits) : DecodeM Axiom := do
  let isUnsafe ← liftSyntax (getStrictBool "getAxiom")
  let levels := (← liftSyntax getTag0).size
  let type ← getExprBounded limits limits.maxExpressionDepth
  return ⟨isUnsafe, levels, type⟩

private def getQuotientBounded (limits : Limits) : DecodeM Quotient := do
  let kind ← liftSyntax getQuotKind
  let levels := (← liftSyntax getTag0).size
  let type ← getExprBounded limits limits.maxExpressionDepth
  return ⟨kind, levels, type⟩

private def getConstructorBounded (limits : Limits) : DecodeM Constructor := do
  let isUnsafe ← liftSyntax (getStrictBool "getConstructor")
  let levels := (← liftSyntax getTag0).size
  let cidx := (← liftSyntax getTag0).size
  let params := (← liftSyntax getTag0).size
  let fields := (← liftSyntax getTag0).size
  let type ← getExprBounded limits limits.maxExpressionDepth
  return ⟨isUnsafe, levels, cidx, params, fields, type⟩

private def getInductiveBounded (limits : Limits) : DecodeM Inductive := do
  let isUnsafe ← liftSyntax (getStrictBool "getInductive")
  let levels := (← liftSyntax getTag0).size
  let params := (← liftSyntax getTag0).size
  let indices := (← liftSyntax getTag0).size
  let type ← getExprBounded limits limits.maxExpressionDepth
  let constructors ← getCountedArrayBounded limits .constructors
    (getConstructorBounded limits)
  return ⟨isUnsafe, levels, params, indices, type, constructors⟩

private def getMutConstBounded (limits : Limits) : DecodeM MutConst := do
  match ← liftSyntax getU8 with
  | 0 => return .defn (← getDefinitionBounded limits)
  | 1 => return .indc (← getInductiveBounded limits)
  | 2 => return .recr (← getRecursorBounded limits)
  | tag => throw (.syntax s!"getMutConst: invalid tag {tag}")

private def getConstantInfoVariantBounded (limits : Limits)
    (variant : UInt64) : DecodeM ConstantInfo := do
  if variant == ConstantInfo.CONST_DEFN then
    return .defn (← getDefinitionBounded limits)
  else if variant == ConstantInfo.CONST_RECR then
    return .recr (← getRecursorBounded limits)
  else if variant == ConstantInfo.CONST_AXIO then
    return .axio (← getAxiomBounded limits)
  else if variant == ConstantInfo.CONST_QUOT then
    return .quot (← getQuotientBounded limits)
  else if variant == ConstantInfo.CONST_CPRJ then
    return .cPrj (← liftSyntax getConstructorProj)
  else if variant == ConstantInfo.CONST_RPRJ then
    return .rPrj (← liftSyntax getRecursorProj)
  else if variant == ConstantInfo.CONST_IPRJ then
    return .iPrj (← liftSyntax getInductiveProj)
  else if variant == ConstantInfo.CONST_DPRJ then
    return .dPrj (← liftSyntax getDefinitionProj)
  else
    throw (.syntax s!"getConstantInfo: invalid variant {variant}")

private def getConstantInfoBounded (limits : Limits) : DecodeM ConstantInfo := do
  let tag ← liftSyntax getTag4
  if tag.flag == Constant.FLAG_MUTS then
    return .muts (← getArrayBounded limits .mutualMembers
      (getMutConstBounded limits) tag.size.toNat)
  else if tag.flag == Constant.FLAG then
    getConstantInfoVariantBounded limits tag.size
  else
    throw (.syntax s!"getConstantInfo: invalid flag {tag.flag}")

private def checkSharing (requireUsedTwice : Bool) (info : ConstantInfo)
    (sharing : Array Expr) : DecodeM Unit := do
  unless Sharing.tableWF sharing do throw .sharingInvariant
  let bodies := info.exprs.toArray
  unless bodies.all (Sharing.sharesBelow sharing.size) do
    throw .sharingInvariant
  if requireUsedTwice then
    unless Sharing.entriesUsedTwice sharing bodies do
      throw .sharingInvariant

private def getConstantBoundedWith (requireUsedTwice : Bool)
    (limits : Limits) : DecodeM Constant := do
  let info ← getConstantInfoBounded limits
  let sharing ← getCountedArrayBounded limits .sharingTable
    (getExprBounded limits limits.maxExpressionDepth)
  checkSharing requireUsedTwice info sharing
  let refs ← getCountedArrayBounded limits .references
    (liftSyntax (Serialize.get : GetM Address))
  let univs ← getCountedArrayBounded limits .universes
    (getUnivBounded limits limits.maxUniverseDepth)
  return ⟨info, sharing, refs, univs⟩

private def getConstantBounded (limits : Limits) : DecodeM Constant :=
  getConstantBoundedWith true limits

private def getIxonV2ConstantBounded (limits : Limits) : DecodeM Constant :=
  getConstantBoundedWith false limits

private def runDecodeM (get : DecodeM α) (bytes : ByteArray) :
    Except Error α := do
  let (value, state) ← get.run ⟨bytes, 0⟩
  if state.idx != state.bytes.size then
    throw (.syntax s!"trailing bytes: consumed {state.idx} of {state.bytes.size}")
  return value

private def checkRefIndex (site : Site) (kind : RefKind)
    (bound : Nat) (index : UInt64) : CheckM Unit :=
  if index.toNat < bound then .ok ()
  else .error (.refIndex site kind index.toNat bound)

/-- Validate every declaration-level universe variable in one local universe
expression.  This closes the evaluator's `getD 0` fallback for malformed
`Univ.var` indices. -/
private def checkUniv (site : Site) (levels : Nat) : Univ → CheckM Unit
  | .zero => .ok ()
  | .succ u => checkUniv site levels u
  | .max left right | .imax left right => do
    checkUniv site levels left
    checkUniv site levels right
  | .var index =>
    if index.toNat < levels then .ok ()
    else .error (.universeVariable site index.toNat levels)

private def checkUnivIndex (c : Constant) (site : Site) (levels : Nat)
    (index : UInt64) : CheckM Unit :=
  match c.univs[index.toNat]? with
  | none => .error (.universeIndex site index.toNat c.univs.size)
  | some u => checkUniv site levels u

private def checkUnivArgs (c : Constant) (site : Site) (levels : Nat)
    (indices : Array UInt64) : CheckM Unit := do
  for index in indices do
    checkUnivIndex c site levels index

/-- Check all evaluator-visible local table indices in one fully inlined
expression.  Term-variable scope and foreign declaration arities are separate
typing/store concerns and intentionally do not appear here. -/
private def checkExpr (c : Constant) (selfBound levels : Nat)
    (site : Site) : Expr → CheckM Unit
  | .sort index => checkUnivIndex c site levels index
  | .var _ => .ok ()
  | .ref index univIndices => do
    checkRefIndex site .constant c.refs.size index
    checkUnivArgs c site levels univIndices
  | .recur index univIndices => do
    if index.toNat < selfBound then pure ()
    else throw (.recurIndex site index.toNat selfBound)
    checkUnivArgs c site levels univIndices
  | .prj typeRefIndex _ value => do
    checkRefIndex site .projectionType c.refs.size typeRefIndex
    checkExpr c selfBound levels site value
  | .str index => checkRefIndex site .string c.refs.size index
  | .nat index => checkRefIndex site .natural c.refs.size index
  | .app fn arg => do
    checkExpr c selfBound levels site fn
    checkExpr c selfBound levels site arg
  | .lam _ type body => do
    checkExpr c selfBound levels site type
    checkExpr c selfBound levels site body
  | .all _ _ domain codomain => do
    checkExpr c selfBound levels site domain
    checkExpr c selfBound levels site codomain
  | .letE _ type value body => do
    checkExpr c selfBound levels site type
    checkExpr c selfBound levels site value
    checkExpr c selfBound levels site body
  | .share index => .error (.unresolvedShare site index.toNat)

private def inlinedRoot (c : Constant) (e : Expr) : Expr :=
  Sharing.inlineExpr c.sharing e

private def checkRoot (c : Constant) (selfBound : Nat) (levels : UInt64)
    (site : Site) (e : Expr) : CheckM Unit :=
  checkExpr c selfBound levels.toNat site (inlinedRoot c e)

private def checkDefinition (c : Constant) (selfBound : Nat)
    (member : Option Nat) (d : Definition) : CheckM Unit := do
  checkRoot c selfBound d.lvls ⟨member, .definitionType⟩ d.typ
  checkRoot c selfBound d.lvls ⟨member, .definitionValue⟩ d.value

/-- Check the evaluator's recursor slicing contract.  The stored type exposes
all params, motives, minors, indices, and the major premise.  A rule captures
the evaluator's params/motives/minors prefix followed by its constructor
fields; indices are intentionally absent from that rule environment. -/
private def checkRecursor (c : Constant) (selfBound : Nat)
    (member : Option Nat) (r : Recursor) : CheckM Unit := do
  let typeSite : Site := ⟨member, .recursorType⟩
  let typ := inlinedRoot c r.typ
  checkExpr c selfBound r.lvls.toNat typeSite typ
  let expectedType := r.params.toNat + r.motives.toNat + r.minors.toNat +
    r.indices.toNat + 1
  unless typ.allCount == expectedType do
    throw (.recursorTypeArity typeSite expectedType typ.allCount)
  for ruleIndex in [:r.rules.size] do
    let rule := r.rules[ruleIndex]!
    let ruleSite : Site := ⟨member, .recursorRule ruleIndex⟩
    let rhs := inlinedRoot c rule.rhs
    checkExpr c selfBound r.lvls.toNat ruleSite rhs
    let expectedRule := r.params.toNat + r.motives.toNat +
      r.minors.toNat + rule.fields.toNat
    unless rhs.lamCount == expectedRule do
      throw (.recursorRuleArity ruleSite expectedRule rhs.lamCount)

private def checkInductive (c : Constant) (selfBound : Nat)
    (member : Option Nat) (i : Inductive) : CheckM Unit := do
  checkRoot c selfBound i.lvls ⟨member, .inductiveType⟩ i.typ
  for ctorIndex in [:i.ctors.size] do
    let ctor := i.ctors[ctorIndex]!
    checkRoot c selfBound ctor.lvls
      ⟨member, .constructorType ctorIndex⟩ ctor.typ

private def checkMutConst (c : Constant) (selfBound memberIndex : Nat) :
    MutConst → CheckM Unit
  | .defn d => checkDefinition c selfBound (some memberIndex) d
  | .indc i => checkInductive c selfBound (some memberIndex) i
  | .recr r => checkRecursor c selfBound (some memberIndex) r

private def checkConstantCore (c : Constant) : CheckM Unit := do
  match c.info with
  -- ix collapses singleton recursive blocks to standalone Defn/Recr values,
  -- retaining `.recur 0` as the self reference.
  | .defn d => checkDefinition c 1 none d
  | .recr r => checkRecursor c 1 none r
  | .axio a => checkRoot c 0 a.lvls ⟨none, .axiomType⟩ a.typ
  | .quot q => checkRoot c 0 q.lvls ⟨none, .quotientType⟩ q.typ
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => pure ()
  | .muts members =>
    for memberIndex in [:members.size] do
      checkMutConst c members.size memberIndex members[memberIndex]!

/-- Validate every local semantic index and recursor slicing count in a
decoded constant.  This function is also useful for programmatically-built
constants; malformed sharing is rejected before inlining. -/
def checkConstant (c : Constant) : CheckM Unit := do
  unless c.sharingWF do
    throw .sharingInvariant
  checkConstantCore c

/-- Local semantic validation under the safety-critical sharing invariant
used by the pinned upstream ixon-v2 compressor.  Exact external compressor
image is checked separately at the address boundary. -/
def checkIxonV2Constant (c : Constant) : CheckM Unit := do
  unless Sharing.structuralWF c.sharing c.info.exprs.toArray do
    throw .sharingInvariant
  checkConstantCore c

/-- Resource-gated local validation.  The linear counter runs before the
quadratic sharing predicate, so an over-budget object is rejected without
entering `entriesUsedTwice`. -/
def checkConstantWith (limits : Limits) (c : Constant) : CheckM Unit := do
  let work := Work.layer1NodeVisits c.sharing c.info.exprs.toArray
  match Work.ensure .layer1NodeVisits work limits.maxLayer1NodeVisits with
  | .error exceeded => throw (.resource exceeded)
  | .ok _ => checkConstant c

def checkIxonV2ConstantWith (limits : Limits) (c : Constant) : CheckM Unit := do
  let work := Work.layer1NodeVisits c.sharing c.info.exprs.toArray
  match Work.ensure .layer1NodeVisits work limits.maxLayer1NodeVisits with
  | .error exceeded => throw (.resource exceeded)
  | .ok _ => checkIxonV2Constant c

theorem checkConstant_of_checkConstantWith {limits : Limits} {c : Constant}
    (h : checkConstantWith limits c = .ok ()) :
    checkConstant c = .ok () := by
  unfold checkConstantWith at h
  cases hwork : Work.ensure .layer1NodeVisits
      (Work.layer1NodeVisits c.sharing c.info.exprs.toArray)
      limits.maxLayer1NodeVisits with
  | error exceeded => simp [hwork] at h
  | ok result =>
    cases result
    simpa [hwork] using h

theorem checkIxonV2Constant_of_checkIxonV2ConstantWith
    {limits : Limits} {c : Constant}
    (h : checkIxonV2ConstantWith limits c = .ok ()) :
    checkIxonV2Constant c = .ok () := by
  unfold checkIxonV2ConstantWith at h
  cases hwork : Work.ensure .layer1NodeVisits
      (Work.layer1NodeVisits c.sharing c.info.exprs.toArray)
      limits.maxLayer1NodeVisits with
  | error exceeded => simp [hwork] at h
  | ok result =>
    cases result
    simpa [hwork] using h

def localWF (c : Constant) : Bool :=
  match checkConstant c with
  | .ok _ => true
  | .error _ => false

/-- Exact executable predicate for constants accepted by the checked writer:
the proved wire-representability domain plus local semantic validation. -/
def checkedWF (c : Constant) : Bool :=
  wireConstantWF c && localWF c

theorem wireWF_of_checkedWF {c : Constant} (h : checkedWF c = true) :
    c.wireWF := by
  have hwire : wireConstantWF c = true := (Bool.and_eq_true_iff.mp h).1
  exact (wireConstantWF_eq_true_iff c).mp hwire

/-- Resource-bounded checked counterpart of raw `ser`.  It cannot silently
truncate a source count and it refuses malformed sharing/local evaluator
indices before serialization. -/
def encodeCheckedWith (limits : Limits) (c : Constant) :
    Except EncodeError ByteArray :=
  if wireConstantWF c then
    match checkConstantWith limits c with
    | .ok _ => .ok (ser c)
    | .error error => .error (.invalid error)
  else
    .error .wireNotRepresentable

def encodeChecked (c : Constant) : Except EncodeError ByteArray :=
  encodeCheckedWith defaultLimits c

theorem encodeChecked_sound {c : Constant} {bytes : ByteArray}
    (h : encodeChecked c = .ok bytes) :
    c.wireWF ∧ checkConstant c = .ok () ∧ bytes = ser c := by
  unfold encodeChecked at h
  unfold encodeCheckedWith at h
  split at h
  · rename_i hwire
    cases hlocal : checkConstantWith defaultLimits c with
    | error error => simp [hlocal] at h
    | ok result =>
      cases result
      simp [hlocal] at h
      exact ⟨(wireConstantWF_eq_true_iff c).mp hwire,
        checkConstant_of_checkConstantWith hlocal, h.symm⟩
  · contradiction

/-- Resource-bounded strict byte decode followed by local semantic
validation. Parser errors are retained verbatim inside `Error.syntax`;
post-decode errors are structured and never depend on diagnostic strings. -/
def decodeCheckedWith (limits : Limits) (bytes : ByteArray) :
    Except Error Constant := do
  if bytes.size > limits.maxObjectBytes then
    throw (.objectTooLarge bytes.size limits.maxObjectBytes)
  let c ← runDecodeM (getConstantBounded limits) bytes
  checkConstantWith limits c
  return c

def decodeChecked (bytes : ByteArray) : Except Error Constant :=
  decodeCheckedWith defaultLimits bytes

/-- Strict resource-bounded decode for external bytes produced by the pinned
ixon-v2 writer.  It accepts the writer's deterministic nested-sharing shape
while retaining structural sharing safety and every local semantic check.
Callers establishing content identity must additionally use
`Constant.addressIxonV2CheckedWith`. -/
def decodeIxonV2CheckedWith (limits : Limits) (bytes : ByteArray) :
    Except Error Constant := do
  if bytes.size > limits.maxObjectBytes then
    throw (.objectTooLarge bytes.size limits.maxObjectBytes)
  let c ← runDecodeM (getIxonV2ConstantBounded limits) bytes
  checkIxonV2ConstantWith limits c
  return c

def decodeIxonV2Checked (bytes : ByteArray) : Except Error Constant :=
  decodeIxonV2CheckedWith defaultLimits bytes

end Ix.Compiler.Ixon.DecodeCheck
