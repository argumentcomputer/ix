import Ix.Compiler.IxIR2.EvalCounter
import Ix.Compiler.IxIR2.Liveness

/-!
# Checked dynamic shared reuse insertion

The optimizer recognizes the compiler-emitted consuming-case prefix produced
by `IxIR1.Lower.lowerRecursor`: every shared field is fetched and retained,
the shared parent is released at its checked last use, a compatible cell is
allocated, and the function tail-calls itself.  Constructor arity, source
parameter position, allocation argument order, and tail argument order are
recovered from the block rather than fixed to the first reversal benchmark.

The rewrite fuses those heap operations into `resetShared`, splits the
optional credit with `branchCredit`, and consumes the credit with `allocWith`
on both hot and cold paths.  Existing blocks retain their IDs; the two credit
blocks are appended, so unrelated CFG edges need no renumbering.  Both the
input and output cross the ordinary bounded IxIR₂ validator.  The executable
traversal also retains a typed decision trace: every source block records the
exact shape, liveness, representation, and operand-mapping decision that
justified its rewrite or left it unchanged.  That trace is the proof-facing
input to block/function/program simulation; this module does not yet claim
the completed semantic lifting theorem.
-/

namespace Ix.Compiler.IxIR2.Reuse

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR2

/-- Stable counters for the deliberately narrow first insertion pass. -/
structure Report where
  scannedBlocks : Nat := 0
  shapeCandidates : Nat := 0
  livenessRejected : Nat := 0
  rewritten : Nat := 0
  incompatibleLayouts : Nat := 0
  unmappableOperands : Nat := 0
  helperBlocks : Nat := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Report.add (left right : Report) : Report :=
  { scannedBlocks := left.scannedBlocks + right.scannedBlocks
    shapeCandidates := left.shapeCandidates + right.shapeCandidates
    livenessRejected := left.livenessRejected + right.livenessRejected
    rewritten := left.rewritten + right.rewritten
    incompatibleLayouts :=
      left.incompatibleLayouts + right.incompatibleLayouts
    unmappableOperands := left.unmappableOperands + right.unmappableOperands
    helperBlocks := left.helperBlocks + right.helperBlocks }

/-- A proof-carrying candidate position.  Coverage is checked independently
of inference, and exactness at the proposed position supplies the local fact
needed before moving a consuming reset there. -/
structure Placement (block : Block) where
  value : ValueId
  position : Nat
  liveness : Liveness.CheckedBlock block
  exact : liveness.summary.lastUse? value = some position

namespace Placement

theorem noUseAfter {block : Block} (placement : Placement block) :
    ∀ index, (bound : index < (Liveness.blockUses block).size) →
      (Liveness.blockUses block)[index].value = placement.value →
      (Liveness.blockUses block)[index].position ≤ placement.position :=
  placement.liveness.no_use_after placement.exact

end Placement

/-- Infer a local solution, check it under the caller's resource policy, and
retain a placement only when the requested position is the exact last use. -/
def inferPlacementWith (limits : Validate.Limits) (block : Block)
    (value : ValueId) (position : Nat) :
    Except Liveness.Error (Option (Placement block)) :=
  match Liveness.inferCheckedWith limits block with
  | .error error => .error error
  | .ok liveness =>
      if exact : liveness.summary.lastUse? value = some position then
        .ok (some { value, position, liveness, exact })
      else
        .ok none

def inferPlacement (block : Block) (value : ValueId) (position : Nat) :
    Except Liveness.Error (Option (Placement block)) :=
  inferPlacementWith Validate.defaultLimits block value position

/-- A successful liveness placement retains the exact requested register and
instruction position. -/
theorem inferPlacementWith_sound {limits : Validate.Limits} {block : Block}
    {value position : Nat} {placement : Placement block}
    (found : inferPlacementWith limits block value position =
      .ok (some placement)) :
    placement.value = value ∧ placement.position = position := by
  unfold inferPlacementWith at found
  split at found
  · cases found
  · split at found
    · simp only [Except.ok.injEq, Option.some.injEq] at found
      subst placement
      exact ⟨rfl, rfl⟩
    · cases found

/-- Information recovered from a general compiler-emitted consuming-case
prefix before consulting the representation schema. -/
structure Shape where
  parameterCount : Nat
  source : ValueId
  sourceConstructor : CtorId
  fieldCount : Nat
  releasePosition : Nat
  allocationConstructor : CtorId
  allocationArguments : Array Atom
  tailArguments : Array Atom

/-- Recognize the complete generic prefix
`fetchⁿ; retainSharedⁿ; releaseShared; alloc; tailCallSelf`.  Result register
numbers follow directly from IxIR₂'s append-only block register discipline. -/
def reuseShape? (block : Block) : Option Shape :=
  let instructionCount := block.instructions.size
  if instructionCount < 4 then
    none
  else
    let fieldCount := (instructionCount - 2) / 2
    let parameterCount := block.valueParams.size
    match block.instructions[0]? with
    | some (Instr.fetch (Atom.reg source) sourceConstructor 0) =>
        let fetchesMatch := (List.range fieldCount).all fun field =>
          block.instructions[field]? ==
            some (.fetch (.reg source) sourceConstructor field)
        let retainsMatch := (List.range fieldCount).all fun field =>
          block.instructions[fieldCount + field]? ==
            some (.retainShared (.reg (parameterCount + field)))
        if fieldCount == 0 || instructionCount != 2 * fieldCount + 2 ||
            source ≥ parameterCount ||
            block.valueParams[source]? != some (.owned .shared) ||
            !block.creditParams.isEmpty || !fetchesMatch || !retainsMatch then
          none
        else
          match block.instructions[2 * fieldCount]?,
              block.instructions[2 * fieldCount + 1]?, block.terminator with
          | some (.releaseShared (.reg released)),
              some (.alloc .shared allocationConstructor allocationArguments),
              .tailCallSelf tailArguments =>
              if released == source then
                some {
                  parameterCount
                  source
                  sourceConstructor
                  fieldCount
                  releasePosition := 2 * fieldCount
                  allocationConstructor
                  allocationArguments
                  tailArguments }
              else
                none
          | _, _, _ => none
    | _ => none

namespace Shape

/-- Exact baseline syntax certified by a successful generic-prefix match. -/
structure Fits (block : Block) (shape : Shape) : Prop where
  instructionCountAtLeastFour : 4 ≤ block.instructions.size
  fieldCountPositive : 0 < shape.fieldCount
  instructionCount :
    block.instructions.size = 2 * shape.fieldCount + 2
  parameterCount : shape.parameterCount = block.valueParams.size
  sourceBound : shape.source < shape.parameterCount
  sourceOwned :
    block.valueParams[shape.source]? = some (.owned .shared)
  noCredits : block.creditParams = #[]
  fetches : ∀ field, field < shape.fieldCount →
    block.instructions[field]? = some
      (.fetch (.reg shape.source) shape.sourceConstructor field)
  retains : ∀ field, field < shape.fieldCount →
    block.instructions[shape.fieldCount + field]? = some
      (.retainShared (.reg (shape.parameterCount + field)))
  release : block.instructions[shape.releasePosition]? =
    some (.releaseShared (.reg shape.source))
  releasePosition : shape.releasePosition = 2 * shape.fieldCount
  allocation : block.instructions[shape.releasePosition + 1]? =
    some (.alloc .shared shape.allocationConstructor
      shape.allocationArguments)
  terminator : block.terminator = .tailCallSelf shape.tailArguments

end Shape

/-- Invert the executable recognizer into its exact generalized baseline
prefix.  This is the structural induction interface used by block simulation. -/
theorem reuseShape?_sound {block : Block} {shape : Shape}
    (found : reuseShape? block = some shape) : Shape.Fits block shape := by
  unfold reuseShape? at found
  split at found
  · simp at found
    · rcases found with ⟨minSize, checks, final⟩
      split at final
      · split at final
        · simp only [Option.some.injEq] at final
          rename_i _ source sourceConstructor firstAt _ _ _ released
            allocationConstructor allocationArguments tailArguments
            releaseAt allocationAt terminatorAt releaseEq
          subst shape
          rcases checks with
            ⟨⟨⟨⟨⟨⟨two, instructionCount⟩, sourceBound⟩, sourceOwned⟩,
              noCredits⟩, fetches⟩, retains⟩
          constructor
          · exact minSize
          · exact Nat.div_pos two (by omega)
          · exact instructionCount
          · rfl
          · exact sourceBound
          · exact sourceOwned
          · exact noCredits
          · exact fetches
          · exact retains
          · dsimp
            rw [← releaseEq]
            exact releaseAt
          · rfl
          · dsimp
            exact allocationAt
          · dsimp
            exact terminatorAt
        · simp at final
      · simp at final
  · simp at found

structure Representation where
  layout : LayoutId

/-- Exact-layout eligibility.  Layout identity alone is not allowed to hide
an inconsistent schema table: source and target field worlds must also agree,
and this dynamic lane currently consumes compiler-emitted shared retains. -/
def representation? (context : Validate.Context) (shape : Shape) :
    Option Representation := do
  let sourceSchema ← context.schemas .shared shape.sourceConstructor
  let allocationSchema ← context.schemas .shared shape.allocationConstructor
  let expectedFields := Array.replicate shape.fieldCount .shared
  if sourceSchema.fields == expectedFields &&
      allocationSchema.fields == sourceSchema.fields &&
      sourceSchema.layout == allocationSchema.layout then
    some { layout := sourceSchema.layout }
  else
    none

/-- Invert an accepted representation decision into the two exact schema
lookups and all three compatibility equations used by reset/allocation
simulation. -/
theorem representation?_sound {context : Validate.Context} {shape : Shape}
    {representation : Representation}
    (found : representation? context shape = some representation) :
    ∃ sourceSchema allocationSchema,
      context.schemas .shared shape.sourceConstructor = some sourceSchema ∧
      context.schemas .shared shape.allocationConstructor =
        some allocationSchema ∧
      sourceSchema.fields = Array.replicate shape.fieldCount .shared ∧
      allocationSchema.fields = sourceSchema.fields ∧
      sourceSchema.layout = allocationSchema.layout ∧
      representation.layout = sourceSchema.layout := by
  unfold representation? at found
  cases sourceAt : context.schemas .shared shape.sourceConstructor with
  | none => simp [sourceAt] at found
  | some sourceSchema =>
      cases allocationAt :
          context.schemas .shared shape.allocationConstructor with
      | none => simp [sourceAt, allocationAt] at found
      | some allocationSchema =>
          refine ⟨sourceSchema, allocationSchema, rfl, rfl, ?_⟩
          simp [sourceAt, allocationAt] at found
          rcases found with
            ⟨⟨⟨sourceFields, allocationFields⟩, layouts⟩,
              representationEq⟩
          subst representation
          exact ⟨sourceFields, allocationFields, layouts, rfl⟩

def translateRegister? (shape : Shape) (value : ValueId) :
    Option ValueId :=
  if value < shape.parameterCount then
    if value == shape.source then
      none
    else if value < shape.source then
      some (shape.fieldCount + value)
    else
      some (shape.fieldCount + (value - 1))
  else if value < shape.parameterCount + shape.fieldCount then
    none
  else if value < shape.parameterCount + 2 * shape.fieldCount then
    some (value - (shape.parameterCount + shape.fieldCount))
  else if value == shape.parameterCount + 2 * shape.fieldCount then
    some (shape.fieldCount + (shape.parameterCount - 1))
  else
    none

def translateAtom? (shape : Shape) : Atom → Option Atom
  | .reg value => (translateRegister? shape value).map .reg
  | .lit literal => some (.lit literal)
  | .erased => some .erased

def translateAtoms? (shape : Shape) (values : Array Atom) :
    Option (Array Atom) :=
  (values.toList.mapM (translateAtom? shape)).map List.toArray

def branchValues (shape : Shape) : Array Atom :=
  let fields := (List.range shape.fieldCount).map fun field =>
    .reg (shape.parameterCount + field)
  let parameters := ((List.range shape.parameterCount).filter fun value =>
    value != shape.source).map fun value => .reg value
  (fields ++ parameters).toArray

structure Candidate (block : Block) where
  placement : Placement block
  sourceConstructor : CtorId
  allocationConstructor : CtorId
  layout : LayoutId
  helperValueParams : Array ValueCap
  resetValues : Array Atom
  allocationArguments : Array Atom
  tailArguments : Array Atom

def candidate? (block : Block) (shape : Shape)
    (representation : Representation) (placement : Placement block) :
    Option (Candidate block) := do
  let allocationArguments ←
    translateAtoms? shape shape.allocationArguments
  let tailArguments ← translateAtoms? shape shape.tailArguments
  let helperValueParams :=
    Array.replicate shape.fieldCount (.owned .shared) ++
      (block.valueParams.toList.eraseIdx shape.source).toArray
  some {
    placement
    sourceConstructor := shape.sourceConstructor
    allocationConstructor := shape.allocationConstructor
    layout := representation.layout
    helperValueParams
    resetValues := branchValues shape
    allocationArguments
    tailArguments }

/-- Invert successful operand translation once, exposing the exact helper
operands and every structural field copied into the accepted candidate. -/
theorem candidate?_sound {block : Block} {shape : Shape}
    {representation : Representation} {placement : Placement block}
    {candidate : Candidate block}
    (found : candidate? block shape representation placement =
      some candidate) :
    translateAtoms? shape shape.allocationArguments =
        some candidate.allocationArguments ∧
    translateAtoms? shape shape.tailArguments =
        some candidate.tailArguments ∧
    candidate.placement = placement ∧
    candidate.sourceConstructor = shape.sourceConstructor ∧
    candidate.allocationConstructor = shape.allocationConstructor ∧
    candidate.layout = representation.layout ∧
    candidate.helperValueParams =
      Array.replicate shape.fieldCount (.owned .shared) ++
        (block.valueParams.toList.eraseIdx shape.source).toArray ∧
    candidate.resetValues = branchValues shape := by
  unfold candidate? at found
  cases allocationAt : translateAtoms? shape shape.allocationArguments with
  | none => simp [allocationAt] at found
  | some allocationArguments =>
      cases tailAt : translateAtoms? shape shape.tailArguments with
      | none => simp [allocationAt, tailAt] at found
      | some tailArguments =>
          simp [allocationAt, tailAt] at found
          subst candidate
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def creditBlock {block : Block} (candidate : Candidate block)
    (credit : CreditCap) : Block :=
  { valueParams := candidate.helperValueParams
    creditParams := #[credit]
    instructions := #[
      .allocWith 0 .shared candidate.allocationConstructor
        candidate.allocationArguments]
    terminator := .tailCallSelf candidate.tailArguments }

def resetBlock {block : Block} (candidate : Candidate block)
    (hot cold : BlockId) : Block :=
  { valueParams := block.valueParams
    creditParams := #[]
    instructions := #[.resetShared (.reg candidate.placement.value)
      candidate.sourceConstructor]
    terminator := .branchCredit 0
      { target := hot
        values := candidate.resetValues
        credits := #[0] }
      { target := cold
        values := candidate.resetValues
        credits := #[0] } }

/-- Every premise used to accept one block rewrite, retained at the exact
source block.  Proof consumers can recover the recognized baseline syntax,
the checked last-use placement, exact layout compatibility, and the translated
operand vectors without rerunning or inverting the optimizer. -/
structure Site (limits : Validate.Limits) (context : Validate.Context)
    (block : Block) where
  shape : Shape
  shapeFound : reuseShape? block = some shape
  placement : Placement block
  placementFound : inferPlacementWith limits block shape.source
    shape.releasePosition = .ok (some placement)
  representation : Representation
  representationFound : representation? context shape = some representation
  candidate : Candidate block
  candidateFound : candidate? block shape representation placement =
    some candidate

namespace Site

/-- The exact generalized baseline prefix retained by an accepted site. -/
theorem fits {limits : Validate.Limits} {context : Validate.Context}
    {block : Block} (site : Site limits context block) :
    Shape.Fits block site.shape :=
  reuseShape?_sound site.shapeFound

/-- The liveness witness is attached to the recognized source register at its
exact baseline release instruction. -/
theorem placementCoordinates {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) :
    site.placement.value = site.shape.source ∧
      site.placement.position = site.shape.releasePosition :=
  inferPlacementWith_sound site.placementFound

/-- No use of the recognized source occurs after the release position selected
by the accepted site. -/
theorem noUseAfter {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) :
    ∀ index, (bound : index < (Liveness.blockUses block).size) →
      (Liveness.blockUses block)[index].value = site.shape.source →
      (Liveness.blockUses block)[index].position ≤
        site.shape.releasePosition := by
  intro index bound sourceUse
  have checked := site.placement.noUseAfter index bound
  rw [site.placementCoordinates.1, site.placementCoordinates.2] at checked
  exact checked sourceUse

/-- Every instruction in an accepted source block belongs to its recognized
fetch/retain/release/allocation prefix. This inversion is useful outside the
local macro proof, where a suspended caller's call instruction rules out that
its block was accepted by the reuse pass. -/
theorem instructionCases {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) {position : Nat} {instruction : Instr}
    (found : block.instructions[position]? = some instruction) :
    (∃ field, field < site.shape.fieldCount ∧
      instruction = .fetch (.reg site.shape.source)
        site.shape.sourceConstructor field) ∨
    (∃ field, field < site.shape.fieldCount ∧
      instruction = .retainShared
        (.reg (site.shape.parameterCount + field))) ∨
    instruction = .releaseShared (.reg site.shape.source) ∨
    instruction = .alloc .shared site.shape.allocationConstructor
      site.shape.allocationArguments := by
  have positionBound : position < block.instructions.size :=
    (Array.getElem?_eq_some_iff.mp found).1
  have positionLimit : position < 2 * site.shape.fieldCount + 2 := by
    simpa [site.fits.instructionCount] using positionBound
  by_cases fetchRange : position < site.shape.fieldCount
  · left
    exact ⟨position, fetchRange,
      Option.some.inj (found.symm.trans
        (site.fits.fetches position fetchRange))⟩
  by_cases retainRange : position < 2 * site.shape.fieldCount
  · right
    left
    let field := position - site.shape.fieldCount
    have fieldBound : field < site.shape.fieldCount := by
      dsimp [field]
      omega
    have positionEq : position = site.shape.fieldCount + field := by
      dsimp [field]
      omega
    have retained := site.fits.retains field fieldBound
    have found' : block.instructions[site.shape.fieldCount + field]? =
        some instruction := by
      simpa [positionEq] using found
    exact ⟨field, fieldBound, Option.some.inj (found'.symm.trans retained)⟩
  have finalCases : position = 2 * site.shape.fieldCount ∨
      position = 2 * site.shape.fieldCount + 1 := by
    omega
  cases finalCases with
  | inl releasePosition =>
      right
      right
      left
      have positionEq : position = site.shape.releasePosition := by
        rw [site.fits.releasePosition]
        exact releasePosition
      have found' : block.instructions[site.shape.releasePosition]? =
          some instruction := by
        simpa [positionEq] using found
      exact Option.some.inj (found'.symm.trans site.fits.release)
  | inr allocationPosition =>
      right
      right
      right
      have positionEq : position = site.shape.releasePosition + 1 := by
        rw [site.fits.releasePosition]
        exact allocationPosition
      have found' : block.instructions[site.shape.releasePosition + 1]? =
          some instruction := by
        simpa [positionEq] using found
      exact Option.some.inj (found'.symm.trans site.fits.allocation)

/-- Accepted source blocks contain no addressed call instruction. -/
theorem noCall {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) {position : Nat}
    {address : Ixon.Address} {arguments : Array Atom}
    (found : block.instructions[position]? = some (.call address arguments)) :
    False := by
  rcases site.instructionCases found with
    ⟨field, bound, impossible⟩ | ⟨field, bound, impossible⟩ |
      impossible | impossible <;> cases impossible

/-- Accepted source blocks contain no recursive call instruction. -/
theorem noCallSelf {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) {position : Nat}
    {arguments : Array Atom}
    (found : block.instructions[position]? = some (.callSelf arguments)) :
    False := by
  rcases site.instructionCases found with
    ⟨field, bound, impossible⟩ | ⟨field, bound, impossible⟩ |
      impossible | impossible <;> cases impossible

/-- Accepted source blocks contain no dynamic application instruction. -/
theorem noApply {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) {position : Nat}
    {function : Atom} {arguments : Array Atom}
    (found : block.instructions[position]? = some (.apply function arguments)) :
    False := by
  rcases site.instructionCases found with
    ⟨field, bound, impossible⟩ | ⟨field, bound, impossible⟩ |
      impossible | impossible <;> cases impossible

/-- Accepted source blocks contain no ordinary move instruction. -/
theorem noMove {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) {position : Nat} {atom : Atom}
    (found : block.instructions[position]? = some (.move atom)) : False := by
  rcases site.instructionCases found with
    ⟨field, bound, impossible⟩ | ⟨field, bound, impossible⟩ |
      impossible | impossible <;> cases impossible

/-- Accepted source blocks contain no unique-free instruction. -/
theorem noFreeUnique {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) {position : Nat} {atom : Atom}
    {identity : CtorId}
    (found : block.instructions[position]? =
      some (.freeUnique atom identity)) : False := by
  rcases site.instructionCases found with
    ⟨field, bound, impossible⟩ | ⟨field, bound, impossible⟩ |
      impossible | impossible <;> cases impossible

/-- Accepted source blocks contain no function-partial-application
instruction. -/
theorem noPapp {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) {position : Nat}
    {address : Ixon.Address} {arguments : Array Atom}
    (found : block.instructions[position]? =
      some (.papp address arguments)) : False := by
  rcases site.instructionCases found with
    ⟨field, bound, impossible⟩ | ⟨field, bound, impossible⟩ |
      impossible | impossible <;> cases impossible

/-- Accepted source blocks contain no unique-drop instruction. -/
theorem noDropUnique {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) {position : Nat} {atom : Atom}
    (found : block.instructions[position]? = some (.dropUnique atom)) :
    False := by
  rcases site.instructionCases found with
    ⟨field, bound, impossible⟩ | ⟨field, bound, impossible⟩ |
      impossible | impossible <;> cases impossible

/-- Accepted source blocks contain no unique allocation instruction. -/
theorem noAllocUnique {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) {position : Nat} {identity : CtorId}
    {arguments : Array Atom}
    (found : block.instructions[position]? =
      some (.alloc .unique identity arguments)) : False := by
  rcases site.instructionCases found with
    ⟨field, bound, impossible⟩ | ⟨field, bound, impossible⟩ |
      impossible | impossible <;> cases impossible

/-- Core candidate fields are copied exactly from the recognized site; the
reset target additionally agrees with the liveness-checked source register. -/
theorem candidateCore {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) :
    site.candidate.placement.value = site.shape.source ∧
      site.candidate.sourceConstructor = site.shape.sourceConstructor ∧
      site.candidate.allocationConstructor =
        site.shape.allocationConstructor ∧
      site.candidate.layout = site.representation.layout := by
  rcases candidate?_sound site.candidateFound with
    ⟨_, _, placement, sourceConstructor, allocationConstructor, layout,
      _, _⟩
  have sourceValue := congrArg (fun selected => selected.value) placement
  exact ⟨sourceValue.trans site.placementCoordinates.1, sourceConstructor,
    allocationConstructor, layout⟩

/-- Helper ABI and branch operands are copied from the recognized shape. -/
theorem candidateVectors {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) :
    site.candidate.helperValueParams =
        Array.replicate site.shape.fieldCount (.owned .shared) ++
          (block.valueParams.toList.eraseIdx site.shape.source).toArray ∧
      site.candidate.resetValues = branchValues site.shape := by
  rcases candidate?_sound site.candidateFound with
    ⟨_, _, _, _, _, _, helperValueParams, resetValues⟩
  exact ⟨helperValueParams, resetValues⟩

/-- Fully exposed syntax of the replacement block emitted for this site. -/
theorem resetBlock_eq {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) (hot cold : BlockId) :
    resetBlock site.candidate hot cold =
      { valueParams := block.valueParams
        creditParams := #[]
        instructions := #[.resetShared (.reg site.shape.source)
          site.shape.sourceConstructor]
        terminator := .branchCredit 0
          { target := hot
            values := branchValues site.shape
            credits := #[0] }
          { target := cold
            values := branchValues site.shape
            credits := #[0] } } := by
  simp [resetBlock, site.candidateCore.1, site.candidateCore.2.1,
    site.candidateVectors.2]

/-- An accepted source block is never literally its reset replacement. The
recognized source begins with a field fetch (and has positive field count),
whereas the replacement begins with `resetShared`. -/
theorem ne_resetBlock {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) (hot cold : BlockId) :
    block ≠ resetBlock site.candidate hot cold := by
  intro equal
  have sizes := congrArg (fun selected => selected.instructions.size) equal
  have resetSize : (resetBlock site.candidate hot cold).instructions.size = 1 :=
    by rfl
  rw [resetSize] at sizes
  rw [site.fits.instructionCount] at sizes
  omega

/-- Fully exposed syntax of either required- or optional-credit helper. -/
theorem creditBlock_eq {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) (credit : CreditCap) :
    creditBlock site.candidate credit =
      { valueParams :=
          Array.replicate site.shape.fieldCount (.owned .shared) ++
            (block.valueParams.toList.eraseIdx site.shape.source).toArray
        creditParams := #[credit]
        instructions := #[.allocWith 0 .shared
          site.shape.allocationConstructor
          site.candidate.allocationArguments]
        terminator := .tailCallSelf site.candidate.tailArguments } := by
  simp [creditBlock, site.candidateCore.2.2.1,
    site.candidateVectors.1]

/-- The exact source/allocation schemas and compatibility equations retained
by an accepted site. -/
theorem schemas {limits : Validate.Limits} {context : Validate.Context}
    {block : Block} (site : Site limits context block) :
    ∃ sourceSchema allocationSchema,
      context.schemas .shared site.shape.sourceConstructor =
        some sourceSchema ∧
      context.schemas .shared site.shape.allocationConstructor =
        some allocationSchema ∧
      sourceSchema.fields =
        Array.replicate site.shape.fieldCount .shared ∧
      allocationSchema.fields = sourceSchema.fields ∧
      sourceSchema.layout = allocationSchema.layout ∧
      site.representation.layout = sourceSchema.layout :=
  representation?_sound site.representationFound

/-- Schema facts in the exact form consumed by reset and `allocWith`: both
lookups succeed, both field vectors are uniformly shared, and the emitted
credit layout matches both constructors. -/
theorem runtimeSchemas {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) :
    ∃ sourceSchema allocationSchema,
      context.schemas .shared site.shape.sourceConstructor =
        some sourceSchema ∧
      context.schemas .shared site.shape.allocationConstructor =
        some allocationSchema ∧
      sourceSchema.fields =
        Array.replicate site.shape.fieldCount .shared ∧
      allocationSchema.fields = sourceSchema.fields ∧
      site.candidate.layout = sourceSchema.layout ∧
      site.candidate.layout = allocationSchema.layout := by
  obtain ⟨sourceSchema, allocationSchema, sourceAt, allocationAt,
      sourceFields, allocationFields, layouts, representationLayout⟩ :=
    site.schemas
  have candidateRepresentation := site.candidateCore.2.2.2
  have candidateSource := candidateRepresentation.trans representationLayout
  exact ⟨sourceSchema, allocationSchema, sourceAt, allocationAt,
    sourceFields, allocationFields, candidateSource,
    candidateSource.trans layouts⟩

/-- Accepted allocation operands are the successful register translation of
the recognized baseline allocation operands. -/
theorem allocationArgumentsFound {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) :
    translateAtoms? site.shape site.shape.allocationArguments =
      some site.candidate.allocationArguments :=
  (candidate?_sound site.candidateFound).1

/-- Accepted tail operands are the successful register translation of the
recognized baseline tail operands. -/
theorem tailArgumentsFound {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Site limits context block) :
    translateAtoms? site.shape site.shape.tailArguments =
      some site.candidate.tailArguments :=
  (candidate?_sound site.candidateFound).2.1

end Site

/-- Exhaustive checked decision for one source block.  Rejection constructors
retain the exact failed phase as well, so an unchanged block is justified by
the same computation that produced the output rather than by a later Boolean
audit. -/
inductive Decision (limits : Validate.Limits) (context : Validate.Context)
    (block : Block) : Type where
  | noShape (notFound : reuseShape? block = none)
  | livenessError (shape : Shape)
      (shapeFound : reuseShape? block = some shape)
      (error : Liveness.Error)
      (rejected : inferPlacementWith limits block shape.source
        shape.releasePosition = .error error)
  | livenessMiss (shape : Shape)
      (shapeFound : reuseShape? block = some shape)
      (rejected : inferPlacementWith limits block shape.source
        shape.releasePosition = .ok none)
  | representationMiss (shape : Shape)
      (shapeFound : reuseShape? block = some shape)
      (placement : Placement block)
      (placementFound : inferPlacementWith limits block shape.source
        shape.releasePosition = .ok (some placement))
      (notFound : representation? context shape = none)
  | operandMiss (shape : Shape)
      (shapeFound : reuseShape? block = some shape)
      (placement : Placement block)
      (placementFound : inferPlacementWith limits block shape.source
        shape.releasePosition = .ok (some placement))
      (representation : Representation)
      (representationFound : representation? context shape =
        some representation)
      (notFound : candidate? block shape representation placement = none)
  | accepted (site : Site limits context block)

/-- Run the recognizer exactly once and retain its dependent decision. -/
def classifyBlock (limits : Validate.Limits) (context : Validate.Context)
    (block : Block) : Decision limits context block := by
  match shapeFound : reuseShape? block with
  | none => exact .noShape shapeFound
  | some shape =>
      match placementFound : inferPlacementWith limits block shape.source
          shape.releasePosition with
      | .error error =>
          exact .livenessError shape shapeFound error placementFound
      | .ok none =>
          exact .livenessMiss shape shapeFound placementFound
      | .ok (some placement) =>
          match representationFound : representation? context shape with
          | none =>
              exact .representationMiss shape shapeFound placement
                placementFound representationFound
          | some representation =>
              match candidateFound :
                  candidate? block shape representation placement with
              | none =>
                  exact .operandMiss shape shapeFound placement placementFound
                    representation representationFound candidateFound
              | some candidate =>
                  exact .accepted {
                    shape
                    shapeFound
                    placement
                    placementFound
                    representation
                    representationFound
                    candidate
                    candidateFound }

def Decision.report {limits : Validate.Limits} {context : Validate.Context}
    {block : Block} (decision : Decision limits context block) : Report :=
  match decision with
  | .noShape _ => { scannedBlocks := 1 }
  | .livenessError .. | .livenessMiss .. =>
      { scannedBlocks := 1, shapeCandidates := 1, livenessRejected := 1 }
  | .representationMiss .. =>
      { scannedBlocks := 1, shapeCandidates := 1,
        incompatibleLayouts := 1 }
  | .operandMiss .. =>
      { scannedBlocks := 1, shapeCandidates := 1,
        unmappableOperands := 1 }
  | .accepted _ =>
      { scannedBlocks := 1, shapeCandidates := 1, rewritten := 1,
        helperBlocks := 2 }

/-- Replacement occupying the source block's old ID. -/
def Decision.replacement {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (decision : Decision limits context block) (originalCount helperOffset : Nat) :
    Block :=
  match decision with
  | .accepted site =>
      resetBlock site.candidate (originalCount + helperOffset)
        (originalCount + helperOffset + 1)
  | _ => block

/-- Helper blocks appended for this decision, in hot/required then
cold/optional order. -/
def Decision.helpers {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (decision : Decision limits context block) : List Block :=
  match decision with
  | .accepted site =>
      [creditBlock site.candidate (.required site.candidate.layout),
       creditBlock site.candidate (.optional site.candidate.layout)]
  | _ => []

/-- Replacing an accepted block preserves its externally visible value
parameter ABI; rejected blocks are literal identities. -/
theorem Decision.replacement_valueParams {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (decision : Decision limits context block) (originalCount helperOffset : Nat) :
    (decision.replacement originalCount helperOffset).valueParams =
      block.valueParams := by
  cases decision with
  | noShape => rfl
  | livenessError => rfl
  | livenessMiss => rfl
  | representationMiss => rfl
  | operandMiss => rfl
  | accepted site =>
      simpa [Decision.replacement] using congrArg Block.valueParams
          (site.resetBlock_eq (originalCount + helperOffset)
            (originalCount + helperOffset + 1))

/-- The replacement also preserves the credit-parameter ABI.  Accepted
source blocks are certified credit-free and reset blocks have the same empty
credit vector. -/
theorem Decision.replacement_creditParams {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (decision : Decision limits context block) (originalCount helperOffset : Nat) :
    (decision.replacement originalCount helperOffset).creditParams =
      block.creditParams := by
  cases decision with
  | noShape => rfl
  | livenessError => rfl
  | livenessMiss => rfl
  | representationMiss => rfl
  | operandMiss => rfl
  | accepted site =>
      calc
        (Decision.replacement (.accepted site) originalCount
          helperOffset).creditParams = #[] := by
            simpa [Decision.replacement] using congrArg Block.creditParams
                (site.resetBlock_eq (originalCount + helperOffset)
                  (originalCount + helperOffset + 1))
        _ = block.creditParams := site.fits.noCredits.symm

/-- Heterogeneous decision list indexed by the exact source block list. -/
inductive FunctionDecisions (limits : Validate.Limits)
    (context : Validate.Context) : List Block → Type where
  | nil : FunctionDecisions limits context []
  | cons {block : Block} {blocks : List Block}
      (head : Decision limits context block)
      (tail : FunctionDecisions limits context blocks) :
      FunctionDecisions limits context (block :: blocks)

def classifyBlocks (limits : Validate.Limits) (context : Validate.Context) :
    (blocks : List Block) → FunctionDecisions limits context blocks
  | [] => .nil
  | block :: blocks =>
      .cons (classifyBlock limits context block)
        (classifyBlocks limits context blocks)

structure Realization where
  originals : List Block := []
  helpers : List Block := []
  report : Report := {}

namespace FunctionDecisions

/-- Materialize a decision list while threading the number of helpers already
assigned IDs.  Because every accepted site contributes its two helpers before
the tail is realized, their IDs agree with the append-only executable pass. -/
def realize {limits : Validate.Limits} {context : Validate.Context}
    (originalCount : Nat) : {blocks : List Block} →
      FunctionDecisions limits context blocks → Nat → Realization
  | [], .nil, _ => {}
  | _ :: _, .cons head tail, helperOffset =>
      let generated := head.helpers
      let rest := realize originalCount tail (helperOffset + generated.length)
      { originals := head.replacement originalCount helperOffset ::
          rest.originals
        helpers := generated ++ rest.helpers
        report := head.report.add rest.report }

/-- Locate a block decision by its source block ID.  `helperOffset` is the
number of helper blocks contributed by preceding source blocks. -/
inductive At {limits : Validate.Limits} {context : Validate.Context} :
    {blocks : List Block} → FunctionDecisions limits context blocks →
      (index helperOffset : Nat) → (block : Block) →
      Decision limits context block → Prop where
  | zero {block : Block} {blocks : List Block}
      {head : Decision limits context block}
      {tail : FunctionDecisions limits context blocks} :
      At (.cons head tail) 0 0 block head
  | succ {headBlock block : Block} {blocks : List Block}
      {head : Decision limits context headBlock}
      {tail : FunctionDecisions limits context blocks}
      {index helperOffset : Nat}
      {decision : Decision limits context block}
      (found : At tail index helperOffset block decision) :
      At (.cons head tail) (index + 1)
        (head.helpers.length + helperOffset) block decision

theorem exists_at {limits : Validate.Limits} {context : Validate.Context}
    {blocks : List Block} (decisions : FunctionDecisions limits context blocks)
    (index : Nat) (bound : index < blocks.length) :
    ∃ helperOffset block decision,
      At decisions index helperOffset block decision := by
  induction decisions generalizing index with
  | nil => simp at bound
  | @cons block blocks head tail ih =>
      cases index with
      | zero => exact ⟨0, block, head, .zero⟩
      | succ index =>
          have tailBound : index < blocks.length := by
            simpa using bound
          obtain ⟨helperOffset, foundBlock, decision, found⟩ :=
            ih index tailBound
          exact ⟨head.helpers.length + helperOffset, foundBlock, decision,
            .succ found⟩

theorem At.source_get? {limits : Validate.Limits}
    {context : Validate.Context} {blocks : List Block}
    {decisions : FunctionDecisions limits context blocks}
    {index helperOffset : Nat} {block : Block}
    {decision : Decision limits context block}
    (found : At decisions index helperOffset block decision) :
    blocks[index]? = some block := by
  induction found with
  | zero => simp
  | succ _ ih => simpa using ih

@[simp] theorem realize_originals_length {limits : Validate.Limits}
    {context : Validate.Context} {blocks : List Block}
    (decisions : FunctionDecisions limits context blocks)
    (originalCount helperOffset : Nat) :
    (decisions.realize originalCount helperOffset).originals.length =
      blocks.length := by
  induction decisions generalizing helperOffset with
  | nil => rfl
  | cons head tail ih =>
      simp [realize, ih]

theorem At.original_get? {limits : Validate.Limits}
    {context : Validate.Context} {blocks : List Block}
    {decisions : FunctionDecisions limits context blocks}
    {index helperOffset : Nat} {block : Block}
    {decision : Decision limits context block}
    (found : At decisions index helperOffset block decision)
    (originalCount startOffset : Nat) :
    (decisions.realize originalCount startOffset).originals[index]? =
      some (decision.replacement originalCount
        (startOffset + helperOffset)) := by
  induction found generalizing startOffset with
  | zero => simp [realize]
  | @succ headBlock block blocks head tail index helperOffset decision
      found ih =>
      simpa [realize, Nat.add_assoc] using
        ih (startOffset + head.helpers.length)

theorem At.helper_get? {limits : Validate.Limits}
    {context : Validate.Context} {blocks : List Block}
    {decisions : FunctionDecisions limits context blocks}
    {index helperOffset : Nat} {block : Block}
    {decision : Decision limits context block}
    (found : At decisions index helperOffset block decision)
    {inside : Nat} {helper : Block}
    (insideAt : decision.helpers[inside]? = some helper)
    (originalCount startOffset : Nat) :
    (decisions.realize originalCount startOffset).helpers[
        helperOffset + inside]? = some helper := by
  induction found generalizing startOffset with
  | zero =>
      simp only [realize, Nat.zero_add]
      rw [List.getElem?_append_left]
      · exact insideAt
      · exact (List.getElem?_eq_some_iff.mp insideAt).choose
  | @succ headBlock block blocks head tail index helperOffset decision
      found ih =>
      simp only [realize]
      rw [List.getElem?_append_right (by omega)]
      simpa [Nat.add_assoc] using
        ih insideAt (startOffset + head.helpers.length)

theorem At.hot_helper_get? {limits : Validate.Limits}
    {context : Validate.Context} {blocks : List Block}
    {decisions : FunctionDecisions limits context blocks}
    {index helperOffset : Nat} {block : Block}
    {site : Site limits context block}
    (found : At decisions index helperOffset block (.accepted site))
    (originalCount startOffset : Nat) :
    (decisions.realize originalCount startOffset).helpers[helperOffset]? =
      some (creditBlock site.candidate
        (.required site.candidate.layout)) := by
  simpa using found.helper_get?
    (inside := 0) (by simp [Decision.helpers]) originalCount startOffset

theorem At.cold_helper_get? {limits : Validate.Limits}
    {context : Validate.Context} {blocks : List Block}
    {decisions : FunctionDecisions limits context blocks}
    {index helperOffset : Nat} {block : Block}
    {site : Site limits context block}
    (found : At decisions index helperOffset block (.accepted site))
    (originalCount startOffset : Nat) :
    (decisions.realize originalCount startOffset).helpers[helperOffset + 1]? =
      some (creditBlock site.candidate
        (.optional site.candidate.layout)) := by
  exact found.helper_get?
    (inside := 1) (by simp [Decision.helpers]) originalCount startOffset

end FunctionDecisions

/-- Complete proof-carrying rewrite of one function. -/
structure FunctionRewrite (limits : Validate.Limits)
    (context : Validate.Context) (source : Function) where
  decisions : FunctionDecisions limits context source.blocks.toList

namespace FunctionRewrite

def realization {limits : Validate.Limits} {context : Validate.Context}
    {source : Function} (rewrite : FunctionRewrite limits context source) :
    Realization :=
  rewrite.decisions.realize source.blocks.size 0

def definition {limits : Validate.Limits} {context : Validate.Context}
    {source : Function} (rewrite : FunctionRewrite limits context source) :
    Function :=
  { source with blocks :=
      (rewrite.realization.originals ++ rewrite.realization.helpers).toArray }

def report {limits : Validate.Limits} {context : Validate.Context}
    {source : Function} (rewrite : FunctionRewrite limits context source) :
    Report :=
  rewrite.realization.report

@[simp] theorem definition_signature {limits : Validate.Limits}
    {context : Validate.Context} {source : Function}
    (rewrite : FunctionRewrite limits context source) :
    rewrite.definition.signature = source.signature := by
  rfl

/-- Every original block ID has one exhaustive source decision and resolves to
that decision's replacement at the same target ID. -/
theorem decisionAt {limits : Validate.Limits} {context : Validate.Context}
    {source : Function} (rewrite : FunctionRewrite limits context source)
    (index : Nat) (bound : index < source.blocks.size) :
    ∃ helperOffset block decision,
      FunctionDecisions.At rewrite.decisions index helperOffset block
        decision ∧
      source.blocks[index]? = some block ∧
      rewrite.definition.blocks[index]? =
        some (decision.replacement source.blocks.size helperOffset) := by
  have listBound : index < source.blocks.toList.length := by
    simpa using bound
  obtain ⟨helperOffset, block, decision, found⟩ :=
    FunctionDecisions.exists_at rewrite.decisions index listBound
  have sourceAt : source.blocks[index]? = some block := by
    simpa only [Array.getElem?_toList] using found.source_get?
  let realized := rewrite.realization
  have originalsLength : realized.originals.length = source.blocks.size := by
    simp [realized, realization]
  have originalAt : realized.originals[index]? =
      some (decision.replacement source.blocks.size helperOffset) := by
    simpa [realized, realization] using
      found.original_get? source.blocks.size 0
  have originalBound : index < realized.originals.length := by
    simpa [originalsLength] using bound
  have targetAt : rewrite.definition.blocks[index]? =
      some (decision.replacement source.blocks.size helperOffset) := by
    change (realized.originals ++ realized.helpers).toArray[index]? = _
    rw [List.getElem?_toArray, List.getElem?_append_left originalBound]
    exact originalAt
  exact ⟨helperOffset, block, decision, found, sourceAt, targetAt⟩

/-- An accepted decision exposes all three target block lookups needed by the
semantic diamond: the reset replacement at the old ID and the appended hot
and cold credit blocks. -/
theorem acceptedAt {limits : Validate.Limits} {context : Validate.Context}
    {source : Function} (rewrite : FunctionRewrite limits context source)
    {index helperOffset : Nat} {block : Block}
    {site : Site limits context block}
    (found : FunctionDecisions.At rewrite.decisions index helperOffset block
      (.accepted site)) :
    source.blocks[index]? = some block ∧
    rewrite.definition.blocks[index]? =
      some (resetBlock site.candidate
        (source.blocks.size + helperOffset)
        (source.blocks.size + helperOffset + 1)) ∧
    rewrite.definition.blocks[source.blocks.size + helperOffset]? =
      some (creditBlock site.candidate
        (.required site.candidate.layout)) ∧
    rewrite.definition.blocks[source.blocks.size + helperOffset + 1]? =
      some (creditBlock site.candidate
        (.optional site.candidate.layout)) := by
  let realized := rewrite.realization
  have sourceAt : source.blocks[index]? = some block := by
    simpa only [Array.getElem?_toList] using found.source_get?
  have originalsLength : realized.originals.length = source.blocks.size := by
    simp [realized, realization]
  have originalAt : realized.originals[index]? =
      some (resetBlock site.candidate
        (source.blocks.size + helperOffset)
        (source.blocks.size + helperOffset + 1)) := by
    simpa [realized, realization, Decision.replacement] using
      found.original_get? source.blocks.size 0
  have originalBound : index < realized.originals.length := by
    rw [originalsLength]
    simpa using (List.getElem?_eq_some_iff.mp found.source_get?).choose
  have targetOriginal : rewrite.definition.blocks[index]? =
      some (resetBlock site.candidate
        (source.blocks.size + helperOffset)
        (source.blocks.size + helperOffset + 1)) := by
    change (realized.originals ++ realized.helpers).toArray[index]? = _
    rw [List.getElem?_toArray, List.getElem?_append_left originalBound]
    exact originalAt
  have hotAt : realized.helpers[helperOffset]? =
      some (creditBlock site.candidate
        (.required site.candidate.layout)) := by
    simpa [realized, realization] using
      found.hot_helper_get? source.blocks.size 0
  have coldAt : realized.helpers[helperOffset + 1]? =
      some (creditBlock site.candidate
        (.optional site.candidate.layout)) := by
    simpa [realized, realization] using
      found.cold_helper_get? source.blocks.size 0
  have targetHot :
      rewrite.definition.blocks[source.blocks.size + helperOffset]? =
        some (creditBlock site.candidate
          (.required site.candidate.layout)) := by
    change (realized.originals ++ realized.helpers).toArray[
      source.blocks.size + helperOffset]? = _
    rw [List.getElem?_toArray, ← originalsLength,
      List.getElem?_append_right (by omega)]
    simpa using hotAt
  have targetCold :
      rewrite.definition.blocks[source.blocks.size + helperOffset + 1]? =
        some (creditBlock site.candidate
          (.optional site.candidate.layout)) := by
    change (realized.originals ++ realized.helpers).toArray[
      source.blocks.size + helperOffset + 1]? = _
    rw [List.getElem?_toArray, ← originalsLength,
      List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc] using coldAt
  exact ⟨sourceAt, targetOriginal, targetHot, targetCold⟩

/-- At an accepted original block ID, the rewritten block cannot remain the
literal source block. This is the decision-level disjointness fact used to
show that unchanged synchronized blocks have no accepted-entry phase
obligation. -/
theorem accepted_target_ne_source {limits : Validate.Limits}
    {context : Validate.Context} {source : Function}
    (rewrite : FunctionRewrite limits context source)
    {index helperOffset : Nat} {block : Block}
    {site : Site limits context block}
    (found : FunctionDecisions.At rewrite.decisions index helperOffset block
      (.accepted site)) :
    rewrite.definition.blocks[index]? ≠ some block := by
  intro unchanged
  have target := (rewrite.acceptedAt found).2.1
  have equal : resetBlock site.candidate
      (source.blocks.size + helperOffset)
      (source.blocks.size + helperOffset + 1) = block :=
    Option.some.inj (target.symm.trans unchanged)
  exact site.ne_resetBlock _ _ equal.symm

/-- Exhaustive proof-facing classification of one original block ID.  A
rejected decision exposes literal source/target block equality; an accepted
decision retains the dependent site witness from which `acceptedAt` recovers
the reset and both helper blocks. -/
inductive BlockCase {limits : Validate.Limits} {context : Validate.Context}
    {source : Function} (rewrite : FunctionRewrite limits context source)
    (index : Nat) : Prop where
  | unchanged {block : Block}
      (sourceAt : source.blocks[index]? = some block)
      (targetAt : rewrite.definition.blocks[index]? = some block) :
      BlockCase rewrite index
  | accepted {helperOffset : Nat} {block : Block}
      {site : Site limits context block}
      (found : FunctionDecisions.At rewrite.decisions index helperOffset
        block (.accepted site)) :
      BlockCase rewrite index

/-- Every original block ID is either preserved literally or carries the
accepted-site witness needed by the semantic reset/reuse diamond. -/
theorem blockCase {limits : Validate.Limits} {context : Validate.Context}
    {source : Function} (rewrite : FunctionRewrite limits context source)
    (index : Nat) (bound : index < source.blocks.size) :
    BlockCase rewrite index := by
  obtain ⟨helperOffset, block, decision, found, sourceAt, targetAt⟩ :=
    rewrite.decisionAt index bound
  cases decision with
  | noShape notFound =>
      exact .unchanged sourceAt
        (by simpa [Decision.replacement] using targetAt)
  | livenessError shape shapeFound error rejected =>
      exact .unchanged sourceAt
        (by simpa [Decision.replacement] using targetAt)
  | livenessMiss shape shapeFound rejected =>
      exact .unchanged sourceAt
        (by simpa [Decision.replacement] using targetAt)
  | representationMiss shape shapeFound placement placementFound notFound =>
      exact .unchanged sourceAt
        (by simpa [Decision.replacement] using targetAt)
  | operandMiss shape shapeFound placement placementFound representation
      representationFound notFound =>
      exact .unchanged sourceAt
        (by simpa [Decision.replacement] using targetAt)
  | accepted site =>
      exact .accepted found

/-- A successful source lookup supplies the bound needed for exhaustive
decision dispatch. -/
theorem blockCaseOfLookup {limits : Validate.Limits}
    {context : Validate.Context} {source : Function}
    (rewrite : FunctionRewrite limits context source)
    {index : Nat} {block : Block}
    (found : source.blocks[index]? = some block) :
    BlockCase rewrite index := by
  have bound : index < source.blocks.size :=
    (Array.getElem?_eq_some_iff.mp found).choose
  exact rewrite.blockCase index bound

/-- Every original target ID retains the source block's incoming value and
credit ABI, even when its body is replaced by an accepted reset block. -/
theorem targetBlockAbi {limits : Validate.Limits}
    {context : Validate.Context} {source : Function}
    (rewrite : FunctionRewrite limits context source)
    {index : Nat} {block : Block}
    (found : source.blocks[index]? = some block) :
    ∃ targetBlock,
      rewrite.definition.blocks[index]? = some targetBlock ∧
      targetBlock.valueParams = block.valueParams ∧
      targetBlock.creditParams = block.creditParams := by
  have bound : index < source.blocks.size :=
    (Array.getElem?_eq_some_iff.mp found).choose
  obtain ⟨helperOffset, selectedBlock, decision, _selected,
      sourceAt, targetAt⟩ := rewrite.decisionAt index bound
  have blockEq : selectedBlock = block :=
    Option.some.inj (sourceAt.symm.trans found)
  subst selectedBlock
  exact ⟨decision.replacement source.blocks.size helperOffset, targetAt,
    decision.replacement_valueParams source.blocks.size helperOffset,
    decision.replacement_creditParams source.blocks.size helperOffset⟩

/-- Rewriting cannot turn an executable function into an empty one: every
source block keeps an original target coordinate. -/
theorem definition_blocks_nonempty {limits : Validate.Limits}
    {context : Validate.Context} {source : Function}
    (rewrite : FunctionRewrite limits context source)
    (nonempty : source.blocks.isEmpty = false) :
    rewrite.definition.blocks.isEmpty = false := by
  have sourceEntryBound : 0 < source.blocks.size := by
    apply Nat.pos_of_ne_zero
    intro sizeZero
    exact (Array.isEmpty_eq_false_iff.mp nonempty)
      (Array.size_eq_zero_iff.mp sizeZero)
  have sourceEntry : source.blocks[0]? = some source.blocks[0] :=
    Array.getElem?_eq_getElem sourceEntryBound
  obtain ⟨targetEntry, targetEntryAt, _valueParams, _creditParams⟩ :=
    rewrite.targetBlockAbi sourceEntry
  apply Array.isEmpty_eq_false_iff.mpr
  intro targetEmpty
  rw [targetEmpty] at targetEntryAt
  simp at targetEntryAt

end FunctionRewrite

/-- Rewrite every independent matching block in one function while retaining
the exact ordered decision trace. -/
def rewriteFunction (limits : Validate.Limits) (context : Validate.Context)
    (definition : Function) : FunctionRewrite limits context definition :=
  { decisions := classifyBlocks limits context definition.blocks.toList }

/-- Pure rewrite output, separated from validation so its exact result can be
retained in the checked API. -/
structure Rewrite where
  program : Program
  report : Report
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Ordered function traces indexed by the literal declaration list.  Extern
entries are preserved exactly; function entries carry their dependent block
decision trace. -/
inductive DeclarationDecisions (limits : Validate.Limits)
    (context : Validate.Context) :
    List (Ix.Compiler.Ixon.Address × Decl) → Type where
  | nil : DeclarationDecisions limits context []
  | extern (address : Ix.Compiler.Ixon.Address) (arity : Nat)
      {rest : List (Ix.Compiler.Ixon.Address × Decl)}
      (tail : DeclarationDecisions limits context rest) :
      DeclarationDecisions limits context
        ((address, .extern arity) :: rest)
  | fn (address : Ix.Compiler.Ixon.Address) (definition : Function)
      {rest : List (Ix.Compiler.Ixon.Address × Decl)}
      (head : FunctionRewrite limits context definition)
      (tail : DeclarationDecisions limits context rest) :
      DeclarationDecisions limits context
        ((address, .fn definition) :: rest)

def rewriteDeclarations (limits : Validate.Limits)
    (context : Validate.Context) :
    (declarations : List (Ix.Compiler.Ixon.Address × Decl)) →
      DeclarationDecisions limits context declarations
  | [] => .nil
  | (address, .extern arity) :: rest =>
      .extern address arity (rewriteDeclarations limits context rest)
  | (address, .fn definition) :: rest =>
      .fn address definition (rewriteFunction limits context definition)
        (rewriteDeclarations limits context rest)

namespace DeclarationDecisions

def target {limits : Validate.Limits} {context : Validate.Context} :
    {source : List (Ix.Compiler.Ixon.Address × Decl)} →
      DeclarationDecisions limits context source →
      List (Ix.Compiler.Ixon.Address × Decl)
  | [], .nil => []
  | _, .extern address arity tail =>
      (address, .extern arity) :: target tail
  | _, .fn address _ head tail =>
      (address, .fn head.definition) :: target tail

def report {limits : Validate.Limits} {context : Validate.Context} :
    {source : List (Ix.Compiler.Ixon.Address × Decl)} →
      DeclarationDecisions limits context source → Report
  | [], .nil => {}
  | _, .extern _ _ tail => report tail
  | _, .fn _ _ head tail => head.report.add (report tail)

end DeclarationDecisions

/-- Declaration-level relation exported by the rewrite trace. -/
inductive DeclarationRel (limits : Validate.Limits)
    (context : Validate.Context) : Decl → Decl → Prop where
  | extern (arity : Nat) : DeclarationRel limits context
      (.extern arity) (.extern arity)
  | fn {source : Function}
      (rewrite : FunctionRewrite limits context source) :
      DeclarationRel limits context (.fn source) (.fn rewrite.definition)

inductive DeclarationsRel (limits : Validate.Limits)
    (context : Validate.Context) :
    List (Ix.Compiler.Ixon.Address × Decl) →
      List (Ix.Compiler.Ixon.Address × Decl) → Prop where
  | nil : DeclarationsRel limits context [] []
  | extern (address : Ix.Compiler.Ixon.Address) (arity : Nat)
      {sourceTarget : List (Ix.Compiler.Ixon.Address × Decl)}
      {targetTail : List (Ix.Compiler.Ixon.Address × Decl)}
      (tail : DeclarationsRel limits context sourceTarget targetTail) :
      DeclarationsRel limits context
        ((address, .extern arity) :: sourceTarget)
        ((address, .extern arity) :: targetTail)
  | fn (address : Ix.Compiler.Ixon.Address) {source : Function}
      (rewrite : FunctionRewrite limits context source)
      {sourceTail targetTail : List (Ix.Compiler.Ixon.Address × Decl)}
      (tail : DeclarationsRel limits context sourceTail targetTail) :
      DeclarationsRel limits context
        ((address, .fn source) :: sourceTail)
        ((address, .fn rewrite.definition) :: targetTail)

theorem DeclarationDecisions.related {limits : Validate.Limits}
    {context : Validate.Context}
    {source : List (Ix.Compiler.Ixon.Address × Decl)}
    (decisions : DeclarationDecisions limits context source) :
    DeclarationsRel limits context source decisions.target := by
  induction decisions with
  | nil => exact .nil
  | extern address arity tail ih =>
      exact .extern address arity ih
  | fn address definition head tail ih =>
      exact .fn address head ih

/-- Address lookup preserves extern declarations exactly. -/
theorem DeclarationsRel.find?_extern {limits : Validate.Limits}
    {context : Validate.Context}
    {source target : List (Ix.Compiler.Ixon.Address × Decl)}
    (related : DeclarationsRel limits context source target)
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    (found : source.find? (fun entry => entry.1 == address) =
      some (address, .extern arity)) :
    target.find? (fun entry => entry.1 == address) =
      some (address, .extern arity) := by
  induction related with
  | nil => simp at found
  | extern current currentArity tail ih =>
      by_cases same : current = address
      · subst current
        simpa using found
      · simpa [same] using ih (by simpa [same] using found)
  | fn current rewrite tail ih =>
      by_cases same : current = address
      · subst current
        simp at found
      · simpa [same] using ih (by simpa [same] using found)

/-- A source function lookup selects the exact function rewrite retained at
the same target address. -/
theorem DeclarationsRel.find?_fn {limits : Validate.Limits}
    {context : Validate.Context}
    {source target : List (Ix.Compiler.Ixon.Address × Decl)}
    (related : DeclarationsRel limits context source target)
    {address : Ix.Compiler.Ixon.Address} {definition : Function}
    (found : source.find? (fun entry => entry.1 == address) =
      some (address, .fn definition)) :
    ∃ rewrite : FunctionRewrite limits context definition,
      target.find? (fun entry => entry.1 == address) =
        some (address, .fn rewrite.definition) := by
  induction related with
  | nil => simp at found
  | extern current arity tail ih =>
      by_cases same : current = address
      · subst current
        simp at found
      · obtain ⟨selected, selectedAt⟩ :=
          ih (by simpa [same] using found)
        exact ⟨selected, by simpa [same] using selectedAt⟩
  | @fn current currentDefinition rewrite sourceTail targetTail tail ih =>
      by_cases same : current = address
      · subst current
        simp at found
        subst definition
        exact ⟨rewrite, by simp⟩
      · obtain ⟨selected, selectedAt⟩ :=
          ih (by simpa [same] using found)
        exact ⟨selected, by simpa [same] using selectedAt⟩

/-- Complete typed trace for one program rewrite. -/
structure Trace (limits : Validate.Limits) (context : Validate.Context)
    (source : Program) where
  declarations : DeclarationDecisions limits context source.declarations
  main : FunctionRewrite limits context source.main

namespace Trace

def target {limits : Validate.Limits} {context : Validate.Context}
    {source : Program} (trace : Trace limits context source) : Program :=
  { declarations := trace.declarations.target
    main := trace.main.definition }

def report {limits : Validate.Limits} {context : Validate.Context}
    {source : Program} (trace : Trace limits context source) : Report :=
  trace.declarations.report.add trace.main.report

def rewrite {limits : Validate.Limits} {context : Validate.Context}
    {source : Program} (trace : Trace limits context source) : Rewrite :=
  { program := trace.target, report := trace.report }

theorem declarations_related {limits : Validate.Limits}
    {context : Validate.Context} {source : Program}
    (trace : Trace limits context source) :
    DeclarationsRel limits context source.declarations
      trace.target.declarations :=
  trace.declarations.related

@[simp] theorem target_main_signature {limits : Validate.Limits}
    {context : Validate.Context} {source : Program}
    (trace : Trace limits context source) :
    trace.target.main.signature = source.main.signature := by
  exact trace.main.definition_signature

/-- Function lookup in the executable evaluator context selects the exact
function trace at the same address. -/
theorem context_fn {limits : Validate.Limits}
    {context : Validate.Context} {source : Program}
    (trace : Trace limits context source)
    {oracle : Ix.Compiler.Ixon.Address → List Eval.RVal → Option Eval.RVal}
    {address : Ix.Compiler.Ixon.Address} {definition : Function}
    (found : (Eval.Context.ofProgram source context.schemas oracle).declarations
      address = some (.fn definition)) :
    ∃ rewrite : FunctionRewrite limits context definition,
      (Eval.Context.ofProgram trace.target context.schemas oracle).declarations
        address = some (.fn rewrite.definition) := by
  change (source.declarations.find? (fun entry => entry.1 == address)).map
      (fun entry => entry.2) = some (.fn definition) at found
  cases sourceFind :
      source.declarations.find? (fun entry => entry.1 == address) with
  | none => simp [sourceFind] at found
  | some entry =>
      obtain ⟨entryAddress, entryDecl⟩ := entry
      have addressEq : entryAddress = address := by
        apply beq_iff_eq.mp
        exact List.find?_some
          (p := fun entry : Ix.Compiler.Ixon.Address × Decl =>
            entry.1 == address) sourceFind
      subst entryAddress
      have declarationEq : entryDecl = .fn definition := by
        simpa [sourceFind] using found
      subst entryDecl
      obtain ⟨rewrite, targetFind⟩ :=
        trace.declarations_related.find?_fn sourceFind
      exact ⟨rewrite, by
        change (trace.target.declarations.find?
          (fun entry => entry.1 == address)).map (fun entry => entry.2) = _
        simp [targetFind]⟩

/-- Extern lookup is preserved literally in the rewritten evaluator
context. -/
theorem context_extern {limits : Validate.Limits}
    {context : Validate.Context} {source : Program}
    (trace : Trace limits context source)
    {oracle : Ix.Compiler.Ixon.Address → List Eval.RVal → Option Eval.RVal}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    (found : (Eval.Context.ofProgram source context.schemas oracle).declarations
      address = some (.extern arity)) :
    (Eval.Context.ofProgram trace.target context.schemas oracle).declarations
      address = some (.extern arity) := by
  change (source.declarations.find? (fun entry => entry.1 == address)).map
      (fun entry => entry.2) = some (.extern arity) at found
  cases sourceFind :
      source.declarations.find? (fun entry => entry.1 == address) with
  | none => simp [sourceFind] at found
  | some entry =>
      obtain ⟨entryAddress, entryDecl⟩ := entry
      have addressEq : entryAddress = address := by
        apply beq_iff_eq.mp
        exact List.find?_some
          (p := fun entry : Ix.Compiler.Ixon.Address × Decl =>
            entry.1 == address) sourceFind
      subst entryAddress
      have declarationEq : entryDecl = .extern arity := by
        simpa [sourceFind] using found
      subst entryDecl
      have targetFind :=
        trace.declarations_related.find?_extern sourceFind
      change (trace.target.declarations.find?
        (fun entry => entry.1 == address)).map (fun entry => entry.2) = _
      simp [targetFind]

end Trace

/-- Produce the target and the proof-facing decision trace in one traversal. -/
def traceProgramWith (limits : Validate.Limits) (context : Validate.Context)
    (program : Program) : Trace limits context program :=
  { declarations := rewriteDeclarations limits context program.declarations
    main := rewriteFunction limits context program.main }

def rewriteProgramWith (limits : Validate.Limits) (context : Validate.Context)
    (program : Program) : Rewrite :=
  (traceProgramWith limits context program).rewrite

def rewriteProgram (context : Validate.Context) (program : Program) : Rewrite :=
  rewriteProgramWith Validate.defaultLimits context program

inductive Error where
  | invalidSource (error : Validate.Error)
  | invalidTarget (error : Validate.Error)
  deriving BEq, Repr

/-- A rewrite whose source and target both passed the same bounded ownership,
credit, call, schema, and CFG checker. -/
structure Output (limits : Validate.Limits) (context : Validate.Context)
    (source : Program) where
  rewrite : Rewrite
  trace : Trace limits context source
  traceProduces : trace.rewrite = rewrite
  sourceStats : Validate.Stats
  targetStats : Validate.Stats
  sourceAccepted :
    Validate.validateWith limits context source = .ok sourceStats
  targetAccepted :
    Validate.validateWith limits context rewrite.program = .ok targetStats

namespace Output

def target {limits : Validate.Limits} {context : Validate.Context}
    {source : Program} (output : Output limits context source) : Program :=
  output.rewrite.program

def report {limits : Validate.Limits} {context : Validate.Context}
    {source : Program} (output : Output limits context source) : Report :=
  output.rewrite.report

/-- The retained decision trace materializes the exact validated target. -/
theorem trace_target {limits : Validate.Limits} {context : Validate.Context}
    {source : Program} (output : Output limits context source) :
    output.trace.target = output.target := by
  exact congrArg Rewrite.program output.traceProduces

/-- Report counters are computed from the same exhaustive trace. -/
theorem trace_report {limits : Validate.Limits} {context : Validate.Context}
    {source : Program} (output : Output limits context source) :
    output.trace.report = output.report := by
  exact congrArg Rewrite.report output.traceProduces

theorem sourceValid {limits : Validate.Limits} {context : Validate.Context}
    {source : Program} (output : Output limits context source) :
    Validate.ValidWith limits context source :=
  ⟨output.sourceStats, output.sourceAccepted⟩

theorem targetValid {limits : Validate.Limits} {context : Validate.Context}
    {source : Program} (output : Output limits context source) :
    Validate.ValidWith limits context output.target :=
  ⟨output.targetStats, output.targetAccepted⟩

end Output

/-- Validate, rewrite, and validate again under one explicit resource policy. -/
def optimizeWith (limits : Validate.Limits) (context : Validate.Context)
    (source : Program) : Except Error (Output limits context source) :=
  match sourceAccepted : Validate.validateWith limits context source with
  | .error error => .error (.invalidSource error)
  | .ok sourceStats =>
      let trace := traceProgramWith limits context source
      let rewrite := trace.rewrite
      match targetAccepted :
          Validate.validateWith limits context rewrite.program with
      | .error error => .error (.invalidTarget error)
      | .ok targetStats =>
          .ok { rewrite, trace, traceProduces := rfl, sourceStats, targetStats,
                sourceAccepted, targetAccepted }

def optimize (context : Validate.Context) (source : Program) :
    Except Error (Output Validate.defaultLimits context source) :=
  optimizeWith Validate.defaultLimits context source

/-- A target-validation failure can occur only after the source passed the
same validator. This checked baseline is the fallback for an optional rewrite. -/
theorem sourceValid_of_invalidTarget {limits : Validate.Limits}
    {context : Validate.Context} {source : Program} {error : Validate.Error}
    (rejected : optimizeWith limits context source = .error (.invalidTarget error)) :
    Validate.ValidWith limits context source := by
  unfold optimizeWith at rejected
  split at rejected
  next sourceError _sourceRejected => cases rejected
  next stats accepted => exact ⟨stats, accepted⟩

/-- Invalid source input remains a compilation error; it is never a usable
fallback merely because optimization was optional. -/
theorem sourceRejected_of_invalidSource {limits : Validate.Limits}
    {context : Validate.Context} {source : Program} {error : Validate.Error}
    (rejected : optimizeWith limits context source = .error (.invalidSource error)) :
    Validate.validateWith limits context source = .error error := by
  unfold optimizeWith at rejected
  split at rejected
  next sourceError accepted =>
    cases rejected
    exact accepted
  next _stats _accepted =>
    dsimp only at rejected
    split at rejected <;> cases rejected

/-- The production outcome names either the exact validated rewrite or the
exact rejected attempt which selects the already-validated baseline. -/
inductive Selection (limits : Validate.Limits) (context : Validate.Context)
    (source : Program) where
  | optimized (output : Output limits context source)
      (produced : optimizeWith limits context source = .ok output)
  | baseline (error : Validate.Error)
      (rejected : optimizeWith limits context source = .error (.invalidTarget error))

/-- A skipped optimization reports its target-validation error explicitly. -/
inductive SelectionReport where
  | applied (report : Report)
  | skipped (error : Validate.Error)
  deriving BEq, Repr

namespace Selection

def target {limits : Validate.Limits} {context : Validate.Context}
    {source : Program} : Selection limits context source → Program
  | .optimized output _ => output.target
  | .baseline _ _ => source

def report {limits : Validate.Limits} {context : Validate.Context}
    {source : Program} : Selection limits context source → SelectionReport
  | .optimized output _ => .applied output.report
  | .baseline error _ => .skipped error

/-- Production selection always returns a program accepted by the requested
bounded validator, including when the optional rewrite was rejected. -/
theorem valid {limits : Validate.Limits} {context : Validate.Context}
    {source : Program} (selection : Selection limits context source) :
    Validate.ValidWith limits context selection.target := by
  cases selection with
  | optimized output _ => exact output.targetValid
  | baseline _ rejected => exact sourceValid_of_invalidTarget rejected

end Selection

/-- Attempt dynamic reuse while preserving a checked baseline on target
rejection. Source-validation errors retain the diagnostic API's error type. -/
def selectWith (limits : Validate.Limits) (context : Validate.Context)
    (source : Program) : Except Error (Selection limits context source) :=
  match produced : optimizeWith limits context source with
  | .ok output => .ok (.optimized output produced)
  | .error (.invalidTarget error) => .ok (.baseline error produced)
  | .error (.invalidSource error) => .error (.invalidSource error)

def select (context : Validate.Context) (source : Program) :
    Except Error (Selection Validate.defaultLimits context source) :=
  selectWith Validate.defaultLimits context source

/-- Selection is total once the baseline is checked. The proof argument is
erased at runtime, and the optional optimizer still records its exact outcome. -/
def selectCheckedWith (limits : Validate.Limits) (context : Validate.Context)
    (source : Program) (valid : Validate.ValidWith limits context source) :
    Selection limits context source :=
  match produced : optimizeWith limits context source with
  | .ok output => .optimized output produced
  | .error (.invalidTarget error) => .baseline error produced
  | .error (.invalidSource error) => False.elim (by
      obtain ⟨stats, accepted⟩ := valid
      have rejected := sourceRejected_of_invalidSource produced
      rw [accepted] at rejected
      cases rejected)

def selectChecked (context : Validate.Context) (source : Program)
    (valid : Validate.ValidWith Validate.defaultLimits context source) :
    Selection Validate.defaultLimits context source :=
  selectCheckedWith Validate.defaultLimits context source valid


end Ix.Compiler.IxIR2.Reuse
