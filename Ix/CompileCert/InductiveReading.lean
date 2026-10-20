import Ix.CompileCert.ReaderIndexDiscovery
import Ix.CompileCert.DefinitionReading
import Ix.CompileCert.ReaderSourceSpines
import Ix.CompileCert.Canon.Ref

/-! # Compiled standalone inductives are read back as their sources

Public dispatch of an inductive compiles its standalone family: one block
`.muts #[.indc target]` (`ProjectionLayout.dispatch_layout`). The certified
reader reads such a record with `readInductive`, which builds the block's
`BlockRead` from its records and lowers it with `lowerInductive`, the
record-agnostic half it shares with `Ix.LeanIngress` (CT-READING-PLAN §3.11).
Its recursors are read from their own records, through the recursor index.

`inductive_reads` composes the compile-side theorem of the family block
(`EmissionBlocks.familyInfo_correct`, with exactly the reader's member
reader) with the reader: a successful compile from a clean state, whose
block the index shapes at member 0, whose keys read, and whose source is
well formed (safe, constructors at their positions, each constructor type a
telescope of its parameters and fields), is read by `readRecord` as
`lowerInductive` of the `BlockRead` the source describes (`sourceBlock`):
the inductive under its key with level parameters `0, …, n - 1` and a type
`Related` to the source's, its constructors in source order under their
keys with types related to the sources', and the recursors the reader's own
loop reads from their records (`readRecursors`; their correspondence with
the compiled recursors is R10b). The returned block decodes exactly.
`inductive_reads_indexed` derives the index shape from the reader's own
index (`ReaderIndex.compiled_order`). The reader runs over the block's blobs
overlaid on the context's (publication is R13).

CT-16's `InductiveReading`, re-derived against `readInductive` = `BlockRead`
+ `lowerInductive` (5b): the donor's family assembly checks are
`lowerInductive`'s now, so the statement is the `BlockRead` itself. The
reader's loops are restated as named steps (`typeStep`, `ctorStep`,
`ctorClassStep`, `recursorStep`) and `readInductive` is that statement by
`rfl` (`readInductive_eq`). Under `surgeryFree` until CQ3.5. -/

namespace Ix.CompileCert.InductiveReading

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam ConstRef)
open Ix.Kernel.Reader
open Ix.Sharing.Verify (BlockWireTablesWF BlockResultCodecWF)

variable {md : Mode}

/-! ## The reader's inductive block, step by step -/

/-- The self references of a block's members, as `readInductive` reads them:
member `i` of the block is its key. -/
def blockSelf (cx : Ctx md) (owner : Address) (ms : Array Ixon.MutConst) : Nat → Option (ReadM (CName md)) :=
  fun i => if i < ms.size then some (cx.memberKey (.member owner i)) else none

/-- The inductive at a block position, as `readInductive` selects it. -/
def indcAt (ms : Array Ixon.MutConst) (i : Nat) : Option (Nat × Ixon.Inductive) :=
  match (ms[i]? : Option Ixon.MutConst) with
  | some (.indc ind) => some (i, ind)
  | _ => none

/-- One type of the block, in motive order. -/
def typeStep (cx : Ctx md) (owner : Address) (mrInd : MemberReader md) (x : Nat × Ixon.Inductive)
    (types : Array (CVal md × Nat × Nat)) : ReadM (ForInStep (Array (CVal md × Nat × Nat))) :=
  match x with
  | (i, ind) => do
    let name ← cx.memberKey (.member owner i)
    let type ← mrInd.read ind.typ
    pure (.yield (types.push (⟨name, List.range ind.lvls.toNat, type⟩, ind.params.toNat, ind.indices.toNat)))

/-- One constructor of the block's type `i`, in the block's order. -/
def ctorStep (cx : Ctx md) (owner : Address) (mrInd : MemberReader md) (nPd i : Nat) (x : Ixon.Constructor × Nat)
    (state : Array (CVal md × Nat × Nat) × List (CName md)) :
    ReadM (ForInStep (Array (CVal md × Nat × Nat) × List (CName md))) := do
  let ctors := state.1
  let names := state.2
  match x with
  | (ctor, j) =>
    unless ctor.cidx.toNat == j do malformed "constructor index differs from its position"
    if ctor.isUnsafe then declined "unsafe inductive declaration"
    let cv : CVal md :=
      ⟨← cx.memberKey (.ctor owner i j), List.range ctor.lvls.toNat, ← mrInd.read ctor.typ⟩
    unless nPd + ctor.fields.toNat == piTeleLen cv.type do
      malformed s!"constructor {cv.name} declares {ctor.fields} fields at {nPd} parameters; \
        its type has {piTeleLen cv.type} binders"
    pure (.yield (ctors.push (cv, ctor.params.toNat, ctor.fields.toNat), names ++ [cv.name]))

/-- The constructors of the block's type `i`. -/
def ctorClassStep (cx : Ctx md) (owner : Address) (mrInd : MemberReader md) (nPd : Nat)
    (x : Nat × Ixon.Inductive) (state : Array (CVal md × Nat × Nat) × Array (List (CName md))) :
    ReadM (ForInStep (Array (CVal md × Nat × Nat) × Array (List (CName md)))) := do
  let ctors := state.1
  let ctorNames := state.2
  match x with
  | (i, ind) => do
    let result ← forIn ind.ctors.zipIdx (ctors, ([] : List (CName md))) (ctorStep cx owner mrInd nPd i)
    pure (.yield (result.1, ctorNames.push result.2))

/-- One recursor of the block, read from its own record. -/
def recursorStep (cx : Ctx md) (blockLps : List LevelParam) (ref : ConstRef Address)
    (recs : Array (CVal md × RecCounts × List (Ix.Kernel.RecRule md))) :
    ReadM (ForInStep (Array (CVal md × RecCounts × List (Ix.Kernel.RecRule md)))) := do
  let some entry := cx.index.recs[ref]? | malformed "unindexed recursor"
  let .member rOwner j := ref | malformed "recursor reference is a constructor"
  let some rc := cx.store rOwner | malformed "recursor record is missing"
  let some (_, r) := (recursorMembers rc).find? (·.1 == j) | malformed "recursor member is missing"
  if r.isUnsafe then declined "unsafe inductive declaration"
  let key ← cx.memberKey ref
  let rself : Nat → Option (ReadM (CName md)) := fun i => match rc.info with
    | .muts rms => if i < rms.size then some (cx.memberKey (.member rOwner i)) else none
    | _ => if i == 0 then some (pure key) else none
  let lps := recLps entry.large blockLps
  let mr := MemberReader.mk' cx rc (recParam lps) rself
  let cv : CVal md := ⟨key, lps, ← mr.read r.typ⟩
  let some major := inductiveAt cx.store entry.major
    | declined s!"recursor {key}: its major premise is not an inductive"
  unless major.ctors.size == r.rules.size do
    malformed s!"recursor {key} has {r.rules.size} rules for {major.ctors.size} constructors"
  let .member mb mi := entry.major | malformed "recursor major is a constructor"
  let mut rules : List (Ix.Kernel.RecRule md) := []
  for (rule, k) in r.rules.zipIdx do
    rules := rules ++ [Ix.Kernel.RecRule.mk (← cx.memberKey (.ctor mb mi k)) rule.fields.toNat 0 .inert
      (← mr.read rule.rhs) false false false]
  pure (.yield (recs.push (cv, ⟨r.params.toNat, r.motives.toNat, r.minors.toNat, r.indices.toNat, r.k,
    some entry.motive⟩, rules)))

/-- **The block's recursors, as the reader reads them** from their own
records, in the block shape's motive order. -/
def readRecursors (cx : Ctx md) (blockLps : List LevelParam) (refs : Array (ConstRef Address)) :
    ReadM (Array (CVal md × RecCounts × List (Ix.Kernel.RecRule md))) :=
  forIn refs #[] (recursorStep cx blockLps)

/-- `readInductive` with its loops as named steps. -/
def readInductiveSpec (cx : Ctx md) (st : State md) (owner : Address) (c : Ixon.Constant)
    (ms : Array Ixon.MutConst) : ReadM (Read md) := do
  let some shape := cx.index.blocks[owner]?
    | declined "inductive block without a recursor in the input"
  let indcs : Array (Nat × Ixon.Inductive) := shape.order.filterMap (indcAt ms)
  unless indcs.size == shape.order.size do malformed "recursor motive is not a member of its block"
  let some (_, first) := indcs[0]? | malformed "empty inductive block"
  if indcs.any (·.2.isUnsafe) then declined "unsafe inductive declaration"
  let nPd := first.params.toNat
  unless indcs.all (·.2.params.toNat == nPd) do
    declined "inductive block whose type records disagree on numParams"
  let blockLps := List.range first.lvls.toNat
  let mrInd := MemberReader.mk' cx c id (blockSelf cx owner ms)
  let types ← forIn indcs #[] (typeStep cx owner mrInd)
  let result ← forIn indcs (#[], #[]) (ctorClassStep cx owner mrInd nPd)
  let recs ← readRecursors cx blockLps shape.recs
  lowerInductive st ⟨nPd, types, result.1, result.2, recs⟩

theorem readInductive_eq (cx : Ctx md) (st : State md) (owner : Address) (c : Ixon.Constant)
    (ms : Array Ixon.MutConst) : readInductive cx st owner c ms = readInductiveSpec cx st owner c ms := rfl

theorem blockSelf_blobs (cx : Ctx md) (state : BlockState) (owner : Address) (ms : Array Ixon.MutConst) :
    blockSelf (ExpressionRead.withBlockBlobs cx state) owner ms = blockSelf cx owner ms := rfl

/-! ## The reader on a standalone inductive block -/

theorem readRecord_inductive (cx : Ctx md) (st : State md) (owner : Address) (c : Ixon.Constant)
    (target : Ixon.Inductive) (info : c.info = .muts #[.indc target]) :
    readRecord cx st owner c = readInductive cx st owner c #[.indc target] := by
  unfold readRecord
  rw [info]
  simp

theorem indcs_singleton (target : Ixon.Inductive) :
    (#[0] : Array Nat).filterMap (indcAt #[.indc target]) = #[(0, target)] := rfl

theorem typeLoop (cx : Ctx md) (owner : Address) (mr : MemberReader md) (target : Ixon.Inductive)
    {key : CName md} {type : CExpr md} (keyed : cx.memberKey (.member owner 0) = .ok key)
    (typeRead : mr.read target.typ = .ok type) :
    forIn (#[(0, target)] : Array (Nat × Ixon.Inductive)) #[] (typeStep cx owner mr) =
      .ok #[(⟨key, List.range target.lvls.toNat, type⟩, target.params.toNat, target.indices.toNat)] := by
  simp only [List.forIn_toArray, List.forIn_cons, List.forIn_nil, typeStep, keyed, typeRead, bind, Except.bind,
    pure, Except.pure]
  rfl

/-- What the reader reads of each constructor, from position `j`. -/
def ctorReads (ctorKey : Nat → CName md) : Nat → List Ixon.Constructor → List (CExpr md) →
    List (CVal md × Nat × Nat)
  | j, ctor :: ctors, type :: types =>
    (⟨ctorKey j, List.range ctor.lvls.toNat, type⟩, ctor.params.toNat, ctor.fields.toNat) ::
      ctorReads ctorKey (j + 1) ctors types
  | _, _, _ => []

/-- The constructor loop's checks pass and its reads succeed, constructor by
constructor, from position `j`. -/
def CtorFacts (cx : Ctx md) (owner : Address) (mr : MemberReader md) (nPd : Nat) (ctorKey : Nat → CName md) :
    Nat → List Ixon.Constructor → List (CExpr md) → Prop
  | _, [], [] => True
  | j, ctor :: ctors, type :: types =>
    ctor.cidx.toNat = j ∧ ctor.isUnsafe = false ∧ cx.memberKey (.ctor owner 0 j) = .ok (ctorKey j) ∧
      mr.read ctor.typ = .ok type ∧ nPd + ctor.fields.toNat = piTeleLen type ∧
      CtorFacts cx owner mr nPd ctorKey (j + 1) ctors types
  | _, _, _ => False

theorem ctorStep_ok (cx : Ctx md) (owner : Address) (mr : MemberReader md) (nPd : Nat) (ctor : Ixon.Constructor)
    (j : Nat) (state : Array (CVal md × Nat × Nat) × List (CName md)) {key : CName md} {type : CExpr md}
    (index : ctor.cidx.toNat = j) (safe : ctor.isUnsafe = false)
    (keyed : cx.memberKey (.ctor owner 0 j) = .ok key) (read : mr.read ctor.typ = .ok type)
    (arity : nPd + ctor.fields.toNat = piTeleLen type) :
    ctorStep cx owner mr nPd 0 (ctor, j) state =
      .ok (.yield (state.1.push (⟨key, List.range ctor.lvls.toNat, type⟩, ctor.params.toNat, ctor.fields.toNat),
        state.2 ++ [key])) := by
  simp only [ctorStep, index, safe, keyed, read, arity, beq_self_eq_true, Bool.false_eq_true,
    ↓reduceIte, bind, Except.bind, pure, Except.pure]

theorem ctorLoop_ok (cx : Ctx md) (owner : Address) (mr : MemberReader md) (nPd : Nat) (ctorKey : Nat → CName md) :
    ∀ (targets : List Ixon.Constructor) (j : Nat) (types : List (CExpr md))
      (state : Array (CVal md × Nat × Nat) × List (CName md)),
      CtorFacts cx owner mr nPd ctorKey j targets types →
      forIn (targets.zipIdx j) state (ctorStep cx owner mr nPd 0) =
        .ok ((state.1.toList ++ ctorReads ctorKey j targets types).toArray,
          state.2 ++ (ctorReads ctorKey j targets types).map (·.1.name)) := by
  intro targets
  induction targets with
  | nil =>
    intro j types state facts
    cases types with
    | nil => simp [ctorReads]; rfl
    | cons _ _ => exact False.elim facts
  | cons ctor rest ih =>
    intro j types state facts
    cases types with
    | nil => exact False.elim facts
    | cons type types =>
      obtain ⟨index, safe, keyed, read, arity, tail⟩ := facts
      rw [List.zipIdx_cons, List.forIn_cons, ctorStep_ok cx owner mr nPd ctor j state index safe keyed read arity]
      simp only [bind, Except.bind]
      rw [ih (j + 1) types _ tail]
      simp [ctorReads]

theorem ctorClassLoop (cx : Ctx md) (owner : Address) (mr : MemberReader md) (target : Ixon.Inductive)
    (ctorKey : Nat → CName md) (types : List (CExpr md))
    (facts : CtorFacts cx owner mr target.params.toNat ctorKey 0 target.ctors.toList types) :
    forIn (#[(0, target)] : Array (Nat × Ixon.Inductive)) (#[], #[]) (ctorClassStep cx owner mr target.params.toNat) =
      .ok ((ctorReads ctorKey 0 target.ctors.toList types).toArray,
        #[(ctorReads ctorKey 0 target.ctors.toList types).map (·.1.name)]) := by
  simp only [List.forIn_toArray, List.forIn_cons, List.forIn_nil, ctorClassStep]
  rw [← Array.forIn_toList, Array.toList_zipIdx,
    ctorLoop_ok cx owner mr target.params.toNat ctorKey target.ctors.toList 0 types (#[], []) facts]
  simp [bind, Except.bind, pure, Except.pure]

/-- **The reader on a standalone inductive block**: indexed at member 0,
safe, its key and type reading, and its constructor loop's checks passing,
the record reads as `lowerInductive` of the block's types, its
constructors, and the recursors its own loop reads. -/
theorem readRecord_singleton (cx : Ctx md) (st : State md) (owner : Address) (c : Ixon.Constant)
    (target : Ixon.Inductive) (info : c.info = .muts #[.indc target]) {shape : BlockShape}
    (indexed : cx.index.blocks[owner]? = some shape) (order : shape.order = #[0]) (safe : target.isUnsafe = false)
    {key : CName md} (keyed : cx.memberKey (.member owner 0) = .ok key) {type : CExpr md}
    (typeRead : (MemberReader.mk' cx c id (blockSelf cx owner #[.indc target])).read target.typ = .ok type)
    (ctorKey : Nat → CName md) (ctorTypes : List (CExpr md))
    (ctors : CtorFacts cx owner (MemberReader.mk' cx c id (blockSelf cx owner #[.indc target]))
      target.params.toNat ctorKey 0 target.ctors.toList ctorTypes) :
    readRecord cx st owner c =
      readRecursors cx (List.range target.lvls.toNat) shape.recs >>= fun recs =>
        lowerInductive st ⟨target.params.toNat,
          #[(⟨key, List.range target.lvls.toNat, type⟩, target.params.toNat, target.indices.toNat)],
          (ctorReads ctorKey 0 target.ctors.toList ctorTypes).toArray,
          #[(ctorReads ctorKey 0 target.ctors.toList ctorTypes).map (·.1.name)], recs⟩ := by
  rw [readRecord_inductive cx st owner c target info, readInductive_eq]
  unfold readInductiveSpec
  rw [indexed]
  dsimp only
  rw [order, indcs_singleton]
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, beq_self_eq_true,
    Bool.false_eq_true, ↓reduceIte, List.getElem?_toArray, List.getElem?_cons_zero,
    List.any_toArray', List.all_toArray', List.any_cons, List.any_nil, List.all_cons, List.all_nil, safe,
    Bool.or_false, Bool.and_true]
  rw [typeLoop cx owner _ target keyed typeRead, ctorClassLoop cx owner _ target ctorKey ctorTypes ctors]
  rfl

/-! ## What the compiled family keeps of the source -/

/-- The reader's self map of a one-member block. -/
def inductiveSelf (cx : Ctx md) (owner : Address) : Nat → Option (ReadM (CName md)) :=
  fun i => if i < 1 then some (cx.memberKey (.member owner i)) else none

theorem blockSelf_singleton (cx : Ctx md) (state : BlockState) (owner : Address) (member : Ixon.MutConst) :
    blockSelf (ExpressionRead.withBlockBlobs cx state) owner #[member] = inductiveSelf cx owner := rfl

/-- A write-back of a one-inductive block keeps everything but its roots. -/
theorem erase_singleton {info : Ixon.ConstantInfo} {payload : Ixon.Inductive}
    (same : SharingRoots.erase info = SharingRoots.erase (.muts #[.indc payload])) :
    ∃ target : Ixon.Inductive, info = .muts #[.indc target] ∧ target.isUnsafe = payload.isUnsafe ∧
      target.lvls = payload.lvls ∧ target.params = payload.params ∧ target.indices = payload.indices ∧
      target.ctors.toList.map (fun ctor => { ctor with typ := Ixon.Expr.sort 0 }) =
        payload.ctors.toList.map (fun ctor => { ctor with typ := Ixon.Expr.sort 0 }) := by
  cases info with
  | muts members =>
    rcases members with ⟨list⟩
    rcases list with _ | ⟨member, _ | ⟨next, rest⟩⟩
    · simp [SharingRoots.erase, Ix.Sharing.Exact.mapRoots] at same
    · cases member with
      | indc target =>
        simp [SharingRoots.erase, Ix.Sharing.Exact.mapRoots, Ix.Sharing.Exact.mapMutConstRoots] at same
        refine ⟨target, rfl, same.1, same.2.1, same.2.2.1, same.2.2.2.1, ?_⟩
        simpa using congrArg Array.toList same.2.2.2.2
      | defn _ | recr _ =>
        simp [SharingRoots.erase, Ix.Sharing.Exact.mapRoots, Ix.Sharing.Exact.mapMutConstRoots] at same
    · simp [SharingRoots.erase, Ix.Sharing.Exact.mapRoots] at same
  | _ => simp [SharingRoots.erase, Ix.Sharing.Exact.mapRoots] at same

theorem headers_transfer : ∀ {sources : List ConstructorVal} {payloads targets : List Ixon.Constructor},
    List.Forall₂ ProjectionLayout.CtorHeader sources payloads →
    targets.map (fun ctor => { ctor with typ := Ixon.Expr.sort 0 }) =
      payloads.map (fun ctor => { ctor with typ := Ixon.Expr.sort 0 }) →
    List.Forall₂ ProjectionLayout.CtorHeader sources targets := by
  intro sources payloads targets headers same
  induction headers generalizing targets with
  | nil =>
    cases targets with
    | nil => exact .nil
    | cons _ _ => simp at same
  | cons header _ ih =>
    cases targets with
    | nil => simp at same
    | cons target targets =>
      simp only [List.map_cons, List.cons.injEq] at same
      obtain ⟨first, rest⟩ := same
      simp only [Ixon.Constructor.mk.injEq] at first
      refine .cons ?_ (ih rest)
      obtain ⟨_, lvls, cidx, params, fields, _⟩ := first
      unfold ProjectionLayout.CtorHeader at header ⊢
      rw [lvls, cidx, params, fields]
      exact header

/-- **The compiled family's headers**: one inductive whose header and every
constructor's header are the source's, as natural numbers. -/
theorem family_headers (source : InductiveVal) (constructors : Array ConstructorVal) :
    Emission.Yields (compileInductiveFamilyBlock source constructors) (fun output =>
      ∃ target, output.block.info = .muts #[.indc target] ∧
        ProjectionLayout.IndHeader (Emission.sourceData source constructors) target ∧
        List.Forall₂ ProjectionLayout.CtorHeader constructors.toList target.ctors.toList) := by
  intro context before output after ran
  unfold compileInductiveFamilyBlock at ran
  obtain ⟨payload, middle, compiled, finished⟩ := bind_ok ran
  rw [Emission.compileInductive_eq] at compiled
  obtain ⟨header, ctorHeaders, _⟩ :=
    ProjectionLayout.inductiveData_headers (Emission.sourceData source constructors) context before payload middle
      compiled
  obtain ⟨ind, indMeta, pairs, exprs⟩ := payload
  dsimp only at finished header ctorHeaders
  obtain ⟨_, built, _⟩ := EmissionBlocks.familyFinish_ok source ind indMeta pairs finished
  obtain ⟨erased, _, _, _⟩ := SharingRoots.build_roots (md := .anon) _ _ _ _ _ built
  obtain ⟨target, info, _, lvls, params, indices, ctors⟩ := erase_singleton erased
  refine ⟨target, info, ?_, headers_transfer ctorHeaders ctors⟩
  obtain ⟨headerLvls, headerParams, headerIndices, headerCtors⟩ := header
  have sizes : target.ctors.size = ind.ctors.size := by
    simpa using congrArg List.length ctors
  exact ⟨lvls ▸ headerLvls, params ▸ headerParams, indices ▸ headerIndices, sizes ▸ headerCtors⟩

theorem familyInfo_headers (source : InductiveVal) (constructors : Array ConstructorVal) :
    Emission.Yields (compileInductiveFamilyInfo source constructors) (fun output =>
      ∃ target, output.block.info = .muts #[.indc target] ∧
        ProjectionLayout.IndHeader (Emission.sourceData source constructors) target ∧
        List.Forall₂ ProjectionLayout.CtorHeader constructors.toList target.ctors.toList) := by
  unfold compileInductiveFamilyInfo
  exact Emission.Yields.bindAny _ fun _ => family_headers source constructors

/-- The family's skeleton fixes its safety and its constructors'. -/
theorem erase_family {info : Ixon.ConstantInfo} {source : InductiveVal} {constructors : Array ConstructorVal}
    (same : SharingRoots.erase info =
      SharingRoots.erase (EmissionBlocks.inductiveSkeleton (Emission.sourceData source constructors))) :
    ∃ target : Ixon.Inductive, info = .muts #[.indc target] ∧ target.isUnsafe = source.isUnsafe ∧
      List.Forall₂ (fun ctor (t : Ixon.Constructor) => t.isUnsafe = ctor.isUnsafe)
        constructors.toList target.ctors.toList := by
  obtain ⟨target, info, unsafeEq, _, _, _, ctors⟩ := erase_singleton same
  refine ⟨target, info, by simpa [Emission.inductivePayload, Emission.sourceData] using unsafeEq, ?_⟩
  have list : target.ctors.toList.map (fun ctor => { ctor with typ := Ixon.Expr.sort 0 }) =
      constructors.toList.map (fun ctor => Emission.constructorPayload ctor (.sort 0)) := by
    rw [ctors]
    simp [Emission.inductivePayload, Emission.constructorPayload, Emission.sourceData, Function.comp_def]
  clear ctors
  generalize constructors.toList = sources at list
  generalize target.ctors.toList = targets at list
  induction sources generalizing targets with
  | nil =>
    cases targets with
    | nil => exact .nil
    | cons _ _ => simp at list
  | cons source rest ih =>
    cases targets with
    | nil => simp at list
    | cons target targets =>
      simp only [List.map_cons, List.cons.injEq] at list
      refine .cons ?_ (ih targets list.2)
      have first := congrArg Ixon.Constructor.isUnsafe list.1
      simpa [Emission.constructorPayload] using first

/-! ## Constructor telescopes -/

theorem piTeleLen_of_piTypes : ∀ (count : Nat) (target : CExpr md) (types : List (CExpr md)) (residual : CExpr md),
    ReaderSourceSpines.piTypes count target = some (types, residual) → ReaderSourceSpines.KernelNonForall residual →
    piTeleLen target = count := by
  intro count
  induction count with
  | zero =>
    intro target types residual stripped last
    rw [ReaderSourceSpines.piTypes_zero] at stripped
    cases stripped
    cases target <;> simp_all [piTeleLen, ReaderSourceSpines.KernelNonForall]
  | succ count ih =>
    intro target types residual stripped last
    cases target with
    | forallE type body binder =>
      rw [ReaderSourceSpines.piTypes_forall] at stripped
      cases inner : ReaderSourceSpines.piTypes count body with
      | none => rw [inner] at stripped; cases stripped
      | some result =>
        rcases result with ⟨rest, final⟩
        rw [inner] at stripped
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at stripped
        obtain ⟨_, rfl⟩ := stripped
        simp only [piTeleLen, ih body rest final inner last]
    | _ => simp [ReaderSourceSpines.piTypes, Ix.Kernel.Expr.stripPis] at stripped

/-- A reading related to a source telescope of `count` binders, ending in a
non-binder, has exactly `count` binders. -/
theorem arity_of_related {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop}
    {source : Ix.Expr} {target : CExpr md} (related : Related names levels source target) {count : Nat}
    {types : List Ix.Expr} {body : Ix.Expr} (strip : ReaderSourceSpines.sourceStrip count source = some (types, body))
    (last : ReaderSourceSpines.SourceNonForall body) : piTeleLen target = count := by
  obtain ⟨targetTypes, residual, stripped, _, bodyRel⟩ :=
    ReaderSourceSpines.related_strip count related types body strip
  exact piTeleLen_of_piTypes count target targetTypes residual stripped
    (ReaderSourceSpines.related_kernelNonForall bodyRel last)

theorem rootsRead_split {reader : MemberReader md} {related : Ix.Expr → CExpr md → Prop} :
    ∀ {sources : List Ix.Expr} {roots : List Ixon.Expr}, SharingRoots.RootsRead reader related sources roots →
      ∃ targets, List.Forall₂ related sources targets ∧
        List.Forall₂ (fun root target => reader.read root = .ok target) roots targets := by
  intro sources roots holds
  induction holds with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons head _ ih =>
    obtain ⟨target, rel, read⟩ := head
    obtain ⟨targets, rels, reads⟩ := ih
    exact ⟨target :: targets, .cons rel rels, .cons read reads⟩

/-- The constructor loop's facts from the compiled family's: headers,
safety, readings, keys, positions and telescopes. -/
theorem ctorFacts_of (cx : Ctx md) (owner : Address) (mr : MemberReader md) (nPd : Nat) (ctorKey : Nat → CName md)
    {names : Ix.Name → CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} :
    ∀ (sources : List ConstructorVal) (targets : List Ixon.Constructor) (types : List (CExpr md)) (j : Nat),
      List.Forall₂ ProjectionLayout.CtorHeader sources targets →
      List.Forall₂ (fun ctor (t : Ixon.Constructor) => t.isUnsafe = ctor.isUnsafe) sources targets →
      List.Forall₂ (fun (t : Ixon.Constructor) type => mr.read t.typ = .ok type) targets types →
      List.Forall₂ (Related names levels) (sources.map (·.cnst.type)) types →
      (∀ k (h : k < sources.length), sources[k].cidx = j + k) →
      (∀ k, k < sources.length → cx.memberKey (.ctor owner 0 (j + k)) = .ok (ctorKey (j + k))) →
      (∀ ctor ∈ sources, ctor.isUnsafe = false) →
      (∀ ctor ∈ sources, ∃ types body,
        ReaderSourceSpines.sourceStrip (nPd + ctor.numFields) ctor.cnst.type = some (types, body) ∧
          ReaderSourceSpines.SourceNonForall body) →
      CtorFacts cx owner mr nPd ctorKey j targets types := by
  intro sources
  induction sources with
  | nil =>
    intro targets types j headers _ reads _ _ _ _ _
    cases headers
    cases reads
    trivial
  | cons source rest ih =>
    intro targets types j headers unsafes reads rels positions keys safe arity
    cases targets with
    | nil => cases headers
    | cons target targets =>
      cases types with
      | nil => cases reads
      | cons type types =>
        rw [List.forall₂_cons] at headers unsafes reads
        simp only [List.map_cons, List.forall₂_cons] at rels
        refine ⟨?_, ?_, ?_, reads.1, ?_, ih targets types (j + 1) headers.2 unsafes.2 reads.2 rels.2 ?_ ?_ ?_ ?_⟩
        · rw [headers.1.2.1]
          exact positions 0 (by simp)
        · rw [unsafes.1]
          exact safe source (by simp)
        · simpa using keys 0 (by simp)
        · rw [headers.1.2.2.2]
          obtain ⟨sourceTypes, body, strip, last⟩ := arity source (by simp)
          exact (arity_of_related rels.1 strip last).symm
        · intro k inside
          have shifted := positions (k + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at shifted
          rw [shifted]
          omega
        · intro k inside
          have shifted := keys (k + 1) (by simp; omega)
          rw [show j + 1 + k = j + (k + 1) by omega]
          exact shifted
        · intro ctor present
          exact safe ctor (by simp [present])
        · intro ctor present
          exact arity ctor (by simp [present])

/-- What the reader reads of the source's constructors, from position `j`. -/
def sourceCtorReads (ctorKey : Nat → CName md) : Nat → List ConstructorVal → List (CExpr md) →
    List (CVal md × Nat × Nat)
  | j, ctor :: ctors, type :: types =>
    (⟨ctorKey j, List.range ctor.cnst.levelParams.size, type⟩, ctor.numParams, ctor.numFields) ::
      sourceCtorReads ctorKey (j + 1) ctors types
  | _, _, _ => []

theorem ctorReads_source (ctorKey : Nat → CName md) :
    ∀ {sources : List ConstructorVal} {targets : List Ixon.Constructor} (j : Nat) (types : List (CExpr md)),
      List.Forall₂ ProjectionLayout.CtorHeader sources targets →
      ctorReads ctorKey j targets types = sourceCtorReads ctorKey j sources types := by
  intro sources targets j types headers
  induction headers generalizing j types with
  | nil => cases types <;> rfl
  | cons header _ ih =>
    cases types with
    | nil => rfl
    | cons type types =>
      obtain ⟨lvls, _, params, fields⟩ := header
      simp only [ctorReads, sourceCtorReads, lvls, params, fields, ih]

/-- **The `BlockRead` a standalone inductive's source describes**: the
inductive under its key, with the level parameters `0, …, n - 1`, its type
reading and its counts; its constructors in source order under their keys,
with their level parameters, type readings and counts; and the recursors. -/
def sourceBlock (key : CName md) (ctorKey : Nat → CName md) (type : CExpr md) (ctorTypes : List (CExpr md))
    (source : InductiveVal) (constructors : Array ConstructorVal)
    (recs : Array (CVal md × RecCounts × List (Ix.Kernel.RecRule md))) : BlockRead md :=
  ⟨source.numParams,
    #[(⟨key, List.range source.cnst.levelParams.size, type⟩, source.numParams, source.numIndices)],
    (sourceCtorReads ctorKey 0 constructors.toList ctorTypes).toArray,
    #[(sourceCtorReads ctorKey 0 constructors.toList ctorTypes).map (·.1.name)], recs⟩

theorem forall₂_map_left {f : α → β} {R : β → γ → Prop} :
    ∀ {l : List α} {l' : List γ}, List.Forall₂ R (l.map f) l' → List.Forall₂ (fun a c => R (f a) c) l l' := by
  intro l
  induction l with
  | nil => intro l' h; cases h; exact .nil
  | cons a l ih => intro l' h; cases h with | cons head tail => exact .cons head (ih tail)

theorem rootsRead_cons {reader : MemberReader md} {related : Ix.Expr → CExpr md → Prop} {source : Ix.Expr}
    {sources : List Ix.Expr} {root : Ixon.Expr} {roots : List Ixon.Expr}
    (holds : SharingRoots.RootsRead reader related (source :: sources) (root :: roots)) :
    (∃ target, related source target ∧ reader.read root = .ok target) ∧
      SharingRoots.RootsRead reader related sources roots :=
  List.forall₂_cons.mp holds

/-! ## No constructor of the family occurs (N-READS, N4)

The reader reads a standalone family's types with only the inductive as its
self (`inductiveSelf`), so a constructor of the family occurring in them
would not read. `NoCtorIn` says none occurs; with the family's own name
related to its key (R13's half), it gives `inductive_reads`' self-reference
condition (`scope_of_noCtor`). -/

/-- No constructor of the family occurs as a constant of `e`. -/
def NoCtorIn (constructors : Array ConstructorVal) : Ix.Expr → Prop :=
  ConstsSatisfy fun name => ∀ ctor ∈ constructors.toList, name ≠ ctor.cnst.name

/-- `NoCtorIn` as a check (names compared structurally). -/
def noCtorIn (constructors : Array ConstructorVal) : Ix.Expr → Bool
  | .const name _ _ => constructors.all fun ctor => Ix.nameCompareExact name ctor.cnst.name != .eq
  | .app f a _ => noCtorIn constructors f && noCtorIn constructors a
  | .lam _ t b _ _ | .forallE _ t b _ _ => noCtorIn constructors t && noCtorIn constructors b
  | .letE _ t v b _ _ => noCtorIn constructors t && noCtorIn constructors v && noCtorIn constructors b
  | .proj _ _ e _ => noCtorIn constructors e
  | .mdata _ e _ => noCtorIn constructors e
  | _ => true

theorem noCtorIn_iff (constructors : Array ConstructorVal) :
    ∀ e, noCtorIn constructors e = true ↔ NoCtorIn constructors e := by
  intro e
  induction e with
  | const name _ _ =>
    show (constructors.all fun ctor => Ix.nameCompareExact name ctor.cnst.name != .eq) = true ↔
      ∀ ctor ∈ constructors.toList, name ≠ ctor.cnst.name
    rw [Array.all_eq_true_iff_forall_mem]
    constructor
    · intro absent ctor present same
      have h := absent ctor (Array.mem_toList_iff.1 present)
      rw [same, Std.ReflCmp.compare_self (cmp := Ix.nameCompareExact)] at h
      exact absurd h (by decide)
    · intro absent ctor present
      apply bne_iff_ne.2
      intro same
      exact absent ctor (Array.mem_toList_iff.2 present) (Std.LawfulEqCmp.eq_of_compare same)
  | app f a _ ihf iha =>
    simp only [noCtorIn, NoCtorIn, ConstsSatisfy, Bool.and_eq_true] at ihf iha ⊢
    rw [ihf, iha]
  | lam _ t b _ _ iht ihb =>
    simp only [noCtorIn, NoCtorIn, ConstsSatisfy, Bool.and_eq_true] at iht ihb ⊢
    rw [iht, ihb]
  | forallE _ t b _ _ iht ihb =>
    simp only [noCtorIn, NoCtorIn, ConstsSatisfy, Bool.and_eq_true] at iht ihb ⊢
    rw [iht, ihb]
  | letE _ t v b _ _ iht ihv ihb =>
    simp only [noCtorIn, NoCtorIn, ConstsSatisfy, Bool.and_eq_true] at iht ihv ihb ⊢
    rw [iht, ihv, ihb, and_assoc]
  | proj _ _ e _ ih => simpa only [noCtorIn, NoCtorIn, ConstsSatisfy] using ih
  | mdata _ e _ ih => simpa only [noCtorIn, NoCtorIn, ConstsSatisfy] using ih
  | _ => simp [noCtorIn, NoCtorIn, ConstsSatisfy]

/-- A name the family's mutual context maps, other than a constructor's, is
the inductive's, at slot 0. -/
theorem familyCtx_lookup (source : InductiveVal) (constructors : Array ConstructorVal) {query : Ix.Name}
    {index : Nat} (absent : ∀ ctor ∈ constructors.toList, query ≠ ctor.cnst.name)
    (found : (buildInductiveMutCtx source constructors).get? query = some index) :
    query = source.cnst.name ∧ index = 0 := by
  have step : ∀ (entries : List (ConstructorVal × Nat)) (ctx : Ix.MutCtx),
      (∀ entry ∈ entries, query ≠ entry.1.cnst.name) →
      (entries.foldl (fun ctx entry => ctx.insert entry.1.cnst.name (entry.2 + 1)) ctx).get? query =
        ctx.get? query := by
    intro entries
    induction entries with
    | nil => intro ctx _; rfl
    | cons entry rest ih =>
      intro ctx outside
      rw [List.foldl_cons, ih _ (fun e present => outside e (List.mem_cons_of_mem _ present))]
      rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
      have different : Ix.nameCompareExact entry.1.cnst.name query ≠ .eq := by
        intro same
        exact outside entry List.mem_cons_self (Std.LawfulEqCmp.eq_of_compare same).symm
      simp only [different, ↓reduceIte]
  have unfolded : buildInductiveMutCtx source constructors =
      constructors.zipIdx.foldl (fun ctx entry => ctx.insert entry.1.cnst.name (entry.2 + 1))
        ((Std.TreeMap.empty : Ix.MutCtx).insert source.cnst.name 0) := by
    simp [buildInductiveMutCtx]
  rw [unfolded, ← Array.foldl_toList, step _ _ (fun entry present => by
    rw [Array.mem_toList_iff] at present
    have member : entry.1 ∈ constructors := by
      have mapped := Array.mem_map_of_mem (f := Prod.fst) present
      rwa [Array.zipIdx_map_fst] at mapped
    exact absent entry.1 (Array.mem_toList_iff.2 member))] at found
  exact DefinitionReading.singleton_lookup source.cnst.name query index found |>.imp
    Std.LawfulEqCmp.eq_of_compare id

/-! ## Compiled inductives read back -/

section Reading

variable (cx : Ctx md) (names : Ix.Name → CName md → Prop) (σ : Ix.Name → LevelParam) (bindings : Bindings)

/-- The source relation of an inductive's terms: levels mean its own level
parameters, read positionally. -/
abbrev related (source : InductiveVal) : Ix.Expr → CExpr md → Prop :=
  Related names (LevelMeaning source.cnst.levelParams.toList σ id)

/-- The block environment the family compile installs: the inductive at
slot 0, its constructors after it (`buildInductiveMutCtx`). -/
abbrev familyBlock (source : InductiveVal) (constructors : Array ConstructorVal)
    (context : CompileEnv × BlockEnv) : BlockEnv :=
  (EmissionDispatch.familyContext source constructors (EmissionDispatch.singletonContext source.cnst.name context)).2

/-- **The self references are in scope** when no constructor of the family
occurs (`NoCtorIn`) and the family's own name is related to its key (R13's
half): the only other name the family's mutual context maps is the
inductive's, at the slot `inductiveSelf` reads as the key
(`familyCtx_lookup`). -/
theorem scope_of_noCtor (source : InductiveVal) (constructors : Array ConstructorVal)
    (context : CompileEnv × BlockEnv) (owner : Address) {key : CName md}
    (keyed : cx.memberKey (.member owner 0) = .ok key) (selfKey : names source.cnst.name key)
    {e : Ix.Expr} (noCtor : NoCtorIn constructors e) :
    ConstsSatisfy (SelfName (familyBlock source constructors context) (inductiveSelf cx owner) names) e :=
  constsSatisfy_mono (fun _ absent index found => by
      obtain ⟨rfl, rfl⟩ := familyCtx_lookup source constructors absent found
      exact ⟨key, by simp [inductiveSelf, keyed], selfKey⟩) e noCtor

/-- **A compiled standalone inductive is read back as its source**: public
dispatch of an inductive, under an environment without call-site plans,
from a clean state whose tables are on the wire, returns a block that decodes
exactly, whose projections are the family's layout, and that `readRecord`
(over the block's blobs overlaid on the context's) reads as `lowerInductive`
of the `BlockRead` the source describes (`sourceBlock`): its type and its
constructors' types are readings related to the sources', and its
recursors are what the reader's own loop reads from their records
(`readRecursors`). Given: the constructors the dispatch resolves; the
index shaping the block at member 0 (`inductive_reads_indexed` derives it
from the reader's index); the keys reading; the self references: the
family's own name related to its key (`selfKey`, R13's half) and no
constructor of the family occurring in the types (`NoCtorIn`; N-READS N4:
proved from Source acceptance once IxC's modeled route checks constructor
types before the block's constructors exist, until then tested); and a
well-formed source (safe, constructors at their positions, each constructor's type a
telescope of the parameters and its fields). -/
theorem inductive_reads (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : InductiveVal)
    (constructors : Array ConstructorVal) {before after : BlockState} {output : BlockResult}
    (found : (rawRun (lookupInductiveConstructors source)
      (EmissionDispatch.singletonContext source.cnst.name context) before).1 = .ok constructors)
    (state : State md) {shape : BlockShape} (indexed : cx.index.blocks[output.blockAddr]? = some shape)
    (order : shape.order = #[0]) {key : CName md} (keyed : cx.memberKey (.member output.blockAddr 0) = .ok key)
    (ctorKey : Nat → CName md)
    (ctorKeyed : ∀ j, j < constructors.size → cx.memberKey (.ctor output.blockAddr 0 j) = .ok (ctorKey j))
    (selfKey : names source.cnst.name key) (typeNoCtor : NoCtorIn constructors source.cnst.type)
    (ctorNoCtor : ∀ ctor ∈ constructors.toList, NoCtorIn constructors ctor.cnst.type)
    (safe : source.isUnsafe = false) (ctorSafe : ∀ ctor ∈ constructors.toList, ctor.isUnsafe = false)
    (positions : ∀ j (inside : j < constructors.size), constructors[j].cidx = j)
    (arity : ∀ ctor ∈ constructors.toList, ∃ types body,
      ReaderSourceSpines.sourceStrip (source.numParams + ctor.numFields) ctor.cnst.type = some (types, body) ∧
        ReaderSourceSpines.SourceNonForall body)
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after)) :
    BlockResultCodecWF output ∧ ProjectionLayout.InductiveLayout source constructors output ∧
      ∃ type ctorTypes, related names σ source source.cnst.type type ∧
        List.Forall₂ (related names σ source) (constructors.toList.map (·.cnst.type)) ctorTypes ∧
        readRecord (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block =
          readRecursors (ExpressionRead.withBlockBlobs cx after) (List.range source.cnst.levelParams.size)
              shape.recs >>= fun recs =>
            lowerInductive state (sourceBlock key ctorKey type ctorTypes source constructors recs) := by
  have codec := EmissionDispatch.constant_codec context free _ wire ran
  have sameCtors : ∀ other, rawRun (lookupInductiveConstructors source)
      (EmissionDispatch.singletonContext source.cnst.name context) before = (.ok other, before) →
      other = constructors := by
    intro other run
    rw [run] at found
    exact Except.ok.inj found
  obtain ⟨layoutCtors, layoutLookup, layout⟩ := ProjectionLayout.dispatch_layout context free source ran
  cases sameCtors layoutCtors layoutLookup
  rw [EmissionDispatch.inductive_run context free] at ran
  obtain ⟨familyCtors, familyLookup, compiled⟩ :=
    EmissionDispatch.family_run (EmissionDispatch.singletonContext source.cnst.name context) free source ran
  cases sameCtors familyCtors familyLookup
  obtain ⟨_, _, _, erased, roots⟩ := EmissionBlocks.familyInfo_correct cx id (inductiveSelf cx output.blockAddr)
    names σ bindings
    (EmissionDispatch.familyContext source constructors (EmissionDispatch.singletonContext source.cnst.name context))
    free aligned external source constructors
    (scope_of_noCtor cx names source constructors context output.blockAddr keyed selfKey typeNoCtor)
    (fun ctor present => scope_of_noCtor cx names source constructors context output.blockAddr keyed selfKey
      (ctorNoCtor ctor present)) clean compiled
  obtain ⟨target, info, indHeader, ctorHeaders⟩ :=
    familyInfo_headers source constructors _ before output after compiled
  obtain ⟨target', info', unsafeEq, ctorUnsafe⟩ := erase_family erased
  rw [info] at info'
  cases info'
  rw [info, EmissionBlocks.family_roots] at roots
  obtain ⟨⟨type, typeRel, typeRead⟩, ctorRoots⟩ := rootsRead_cons roots
  obtain ⟨ctorTypes, ctorRels, ctorReadList⟩ := rootsRead_split ctorRoots
  obtain ⟨lvls, params, indices, _⟩ := indHeader
  simp only [Emission.sourceData] at lvls params indices
  have selfEq : blockSelf (ExpressionRead.withBlockBlobs cx after) output.blockAddr #[Ixon.MutConst.indc target] =
      inductiveSelf cx output.blockAddr := blockSelf_singleton cx after output.blockAddr _
  have typeRead' : (MemberReader.mk' (ExpressionRead.withBlockBlobs cx after) output.block id
      (blockSelf (ExpressionRead.withBlockBlobs cx after) output.blockAddr #[.indc target])).read target.typ =
        .ok type := by
    rw [selfEq]
    exact typeRead
  have readsMapped : List.Forall₂ (fun (ctor : Ixon.Constructor) ctorType =>
      (MemberReader.mk' (ExpressionRead.withBlockBlobs cx after) output.block id
        (blockSelf (ExpressionRead.withBlockBlobs cx after) output.blockAddr #[.indc target])).read ctor.typ =
          .ok ctorType) target.ctors.toList ctorTypes := by
    rw [selfEq]
    exact forall₂_map_left ctorReadList
  have facts := ctorFacts_of (ExpressionRead.withBlockBlobs cx after) output.blockAddr
    (MemberReader.mk' (ExpressionRead.withBlockBlobs cx after) output.block id
      (blockSelf (ExpressionRead.withBlockBlobs cx after) output.blockAddr #[.indc target]))
    target.params.toNat ctorKey constructors.toList target.ctors.toList ctorTypes 0 ctorHeaders ctorUnsafe
    readsMapped ctorRels
    (fun k inside => by simpa using positions k (by simpa using inside))
    (fun k inside => by rw [Nat.zero_add]; exact ctorKeyed k (by simpa using inside)) ctorSafe
    (fun ctor present => by rw [params]; exact arity ctor present)
  have read := readRecord_singleton (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block
    target info indexed order (unsafeEq.trans safe) keyed typeRead' ctorKey ctorTypes facts
  refine ⟨codec, layout, type, ctorTypes, typeRel, ctorRels, ?_⟩
  rw [read, lvls, params, indices, ctorReads_source ctorKey 0 ctorTypes ctorHeaders]
  unfold sourceBlock
  rfl

/-- **`inductive_reads` over the reader's own index**: in a context whose
index is the reader's (`buildIndex`) over a store holding the block, the
block's shape is at member 0 by `ReaderIndex.compiled_order`. -/
theorem inductive_reads_indexed (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : InductiveVal)
    (constructors : Array ConstructorVal) {before after : BlockState} {output : BlockResult}
    (found : (rawRun (lookupInductiveConstructors source)
      (EmissionDispatch.singletonContext source.cnst.name context) before).1 = .ok constructors)
    (state : State md) (records : Array (Address × Ixon.Constant)) (indexBuilt : cx.index = buildIndex cx.store records)
    (stored : cx.store output.blockAddr = some output.block)
    {shape : BlockShape} (indexed : cx.index.blocks[output.blockAddr]? = some shape)
    {key : CName md} (keyed : cx.memberKey (.member output.blockAddr 0) = .ok key)
    (ctorKey : Nat → CName md)
    (ctorKeyed : ∀ j, j < constructors.size → cx.memberKey (.ctor output.blockAddr 0 j) = .ok (ctorKey j))
    (selfKey : names source.cnst.name key) (typeNoCtor : NoCtorIn constructors source.cnst.type)
    (ctorNoCtor : ∀ ctor ∈ constructors.toList, NoCtorIn constructors ctor.cnst.type)
    (safe : source.isUnsafe = false) (ctorSafe : ∀ ctor ∈ constructors.toList, ctor.isUnsafe = false)
    (positions : ∀ j (inside : j < constructors.size), constructors[j].cidx = j)
    (arity : ∀ ctor ∈ constructors.toList, ∃ types body,
      ReaderSourceSpines.sourceStrip (source.numParams + ctor.numFields) ctor.cnst.type = some (types, body) ∧
        ReaderSourceSpines.SourceNonForall body)
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after)) :
    BlockResultCodecWF output ∧ ProjectionLayout.InductiveLayout source constructors output ∧
      ∃ type ctorTypes, related names σ source source.cnst.type type ∧
        List.Forall₂ (related names σ source) (constructors.toList.map (·.cnst.type)) ctorTypes ∧
        readRecord (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block =
          readRecursors (ExpressionRead.withBlockBlobs cx after) (List.range source.cnst.levelParams.size)
              shape.recs >>= fun recs =>
            lowerInductive state (sourceBlock key ctorKey type ctorTypes source constructors recs) := by
  have order := ReaderIndex.compiled_order context free source ran cx.store records shape stored
    (indexBuilt ▸ indexed)
  exact inductive_reads cx names σ bindings context free aligned external source constructors found state indexed
    order keyed ctorKey ctorKeyed selfKey typeNoCtor ctorNoCtor safe ctorSafe positions arity clean wire ran

/-- **A compiled inductive with no recursor in the input declines.** -/
theorem inductive_declines_unindexed (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (source : InductiveVal) {before after : BlockState} {output : BlockResult} (state : State md)
    (unindexed : cx.index.blocks[output.blockAddr]? = none)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after)) :
    readRecord (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block =
      .error (.declined "inductive block without a recursor in the input") := by
  obtain ⟨_, _, target, _, _, info, _⟩ := ProjectionLayout.dispatch_layout context free source ran
  rw [readRecord_inductive _ state output.blockAddr output.block target info, readInductive_eq]
  unfold readInductiveSpec
  rw [show (ExpressionRead.withBlockBlobs cx after).index.blocks[output.blockAddr]? = none from unindexed]
  rfl

end Reading

end Ix.CompileCert.InductiveReading
