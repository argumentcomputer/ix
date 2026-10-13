import Ix.CompileCert.InductiveBlock
import Ix.CompileCert.RecursorBlock

/-! Proof-visible stages of the actual anonymous inductive-family reader.
These definitions are connected to `readInductive` without changing kernel
code. They expose its type, constructor and recursor loops for composition
with source-related compiler outputs. -/

namespace Ix.CompileCert.FamilyReader

open Ix Kernel.Reader
open _root_.Ix.Kernel (ConstRef)

abbrev CtorRow := CVal × Nat × Nat
abbrev RecRow := CVal × Ixon.Recursor × List Kernel.RecRule

def readTypes (cx : Ctx) (owner : Address) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (indcs : Array (Nat × Ixon.Inductive)) :
    ReadM (Array CVal × Array (Nat × Ixon.Inductive)) := do
  let mut types : Array CVal := #[]
  let mut tyRecs : Array (Nat × Ixon.Inductive) := #[]
  for (i, ind) in indcs do
    types := types.push ⟨cx.nameOf (.member owner i), lpsAt ind.lvls, ← member.read ind.typ⟩
    tyRecs := tyRecs.push (i, ind)
  pure (types, tyRecs)

def readConstructors (cx : Ctx) (owner : Address) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (nPd : Nat) (indcs : Array (Nat × Ixon.Inductive)) :
    ReadM (Array CtorRow × Array (List Kernel.Name)) := do
  let mut ctors : Array CtorRow := #[]
  let mut ctorNames : Array (List Kernel.Name) := #[]
  for (i, ind) in indcs do
    let mut names : List Kernel.Name := []
    for (ctor, j) in ind.ctors.zipIdx do
      unless ctor.cidx.toNat == j do malformed "constructor index differs from its position"
      if ctor.isUnsafe then declined "unsafe inductive declaration"
      let cv : CVal := ⟨cx.nameOf (.ctor owner i j), lpsAt ctor.lvls, ← member.read ctor.typ⟩
      unless nPd + ctor.fields.toNat == piTeleLen cv.type do
        malformed s!"constructor {cv.name} declares {ctor.fields} fields at {nPd} parameters; \
          its type has {piTeleLen cv.type} binders"
      ctors := ctors.push (cv, ctor.params.toNat, ctor.fields.toNat)
      names := names ++ [cv.name]
    ctorNames := ctorNames.push names
  pure (ctors, ctorNames)

def recursorSelf (cx : Ctx) (owner : Address) (constant : Ixon.Constant) (entry : RecEntry) :
    Nat → Option Kernel.Name := fun i => match constant.info with
  | .muts members => if i < members.size then some (cx.nameOf (.member owner i)) else none
  | _ => if i == 0 then some entry.name else none

def readRules (cx : Ctx) (member : MemberReader) (block : Address) (index : Nat)
    (sources : Array Ixon.RecursorRule) : ReadM (List Kernel.RecRule) := do
  let mut rules : List Kernel.RecRule := []
  for (rule, k) in sources.zipIdx do
    rules := rules ++ [Kernel.RecRule.mk (cx.nameOf (.ctor block index k)) rule.fields.toNat 0 .inert
      (← member.read rule.rhs) false false false]
  pure rules

def recursorAction (cx : Ctx) (blockLps : List Kernel.Name) (ref : ConstRef Address)
    (next : RecRow → ReadM α) : ReadM α := do
  let some entry := cx.index.recs[ref]? | malformed "unindexed recursor"
  let .member rOwner j := ref | malformed "recursor reference is a constructor"
  let some rc := cx.store rOwner | malformed "recursor record is missing"
  let some (_, r) := (recursorMembers rc).find? (·.1 == j) | malformed "recursor member is missing"
  if r.isUnsafe then declined "unsafe inductive declaration"
  let lps := cx.recLps ref entry.large r.lvls.toNat blockLps
  let mr := MemberReader.mk' cx rc (paramOf lps) (recursorSelf cx rOwner rc entry)
  let cv : CVal := ⟨entry.name, lps, ← mr.read r.typ⟩
  let some major := inductiveAt cx.store entry.major
    | declined s!"recursor {entry.name}: its major premise is not an inductive"
  unless major.ctors.size == r.rules.size do
    malformed s!"recursor {entry.name} has {r.rules.size} rules for {major.ctors.size} constructors"
  let .member mb mi := entry.major | malformed "recursor major is a constructor"
  let rules ← readRules cx mr mb mi r.rules
  next (cv, r, rules)

def readRecursor (cx : Ctx) (blockLps : List Kernel.Name) (ref : ConstRef Address) : ReadM RecRow :=
  recursorAction cx blockLps ref pure

def readRecursors (cx : Ctx) (blockLps : List Kernel.Name) (refs : Array (ConstRef Address)) :
    ReadM (Array RecRow) :=
  forIn refs #[] fun ref recs => recursorAction cx blockLps ref fun row => pure (.yield (recs.push row))

def finish (st : State) (nPd : Nat) (types : Array CVal)
    (tyRecs : Array (Nat × Ixon.Inductive)) (ctors : Array CtorRow)
    (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow) : ReadM Read := do
  let nTypes := types.size
  let nCtors := ctors.size
  let numNested := match recs[0]? with
    | some (_, r, _) => r.motives.toNat - nTypes
    | none => 0
  let nested := numNested != 0
  let kExpected? : Option Bool :=
    match types.toList, ctorNames.toList, ctors.toList with
    | [ty], [[_]], [(_, _, nF)] =>
      match ty.type.piResult with
      | .sort s => some (nF == 0 && Kernel.Level.isEquiv s .zero == some true)
      | _ => none
    | _, _, _ => some false
  unless nested do
    for (cv, r, _) in recs do
      unless r.params.toNat == nPd do
        malformed s!"recursor {cv.name} declares {r.params} parameters; the block declares {nPd}"
      unless r.motives.toNat == nTypes do
        malformed s!"recursor {cv.name} declares {r.motives} motives; the block has {nTypes} types"
      unless r.minors.toNat == nCtors do
        malformed s!"recursor {cv.name} declares {r.minors} minor premises; the block has {nCtors} constructors"
      if let some kE := kExpected? then
        unless r.k == kE do
          malformed s!"recursor {cv.name} declares k := {r.k}; the generated recursor is{if kE then "" else " not"} K-like"
      if let .str T "rec" := cv.name then
        for ty in types do
          if ty.name == T then
            if let some n := ty.type.piSortTeleLen? then
              unless nPd + r.indices.toNat == n do
                malformed s!"recursor {cv.name} declares {r.indices} indices; {T} has {n - nPd}"
  let typeInfos : List CInfo := types.toList.map (.indInfo · {})
  let ctorInfos : List CInfo := ctors.toList.map fun (cv, nP, nF) => .ctorInfo cv nP nF
  let recInfos : List CInfo := recs.toList.map fun (cv, r, rules) =>
    let nP := r.params.toNat; let nM := r.motives.toNat
    let nm := r.minors.toNat; let nI := r.indices.toNat
    .recInfo cv (nP + nM + nm + nI) (nP + nM + nm) rules
  let block := typeInfos ++ ctorInfos ++ recInfos
  let memberNames := types.toList.map (·.name)
  let fieldDoms := ctors.toList.flatMap fun (cv, _, _) =>
    (Kernel.Frontend.stripPisAll cv.type).1.map (·.1)
  let isRec := fieldDoms.any fun d => memberNames.any (Kernel.Frontend.occursConstFast · d)
  let isReflexive := fieldDoms.any fun d =>
    let (bs, body) := Kernel.Frontend.stripPisAll d
    !bs.isEmpty && memberNames.any (Kernel.Frontend.headIs · body)
  let ownerTypes := (types.zip tyRecs).toList.zip ctorNames.toList |>.map fun ((cv, (_, ind)), cs) =>
    (cv.name, cv.levelParams, cv.type, ind.params.toNat, ind.indices.toNat, cs, isRec)
  let ownerCtors := ctors.toList.map fun (cv, _, nF) => (cv.name, nF, cv.type)
  let ownerRecs := recs.toList.map fun (cv, r, _) =>
    (cv.name, cv.levelParams, cv.type, r.motives.toNat, r.minors.toNat)
  let owners := Kernel.Frontend.projRecOwners block ownerTypes ownerCtors ownerRecs
  let b : Kernel.Frontend.InModel.BlockRec :=
    ⟨(types.zip tyRecs).toList.zip ctorNames.toList |>.map fun ((cv, (_, ind)), cs) =>
        { cv, nP := ind.params.toNat, nIdx := ind.indices.toNat, ctors := cs, isRec,
          isReflexive, numNested },
     ctors.toList.map fun (cv, nP, nF) => { cv, nP, nF },
     recs.toList.map fun (cv, r, rules) =>
       { cv, nP := r.params.toNat, nM := r.motives.toNat, nm := r.minors.toNat,
         nI := r.indices.toNat, rules }⟩
  let blocks := b.types.map (·.cv.name, b)
  let decl := Kernel.Declaration.indDecl block nPd
  if Kernel.Frontend.InModel.wants b then
    let ctx : Kernel.Frontend.InModel.Ctx :=
      ⟨fun n => st.constTypes[n]?, fun n => st.heights.getD n 0,
       fun n => if memberNames.contains n then some b else st.indBlocks[n]?⟩
    match Kernel.Frontend.InModel.generate ctx b with
    | .error why => declined s!"in-process model of {(types[0]?.map (·.name)).getD .anonymous}: {why}"
    | .ok gen => pure { decls := gen.toArray.push decl, generated := gen.length, owners, blocks }
  else
    pure { decls := #[decl], owners, blocks }

def run (cx : Ctx) (st : State) (owner : Address) (c : Ixon.Constant)
    (ms : Array Ixon.MutConst) : ReadM Read := do
  let some shape := cx.index.blocks[owner]?
    | declined "inductive block without a recursor in the input"
  let self : Nat → Option Kernel.Name := fun i =>
    if i < ms.size then some (cx.nameOf (.member owner i)) else none
  let indcs : Array (Nat × Ixon.Inductive) :=
    shape.order.filterMap fun i => match (ms[i]? : Option Ixon.MutConst) with
      | some (.indc ind) => some (i, ind)
      | _ => none
  unless indcs.size == shape.order.size do malformed "recursor motive is not a member of its block"
  let some (_, first) := indcs[0]? | malformed "empty inductive block"
  if indcs.any (·.2.isUnsafe) then declined "unsafe inductive declaration"
  let nPd := first.params.toNat
  unless indcs.all (·.2.params.toNat == nPd) do
    declined "inductive block whose type records disagree on numParams"
  let blockLps := cx.lpsOf (.member owner (indcs[0]!.1)) first.lvls.toNat
  let mrInd := MemberReader.mk' cx c (paramOf blockLps) self
  let lpsAt (lvls : UInt64) : List Kernel.Name :=
    if lvls == first.lvls then blockLps else levelNames lvls.toNat
  let (types, tyRecs) ← readTypes cx owner mrInd lpsAt indcs
  let (ctors, ctorNames) ← readConstructors cx owner mrInd lpsAt nPd indcs
  let recs ← readRecursors cx blockLps shape.recs
  finish st nPd types tyRecs ctors ctorNames recs

theorem run_eq (cx : Ctx) (st : State) (owner : Address) (c : Ixon.Constant)
    (ms : Array Ixon.MutConst) : run cx st owner c ms = readInductive cx st owner c ms := by
  simp only [run, readTypes, readConstructors, readRecursors, recursorAction, readRules, finish, readInductive,
    bind_assoc, pure_bind]
  rfl

end Ix.CompileCert.FamilyReader
