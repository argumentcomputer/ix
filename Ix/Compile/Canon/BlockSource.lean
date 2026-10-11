module
public import Ix.Compile.Canon.BlockData
public section

/-! The retained finite-source implementation. These complete original bodies
provide explicit comparison functions, not a representation of arbitrary callbacks. -/
namespace Ix.Compile.Canon.SourceBlock
open Ix (Name Level Expr ConstantInfo MutConst ConstructorVal)

/-- The finite canonical expansion used by the retained source implementation. -/
def canonExpand (rules : Rules) (env : SourceEnv) (classes : Array (Array Name)) :
    Except String Expanded :=
  expandSourceSpec env.source rules.dedup (classes.filterMap (·[0]?)) (aliasesOf classes) env.groupOf
    (if rules.nested == .discovery then some env.addr? else none)

/-- The members of `all` as today's sorter sees them. -/
def mutConstOf (env : SourceEnv) (n : Name) : Except String MutConst :=
  match env.const? n with
  | some (.inductInfo v) => do
    let ctors ← v.ctors.mapM fun c =>
      match env.const? c with
      | some (.ctorInfo cv) => pure cv
      | _ => throw s!"expected constructor {namePretty c}"
    pure (MutConst.fromInductiveVal v ctors)
  | some (.defnInfo v) => pure (MutConst.fromDefinitionVal v)
  | some (.thmInfo v) => pure (MutConst.fromTheoremVal v)
  | some (.opaqueInfo v) => pure (MutConst.fromOpaqueVal v)
  | some (.recInfo v) => pure (.recr v)
  | _ => throw s!"no constant {namePretty n}"

/-- The components of a block: members and constructors under the reference
graph, each component's members in `all` order. -/
def blockComponents (env : SourceEnv) (all : Array Name) : Except String (Array (Array Name)) := do
  let mut nodes : Array Name := #[]
  for n in all do
    nodes := nodes.push n
    match env.const? n with
    | some (.inductInfo v) => nodes := nodes ++ v.ctors
    | _ => pure ()
  let refs := fun n => match env.const? n with
    | some c => refsConst c
    | none => {}
  let some comps := sccsOf nodes refs | throw "component computation ran out of fuel"
  let allSet : Std.HashSet Name := all.foldl (·.insert ·) {}
  let comps := comps.filterMap fun c =>
    let ms := all.filter fun n => c.contains n && allSet.contains n
    if ms.isEmpty then none else some ms
  -- deterministic: by first member's position in `all`
  let pos := fun (c : Array Name) => ((c[0]?).bind all.idxOf?).getD 0
  return comps.qsort (fun a b => pos a < pos b)

/-- Nested data of one component, before evaporation. -/
def componentNested (rules : Rules) (env : SourceEnv) (all : Array Name)
    (classes : Array (Array Name)) : Except String (Option NestedCanon) := do
  let reps := classes.filterMap (·[0]?)
  if reps.isEmpty then return none
  let metaNested := all.any fun n => match env.const? n with
    | some (.inductInfo v) => v.numNested > 0
    | _ => false
  let x ← expandSourceSpec env.source rules.dedup reps (aliasesOf classes) env.groupOf
    (if rules.nested == .discovery then some env.addr? else none)
  let structNested := x.types.size > x.nOriginals
  if !metaNested && !structNested then return none
  let (order, addrDecided) ←
    if metaNested && structNested then canonicalAuxOrder rules env.addr? x
    else pure (x.aux.map fun m => #[m.name], false)
  let canon ← sigsInOrder x order
  let src ← expandSourceSpec env.source rules.dedup all
  let source := src.sigs
  let perm ← computePerm env.addr? canon source all (origToCanonOf classes)
  return some { source, canonClasses := order, canon, perm,
                evaporated := Array.replicate perm.size false, addrDecided }

/-- Evaporation (`generateAuxPatches`, the evaporated-alias pass): see
`Nested.lean`. `comps` are all components of the block with their classes. -/
def evaporate (env : SourceEnv) (rules : Rules) (all : Array Name)
    (comps : Array (Array (Array Name))) (here : Nat) (n : NestedCanon) :
    Except String NestedCanon := do
  if !n.perm.contains none then return n
  let some all0 := all[0]? | return n
  let some hereComp := comps[here]? | throw s!"evaporate: component {here} out of range"
  let inHere : Std.HashSet Name := hereComp.foldl (fun s c => c.foldl (·.insert ·) s) {}
  let originals : Std.HashSet Name := all.foldl (·.insert ·) {}
  let mut flags := n.evaporated
  for (p, j) in n.perm.zipIdx do
    if p.isSome then continue
    let some s := n.source[j]? | continue
    if !inHere.contains s.owner then continue
    if (env.const? (Name.mkStr all0 s!"rec_{j + 1}")).isNone then continue
    -- members the occurrence mentions (constants and projection names)
    let refs := s.specs.foldl (init := ({} : Std.HashSet Name)) fun acc e =>
      (constsIn originals e).fold (·.insert ·) acc
    let mut claimed := false
    if !refs.isEmpty then
      for (cls, ci) in comps.zipIdx do
        if ci == here then continue
        let compMembers : Std.HashSet Name := cls.foldl (fun s c => c.foldl (·.insert ·) s) {}
        if !refs.toList.any compMembers.contains then continue
        let reps := cls.filterMap (·[0]?)
        let x ← expandSourceSpec env.source rules.dedup reps (aliasesOf cls) env.groupOf
          (if rules.nested == .discovery then some env.addr? else none)
        let o2c := origToCanonOf cls
        let strict : Std.HashSet Name := all.foldl (init := {}) fun st m =>
          if compMembers.contains m then st else st.insert m
        let specs := s.specs.map (replaceConstNames o2c)
        if (matchSig env.addr? strict x.sigs s.head s.levels specs).isSome then
          claimed := true
    if claimed then continue
    let targetOk := match env.const? (Name.mkStr s.head "rec") with
      | some (.recInfo r) => r.numMotives == 1
      | _ => false
    if targetOk then flags := flags.set! j true
  return { n with evaporated := flags }

/-- The canonical form of the Lean block `all`. -/
def canonBlock (rules : Rules) (env : SourceEnv) (all : Array Name) : Except String BlockCanon := do
  let comps ← blockComponents env all
  let mut out : Array ComponentCanon := #[]
  for members in comps do
    let cs ← members.toList.mapM (mutConstOf env)
    let (classes, stats) ← sortClasses rules env.addr? cs
    let blind ← sortClassesBlind rules cs
    out := out.push { members, classes := classNames classes,
                      blindClasses := classNames blind, stats, nested := none }
  let classesAll := out.map (·.classes)
  let mut out' : Array ComponentCanon := #[]
  for (c, i) in out.zipIdx do
    let nested ← componentNested rules env all c.classes
    let nested ← nested.mapM (evaporate env rules all classesAll i)
    out' := out'.push { c with nested }
  return { all, components := out' }

end Ix.Compile.Canon.SourceBlock

end
