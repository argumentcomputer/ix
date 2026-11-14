module

public import Ix.IxVM.PwHints
public import Ix.RoleBinding.Publication
public import Ix.CompileM

public section

/-!
# The compiler's binder data (the Ixon v5 section)

Every record carries the binder data of its `lam` and `all` nodes
(`Ixon.Constant.binders`): the zero-ness of each binder's codomain sort, as
IxC's annotation pass writes it (`BinderMeta.pw`). The record's address hashes
them with the rest of its bytes. `apply` computes them for a compiled
environment and re-addresses it:

1. **Annotate** every record of the environment, under its own role table and
   the prelude read from its own records (the compiled records are not the
   committed prelude's: the committed prelude is a compile of these records with
   their data). The annotator is IxC's pass over the Ixon tree
   (`IxVM.PwHints.annotateKernel`), in tainting mode: where IxC's datum function
   cannot run and the record's declared type does not give the datum, the node
   is `undecided` (wire tag 4), and so is every binder above it. A datum is
   never guessed.
2. **Write the sections** in the canonical form (`Ixon.Constant.bindersCanonical`):
   the numbered nodes are the `lam` and `all` nodes and the `share` nodes whose
   entry has a binder, in pre-order; one block per root with a numbered node
   (variant 0), one per sharing entry and variant a numbered share names; a
   sharing entry's variants are its distinct node lists in order of first
   occurrence; blocks sorted by `(shared, index, variant)`.
3. **Re-address bottom-up**: a record's data depend on the types of what it
   references, not on their addresses, so the data are computed once, at the old
   addresses. In an order with every record after the records its refs table
   (and a projection's block) names, each record's refs are replaced by their
   new addresses, its section is set, and it is hashed.
4. **Rewrite** everything keyed by a record address: the names (`named`,
   `original`, `addrToName`), the reducibility hints, the role binding (its
   bound roles and proof evidence; its address is the hash of its new bytes),
   `main` and the assumptions.
-/

namespace Ix.Compile.BinderData

open IxVM.PwHints

/-! ## Sections -/

/-- The annotator's numbering of `e`'s numbered nodes (every `lam`, `all` and
`share` in pre-order, a `share` not entered), appended to `out`: `none` at a
binder, `some n` at a share of entry `n`. -/
def kinds (out : Array (Option Nat)) : Ixon.Expr → Array (Option Nat)
  | .lam t b => kinds (kinds (out.push none) t) b
  | .all t b => kinds (kinds (out.push none) t) b
  | .app f a => kinds (kinds out f) a
  | .letE _ _ t v b => kinds (kinds (kinds out t) v) b
  | .prj _ _ v => kinds out v
  | .share n => out.push (some n.toNat)
  | _ => out

/-- The parameters of an `ifAllZero` datum, ascending and without repeats. -/
def canonicalParams (ps : Array Nat) : Array UInt64 :=
  let sorted := ps.qsort (· < ·)
  (sorted.foldl (fun out p => if out.back? == some p then out else out.push p) #[]).map
    (·.toUInt64)

/-- A node in the section's spelling, carrying `mode`. "Always zero" is `.zero`. -/
def nodeOfMode (mode : Ixon.AllMode) : Node → Ixon.BinderNode
  | .binder none => .never mode
  | .binder (some ps) =>
    let params := canonicalParams ps
    if params.isEmpty then .zero mode else .ifAllZero params mode
  | .share v => .share v.toUInt64
  | .undecided => .undecided mode

/-- A node in the section's spelling with the default mode. -/
def nodeOf : Node → Ixon.BinderNode := nodeOfMode {}

/-- Whether `c.binders` gives any binder a mode other than the default. -/
def hasBinderModes (c : Ixon.Constant) : Bool :=
  c.binders.any (·.nodes.any fun node => (node.mode?.getD {}) != {})

/-- Whether `e` has any `letE` node with a non-default `LetMode`. -/
def exprHasLetModes : Ixon.Expr → Bool
  | .lam t b | .all t b | .app t b => exprHasLetModes t || exprHasLetModes b
  | .letE _ m t v b =>
    m != .value .many || exprHasLetModes t || exprHasLetModes v || exprHasLetModes b
  | .prj _ _ v => exprHasLetModes v
  | _ => false

/-- Whether `c` carries any non-default mode across all four mode places:
binder `AllMode`s in `c.binders`, `LetMode`s on `letE`, constructor
`fieldModes`, or definition `asserts`. -/
def hasModes (c : Ixon.Constant) : Bool :=
  hasBinderModes c ||
  c.sharing.any exprHasLetModes ||
  c.info.binderRoots.any exprHasLetModes ||
  match c.info with
  | .defn d => d.asserts != {}
  | .muts ms => ms.any fun
    | .defn d => d.asserts != {}
    | .indc ind => ind.ctors.any (!·.fieldModes.isInherited)
    | .recr _ => false
  | _ => false

private structure CombineSt where
  variants : Array (Array (Array Ixon.BinderNode))
  memo : Std.HashMap (Nat × Nat × Nat) Nat := {}

private def combineNodes (full : Array Bool) (sharing : Array Ixon.Expr)
    (modeMap : Std.HashMap (Bool × Nat × Nat) (Array Ixon.BinderNode))
    (pwMap : Std.HashMap (Bool × Nat × Nat) (Array Node)) :
    Nat → Array (Option Nat) → Array Ixon.BinderNode → Array Node →
    StateT CombineSt (Except String) (Array Ixon.BinderNode)
  | 0, _, _, _ => throw "binder data: sharing depth exceeded"
  | fuel + 1, shape, mNodes, pNodes => do
    unless shape.size == mNodes.size && shape.size == pNodes.size do
      throw "binder data: mode and datum block sizes differ"
    let mut out : Array Ixon.BinderNode := #[]
    for h : i in [:shape.size] do
      let k := shape[i]
      let some mNode := mNodes[i]? | throw "binder data: missing mode node"
      let some pNode := pNodes[i]? | throw "binder data: missing datum node"
      match k, mNode, pNode with
      | none, .share _, _ => throw "binder data: a share mode node at a binder"
      | none, _, .share _ => throw "binder data: a share datum at a binder"
      | none, mNode, pNode =>
        out := out.push (nodeOfMode (mNode.mode?.getD {}) pNode)
      | some subIdx, .share subMVar, .share subPVar =>
        let key := (subIdx, subMVar.toNat, subPVar)
        let v ← match (← get).memo[key]? with
          | some hit => pure hit
          | none => do
            let some entry := sharing[subIdx]?
              | throw s!"binder data: missing sharing entry {subIdx}"
            let some subMNodes := modeMap[(true, subIdx, subMVar.toNat)]?
              | throw s!"binder data: missing mode variant ({subIdx}, {subMVar})"
            let some subPNodes := pwMap[(true, subIdx, subPVar)]?
              | throw s!"binder data: missing datum variant ({subIdx}, {subPVar})"
            let subOut ← combineNodes full sharing modeMap pwMap fuel
              (entry.numberedNodes full #[]) subMNodes subPNodes
            let st ← get
            let cur := st.variants[subIdx]?.getD #[]
            let v := match cur.findIdx? (· == subOut) with
              | some existing => existing
              | none => cur.size
            let cur' := if v < cur.size then cur else cur.push subOut
            set ({ variants := st.variants.set! subIdx cur', memo := st.memo.insert key v } : CombineSt)
            pure v
        out := out.push (.share v.toUInt64)
      | some _, _, _ => throw "binder data: a binder node at a share"
    return out

/-- The section of record `c` from the annotator's blocks: the share nodes of
entries without a binder dropped, the blocks of those entries and the roots
without a numbered node left out, the rest sorted. When `c.binders` already
carries non-default `AllMode`s, those modes are preserved positionally and
sharing variants are deduplicated over whole `(datum, mode)` node lists. -/
def sectionOf (c : Ixon.Constant) (blocks : Array Block) : Except String (Array Ixon.BinderBlock) := do
  let full := binderful c.sharing
  let rs := roots c
  if !hasBinderModes c then
    let mut out : Array Ixon.BinderBlock := #[]
    for b in blocks do
      let shared := b.ekind == 1
      if shared && !(full[b.eidx]?.getD false) then continue
      let some tree := (if shared then c.sharing[b.eidx]? else rs[b.eidx]?)
        | throw s!"binder data: no expression ({b.ekind}, {b.eidx})"
      let ks := kinds #[] tree
      unless ks.size == b.nodes.size do
        throw s!"binder data: expression ({b.ekind}, {b.eidx}) has {ks.size} numbered nodes, \
          the annotator {b.nodes.size}"
      let mut nodes : Array Ixon.BinderNode := #[]
      for (node, k) in b.nodes.zip ks do
        match k, node with
        | none, .share _ => throw s!"binder data: a share datum at a binder of ({b.ekind}, {b.eidx})"
        | some _, .binder _ | some _, .undecided =>
          throw s!"binder data: a binder datum at a share of ({b.ekind}, {b.eidx})"
        | none, _ => nodes := nodes.push (nodeOf node)
        | some n, _ => if full[n]?.getD false then nodes := nodes.push (nodeOf node)
      if nodes.isEmpty then continue
      out := out.push { shared, index := b.eidx.toUInt64, variant := b.variant.toUInt64, nodes }
    return out.qsort (fun x y => x.keyLt y)
  else
    let mut pwMap : Std.HashMap (Bool × Nat × Nat) (Array Node) := {}
    for b in blocks do
      let shared := b.ekind == 1
      if shared && !(full[b.eidx]?.getD false) then continue
      let some tree := (if shared then c.sharing[b.eidx]? else rs[b.eidx]?)
        | throw s!"binder data: no expression ({b.ekind}, {b.eidx})"
      let ks := kinds #[] tree
      unless ks.size == b.nodes.size do
        throw s!"binder data: expression ({b.ekind}, {b.eidx}) has {ks.size} numbered nodes, \
          the annotator {b.nodes.size}"
      let mut kept : Array Node := #[]
      for (node, k) in b.nodes.zip ks do
        match k, node with
        | none, .share _ => throw s!"binder data: a share datum at a binder of ({b.ekind}, {b.eidx})"
        | some _, .binder _ | some _, .undecided =>
          throw s!"binder data: a binder datum at a share of ({b.ekind}, {b.eidx})"
        | none, _ => kept := kept.push node
        | some n, _ => if full[n]?.getD false then kept := kept.push node
      if kept.isEmpty then continue
      pwMap := pwMap.insert (shared, b.eidx, b.variant) kept
    let modeMap : Std.HashMap (Bool × Nat × Nat) (Array Ixon.BinderNode) :=
      c.binders.foldl (fun m b => m.insert (b.shared, b.index.toNat, b.variant.toNat) b.nodes) {}
    let initSt : CombineSt := { variants := Array.replicate c.sharing.size #[] }
    let act : StateT CombineSt (Except String) (Array Ixon.BinderBlock) := do
      let mut rootBlocks : Array Ixon.BinderBlock := #[]
      for h : r in [:rs.size] do
        let shape := rs[r].numberedNodes full #[]
        if shape.isEmpty then continue
        let some mNodes := modeMap[(false, r, 0)]?
          | throw s!"binder data: missing mode block for root {r}"
        let some pNodes := pwMap[(false, r, 0)]?
          | throw s!"binder data: missing datum block for root {r}"
        let nodes ← combineNodes full c.sharing modeMap pwMap (c.sharing.size + 2) shape mNodes pNodes
        rootBlocks := rootBlocks.push { shared := false, index := r.toUInt64, variant := 0, nodes }
      let st ← get
      let mut out := rootBlocks
      for h : n in [:st.variants.size] do
        let vs := st.variants[n]
        for hv : v in [:vs.size] do
          out := out.push { shared := true, index := n.toUInt64, variant := v.toUInt64, nodes := vs[v] }
      return out.qsort (fun x y => x.keyLt y)
    let (out, _) ← act.run initSt
    return out

private structure StripSt where
  variants : Array (Array (Array Ixon.BinderNode))
  memo : Std.HashMap (Nat × Nat) Nat := {}

private def stripNodes (full : Array Bool) (sharing : Array Ixon.Expr)
    (modeMap : Std.HashMap (Bool × Nat × Nat) (Array Ixon.BinderNode)) :
    Nat → Array (Option Nat) → Array Ixon.BinderNode →
    StateT StripSt (Except String) (Array Ixon.BinderNode)
  | 0, _, _ => throw "binder data: sharing depth exceeded"
  | fuel + 1, shape, mNodes => do
    unless shape.size == mNodes.size do
      throw "binder data: block size differs from expression"
    let mut out : Array Ixon.BinderNode := #[]
    for (k, mNode) in shape.zip mNodes do
      match k, mNode with
      | none, .share _ => throw "binder data: a share node at a binder"
      | none, mNode => out := out.push (.undecided (mNode.mode?.getD {}))
      | some subIdx, .share subMVar =>
        let key := (subIdx, subMVar.toNat)
        let v ← match (← get).memo[key]? with
          | some hit => pure hit
          | none => do
            let some entry := sharing[subIdx]?
              | throw s!"binder data: missing sharing entry {subIdx}"
            let some subMNodes := modeMap[(true, subIdx, subMVar.toNat)]?
              | throw s!"binder data: missing variant ({subIdx}, {subMVar})"
            let subOut ← stripNodes full sharing modeMap fuel
              (entry.numberedNodes full #[]) subMNodes
            let st ← get
            let cur := st.variants[subIdx]?.getD #[]
            let v := match cur.findIdx? (· == subOut) with
              | some existing => existing
              | none => cur.size
            let cur' := if v < cur.size then cur else cur.push subOut
            set ({ variants := st.variants.set! subIdx cur', memo := st.memo.insert key v } : StripSt)
            pure v
        out := out.push (.share v.toUInt64)
      | some _, _ => throw "binder data: a binder node at a share"
    return out

/-- The undecided (`0x04`) section of `c`, preserving any non-default `AllMode`s
already in `c.binders` and re-deduplicating sharing variants by whole node lists. -/
def stripSection (c : Ixon.Constant) : Except String (Array Ixon.BinderBlock) := do
  if !hasBinderModes c then
    return Ix.CompileM.undecidedSection c
  let full := Ixon.binderfulEntries c.sharing
  let rs := c.info.binderRoots
  let modeMap : Std.HashMap (Bool × Nat × Nat) (Array Ixon.BinderNode) :=
    c.binders.foldl (fun m b => m.insert (b.shared, b.index.toNat, b.variant.toNat) b.nodes) {}
  let initSt : StripSt := { variants := Array.replicate c.sharing.size #[] }
  let act : StateT StripSt (Except String) (Array Ixon.BinderBlock) := do
    let mut rootBlocks : Array Ixon.BinderBlock := #[]
    for h : r in [:rs.size] do
      let shape := rs[r].numberedNodes full #[]
      if shape.isEmpty then continue
      let some mNodes := modeMap[(false, r, 0)]?
        | throw s!"binder data: missing block for root {r}"
      let nodes ← stripNodes full c.sharing modeMap (c.sharing.size + 2) shape mNodes
      rootBlocks := rootBlocks.push { shared := false, index := r.toUInt64, variant := 0, nodes }
    let st ← get
    let mut out := rootBlocks
    for h : n in [:st.variants.size] do
      let vs := st.variants[n]
      for hv : v in [:vs.size] do
        out := out.push { shared := true, index := n.toUInt64, variant := v.toUInt64, nodes := vs[v] }
    return out.qsort (fun x y => x.keyLt y)
  let (out, _) ← act.run initSt
  return out

/-! ## Source modes onto undecided sections -/

/-- Peel metadata frames around a source expression, keeping the outermost
semantic contract frame (if any) and the underlying expression. -/
def peelSource : Ix.Expr → Option Ix.SemanticContract.Contract × Ix.Expr
  | .mdata d inner _ =>
    if Ix.SemanticContract.hasMetadata d then
      let c? := (Ix.SemanticContract.read d).toOption
      let (innerC?, core) := peelSource inner
      (c?.orElse (fun _ => innerC?), core)
    else
      peelSource inner
  | e => (none, e)

/-- The result modes of a type's leading `forallE` telescope, in binder order. -/
def leadingAllResults : Ix.Expr → Option Ix.SemanticContract.Contract → List Ixon.ResultMode
  | .mdata d inner _, outer? =>
    if Ix.SemanticContract.hasMetadata d then
      leadingAllResults inner ((Ix.SemanticContract.read d).toOption.orElse fun _ => outer?)
    else
      leadingAllResults inner outer?
  | .forallE _ _ body _ _, c? =>
    let r := match c? >>= (·.toAllMode?) with
      | some m => m.result
      | none => .shared
    r :: leadingAllResults body none
  | _, _ => []

private def exprHasContractM (e : Ix.Expr) :
    StateM (Std.HashSet Ix.Compile.ExactKey.ExprKey) Bool := do
  let key : Ix.Compile.ExactKey.ExprKey := ⟨e⟩
  if (← get).contains key then return false
  modify (·.insert key)
  match e with
  | .app f a _ =>
    let hf ← exprHasContractM f
    if hf then return true
    exprHasContractM a
  | .lam _ t b _ _ | .forallE _ t b _ _ =>
    let ht ← exprHasContractM t
    if ht then return true
    exprHasContractM b
  | .letE _ t v b _ _ =>
    let ht ← exprHasContractM t
    if ht then return true
    let hv ← exprHasContractM v
    if hv then return true
    exprHasContractM b
  | .proj _ _ v _ => exprHasContractM v
  | .mdata d inner _ =>
    if Ix.SemanticContract.hasMetadata d then return true
    else exprHasContractM inner
  | _ => return false

private structure MemberRoot where
  expr : Ix.Expr
  teleResults : List Ixon.ResultMode
  isTheorem : Bool

private def memberSourceRoots (find : Ix.Name → Option Ix.ConstantInfo) (ci : Ix.ConstantInfo) :
    Ixon.MutConst ⊕ Ixon.ConstantInfo → Option (Array MemberRoot)
  | .inl (.defn _) | .inr (.defn _) =>
    match ci with
    | .defnInfo d =>
      some #[⟨d.cnst.type, [], false⟩,
             ⟨d.value, leadingAllResults d.cnst.type none, false⟩]
    | .thmInfo t =>
      some #[⟨t.cnst.type, [], true⟩, ⟨t.value, [], true⟩]
    | .opaqueInfo o =>
      some #[⟨o.cnst.type, [], false⟩,
             ⟨o.value, leadingAllResults o.cnst.type none, false⟩]
    | _ => none
  | .inr (.axio _) =>
    match ci with
    | .axiomInfo a => some #[⟨a.cnst.type, [], false⟩]
    | _ => none
  | .inr (.quot _) =>
    match ci with
    | .quotInfo q => some #[⟨q.cnst.type, [], false⟩]
    | _ => none
  | .inl (.recr r) | .inr (.recr r) =>
    match ci with
    | .recInfo v =>
      if v.rules.size == r.rules.size then
        some (#[⟨v.cnst.type, [], false⟩] ++ v.rules.map fun rule => ⟨rule.rhs, [], false⟩)
      else none
    | _ => none
  | .inl (.indc i) =>
    match ci with
    | .inductInfo v => do
      let ctors ← v.ctors.mapM fun n =>
        match find n with
        | some (.ctorInfo k) => some (⟨k.cnst.type, [], false⟩ : MemberRoot)
        | _ => none
      guard (ctors.size == i.ctors.size)
      some (#[⟨v.cnst.type, [], false⟩] ++ ctors)
    | _ => none
  | _ => none

private structure SourceModeSt where
  variants : Array (Array (Array Ixon.BinderNode))
  memo : Std.HashMap (Nat × List Ixon.ResultMode × Ix.Compile.ExactKey.ExprKey) Nat := {}

private def walkModeExpr (full : Array Bool) (sharing : Array Ixon.Expr) :
    Nat → Ixon.Expr → Ix.Expr → List Ixon.ResultMode → Bool → Array Ixon.BinderNode →
    StateT SourceModeSt Option (Array Ixon.BinderNode)
  | 0, _, _, _, _, _ => failure
  | fuel + 1, .share n, src, tele, isThm, out => do
    let idx := n.toNat
    if !(full[idx]?.getD false) then return out
    let key := (idx, tele, (⟨src⟩ : Ix.Compile.ExactKey.ExprKey))
    let v ← match (← get).memo[key]? with
      | some hit => pure hit
      | none => do
        let entry ← sharing[idx]?
        let subNodes ← walkModeExpr full sharing fuel entry src tele isThm #[]
        let st ← get
        let cur := st.variants[idx]?.getD #[]
        let v := match cur.findIdx? (· == subNodes) with
          | some existing => existing
          | none => cur.size
        let cur' := if v < cur.size then cur else cur.push subNodes
        set ({ variants := st.variants.set! idx cur', memo := st.memo.insert key v } : SourceModeSt)
        pure v
    return out.push (.share v.toUInt64)
  | fuel + 1, .lam ixTy ixBody, src, tele, isThm, out => do
    let (c?, core) := peelSource src
    let .lam _ srcTy srcBody _ _ := core | failure
    let base : Ixon.AllMode := if isThm then {} else (c? >>= (·.toAllMode?)).getD {}
    let (m, nextTele) := match tele with
      | r :: rest =>
        ({ base with
           result := if isThm then .shared else if base.result == .shared then r else base.result },
         rest)
      | [] => (base, [])
    let out := out.push (.undecided m)
    let out ← walkModeExpr full sharing (fuel + 1) ixTy srcTy [] isThm out
    walkModeExpr full sharing (fuel + 1) ixBody srcBody nextTele isThm out
  | fuel + 1, .all ixTy ixBody, src, _, isThm, out => do
    let (c?, core) := peelSource src
    let .forallE _ srcTy srcBody _ _ := core | failure
    let m : Ixon.AllMode := if isThm then {} else (c? >>= (·.toAllMode?)).getD {}
    let out := out.push (.undecided m)
    let out ← walkModeExpr full sharing (fuel + 1) ixTy srcTy [] isThm out
    walkModeExpr full sharing (fuel + 1) ixBody srcBody [] isThm out
  | fuel + 1, .app ixFn ixArg, src, _, isThm, out => do
    let (_, core) := peelSource src
    let .app srcFn srcArg _ := core | failure
    let out ← walkModeExpr full sharing (fuel + 1) ixFn srcFn [] isThm out
    walkModeExpr full sharing (fuel + 1) ixArg srcArg [] isThm out
  | fuel + 1, .letE _ _ ixTy ixVal ixBody, src, _, isThm, out => do
    let (_, core) := peelSource src
    let .letE _ srcTy srcVal srcBody _ _ := core | failure
    let out ← walkModeExpr full sharing (fuel + 1) ixTy srcTy [] isThm out
    let out ← walkModeExpr full sharing (fuel + 1) ixVal srcVal [] isThm out
    walkModeExpr full sharing (fuel + 1) ixBody srcBody [] isThm out
  | fuel + 1, .prj _ _ ixVal, src, _, isThm, out => do
    let (_, core) := peelSource src
    let .proj _ _ srcVal _ := core | failure
    walkModeExpr full sharing (fuel + 1) ixVal srcVal [] isThm out
  | _ + 1, _, _, _, _, out => return out
termination_by fuel ix => (fuel, sizeOf ix)

/-- Extract source `AllMode`s onto an undecided (`0x04`) binder-data section for
block record `c` from its member sources `names`, deduplicating sharing-entry
variants by whole `BinderNode` lists. Falls back to `undecidedSection c` when no
member carries `ix.contract` metadata. -/
def sourceModeSection (find : Ix.Name → Option Ix.ConstantInfo) (names : Array Ix.Name)
    (c : Ixon.Constant) : Array Ixon.BinderBlock := Id.run do
  let rs := c.info.binderRoots
  if rs.isEmpty then return #[]
  let ms : Array (Ixon.MutConst ⊕ Ixon.ConstantInfo) := match c.info with
    | .muts ms => ms.map .inl
    | info => #[.inr info]
  if ms.size != names.size then return Ix.CompileM.undecidedSection c
  let mut srcRoots : Array MemberRoot := #[]
  for (m, n) in ms.zip names do
    let some ci := find n | return Ix.CompileM.undecidedSection c
    let some items := memberSourceRoots find ci m | return Ix.CompileM.undecidedSection c
    srcRoots := srcRoots ++ items
  if srcRoots.size != rs.size then return Ix.CompileM.undecidedSection c
  let mut seen : Std.HashSet Ix.Compile.ExactKey.ExprKey := {}
  let mut hasAny := false
  for sr in srcRoots do
    if !sr.isTheorem && !hasAny then
      let (found, seen') := (exprHasContractM sr.expr).run seen
      seen := seen'
      if found then hasAny := true
  if !hasAny then return Ix.CompileM.undecidedSection c
  let full := Ixon.binderfulEntries c.sharing
  let initSt : SourceModeSt := { variants := Array.replicate c.sharing.size #[] }
  let act : StateT SourceModeSt Option (Array Ixon.BinderBlock) := do
    let mut rootBlocks : Array Ixon.BinderBlock := #[]
    for h : r in [:rs.size] do
      let shape := rs[r].numberedNodes full #[]
      if shape.isEmpty then continue
      let sr ← srcRoots[r]?
      let nodes ← walkModeExpr full c.sharing (c.sharing.size + 2)
        rs[r] sr.expr sr.teleResults sr.isTheorem #[]
      rootBlocks := rootBlocks.push { shared := false, index := r.toUInt64, variant := 0, nodes }
    let st ← get
    let mut out := rootBlocks
    for h : n in [:st.variants.size] do
      let vs := st.variants[n]
      for hv : v in [:vs.size] do
        out := out.push { shared := true, index := n.toUInt64, variant := v.toUInt64, nodes := vs[v] }
    return out.qsort (fun x y => x.keyLt y)
  match act.run initSt with
  | some (sec, _) =>
    if Ix.CompileM.sectionAdmissible c sec then sec else Ix.CompileM.undecidedSection c
  | none => Ix.CompileM.undecidedSection c

/-- A mode-only annotator (`requireDecided := false`) that writes source
`AllMode`s onto `0x04` undecided binder nodes when compiling without `pw`
binder-data computation. -/
def modeOnlyAnnotator (env : Ix.Environment) : Ix.BinderAnnotator :=
  { run := fun extra names c =>
      let find (n : Ix.Name) : Option Ix.ConstantInfo :=
        ((extra.find? (·.1 == n)).map (·.2)).orElse fun _ => env.consts.get? n
      sourceModeSection find names c
    requireDecided := false }

/-- An undecided binder: the record (its address before re-addressing), the
block and the node's position in the block. -/
structure Undecided where
  address : Address
  shared : Bool
  index : Nat
  variant : Nat
  node : Nat
  deriving Inhabited

/-- The undecided binders of a section. -/
def undecidedOf (a : Address) (blocks : Array Ixon.BinderBlock) : Array Undecided := Id.run do
  let mut out := #[]
  for b in blocks do
    for (node, i) in b.nodes.zipIdx do
      if node matches .undecided _ then
        out := out.push ⟨a, b.shared, b.index.toNat, b.variant.toNat, i⟩
  return out

/-! ## Annotation -/

/-- The records of `env`, decoded, sorted by address. -/
def recordsOf (env : Ixon.Env) : Except String (Array (Address × Ixon.Constant)) := do
  let mut out := #[]
  for (a, lc) in env.consts do
    match lc.get with
    | .ok c => out := out.push (a, c)
    | .error e => throw s!"binder data: record {a} does not decode: {e}"
  return out.qsort (fun x y => x.1.cmpBytes y.1 == .lt)

/-- The role table of `env`'s binding and the prelude read from `env`'s own
records under it. -/
def preludeOf (env : Ixon.Env) (store : Std.HashMap Address Ixon.Constant) :
    Except String (Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon) := do
  let some binding := env.roleBinding | throw "binder data: the environment has no role binding"
  let some table := Ix.Kernel.RoleTable.ofBytes binding.bytes
    | throw "binder data: the role binding does not decode"
  let preRecords ← Ix.RoleBinding.preludeRecords table (store[·]?) Ix.Kernel.preludeShape
  let blobs := (env.blobs.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList
  let pre ← Ix.Kernel.Reader.readPrelude (md := .anon) table preRecords #[] blobs
  Ix.Kernel.Reader.checkPreludeShape pre
  return (table, pre)

/-- What annotating an environment found. -/
structure Report where
  /-- the annotator's counts -/
  stats : Stats := {}
  /-- records with a non-empty section -/
  sections : Nat := 0
  blocks : Nat := 0
  nodes : Nat := 0
  /-- the undecided binders, by the records' addresses after re-addressing -/
  undecided : Array Undecided := #[]
  /-- the records the kernel refused, why, by their addresses after re-addressing -/
  refused : Array (Address × String) := #[]
  deriving Inhabited

/-- Every record's section (only records with a non-empty one), keyed by the
record's address in `env`, and the report (addresses still `env`'s). -/
def annotate (env : Ixon.Env) (records : Array (Address × Ixon.Constant)) :
    Except String (Std.HashMap Address (Array Ixon.BinderBlock) × Report) := do
  let store : Std.HashMap Address Ixon.Constant := records.foldl (fun m (a, c) => m.insert a c) {}
  let prelude ← preludeOf env store
  let view : View := {
    records, blobs := env.blobs, hints := env.anonHints,
    table := env.roleBinding.map (·.bytes) }
  let k ← KernelEnv.ofView view (prelude? := some prelude)
  let (tables, stats) := annotateKernel k (taint := true)
  let mut sections : Std.HashMap Address (Array Ixon.BinderBlock) := {}
  let mut report : Report := { stats, refused := k.failures }
  for (a, blocks) in tables do
    let some c := store[a]? | continue
    let sec ← if Ix.CompileM.unsafeOrPartial c then stripSection c else sectionOf c blocks
    if sec.isEmpty then continue
    sections := sections.insert a sec
    report := { report with
      sections := report.sections + 1, blocks := report.blocks + sec.size
      nodes := sec.foldl (fun n b => n + b.nodes.size) report.nodes
      undecided := report.undecided ++ undecidedOf a sec }
  return (sections, report)

/-! ## Re-addressing -/

/-- The records a record names by address: its refs table, and a projection's
block. -/
def targets (c : Ixon.Constant) : Array Address :=
  match c.info with
  | .iPrj p => c.refs.push p.block
  | .cPrj p => c.refs.push p.block
  | .rPrj p => c.refs.push p.block
  | .dPrj p => c.refs.push p.block
  | _ => c.refs

/-- The records in an order with every record after the records it names
(an iterative depth-first postorder from the records in address order). A
cycle is an error: a record names another only by its address, the hash of
bytes holding the other's address. -/
def bottomUp (store : Std.HashMap Address Ixon.Constant) (records : Array (Address × Ixon.Constant)) :
    Except String (Array Address) := do
  let mut done : Std.HashSet Address := Std.HashSet.emptyWithCapacity records.size
  let mut active : Std.HashSet Address := {}
  let mut out : Array Address := Array.mkEmpty records.size
  for (root, _) in records do
    if done.contains root then continue
    let mut stack : Array (Address × Bool) := #[(root, false)]
    while !stack.isEmpty do
      let (node, expanded) := stack.back!
      stack := stack.pop
      if expanded then
        active := active.erase node
        unless done.contains node do
          done := done.insert node
          out := out.push node
      else if done.contains node then
        pure ()
      else if active.contains node then
        throw s!"binder data: records name each other in a cycle through {node}"
      else
        active := active.insert node
        stack := stack.push (node, true)
        for dep in (store[node]?.map targets).getD #[] do
          if dep != node && store.contains dep && !done.contains dep then
            if active.contains dep then
              throw s!"binder data: records name each other in a cycle through {dep}"
            stack := stack.push (dep, false)
  return out

/-- A record with its references renamed by `rename` and its section set. -/
def rewriteRecord (rename : Address → Address) (c : Ixon.Constant)
    (binders : Array Ixon.BinderBlock) : Ixon.Constant :=
  let info : Ixon.ConstantInfo := match c.info with
    | .iPrj p => .iPrj { p with block := rename p.block }
    | .cPrj p => .cPrj { p with block := rename p.block }
    | .rPrj p => .rPrj { p with block := rename p.block }
    | .dPrj p => .dPrj { p with block := rename p.block }
    | i => i
  { c with info, refs := c.refs.map rename, binders }

/-- The role table with its record addresses renamed. -/
def renameTable (rename : Address → Address) (t : Ix.Kernel.RoleTable) : Ix.Kernel.RoleTable :=
  { t with
    bound := t.bound.map fun (r, a) => (r, rename a)
    evidence := t.evidence.map fun (r, es) => (r, es.map fun
      | .proof a => .proof (rename a)
      | .defeq => .defeq) }

/-- `env` with each record's section set to its entry in `sections` (empty where
it has none), re-addressed bottom-up, and the map from old addresses to new.
Records that become equal are one record (`strip` of an environment holding a
record both with and without its section). -/
def readdress (env : Ixon.Env) (records : Array (Address × Ixon.Constant))
    (sections : Std.HashMap Address (Array Ixon.BinderBlock)) :
    Except String (Ixon.Env × Std.HashMap Address Address) := do
  unless env.comms.isEmpty do throw "binder data: commitments are not re-addressed"
  unless env.modelRecords.isEmpty && env.models.isEmpty do
    throw "binder data: the environment carries model records"
  let store : Std.HashMap Address Ixon.Constant := records.foldl (fun m (a, c) => m.insert a c) {}
  let order ← bottomUp store records
  let mut renamed : Std.HashMap Address Address := Std.HashMap.emptyWithCapacity records.size
  let mut consts : Std.HashMap Address Ixon.LazyConstant := Std.HashMap.emptyWithCapacity records.size
  for a in order do
    let some c := store[a]? | continue
    let rename (x : Address) : Address := renamed.getD x x
    let c' := rewriteRecord rename c (sections.getD a #[])
    let bytes := Ixon.serConstant c'
    let a' := Address.blake3 bytes
    unless consts.contains a' do
      consts := consts.insert a' { buf := bytes, len := bytes.size, cache := some c' }
    renamed := renamed.insert a a'
  let rename (x : Address) : Address := renamed.getD x x
  let named := env.named.fold (init := ({} : Std.HashMap Ix.Name Ixon.Named)) fun m n entry =>
    m.insert n { entry with
      addr := rename entry.addr
      original := entry.original.map fun (a, cm) => (rename a, cm) }
  let addrToName := env.addrToName.fold (init := ({} : Std.HashMap Address Ix.Name)) fun m a n =>
    m.insert (rename a) n
  let anonHints := env.anonHints.fold
    (init := ({} : Std.HashMap Address Lean.ReducibilityHints)) fun m a h => m.insert (rename a) h
  let roleBinding ← match env.roleBinding with
    | none => pure none
    | some b => do
      let some t := Ix.Kernel.RoleTable.ofBytes b.bytes
        | throw "binder data: the role binding does not decode"
      let bytes := (renameTable rename t).toBytes
      pure (some { address := Address.blake3 bytes, bytes })
  let env' := { env with
    consts, named, addrToName, anonHints, roleBinding
    main := env.main.map rename
    assumptions := env.assumptions.fold (init := ({} : Std.HashSet Address)) fun s a =>
      s.insert (rename a) }
  return (env', renamed)

/-- **`env` with every record's section, re-addressed**, and what was found
(addresses in the report are the new ones). `env`'s records are the compiler's,
without sections, under `env`'s own binding. -/
def apply (env : Ixon.Env) : Except String (Ixon.Env × Report) := do
  let records ← recordsOf env
  let (sections, report) ← annotate env records
  let (env', renamed) ← readdress env records sections
  let rename (x : Address) : Address := renamed.getD x x
  let report := { report with
    undecided := report.undecided.map fun u => { u with address := rename u.address }
    refused := report.refused.map fun (a, why) => (rename a, why) }
  return (env', report)

/-- `env` with every decided `pw` datum replaced by undecided (`0x04`),
preserving all authored resource modes (`AllMode`s in `c.binders`, `LetMode`s,
`fieldModes`, `asserts`), re-deduplicating sharing variants by whole node lists,
and re-addressing bottom-up. An environment whose records already carry their
stripped sections is returned unchanged. -/
def strip (env : Ixon.Env) : Except String Ixon.Env := do
  let records ← recordsOf env
  let mut sections : Std.HashMap Address (Array Ixon.BinderBlock) := {}
  let mut unchanged := true
  for (a, c) in records do
    let sec ← stripSection c
    if c.binders != sec then unchanged := false
    unless sec.isEmpty do sections := sections.insert a sec
  if unchanged then return env
  return (← readdress env records sections).1

/-- `apply` after `strip`: an environment some of whose records carry their
sections already (a compiled closure beside role support records that carry
theirs) is annotated as a whole. -/
def withBinderData (env : Ixon.Env) : Except String (Ixon.Env × Report) := do
  apply (← strip env)

/-- The report's summary line. -/
def Report.summary (r : Report) : String :=
  s!"{r.sections} records with binder data, {r.blocks} blocks, {r.nodes} nodes, \
    {r.undecided.size} undecided; kernel installed {r.stats.installed}, refused {r.refused.size}, \
    data inherited from declared types {r.stats.inherited}"

/-- One line per undecided binder, named by `nameOf`. -/
def Report.undecidedLines (r : Report) (nameOf : Address → String) : Array String :=
  r.undecided.map fun u =>
    s!"undecided binder: {nameOf u.address} ({u.address}), \
      {if u.shared then "sharing entry" else "root"} {u.index} variant {u.variant}, node {u.node}"

/-- A record's names in `env` (a block's: those of the projections into it), for
reports. -/
def namesOf (env : Ixon.Env) (wanted : Std.HashSet Address) : Std.HashMap Address String := Id.run do
  let mut out : Std.HashMap Address String := {}
  for (n, entry) in env.named do
    let owner := match env.getConst? entry.addr with
      | some c => Ixon.CheckOrder.owner entry.addr c
      | none => entry.addr
    if wanted.contains owner && !out.contains owner then out := out.insert owner n.pretty
  return out

/-- Print the summary, and each undecided binder by name (at most `limit`, to
stderr) and each record the kernel refused (at most `limit`). -/
def Report.print (r : Report) (env : Ixon.Env) (tag : String) (limit : Nat := 50) : IO Unit := do
  IO.println s!"[{tag}] binder data: {r.summary}"
  if r.undecided.isEmpty && r.refused.isEmpty then return
  let wanted : Std.HashSet Address :=
    (r.undecided.map (·.address) ++ r.refused.map (·.1)).foldl (·.insert ·) {}
  let names := namesOf env wanted
  let nameOf (a : Address) : String := names.getD a "?"
  let lines := r.undecidedLines nameOf
  for l in lines.extract 0 limit do IO.eprintln s!"[{tag}] {l}"
  if lines.size > limit then IO.eprintln s!"[{tag}] … and {lines.size - limit} more undecided"
  for (a, why) in r.refused.extract 0 limit do
    IO.eprintln s!"[{tag}] binder data: the kernel refused {nameOf a} ({a}): {why}"

end Ix.Compile.BinderData

end
