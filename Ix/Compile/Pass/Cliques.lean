/- # Pass 3: changed definition cliques (design document §2.7, §5; O13–O16)

## Contract
Input: one block about to compile, the compile environment (Lean's
constants, the addresses of everything compiled so far) and, from the
scheduler, the clique edges (`scheduleCliques`). Output, under Pass 3 (the
only mode since M6R slice 6; a hand-built environment runs no hook) and only for a member of a **changed** clique:

* the member's value replaced, in the block's overlay, by its transported
  value `Φ_σ(f_i)` (the clique transport `Ix.Compile.Clique.transport`), whose
  root carries a decompile record (`_ix.inline`) holding Lean's own value: the
  member keeps its Lean name and Lean's type, so it is the faithful constant
  (no image is needed for cliques);
* the canonical constants the transported member references, compiled into
  the block and stored under reserved names (D14): `g._ix._mutual` and
  `g._ix._mutual._proof_k` (well-founded; `g` the first canonical member),
  `g._ix.mutual` and its `_proof_k` (`partial_fixpoint`), `x._ix._f` and
  `x._ix.match_N` (structural); the canonical functional carries the
  side-car record `_ix.clique` (encoding, Lean's order, `σ`, the order's
  source, the transport's causes).

Lean's own encoding constants (`f₀._mutual`, its `_proof_k`, `x._f`, …) keep
their Lean names and Lean's form: their statements follow Lean's order
(cause `ORDER-STMT`), and Lean's equation lemmas (`_mutual.eq_def`, `eq_N`)
refer to them.

**M.1, the clique.** Lean's `all` of a safe definition or a theorem, when it
has two or more members, none of which mentions another directly (a kernel
mutual block, `partial` and `unsafe` cliques, is not an encoded clique and
compiles as today). `all` is `EqnInfo.declNames` on every clique family
(measured, A5 proper), so the compiler reads Pass 1's M.1 from its own input.
**Encoding**: `all₀._mutual` applied by the members (well-founded),
`all₀.mutual` projected by them (`partial_fixpoint`), `x._f` for every member
or the inductive-predicate route (structural). **M.2/M.3, the order**:
`Ix.Compile.Clique.cliqueOrder`, Pass 1's classes over each member's type and
its specification recovered from the encoding and stated in the member's own
parameters; Q6's statement order when the recovery fails; `NOSPEC` when the
statements tie. **M.6, changed**: `σ` is not the identity. (A clique over a
changed block is transported the same way, and its call sites into the
block are then rewritten by Pass 3 as any other constant's.)

## Faithfulness
The member keeps Lean's type (checked); its value is `Φ_σ` of Lean's value.
The correspondence `f_i = f'_{σ i}` is the transport's construction, not a
definitional equality, and is argued per encoding [argued, design document
§5]: **O14** (structural) by joint induction with the block's recursor, the
repacking map on the `below` dictionaries closing each case; **O15**
(well-founded) by `WellFounded.fix_eq` once on each side, the functional
conjugated by the permutation of the `PSum` summands; **O16**
(`partial_fixpoint`) by `Ix.Compile.Clique.FixPerm.fix_iso_proj` [proved],
up to the conversion `F' ≡ φ ∘ F ∘ φ⁻¹`. O13a/b (order only, the fixed
telescope) are ζ/binder permutations inside those. Executable evidence: the
`pass3-cliques` suite (kernels on every transported constant, the value
pins over the members, the twins).

## Canonicity
The canonical functional, its proofs and the members are invariant under the
presentations of a clique (permutation, regrouping, renaming), outside the
non-canonical set (`GUESSLEX`, `RECARG`, `TACTIC-ASYM`, `SHAPE`, `NOSPEC`):
the twins under the switch (`pass3-cliques`).

## Side condition and fallback
No plan (compile as today): not an encoded clique, `σ` the identity, the
order undetermined (`NOSPEC`), or the transport left the clique in Lean's
form (`SHAPE`, the baseline of §0.1). A constant whose proof is outside the
grammar keeps Lean's body under its transported statement (`SHAPE`, in the
side-car record). Every member block of a clique computes the same plan: the
scheduling edges make each wait for everything any member references.

## Non-canonical set and evidence
`ORDER-STMT` for Lean's encoding constants under their Lean names; the
transport's causes. Evidence: `pass3-cliques`, `clique-transport`.
-/
module
public import Ix.CompileM
public import Ix.CondenseM
public import Ix.Compile.Clique.Recover
public import Ix.Compile.Pass.Names
public import Ix.Compile.Pass.Translate
public section

namespace Ix.Compile.Pass

open Ix (Name Level Expr ConstantInfo)
open Ix.CompileM
open Ix.Compile.Clique (Decl Encoding Input Output Cause OrderSource findPacked?)
open Ix.Compile.Canon (getAppFnArgs stripMdata)

/-! ## Names -/

/-- The side-car record key on a canonical functional: `_ix.clique`. -/
def cliqueKey : Name := Name.mkStr (Name.mkStr Name.mkAnon ixComponent) "clique"

/-- The decompile records of transported members use placeholder indices
from here (the call-site rewrite's indices start at `0` in every block). -/
def cliqueRecordBase : Nat := 1 <<< 40

/-- `x ++ s` for a string component. -/
def nameStr (x : Name) (s : String) : Name := Name.mkStr x s

/-- The last string component. -/
def lastStr : Name → String
  | .str _ s _ => s
  | _ => ""

/-- The display name of a Lean encoding constant `x.rest` (`x` a member):
`x._ix.rest`. -/
def cliqueIxName (all : Array Name) (a : Name) : Option Name := do
  let (x, rest) ← all.findSome? fun x =>
    match stripPrefix? x a with
    | some rest => if rest.isEmpty then none else some (x, rest)
    | none => none
  return appendComps (nameStr x ixComponent) rest

/-! ## Terms -/

/-- The constants of `e` satisfying `p`, each once (a walk over distinct
nodes: library proofs are shared DAGs). -/
def constsWhere (p : Name → Bool) (e : Expr) : Array Name := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut found : Std.HashSet Name := {}
  let mut out : Array Name := #[]
  let mut stack : Array Expr := #[e]
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .const n _ _ => if p n && !found.contains n then
        found := found.insert n
        out := out.push n
    | .app f a _ => stack := stack.push a |>.push f
    | .lam _ t b _ _ | .forallE _ t b _ _ => stack := stack.push b |>.push t
    | .letE _ t v b _ _ => stack := stack.push b |>.push v |>.push t
    | .proj _ _ s _ | .mdata _ s _ => stack := stack.push s
    | _ => pure ()
  return out

/-- Rename constants, memoised over the DAG. -/
def renameConstsM (m : Std.HashMap Name Name) (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some r := (← get).get? e then return r
  let r ← match e with
    | .const n us _ => pure (match m.get? n with
      | some n' => Expr.mkConst n' us
      | none => e)
    | .app f a _ => return Expr.mkApp (← renameConstsM m f) (← renameConstsM m a)
    | .lam n t b bi _ => return Expr.mkLam n (← renameConstsM m t) (← renameConstsM m b) bi
    | .forallE n t b bi _ => return Expr.mkForallE n (← renameConstsM m t) (← renameConstsM m b) bi
    | .letE n t v b nd _ =>
      return Expr.mkLetE n (← renameConstsM m t) (← renameConstsM m v) (← renameConstsM m b) nd
    | .proj s i x _ => return Expr.mkProj s i (← renameConstsM m x)
    | .mdata d x _ => return Expr.mkMData d (← renameConstsM m x)
    | _ => pure e
  modify (·.insert e r)
  return r

def renameDecl (m : Std.HashMap Name Name) (d : Decl) : Decl :=
  if m.isEmpty then d else
  let ((type, value), _) := (do
    let t ← renameConstsM m d.type
    let v ← renameConstsM m d.value
    pure (t, v)).run {}
  { d with name := (m.get? d.name).getD d.name, type, value }

/-! ## M.1: the clique of a member -/

/-- Lean's `all`. -/
def allOf : ConstantInfo → Array Name
  | .defnInfo v => v.all
  | .thmInfo v => v.all
  | _ => #[]

/-- A safe definition or a theorem, as the transport's declaration. -/
def cliqueDecl? (ci : ConstantInfo) : Option Decl :=
  match ci with
  | .defnInfo v => if v.safety == .safe then Decl.ofConstantInfo? ci else none
  | .thmInfo _ => Decl.ofConstantInfo? ci
  | _ => none

/-- A name that marks a clique encoding in a reference set: `_mutual`
(well-founded), `mutual` (`partial_fixpoint`), `_f` (structural), or the
`brecOn` of an inductive predicate whose `below` is an inductive (the
inductive-predicate route). -/
def isEncodingMarker (const? : Name → Option ConstantInfo) (n : Name) : Bool :=
  match n with
  | .str p s _ =>
    s == "_mutual" || s == "mutual" || s == "_f" ||
      (s == "brecOn" && (match const? (nameStr p "below") with
        | some (.inductInfo _) => true
        | _ => false))
  | _ => false

/-! ## The clique table and the scheduling edges -/

/-- The cliques of the input (M.1) whose members are separate blocks, by
Lean's `all`. Only blocks that reference an encoding marker are read. -/
def inputCliques (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Array (Array Name) := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out : Array (Array Name) := #[]
  for (lo, mems) in blocks.blocks do
    let refs := blocks.blockRefs.getD lo {}
    unless refs.toList.any (isEncodingMarker env.get?) do continue
    for m in mems do
      if seen.contains m then continue
      let some ci := env.get? m | continue
      let all := allOf ci
      if all.size < 2 || (cliqueDecl? ci).isNone then continue
      for a in all do seen := seen.insert a
      -- every member present, each in its own block
      let los := all.filterMap blocks.lowLinks.get?
      if los.size != all.size then continue
      let loSet : Std.HashSet Name := los.foldl (·.insert ·) {}
      if loSet.size != all.size then continue
      out := out.push all
  return out

/-- A Lean encoding constant of a clique, by name: `all₀._mutual` and
`all₀.mutual` with everything under them (proofs, equation lemmas), `m._f`. -/
def isEncodingName (all : Array Name) (n : Name) : Bool :=
  match all[0]? with
  | none => false
  | some all0 =>
    (stripPrefix? (nameStr all0 "_mutual") n).isSome || (stripPrefix? (nameStr all0 "mutual") n).isSome ||
      (match n with
        | .str p "_f" _ => all.contains p
        | _ => false)

/-- The library constants the transport may introduce (the composition
fallback of `partial_fixpoint`, the case split of a regenerated equation
lemma): every clique block waits for them too, when the input has them. -/
def transportPrereqs : Array Name :=
  #[``Lean.Order.monotone_compose, ``PSigma.casesOn, ``PSigma.mk, ``PSum.casesOn, ``PSum.inl,
    ``PSum.inr, ``Eq, ``Eq.trans, ``id].map Ix.Name.fromLeanName

/-- `_private.<module>.0.<n>` ↦ `n` (Lean's `privateToUserName?`): the
module system realises an on-demand lemma of a public definition under a
private name when a private declaration asks for it. -/
def privateUserName? (n : Name) : Option Name :=
  match comps n [] with
  | .inl "_private" :: rest => do
    -- the marker is the number 0 (Lean) or, in names that went through a
    -- string form, the component "0"
    let i ← rest.findIdx? fun c => c == .inr 0 || c == .inl "0"
    some ((rest.drop (i + 1)).foldl (init := Name.mkAnon) fun acc c => match c with
      | .inl s => Name.mkStr acc s
      | .inr k => Name.mkNat acc k)
  | _ => none
where
  comps : Name → List (String ⊕ Nat) → List (String ⊕ Nat)
    | .anonymous _, acc => acc
    | .str p s _, acc => comps p (.inl s :: acc)
    | .num p k _, acc => comps p (.inr k :: acc)

/-- An equation lemma's last component: `eq_def`, `eq_unfold`, `eq_<k>`. -/
def isEqSuffix (s : String) : Bool :=
  s == "eq_def" || s == "eq_unfold" ||
    (s.startsWith "eq_" && (s.drop 3).all Char.isDigit && !(s.drop 3).isEmpty)

/-- The equation lemmas the input has under a private name, by their user
name (`privateUserName?`). An index of names only: a clique reads the
entries of its own members' lemma names. -/
def privateEqLemmas (blocks : Ix.CondensedBlocks) : Std.HashMap Name (Array Name) := Id.run do
  let mut out : Std.HashMap Name (Array Name) := {}
  for (_, mems) in blocks.blocks do
    for n in mems do
      let some u := privateUserName? n | continue
      let .str _ s _ := u | continue
      if isEqSuffix s then out := out.insert u ((out.getD u #[]).push n)
  return out

/-- The equation lemmas of a member that the input has, by name: `m.eq_def`,
`m.eq_unfold` and `m.eq_1`, `m.eq_2`, … (numbered from 1 without gaps, as
Lean realises them), under that name or under a private name whose user name
it is (`priv`, `privateEqLemmas`). They are on-demand auxiliaries of the
clique's own unit (design document §6.3): reading them is reading the unit. -/
def memberEqLemmas (const? : Name → Option ConstantInfo) (priv : Std.HashMap Name (Array Name))
    (m : Name) : Array Name := Id.run do
  let mut out : Array Name := #[]
  let present (n : Name) : Array Name :=
    (if (const? n).isSome then #[n] else #[]) ++
      ((priv.getD n #[]).qsort fun a b => a.pretty < b.pretty)
  for s in ["eq_def", "eq_unfold"] do
    out := out ++ present (nameStr m s)
  for k in [1:1000000] do
    let found := present (nameStr m s!"eq_{k}")
    if found.isEmpty then break
    out := out ++ found
  return out

/-- The clique whose Lean encoding constant `n` is (`isEncodingName`), from a
map of the encoding roots (`all₀._mutual`, `all₀.mutual`, `m._f`) to the
cliques: `n` or one of its prefixes is a root. -/
def encodingOwner? (roots : Std.HashMap Name (Array Name)) (n : Name) : Option (Array Name) := Id.run do
  let mut cur := n
  for _ in [0:64] do
    if let some all := roots.get? cur then
      if isEncodingName all n then return some all
    match cur with
    | .str p _ _ | .num p _ _ => cur := p
    | .anonymous _ => return none
  return none

/-- The changed-clique table and the scheduling edges (called once per
compile under the switch, before the schedule; identity otherwise). The
form of a clique is decided from the clique, its own logical unit and its
dependencies only (design document §6.3): no caller is read.

* **The table.** Every member of an input clique (`inputCliques`) ↦ (Lean's
  `all`, the carried lemmas). The **carried lemmas** are the members' own
  equation lemmas (`memberEqLemmas`, read by name: the clique's unit) that
  reference a member and one of Lean's encoding constants of the clique
  (`isEncodingName`): their proofs unfold the members to Lean's encoding, so
  they are transported with the clique (each carried lemma is in the table
  too), or the clique stays in Lean's form when one cannot be carried
  (`planClique`).
* **The encoding roots.** `all₀._mutual`, `all₀.mutual` and every `m._f` ↦
  the clique, so that a block can tell that it references a clique's
  encoding (`encodingOwner?`). A block outside the unit that references a
  member and an encoding constant of a transported clique is refused when it
  compiles (`cliqueCallers`); the clique is never changed for it.
* **The edges.** Every member block, and every carried lemma's block, also
  waits for everything any member references (the encoding constants, the
  other members' matchers and proofs, the constants their statements
  mention), so that each such block can plan the clique alone: the
  specifications' external references and the canonical constants'
  dependencies are compiled before it. The clique's other blocks also wait
  for the block of its first member (`all₀`), which plans the clique first:
  they take its plan from the plan table (`cliquePlanFor`). These edges only
  order blocks; they change no byte (the sequential driver already compiles
  the blocks one after another). -/
def scheduleCliques (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Ix.CondensedBlocks × Std.HashMap Name (Array Name × Array Name) × Std.HashMap Name (Array Name) :=
    Id.run do
  let cliques := inputCliques env blocks
  let priv := if cliques.isEmpty then {} else privateEqLemmas blocks
  let mut roots : Std.HashMap Name (Array Name) := {}
  let mut table : Std.HashMap Name (Array Name × Array Name) := {}
  let mut blockRefs := blocks.blockRefs
  for all in cliques do
    if let some all0 := all[0]? then
      roots := roots.insert (nameStr all0 "_mutual") all |>.insert (nameStr all0 "mutual") all
    for m in all do roots := roots.insert (nameStr m "_f") all
    -- the carried lemmas: the members' equation lemmas over Lean's encoding
    let mut found : Array Name := #[]
    for m in all do
      for c in memberEqLemmas env.get? priv m do
        let some lo := blocks.lowLinks.get? c | continue
        let refs := blocks.blockRefs.getD lo {}
        if refs.toList.any (isEncodingName all ·) && refs.toList.any all.contains then
          found := found.push c
    let carried := found.qsort fun a b => a.pretty < b.pretty
    for m in all do table := table.insert m (all, carried)
    for c in carried do table := table.insert c (all, carried)
    -- the edges
    let members : Std.HashSet Name := all.foldl (·.insert ·) {}
    let los := all.filterMap blocks.lowLinks.get?
    let mut union : Ix.Set Name := {}
    for p in transportPrereqs do
      if blocks.lowLinks.contains p then union := union.insert p
    for lo in los do
      for r in blocks.blockRefs.getD lo {} do
        if !members.contains r then union := union.insert r
    -- one block plans the clique first (the block of `all₀`); the clique's
    -- other blocks also wait for it, so that they take the plan from the
    -- plan table (`cliquePlanFor`) instead of planning it again in its wave
    let all0? := all[0]?
    let plannerLo? := all0?.bind blocks.lowLinks.get?
    for lo in los ++ carried.filterMap blocks.lowLinks.get? do
      let own := blocks.blocks.getD lo {}
      let mut rs := blockRefs.getD lo {}
      for r in union do
        if !own.contains r then rs := rs.insert r
      if let some all0 := all0? then
        if plannerLo? != some lo && !own.contains all0 then rs := rs.insert all0
      blockRefs := blockRefs.insert lo rs
  return ({ blocks with blockRefs }, table, roots)

/-! ## The plan of a clique -/

/-- The abstracted proofs of a packed constant (`p._proof_k`), reached from
its type and value and from each other. -/
def encodingProofs (const? : Name → Option ConstantInfo) (packed : Decl) : Array Decl := Id.run do
  let isProof (n : Name) : Bool := match n with
    | .str q s _ => q == packed.name && s.startsWith "_proof_"
    | _ => false
  let mut todo := constsWhere isProof packed.type ++ constsWhere isProof packed.value
  let mut seen : Std.HashSet Name := {}
  let mut out : Array Decl := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some d := (const? n).bind Decl.ofConstantInfo? | continue
    out := out.push d
    todo := todo ++ constsWhere isProof d.type ++ constsWhere isProof d.value
  return out.qsort fun a b => a.name.pretty < b.name.pretty

/-- The encoding of a clique and its constants besides the members. -/
def encodingOf (const? : Name → Option ConstantInfo) (all : Array Name) (members : Array Decl) :
    Option (Encoding × Array Decl) := do
  let all0 ← all[0]?
  let packedOf (s : String) : Option Decl := do
    let d ← (const? (nameStr all0 s)).bind Decl.ofConstantInfo?
    let p ← findPacked? members #[d]
    if p.name == d.name then some d else none
  if let some d := packedOf "_mutual" then
    return (.wellFounded, #[d] ++ encodingProofs const? d)
  if let some d := packedOf "mutual" then
    return (.partialFixpoint, #[d] ++ encodingProofs const? d)
  -- structural: the functionals, and the "below" matchers the members apply
  let fs := all.filterMap fun m => (const? (nameStr m "_f")).bind Decl.ofConstantInfo?
  let matchers := (members.foldl (init := #[]) fun acc d =>
      acc ++ constsWhere (fun n => (lastStr n).startsWith "match_") d.value).foldl
    (init := #[]) fun acc n => if acc.contains n then acc else acc.push n
  let ms := (matchers.qsort fun a b => a.pretty < b.pretty).filterMap fun n =>
    (const? n).bind Decl.ofConstantInfo?
  if fs.size == all.size then return (.structural, fs ++ ms)
  if fs.isEmpty && members.all (fun d => (constsWhere (isEncodingMarker const?) d.value).size > 0) then
    return (.structural, ms)
  none

/-- The equation lemmas of the packed constant `p` that the carried lemmas
reach (`p.eq_def`, `p.eq_unfold`, `p.eq_<k>`), transitively. -/
def packedLemmas (const? : Name → Option ConstantInfo) (p : Name) (carried : Array Decl) :
    Array Decl := Id.run do
  let isPackedEq (n : Name) : Bool := match n with
    | .str q s _ => q == p && (s == "eq_def" || s == "eq_unfold" || s.startsWith "eq_")
    | _ => false
  let mut todo : Array Name := carried.foldl (fun acc d => acc ++ constsWhere isPackedEq d.value) #[]
  let mut seen : Std.HashSet Name := {}
  let mut out : Array Decl := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some d := (const? n).bind Decl.ofConstantInfo? | continue
    out := out.push d
    todo := todo ++ constsWhere isPackedEq d.value
  return out.qsort fun a b => a.name.pretty < b.name.pretty

/-- The plan of a clique (`all`, Lean's order) with its carried equation
lemmas (pure; every block of the clique computes the same one). -/
def planClique (const? : Name → Option ConstantInfo) (addr? : Name → Option Address)
    (all : Array Name) (carried : Array Name) : CliqueOutcome := Id.run do
  if all.size < 2 then return .notEncoded "a single member"
  let mut members : Array Decl := #[]
  for m in all do
    let some cm := const? m | return .notEncoded s!"member {m.pretty} is not in the input"
    let some d := cliqueDecl? cm | return .notEncoded s!"member {m.pretty} is not a safe definition or a theorem"
    if allOf cm != all then return .notEncoded s!"member {m.pretty} has another clique"
    members := members.push d
  -- a kernel mutual block (members referencing each other) is not encoded
  let memberSet : Std.HashSet Name := all.foldl (·.insert ·) {}
  for d in members do
    if !(constsWhere memberSet.contains d.value).isEmpty then
      return .notEncoded "members reference each other (a kernel mutual block)"
  let some (enc, aux) := encodingOf const? all members | return .notEncoded "no encoding recognised"
  let inp0 : Input := { encoding := enc, members, aux, sigma := Ix.Compile.Clique.idPerm all.size,
                        newEncName := all[0]!, const? }
  let ord := Ix.Compile.Clique.cliqueOrder Ix.Compile.Canon.Rules.phaseA addr? inp0
  if let .error why := ord then return .baseline enc "NOSPEC" why
  let .ok (σ, classes, source) := ord | return .notEncoded "unreachable"
  -- O17: the members of a class of two or more (equal specifications) are
  -- one constant, the representative's (the first of the class in the
  -- canonical order); not when one of them carries an equation lemma, whose
  -- proof unfolds that member
  let carriedOwners : Std.HashSet Name := carried.foldl (init := {}) fun s c => match (privateUserName? c).getD c with
    | .str p _ _ => s.insert p
    | _ => s
  let mut aliases : Array (Name × Name) := #[]
  for cls in classes do
    let some rep := cls[0]? | continue
    let some repDecl := members.find? (·.name == rep) | continue
    if cls.size < 2 || cls.any carriedOwners.contains then continue
    for m in cls.extract 1 cls.size do
      let some md := members.find? (·.name == m) | continue
      if md.levelParams == repDecl.levelParams &&
          Ix.Compile.Clique.alphaEq (Ix.Compile.Clique.stripAllMdata md.type)
            (Ix.Compile.Clique.stripAllMdata repDecl.type) then
        aliases := aliases.push (m, rep)
  let identity := (List.range σ.size).all (fun i => σ[i]! == i)
  if identity && aliases.isEmpty then return .unchanged enc source
  if identity then
    -- the order is Lean's, but classes merge: the aliases alone
    let mut transported : Std.HashMap Name Decl := {}
    for (m, rep) in aliases do
      if let some rd := members.find? (·.name == rep) then
        transported := transported.insert m { rd with name := m }
    return .transported { all, encoding := enc, sigma := σ, classes, source, members := transported,
                          canon := #[], functionals := #[], causes := #[], aliases }
  let g := all[(Ix.Compile.Clique.invPerm σ)[0]!]!
  let newEncName := match enc with
    | .wellFounded => nameStr (nameStr g ixComponent) "_mutual"
    | .partialFixpoint => nameStr (nameStr g ixComponent) "mutual"
    | .structural => g
  -- the carried lemmas: the members' own (Lean names), and the packed
  -- constant's that they reach (canonical names)
  let mut carriedDecls : Array Decl := #[]
  for c in carried do
    let some d := (const? c).bind Decl.ofConstantInfo? | return .baseline enc "SHAPE" s!"carried lemma {c.pretty} is not a theorem"
    carriedDecls := carriedDecls.push d
  let packedName := match aux[0]? with
    | some d => if enc == .structural then Name.mkAnon else d.name
    | none => Name.mkAnon
  let packedLs := if carried.isEmpty || enc == .structural then #[] else
    packedLemmas const? packedName carriedDecls
  let lemmas : Array (Decl × Name) := carriedDecls.map (fun d => (d, d.name)) ++
    packedLs.map fun d => (d, nameStr newEncName (lastStr d.name))
  let carriedSet : Std.HashSet Name := carried.foldl (·.insert ·) {}
  let out := Ix.Compile.Clique.transport { inp0 with sigma := σ, newEncName, lemmas }
  if out.baseline then
    return .baseline enc "SHAPE" ((out.causes[0]?).map (·.2.2) |>.getD "the transport kept Lean's form")
  -- (R): Lean's encoding constant ↦ canonical name
  let mut ren : Std.HashMap Name Name := {}
  let mut origin : Std.HashMap Name Name := {}
  for (a, b) in out.renames do origin := origin.insert b a
  if enc == .structural then
    for d in aux do
      if let some x := cliqueIxName all d.name then
        ren := ren.insert d.name x
        origin := origin.insert x d.name
  let decls := out.decls.map (renameDecl ren)
  let causes := out.causes.map fun (c, k, why) => ((ren.get? c).getD c, k, why)
  let mut transported : Std.HashMap Name Decl := {}
  let mut canon : Array (Decl × Name) := #[]
  for d in decls do
    if memberSet.contains d.name || carriedSet.contains d.name then
      -- a member or a member's lemma keeps its Lean name and Lean's type
      let some lean := (members ++ carriedDecls).find? (·.name == d.name) | continue
      unless Ix.Compile.Clique.alphaEq (Ix.Compile.Clique.stripAllMdata d.type)
          (Ix.Compile.Clique.stripAllMdata lean.type) do
        return .baseline enc "SHAPE" s!"the transported {d.name.pretty} does not have Lean's type"
      transported := transported.insert d.name d
    else
      let src := (origin.get? d.name).getD d.name
      if src == d.name then
        return .baseline enc "SHAPE" s!"an encoding constant {d.name.pretty} kept its Lean name"
      canon := canon.push (d, src)
  if transported.size != all.size + carried.size then
    return .baseline enc "SHAPE" "the transport did not return every member and carried lemma"
  for (m, rep) in aliases do
    if let some rd := transported.get? rep then
      transported := transported.insert m { rd with name := m }
  if !causes.isEmpty && !carried.isEmpty then
    -- a carried lemma must be transported exactly: a verbatim proof body
    -- would prove Lean's statement about Lean's encoding
    if causes.any (fun (c, _, _) => carriedSet.contains c || packedLs.any (·.name == c)) then
      return .baseline enc "SHAPE" "a carried equation lemma is outside the grammar"
  -- a constant the transport introduced (the composition fallback, a
  -- regenerated case split) must be in the input: otherwise Lean's form
  let leanRefs : Std.HashSet Name := (members ++ carriedDecls ++ aux ++ packedLs).foldl (init := {})
    fun s d => (constsWhere (fun _ => true) d.type ++ constsWhere (fun _ => true) d.value).foldl (·.insert ·) s
  let produced : Std.HashSet Name := decls.foldl (fun s d => s.insert d.name) {}
  for d in decls do
    for c in constsWhere (fun c => !leanRefs.contains c && !produced.contains c) d.type ++
        constsWhere (fun c => !leanRefs.contains c && !produced.contains c) d.value do
      if (const? c).isNone then
        return .baseline enc "SHAPE" s!"{d.name.pretty} needs {c.pretty}, which is not in the input"
  let functionals := match enc with
    | .structural => canon.filterMap fun (d, _) => if lastStr d.name == "_f" then some d.name else none
    | _ => #[newEncName]
  return .transported { all, encoding := enc, sigma := σ, classes, source, members := transported,
                        canon, functionals, causes, aliases }

/-! ## The hook -/

/-- `stt.resolve_addr` over a compile environment. -/
def cliqueAddr (cenv : CompileEnv) (n : Name) : Option Address :=
  match cenv.nameToAddr.get? n with
  | some a => some a
  | none => cenv.auxNameToAddr.get? n

/-- The value of a definition or theorem. -/
def valueOf? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | _ => none

/-- Lean's constant with another value. -/
def withValue : ConstantInfo → Expr → ConstantInfo
  | .defnInfo v, e => .defnInfo { v with value := e }
  | .thmInfo v, e => .thmInfo { v with value := e }
  | ci, _ => ci

/-- A canonical constant as an input constant: a theorem, or a safe
definition with the hints of the Lean constant it transports. -/
def canonConst (const? : Name → Option ConstantInfo) (d : Decl) (src : Name) (record? : Option String) :
    ConstantInfo :=
  let value := match record? with
    | some r => Expr.mkMData #[(cliqueKey, .ofString r)] d.value
    | none => d.value
  let cnst : Ix.ConstantVal := { name := d.name, levelParams := d.levelParams, type := d.type }
  if d.isThm then .thmInfo { cnst, value, all := #[d.name] }
  else
    let hints := match const? src with
      | some (.defnInfo v) => v.hints
      | _ => .opaque
    .defnInfo { cnst, value, hints, safety := .safe, all := #[d.name] }

/-! ## The plan table (a memo of `planClique`) -/

/-- The prefix of the plan-table check's error (`IX_PASS3_CHECK_PLANS=1`);
the drivers turn a block failure with this prefix into a failed compile. -/
def planCheckPrefix : String := "Pass 3 plan cache check:"

/-- The plan of a clique for the current block, and whether it came from the
plan table (`CompileEnv.p3CliquePlans`).

**Why a table is allowed (design document §5.4, §6.3).** `planClique` is a
function of the clique (`all`), its carried lemmas (read from the clique's
own unit by `scheduleCliques`), the input constants of its unit and its
dependencies (`const?`), and the addresses of those dependencies
(`cliqueAddr`). Every block that plans the clique (a member's block, a
carried lemma's block, a caller's block) is scheduled after all of the
members' references (`scheduleCliques`' edges), so each computes the same
plan: the table is a memo of that function, keyed by the clique (`all₀`),
filled by the first block that needs a plan and merged by the driver like
the other Pass 3 tables. It reads nothing outside the block rule: not a
caller, not the schedule (which block filled the entry, or whether one did,
changes no byte and no record, only the time). With `p3CheckPlans`
(`IX_PASS3_CHECK_PLANS=1`) every plan the table supplies is recomputed and a
difference fails the block with `planCheckPrefix`. -/
def cliquePlanFor (cenv : CompileEnv) (cl carried : Array Name) : Except String (CliqueOutcome × Bool) := do
  let compute (_ : Unit) : CliqueOutcome := planClique cenv.env.get? (cliqueAddr cenv) cl carried
  let some key := cl[0]? | return (compute (), false)
  match cenv.p3CliquePlans.get? key with
  | none => return (compute (), false)
  | some o =>
    if cenv.p3CheckPlans then
      let o' := compute ()
      unless o.same o' do
        throw s!"{planCheckPrefix} the plan of the clique {cl.map (·.pretty)} differs from the table's: \
          table {o.tag}; recomputed {o'.tag}"
    return (o, true)

/-- The prefix of a caller's refusal (`cliqueCallers`): the named error the
driver records as the block's failure (`CompileEnv.ungrounded`), by which the
changed-set record (`Ix.Compile.ChangedSet`) tells a refused caller from any
other failed block. -/
def callerRefusalPrefix : String := "Pass 3 cliques: caller refused"

/-- The callers' side of the block rule (design document §6.3, "callers
adapt"; decision 5 of the plan). A block outside a clique's unit (no member,
no carried lemma, no encoding constant of the clique) that references a
member and one of Lean's encoding constants of the clique may rely on the
member unfolding to Lean's encoding. When the clique is transported (its
plan, a function of the clique, its unit and its dependencies, all
compiled before this block: `cliquePlanFor`), that encoding is no longer what the member
unfolds to: the block is refused with a named error, recorded as a block
failure by the driver. The clique is never changed for a caller, and the
caller is never silently compiled against Lean's form.

Returns the refusal, or `none` when the block may compile, with the plans it
computed (for the plan table) and the number it took from the table
(`cliquePlanFor`). Reads only the block (`all`, its references `refs`) and
the cliques it depends on. -/
def cliqueCallers (cenv : CompileEnv) (all : Set Name) (refs : Ix.Set Name) :
    Except String (Option String × Array (Name × CliqueOutcome) × Nat) := do
  if cenv.p3CliqueRoots.isEmpty then return (none, #[], 0)
  let mut seen : Std.HashSet Name := {}
  let mut fresh : Array (Name × CliqueOutcome) := #[]
  let mut reused := 0
  for r in refs do
    let some cl := encodingOwner? cenv.p3CliqueRoots r | continue
    let some key := cl[0]? | continue
    if seen.contains key then continue
    seen := seen.insert key
    let carried := ((cenv.p3Cliques.get? key).map (·.2)).getD #[]
    -- a block of the clique's own unit is not a caller
    if all.toList.any fun n => cl.contains n || carried.contains n || isEncodingName cl n then continue
    let some m := refs.toList.find? cl.contains | continue
    let (outcome, hit) ← cliquePlanFor cenv cl carried
    if hit then reused := reused + 1 else fresh := fresh.push (key, outcome)
    match outcome with
    | .transported plan =>
      let callers := all.toList.map (·.pretty)
      return (some s!"{callerRefusalPrefix} (block rule, callers adapt): {callers} \
        reference{if callers.length == 1 then "s" else ""} {m.pretty} and Lean's encoding constant \
        {r.pretty} of the transported clique {cl.map (·.pretty)} (sigma {plan.sigma}); a caller may \
        not unfold Lean's encoding of a transported clique", fresh, reused)
    | _ => continue
  return (none, fresh, reused)

/-- Before a block compiles (hook of `Ix.Compile.Pass.prepareBlock`): for
every member of a changed clique in the block, and every equation lemma
carried with one, its transported value in the overlay with Lean's value as
the decompile record, and the canonical constants it references compiled
into the block. `rewrite` is Pass 3's call-site rewrite (for canonical
constants over a changed block). A block outside a transported clique's unit
that unfolds its encoding is refused (`cliqueCallers`; `refs` are the
block's references). Identity when no constant of the block is in the clique
table (`CompileEnv.p3Cliques`) and the block is not such a caller. A
clique's plan is taken from the plan table when an earlier block computed
it (`cliquePlanFor`, a memo of `planClique`); the plans computed here go
back to the driver in the block state (`BlockState.p3CliquePlans`). -/
def prepareCliques (cenv : CompileEnv) (all : Set Name) (refs : Ix.Set Name)
    (rewrite : Array (Name × ConstantInfo) → Except String BlockRewrite) :
    Except String (CompileEnv × BlockState) := do
  if !cenv.pass3 || cenv.p3Cliques.isEmpty then return (cenv, {})
  let (refusal?, fresh0, reused0) ← cliqueCallers cenv all refs
  if let some refusal := refusal? then throw refusal
  let const? := cenv.env.get?
  let mut overlay := cenv.env.overlay
  let mut sources := cenv.p3Sources
  let mut k := 0
  let mut canon : Std.HashMap Name ConstantInfo := {}
  let mut wanted : Array Name := #[]
  -- the plans of this block: from the plan table, or computed here and
  -- handed to the driver for the table (`cliquePlanFor`)
  let mut fresh := fresh0
  let mut reused := reused0
  let mut plans : Std.HashMap Name CliqueOutcome := fresh0.foldl (fun m (k, o) => m.insert k o) {}
  for n in all do
    let some (cl, carried) := cenv.p3Cliques.get? n | continue
    let some key := cl[0]? | continue
    let mut outcome : CliqueOutcome := default
    match plans.get? key with
    | some o => outcome := o
    | none =>
      let (o, hit) ← cliquePlanFor cenv cl carried
      if hit then reused := reused + 1 else fresh := fresh.push (key, o)
      outcome := o
    plans := plans.insert key outcome
    let .transported plan := outcome | continue
    let some md := plan.members.get? n | continue
    let some ci := const? n | continue
    let some leanValue := valueOf? ci | continue
    let idx := cliqueRecordBase + k
    k := k + 1
    overlay := overlay.insert n (withValue ci (Expr.mkMData #[(inlineKey, .ofNat idx)] md.value))
    sources := sources.insert idx leanValue
    -- the canonical constants, and the ones this constant reaches
    let canonNames : Std.HashSet Name := plan.canon.foldl (fun s (d, _) => s.insert d.name) {}
    for (d, src) in plan.canon do
      if !canon.contains d.name then
        let record? := if plan.functionals.contains d.name then some plan.record else none
        canon := canon.insert d.name (canonConst const? d src record?)
    let mut todo := constsWhere canonNames.contains md.value
    while !todo.isEmpty do
      let c := todo.back!
      todo := todo.pop
      if wanted.contains c then continue
      wanted := wanted.push c
      if let some cc := canon.get? c then
        todo := todo ++ constsWhere canonNames.contains cc.getCnst.type
        if let some v := valueOf? cc then todo := todo ++ constsWhere canonNames.contains v
  let tableOut : BlockState := { p3CliquePlans := fresh, p3PlanReused := reused }
  if k == 0 then return (cenv, tableOut)
  -- compile the wanted canonical constants, each once its canonical
  -- references are compiled (here, or by an earlier block of the clique)
  let known (init : BlockState) (r : Name) : Bool :=
    init.blockNameToAddr.contains r || (cliqueAddr cenv r).isSome
  let mut init : BlockState := tableOut
  let mut pending := (wanted.filter fun c => (cliqueAddr cenv c).isNone).qsort fun a b => a.pretty < b.pretty
  let mut rounds := pending.size + 1
  while !pending.isEmpty && rounds > 0 do
    rounds := rounds - 1
    let mut rest : Array Name := #[]
    for c in pending do
      let some ci := canon.get? c | throw s!"Pass 3 cliques: no canonical constant {c.pretty}"
      let refs := constsWhere (fun r => canon.contains r && r != c) ci.getCnst.type ++
        ((valueOf? ci).map (constsWhere fun r => canon.contains r && r != c)).getD #[]
      if refs.any (!known init ·) then
        rest := rest.push c
        continue
      -- Pass 3's call-site rewrite, when the clique ranges over a changed block
      let rw ← rewrite #[(c, ci)]
      let ci' := match rw.overlay[0]? with
        | some (_, x) => x
        | none => ci
      let srcs : Std.HashMap Nat Expr := rw.sources.zipIdx.foldl (fun m (e, i) => m.insert i e) {}
      let blockEnv : BlockEnv :=
        { all := ({} : Ix.Set Name).insert c, current := c, mutCtx := default, univCtx := [] }
      let st0 : BlockState := { blockNameToAddr := init.blockNameToAddr }
      match CompileM.run { cenv with p3Sources := srcs } blockEnv st0 (compileConstantInfo ci') with
      | .error e => throw s!"Pass 3 cliques: canonical constant {c.pretty}: {e}"
      | .ok (r, bs) =>
        init := { init with
          blockNameToAddr := init.blockNameToAddr.insert c r.blockAddr
          auxConsts := init.auxConsts.push (r.blockAddr, r.block)
          auxNamed := init.auxNamed.push (c, { addr := r.blockAddr, constMeta := r.blockMeta })
          auxNameToAddr := init.auxNameToAddr.insert c r.blockAddr
          blockBlobs := bs.blockBlobs.fold (fun m k v => m.insert k v) init.blockBlobs
          blockNames := bs.blockNames.fold (fun m k v => m.insert k v) init.blockNames
          defHints := bs.defHints.fold (fun m k v => m.insert k v) init.defHints }
    pending := rest
  if !pending.isEmpty then
    throw s!"Pass 3 cliques: canonical constants with cyclic references: {pending.map (·.pretty)}"
  return ({ cenv with env := { cenv.env with overlay }, p3Sources := sources }, init)

end Ix.Compile.Pass

end
