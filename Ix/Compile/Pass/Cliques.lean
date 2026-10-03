/- # Pass 3: changed definition cliques (design document §2.7, §5; O13–O16)

## Contract
Input: one block about to compile, the compile environment (Lean's
constants, the addresses of everything compiled so far) and, from the
scheduler, the clique edges (`scheduleCliques`). Output, under the switch
(`IX_PASS3=images`) and only for a member of a **changed** clique:

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

/-- An equation lemma of a member (`m.eq_def`, `m.eq_unfold`, `m.eq_<k>`). -/
def isEqLemmaOf (all : Array Name) (n : Name) : Bool :=
  match n with
  | .str p s _ =>
    all.contains p && (s == "eq_def" || s == "eq_unfold" ||
      (s.startsWith "eq_" && (s.drop 3).all Char.isDigit && !(s.drop 3).isEmpty))
  | _ => false

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

/-- The changed-clique table and the scheduling edges (called once per
compile under the switch, before the schedule; identity otherwise).

* **The table.** Every member of an input clique (`inputCliques`) ↦ (Lean's
  `all`, the carried lemmas, the demotion reason). A **dependent** of the
  clique is a constant outside it that references both a member and one of
  Lean's encoding constants (`isEncodingName`): its proof may rely on the
  member unfolding to Lean's encoding, which the transport replaces. The
  members' equation lemmas (`isEqLemmaOf`) are *carried*: transported with
  the clique (each carried lemma is in the table too). Any other dependent
  demotes the clique (it compiles as today; the reason names the dependent).
* **The edges.** Every member block, and every carried lemma's block, also
  waits for everything any member references (the encoding constants, the
  other members' matchers and proofs, the constants their statements
  mention), so that each such block can plan the clique alone: the
  specifications' external references and the canonical constants'
  dependencies are compiled before it. -/
def scheduleCliques (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Ix.CondensedBlocks × Std.HashMap Name (Array Name × Array Name × String) := Id.run do
  let cliques := inputCliques env blocks
  -- the dependents of each clique: the encoding names by their roots
  let mut encRoot : Std.HashMap Name Nat := {}
  for i in [0:cliques.size] do
    let all := cliques[i]!
    if let some all0 := all[0]? then
      encRoot := encRoot.insert (nameStr all0 "_mutual") i |>.insert (nameStr all0 "mutual") i
    for m in all do encRoot := encRoot.insert (nameStr m "_f") i
  let encOwner (n : Name) : Option Nat := Id.run do
    let mut cur := n
    for _ in [0:64] do
      if let some i := encRoot.get? cur then
        if isEncodingName cliques[i]! n then return some i
      match cur with
      | .str p _ _ | .num p _ _ => cur := p
      | .anonymous _ => return none
    return none
  let mut dependents : Array (Array Name) := cliques.map fun _ => #[]
  for (lo, mems) in blocks.blocks do
    let refs := blocks.blockRefs.getD lo {}
    let hits := refs.toList.filterMap encOwner
    if hits.isEmpty then continue
    for i in hits.eraseDups do
      let all := cliques[i]!
      if mems.toList.any fun m => all.contains m || isEncodingName all m then continue
      if refs.toList.any all.contains then
        for m in mems do
          unless dependents[i]!.contains m do dependents := dependents.modify i (·.push m)
  -- the table
  let mut table : Std.HashMap Name (Array Name × Array Name × String) := {}
  let mut blockRefs := blocks.blockRefs
  for i in [0:cliques.size] do
    let all := cliques[i]!
    let deps := dependents[i]!.qsort fun a b => a.pretty < b.pretty
    let carried := deps.filter (isEqLemmaOf all)
    let blocking := deps.filter (!isEqLemmaOf all ·)
    let reason := match blocking[0]? with
      | some u => s!"a dependent unfolds the encoding: {u.pretty}" ++
          (if blocking.size > 1 then s!" (and {blocking.size - 1} more)" else "")
      | none => ""
    for m in all do table := table.insert m (all, carried, reason)
    if !reason.isEmpty then continue
    for c in carried do table := table.insert c (all, carried, reason)
    -- the edges
    let members : Std.HashSet Name := all.foldl (·.insert ·) {}
    let los := all.filterMap blocks.lowLinks.get?
    let mut union : Ix.Set Name := {}
    for p in transportPrereqs do
      if blocks.lowLinks.contains p then union := union.insert p
    for lo in los do
      for r in blocks.blockRefs.getD lo {} do
        if !members.contains r then union := union.insert r
    for lo in los ++ carried.filterMap blocks.lowLinks.get? do
      let own := blocks.blocks.getD lo {}
      let mut rs := blockRefs.getD lo {}
      for r in union do
        if !own.contains r then rs := rs.insert r
      blockRefs := blockRefs.insert lo rs
  return ({ blocks with blockRefs }, table)

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

def _root_.Ix.Compile.Clique.Encoding.tag : Encoding → String
  | .wellFounded => "well-founded"
  | .structural => "structural"
  | .partialFixpoint => "partial_fixpoint"

/-- A changed clique's transport, ready for the members' blocks. -/
structure CliquePlan where
  /-- Lean's order (`all`) -/
  all : Array Name
  encoding : Encoding
  sigma : Array Nat
  classes : Array (Array Name)
  source : OrderSource
  /-- the transported members, by Lean name -/
  members : Std.HashMap Name Decl
  /-- the canonical constants, each with the Lean constant it transports -/
  canon : Array (Decl × Name)
  /-- the canonical functional(s): the side-car record goes on these -/
  functionals : Array Name
  causes : Array (Name × Cause × String)
  /-- O17: a member ↦ the representative of its class, whose constant it is -/
  aliases : Array (Name × Name) := #[]
  deriving Inhabited

/-- What the hook does with a clique. -/
inductive CliqueOutcome where
  /-- not an encoded clique (compiled as today) -/
  | notEncoded (why : String)
  /-- the canonical order is Lean's (compiled as today) -/
  | unchanged (enc : Encoding) (source : OrderSource)
  /-- the order is undetermined (`NOSPEC`) or the transport kept Lean's form
  (`SHAPE`): compiled as today -/
  | baseline (enc : Encoding) (cause : String) (why : String)
  | transported (plan : CliquePlan)
  deriving Inhabited

/-- The side-car record of a plan. -/
def CliquePlan.record (p : CliquePlan) : String :=
  let causes := p.causes.map fun (n, c, why) => s!"{n.pretty} {c.tag}: {why}"
  s!"{p.encoding.tag}; lean order {p.all.map (·.pretty)}; sigma {p.sigma}; \
    order by {p.source.tag}; classes {p.classes.map (·.map (·.pretty))}; \
    aliases (O17) {p.aliases.map fun (m, r) => s!"{m.pretty} = {r.pretty}"}; causes {causes}"

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
  let carriedOwners : Std.HashSet Name := carried.foldl (init := {}) fun s c => match c with
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

/-- Before a block compiles (hook of `Ix.Compile.Pass.prepareBlock`): for
every member of a changed clique in the block, and every equation lemma
carried with one, its transported value in the overlay with Lean's value as
the decompile record, and the canonical constants it references compiled
into the block. `rewrite` is Pass 3's call-site rewrite (for canonical
constants over a changed block). Identity when no constant of the block is
in the clique table (`CompileEnv.p3Cliques`). -/
def prepareCliques (cenv : CompileEnv) (all : Set Name)
    (rewrite : Array (Name × ConstantInfo) → Except String BlockRewrite) :
    Except String (CompileEnv × BlockState) := do
  if !cenv.pass3 || cenv.p3Cliques.isEmpty then return (cenv, {})
  let const? := cenv.env.get?
  let mut overlay := cenv.env.overlay
  let mut sources := cenv.p3Sources
  let mut k := 0
  let mut canon : Std.HashMap Name ConstantInfo := {}
  let mut wanted : Array Name := #[]
  let mut plans : Std.HashMap Name CliqueOutcome := {}
  for n in all do
    let some (cl, carried, demoted) := cenv.p3Cliques.get? n | continue
    if !demoted.isEmpty then continue
    let some key := cl[0]? | continue
    let outcome := match plans.get? key with
      | some o => o
      | none => planClique const? (cliqueAddr cenv) cl carried
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
  if k == 0 then return (cenv, {})
  -- compile the wanted canonical constants, each once its canonical
  -- references are compiled (here, or by an earlier block of the clique)
  let known (init : BlockState) (r : Name) : Bool :=
    init.blockNameToAddr.contains r || (cliqueAddr cenv r).isSome
  let mut init : BlockState := {}
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
