/-
  Ix.Compile.Pass.Clique.PlanClique: the plan of a definition clique
  (`planClique`), and the canonical constants and transported members as
  input constants (`canonConst`, `withValue`).

  **The plan** is a function of the clique (`all`, Lean's order), its carried
  equation lemmas, the input constants (`Ix.Environment`) and the addresses
  of the clique's external references (`addr?`): every block that plans the
  clique computes the same one. It is not an encoded clique (a single member,
  a member that is not a safe definition or a theorem, members of another
  clique or referencing each other, no encoding recognised); unchanged (the
  canonical order is Lean's and no member is an alias); the baseline (the
  order is undetermined, `noSpec`, or the transport kept Lean's form,
  `shape`); or transported (`CliquePlan`).

  **Structural cliques** need the block's authenticated `below`/`brecOn`
  family (`Input.family`): `authenticatedFamily` reads it from the first
  member's `brecOn` head (`familyCandidates`) and keeps the names
  `Ix.AuxGen.SourceFamily.filterHeads` authenticates. The Rust twin computes
  it with `aux_gen::source_family::filter_heads`.

  Total and pure: the closures over the packed constant's proofs and
  equation lemmas run on `eqLemmaBound` (exhaustion is a refusal), no
  panicking access. Pretty-name sorts use `qsort`, which is not stable: two
  distinct names with one pretty form (a string component `"1"` and a number
  component `1`) may come in either order; Lean never generates such a pair
  (as in `Table`).
-/
module
public import Ix.AuxGen.SourceFamily
public import Ix.Compile.Pass.Clique.Table
public import Ix.Compile.Pass.Clique.Recover
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Name Expr ConstantInfo)

/-! ## Closures over named constants -/

/-- Push `xs` onto a stack kept as a list, top first: the last element of
`xs` ends on top (a worklist `todo ++ xs` popped from the back). -/
def pushStack (stack : List Name) (xs : Array Name) : List Name :=
  xs.foldl (fun acc x => x :: acc) stack

/-- Pop names off `stack` until one that is not in `seen`. -/
def popUnseen (seen : Std.HashSet Name) : List Name → Option (Name × List Name)
  | [] => none
  | n :: rest => if seen.contains n then popUnseen seen rest else some (n, rest)

/-- The declarations reached from `stack`: pop a name, skip it when seen,
else mark it, look it up and keep its declaration, then push the names
`next` gives for that declaration. At most `fuel` names are marked; `none`
when one more is due (an exhausted bound is a refusal). -/
def reachDecls (const? : Name → Option ConstantInfo) (next : Decl → Array Name) :
    Nat → List Name → Std.HashSet Name → Array Decl → Option (Array Decl)
  | fuel, stack, seen, out =>
    match popUnseen seen stack with
    | none => some out
    | some (n, rest) =>
      match fuel with
      | 0 => none
      | fuel + 1 =>
        match (const? n).bind Decl.ofConstantInfo? with
        | none => reachDecls const? next fuel rest (seen.insert n) out
        | some d => reachDecls const? next fuel (pushStack rest (next d)) (seen.insert n) (out.push d)

/-- Declarations in pretty-name order (see the module note on ties). -/
def sortDeclsByPretty (ds : Array Decl) : Array Decl :=
  ds.qsort fun a b => a.name.pretty < b.name.pretty

/-! ## The plan of a clique -/

/-- The abstracted proofs of a packed constant (`p._proof_k`), reached from
its type and value and from each other, in pretty-name order. At most
`eqLemmaBound` proof names are visited (as many as the clique table reads of
a member's numbered equation lemmas); `none` past it. -/
def encodingProofs (const? : Name → Option ConstantInfo) (packed : Decl) : Option (Array Decl) :=
  let isProof (n : Name) : Bool := match n with
    | .str q s _ => q == packed.name && s.startsWith "_proof_"
    | _ => false
  let next (d : Decl) : Array Name := constOccurrences isProof d.type ++ constOccurrences isProof d.value
  (reachDecls const? next eqLemmaBound (pushStack [] (next packed)) {} #[]).map sortDeclsByPretty

/-- The encoding of a clique and its constants besides the members:
* `all₀._mutual`, when the first member applies it: well-founded, with its
  abstracted proofs;
* `all₀.mutual`, when the first member projects out of it:
  `partial_fixpoint`, with its proofs;
* structural: the functionals `m._f` of every member, then the candidate
  below matchers; or, when no member has a functional and every member
  references an encoding marker (the inductive-predicate route), the
  candidate matchers alone.

The candidate matchers are the constants whose last component starts with
`match_` that the members' values reference, each once, in pretty-name
order. They are candidates only: `Structural`'s `matcherShape?` decides from
each declaration which of them are below matchers (the others are ordinary
constants of the encoding). `none`: no encoding, or the proofs' bound
exhausted. -/
def encodingOf (const? : Name → Option ConstantInfo) (all : Array Name) (members : Array Decl) :
    Option (Encoding × Array Decl) := do
  let all0 ← all[0]?
  let packedOf (s : String) : Option Decl := do
    let d ← (const? (nameStr all0 s)).bind Decl.ofConstantInfo?
    let p ← findPacked? members #[d]
    if p.name == d.name then some d else none
  if let some d := packedOf "_mutual" then
    return (.wellFounded, #[d] ++ (← encodingProofs const? d))
  if let some d := packedOf "mutual" then
    return (.partialFixpoint, #[d] ++ (← encodingProofs const? d))
  -- structural: the functionals, and the candidate below matchers
  let fs := all.filterMap fun m => (const? (nameStr m "_f")).bind Decl.ofConstantInfo?
  let matchers := (members.foldl (init := #[]) fun acc d =>
      acc ++ constOccurrences (fun n => (lastStr n).startsWith "match_") d.value).foldl
    (init := #[]) fun acc n => if acc.contains n then acc else acc.push n
  let ms := (matchers.qsort fun a b => a.pretty < b.pretty).filterMap fun n =>
    (const? n).bind Decl.ofConstantInfo?
  if fs.size == all.size then return (.structural, fs ++ ms)
  if fs.isEmpty && members.all (fun d => mentionsWhere (isEncodingMarker const?) d.value) then
    return (.structural, ms)
  none

/-- The equation lemmas of the packed constant `p` that the carried lemmas
reach (`p.eq_def`, `p.eq_unfold`, `p.eq_<k>`), transitively, in pretty-name
order. At most `eqLemmaBound` lemma names are visited; `none` past it. -/
def packedLemmas (const? : Name → Option ConstantInfo) (p : Name) (carried : Array Decl) :
    Option (Array Decl) :=
  let isPackedEq (n : Name) : Bool := match n with
    | .str q s _ => q == p && (s == "eq_def" || s == "eq_unfold" || s.startsWith "eq_")
    | _ => false
  let start := carried.foldl (fun acc d => acc ++ constOccurrences isPackedEq d.value) #[]
  (reachDecls const? (fun d => constOccurrences isPackedEq d.value) eqLemmaBound
    (pushStack [] start) {} #[]).map sortDeclsByPretty

/-- The authenticated `below`/`brecOn` family of a structural clique's block
(`Input.family`): the candidates `familyCandidates` lists for the first
member's `brecOn` head, kept by `Ix.AuxGen.SourceFamily.filterHeads` (each
name equal to what Lean's generators build from the block's source
recursors). Empty when the head is not under a recursive inductive of the
input (the structural transport then refuses). An error when the first
member is not a `brecOn` application (`memberShape`): the clique is then not
encoded. -/
def authenticatedFamily (env : Ix.Environment) (members : Array Decl) :
    Except String (Std.HashSet Name) := do
  let some m0 := members[0]? | throw "no member"
  let sh ← memberShape m0
  match familyCandidates env.get? sh.brecOnName with
  | none => pure {}
  | some (all, candidates) =>
    pure ((Ix.AuxGen.SourceFamily.filterHeads env all candidates).foldl (·.insert ·) {})

/-- The plan of a clique (`all`, Lean's order) with its carried equation
lemmas (pure; every block of the clique computes the same one). `env` is the
input (`const? := env.get?`), `addr?` the addresses of the clique's external
references (the order compares them by address). -/
def planClique (env : Ix.Environment) (addr? : Name → Option Address)
    (all carried : Array Name) : CliqueOutcome := Id.run do
  let const? := env.get?
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
    if mentionsWhere memberSet.contains d.value then
      return .notEncoded "members reference each other (a kernel mutual block)"
  let some (enc, aux) := encodingOf const? all members | return .notEncoded "no encoding recognised"
  -- the authenticated family of a structural clique's block
  let mut family : Std.HashSet Name := {}
  if enc == .structural then
    match authenticatedFamily env members with
    | .ok f => family := f
    | .error why => return .notEncoded s!"structural: {why}"
  let some all0 := all[0]? | return .notEncoded "a single member"
  let inp0 : Input := { encoding := enc, members, aux, sigma := idPerm all.size,
                        newEncName := all0, const?, family }
  let ord := cliqueOrder addr? inp0
  let .ok (σ, classes, source) := ord
    | return .baseline enc .noSpec (match ord with | .error why => why | .ok _ => "")
  -- O17: the members of a class of two or more (equal specifications) are
  -- one constant, the representative's (the first of the class in the
  -- canonical order); not when one of them carries an equation lemma, whose
  -- proof unfolds that member
  let carriedOwners : Std.HashSet Name := carried.foldl (init := {}) fun s c =>
    match (privateUserName? c).getD c with
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
          alphaEqSkipMdata (stripAllMdata md.type) (stripAllMdata repDecl.type) then
        aliases := aliases.push (m, rep)
  let identity := σ == idPerm σ.size
  if identity && aliases.isEmpty then return .unchanged enc source
  if identity then
    -- the order is Lean's, but classes merge: the aliases alone
    let mut transported : Std.HashMap Name Decl := {}
    for (m, rep) in aliases do
      if let some rd := members.find? (·.name == rep) then
        transported := transported.insert m { rd with name := m }
    return .transported { all, encoding := enc, sigma := σ, classes, source, members := transported,
                          canon := #[], functionals := #[], causes := #[], aliases }
  -- the first canonical member names the canonical encoding
  let some g := invPerm σ >>= (·[0]?) >>= (all[·]?)
    | return .baseline enc .shape "the canonical order is not a permutation of the members"
  let newEncName := match enc with
    | .wellFounded => nameStr (nameStr g ixComponent) "_mutual"
    | .partialFixpoint => nameStr (nameStr g ixComponent) "mutual"
    | .structural => g
  -- the carried lemmas: the members' own (Lean names), and the packed
  -- constant's that they reach (canonical names)
  let mut carriedDecls : Array Decl := #[]
  for c in carried do
    let some d := (const? c).bind Decl.ofConstantInfo?
      | return .baseline enc .shape s!"carried lemma {c.pretty} is not a theorem"
    carriedDecls := carriedDecls.push d
  let packedName := match aux[0]? with
    | some d => if enc == .structural then Name.mkAnon else d.name
    | none => Name.mkAnon
  let some packedLs := (if carried.isEmpty || enc == .structural then some #[] else
      packedLemmas const? packedName carriedDecls)
    | return .baseline enc .shape s!"the equation lemmas of {packedName.pretty} exceed the bound"
  let lemmas : Array (Decl × Name) := carriedDecls.map (fun d => (d, d.name)) ++
    packedLs.map fun d => (d, nameStr newEncName (lastStr d.name))
  let carriedSet : Std.HashSet Name := carried.foldl (·.insert ·) {}
  let out := transport { inp0 with sigma := σ, newEncName, lemmas }
  if out.baseline then
    return .baseline enc .shape ((out.causes[0]?).map (·.2.2) |>.getD "the transport kept Lean's form")
  -- Lean's encoding constant ↦ its canonical name
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
      unless alphaEqSkipMdata (stripAllMdata d.type) (stripAllMdata lean.type) do
        return .baseline enc .shape s!"the transported {d.name.pretty} does not have Lean's type"
      transported := transported.insert d.name d
    else
      let src := (origin.get? d.name).getD d.name
      if src == d.name then
        return .baseline enc .shape s!"an encoding constant {d.name.pretty} kept its Lean name"
      canon := canon.push (d, src)
  if transported.size != all.size + carried.size then
    return .baseline enc .shape "the transport did not return every member and carried lemma"
  for (m, rep) in aliases do
    if let some rd := transported.get? rep then
      transported := transported.insert m { rd with name := m }
  if !causes.isEmpty && !carried.isEmpty then
    -- a carried lemma must be transported exactly: a verbatim proof body
    -- would prove Lean's statement about Lean's encoding
    if causes.any (fun (c, _, _) => carriedSet.contains c || packedLs.any (·.name == c)) then
      return .baseline enc .shape "a carried equation lemma is outside the grammar"
  -- a constant the transport introduced (the composition fallback, a
  -- regenerated case split) must be in the input: otherwise Lean's form
  let leanRefs : Std.HashSet Name := (members ++ carriedDecls ++ aux ++ packedLs).foldl (init := {})
    fun s d => (constOccurrences (fun _ => true) d.type ++
      constOccurrences (fun _ => true) d.value).foldl (·.insert ·) s
  let produced : Std.HashSet Name := decls.foldl (fun s d => s.insert d.name) {}
  let introduced (c : Name) : Bool := !leanRefs.contains c && !produced.contains c
  for d in decls do
    for c in constOccurrences introduced d.type ++ constOccurrences introduced d.value do
      if (const? c).isNone then
        return .baseline enc .shape s!"{d.name.pretty} needs {c.pretty}, which is not in the input"
  let functionals := match enc with
    | .structural => canon.filterMap fun (d, _) => if lastStr d.name == "_f" then some d.name else none
    | _ => #[newEncName]
  return .transported { all, encoding := enc, sigma := σ, classes, source, members := transported,
                        canon, functionals, causes, aliases }

/-! ## Input constants -/

/-- The value of a definition or theorem. -/
def valueOf? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | _ => none

/-- Lean's constant with another value (a definition or theorem; any other
constant unchanged). -/
def withValue : ConstantInfo → Expr → ConstantInfo
  | .defnInfo v, e => .defnInfo { v with value := e }
  | .thmInfo v, e => .thmInfo { v with value := e }
  | ci, _ => ci

/-- A canonical constant as an input constant: a theorem, or a safe
definition with the hints of the Lean constant `src` it transports. With
`record? = some r` (a canonical functional, `CliquePlan.functionals`), the
value is wrapped in the side-car record `[(cliqueKey, .ofString r)]`, where
`r` is the plan's `CliquePlan.record`. -/
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

end Ix.Compile.Pass.Clique

end
