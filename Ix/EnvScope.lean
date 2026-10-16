/-
  Shared environment-scoping helpers for the CLI drivers: the transitive
  dependency closure and the default (unfiltered) constant list of a file.

  Lives under the `Ix.EnvScope` namespace (not top-level in a Cli module) so
  test modules can import it: `Tests.Ix.Compile.ValidateAux` carries its own
  top-level `collectDeps` mirror, and a top-level name here would collide
  with it as soon as both reach `Tests.Main`.
-/
module
public import Ix.Meta
-- The checker-support ground is derived from the kernel's role table
-- (CQX.3): host → kernel is the layering fence's allowed direction
-- (`Ix/SpecDigest.lean` does the same). This links `IxC.Kernel.Roles`'s
-- import closure into the `ix` binary.
import IxC.Kernel.Roles

public section

namespace Ix.EnvScope

/-! ## Whole logical units

A declaration's **logical unit** (design document §6.3) is its roots — an
inductive's mutual block with its constructors, a definition clique — and
every auxiliary Lean generates for them, eager or on demand, that exists in
the environment: the inductive constructions (recursors, `casesOn`,
`recOn`, `below*`, `brecOn*`, `noConfusion*`, `ctorIdx`, `ctorElim*`, the
size functions and instances, `_sparseCasesOn_N`), the constructor theorems
(`inj`, `injEq`, `hinj`, `sizeOf_spec`, `elim`, `noConfusion`), the
encoding and equation constants of a definition (`_unary`, `_mutual`, `_f`,
`_sunfold`, `_unsafe_rec`, `_proof_N`/`proof_N`, `match_N`, `eq_N`,
`eq_def`, `eq_unfold`, the functional induction and fixpoint principles)
and the reserved names Lean realises on demand for any constant
(`congr_simp`, `hcongr_N`) or for a matcher (`splitter`, `congr_eq_N`,
`_arg_pusher`; the enum `BitVec` lemmas). These belong to the unit, not to
a caller: a block may read them, so a closure that lacked them could compile
the block differently from the whole environment.

Auxiliaries are recognised by name, under the declaration they belong to
(the **owner**): `X.s…` where `X` is a constant and the component `s` is one
Lean's generators use for `X`'s kind (`unitAuxComponent`), with anything
below it (`T.brecOn.go`, `f.match_1.splitter`, `f.match_1.eq_2`). Private
auxiliaries are matched through their user name. The set is a name
convention, so a user declaration that happens to use one of these names
under a constant of the matching kind is carried too: a superset of the
unit, which only enlarges a closure. (Ported from `940e4fe6`, without the
later `UnitView` record and the `_ix` components, R01-19; off the
compiler's import path.) -/

/-- The kind of declaration an auxiliary can hang under. -/
inductive UnitOwnerKind where
  | induct | ctor | defn
  deriving BEq

/-- `s` is `pre` followed by a non-empty run of digits. -/
private def numberedComponent (s pre : String) : Bool :=
  let r := s.toList.drop pre.length
  s.startsWith pre && !r.isEmpty && r.all Char.isDigit

/-- Is `s`, directly under a constant of kind `k`, the first component of a
Lean-generated auxiliary of it? -/
def unitAuxComponent (k : UnitOwnerKind) (s : String) : Bool :=
  match k with
  | .induct =>
    ["rec", "casesOn", "recOn", "below", "brecOn", "binductionOn", "ibelow",
      "noConfusionType", "noConfusion", "_sizeOf_inst", "ctorIdx", "toCtorIdx", "ctorElim",
      "ctorElimType", "congr_simp", "enumToBitVec", "eq_iff_enumToBitVec_eq",
      "enumToBitVec_le"].contains s ||
    ["rec_", "below_", "brecOn_", "_sizeOf_", "_sparseCasesOn_", "hcongr_"].any
      (numberedComponent s ·)
  | .ctor =>
    ["elim", "inj", "injEq", "hinj", "sizeOf_spec", "noConfusion", "congr_simp"].contains s ||
    numberedComponent s "hcongr_"
  | .defn =>
    ["eq_def", "eq_unfold", "_unary", "_binary", "_mutual", "mutual", "_f", "_sunfold",
      "_unsafe_rec", "induct", "mutual_induct", "fun_cases", "induct_unfolding",
      "fixpoint_induct", "partial_correctness", "congr_simp", "_arg_pusher", "splitter",
      "match_eq_cond"].contains s ||
    ["eq_", "match_", "_proof_", "proof_", "hcongr_", "congr_eq_"].any (numberedComponent s ·)

/-- The kind of a constant as an owner of auxiliaries. -/
def unitOwnerKind? : Lean.ConstantInfo → Option UnitOwnerKind
  | .inductInfo _ => some .induct
  | .ctorInfo _ => some .ctor
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => some .defn
  | _ => none

/-- The owner of `n` when `n` is an auxiliary by name: the shortest proper
prefix `X` of `n` that is a constant and whose next component is an
auxiliary component for `X`'s kind. A private name is tried as itself and
then through its user name. -/
def unitAuxOwner? (consts : Lean.ConstMap) (n : Lean.Name) : Option Lean.Name :=
  let walk (m : Lean.Name) : Option Lean.Name := Id.run do
    let comps := m.components
    let mut pre : Lean.Name := .anonymous
    for c in comps do
      if !pre.isAnonymous then
        if let .str .anonymous s := c then
          if let some ci := consts.find? pre then
            if let some k := unitOwnerKind? ci then
              if unitAuxComponent k s then return some pre
      -- component by component (`Name.append` would interpret macro scopes)
      pre := match c with
        | .str _ s => pre.str s
        | .num _ i => pre.num i
        | .anonymous => pre
    return none
  match walk n with
  | some o => some o
  | none => (Lean.privateToUserName? n).bind walk

/-- The roots of the unit of a declaration `o`: an inductive's mutual block
with its constructors (a constructor stands for its inductive's block), a
definition clique's members, or `o` itself. -/
def unitRoots (consts : Lean.ConstMap) (o : Lean.Name) : List Lean.Name :=
  let ofInduct (all : List Lean.Name) : List Lean.Name :=
    all ++ all.flatMap fun m => match consts.find? m with
      | some (.inductInfo v) => v.ctors
      | _ => []
  match consts.find? o with
  | some (.inductInfo v) => ofInduct v.all
  | some (.ctorInfo v) => match consts.find? v.induct with
    | some (.inductInfo iv) => ofInduct iv.all
    | _ => [o]
  | some (.defnInfo v) => v.all
  | some (.thmInfo v) => v.all
  | some (.opaqueInfo v) => v.all
  | _ => [o]

/-- The key of the unit of a declaration `o` (the first root). -/
def unitKey (consts : Lean.ConstMap) (o : Lean.Name) : Lean.Name :=
  (unitRoots consts o).head?.getD o

/-- Every auxiliary of the environment by the key of its owner's unit. Built
once per closure walk (a pass over the constants). -/
abbrev UnitIndex := Std.HashMap Lean.Name (Array Lean.Name)

/-- Build the `UnitIndex` of an environment. -/
def unitIndex (consts : Lean.ConstMap) : UnitIndex := Id.run do
  let mut idx : UnitIndex := {}
  for (n, _) in consts.toList do
    if let some o := unitAuxOwner? consts n then
      let k := unitKey consts o
      idx := idx.insert k ((idx.getD k #[]).push n)
  return idx

/-- The logical unit of `n`'s declaration: its roots and every auxiliary of
them, eager or on demand, that exists in `consts` (an auxiliary stands for
its owner's unit). -/
def unitMembers (consts : Lean.ConstMap) (idx : UnitIndex) (n : Lean.Name) : List Lean.Name :=
  let o := (unitAuxOwner? consts n).getD n
  (unitRoots consts o ++ (idx.getD (unitKey consts o) #[]).toList).filter consts.contains

/-! ## Checker-support ground (CQX.3) -/

/-- Kernel names (`Ix.Kernel.Name`) as Lean names. -/
private def kernelNameToLean : Ix.Kernel.Name → Lean.Name
  | .anonymous => .anonymous
  | .str p s => .str (kernelNameToLean p) s
  | .num p n => .num (kernelNameToLean p) n

/-- Checker-support ground by Lean name: for a role-bound constant
`r.leanName`, the constants of the roles its validation needs (`Role.deps
r`) with their blocks (`Role.block`), the roots of the fold's evidence
closure (`Ix.Kernel.evidenceDepKeys`), without `r` itself. Derived from
`IxC/Kernel/Roles.lean`, not a copy: a superset of the old Nat-operation
table (`997088e9`), and exactly what `RoleTable.wf` requires of a table
that binds `r`. -/
private def checkerSupportTable : Std.HashMap Lean.Name (List Lean.Name) :=
  Ix.Kernel.Role.all.foldl (init := {}) fun m r =>
    let deps := (r.deps.flatMap Ix.Kernel.Role.block).eraseDups.filter (· != r)
    if deps.isEmpty then m
    else m.insert (kernelNameToLean r.leanName) (deps.map (kernelNameToLean ·.leanName))

/-- The checker-support ground of `n` that exists in `consts`: what the
certified checker needs beside `n` to validate it when `n` is role-bound
(a well-founded `Nat` operation's evidence mentions `Nat.mul`, which its
value does not). Existing source records only: selection never
synthesizes a constant, and the checker still validates every record it is
given. -/
def checkerSupportOf (consts : Lean.ConstMap) (n : Lean.Name) : List Lean.Name :=
  (checkerSupportTable.getD n []).filter consts.contains

/-! ## The closure collector -/

/-- The recursors Lean generated for inductive `n`: `n.rec` and the nested
auxiliaries `n.rec_1`, `n.rec_2`, … (present on the first member of a
block). -/
def recursorsOf (consts : Lean.ConstMap) (n : Lean.Name) : List Lean.Name := Id.run do
  let mut out := []
  if consts.contains (Lean.mkRecName n) then out := Lean.mkRecName n :: out
  let mut i := 1
  while consts.contains (n.str s!"rec_{i}") do
    out := n.str s!"rec_{i}" :: out
    i := i + 1
  return out

/-- What a closure carries beyond the references of its declarations. -/
structure ClosureOptions where
  /-- The recursors of every inductive reached (`recursorsOf`: `I.rec`, and
      `I.rec_N` on a nested block's first member). The certified checker
      reads an inductive block together with its recursor and declines it
      otherwise (`reader: inductive block without a recursor in the
      input`); a whole environment always has both. -/
  recursors : Bool := false
  /-- The whole logical unit of every declaration reached (`unitMembers`,
      §6.3). -/
  units : Bool := false
  /-- The checker-support ground of every declaration reached
      (`checkerSupportOf`): a closure handed to the certified checker must
      carry it, or a role-bound operation is declined. -/
  checkerSupport : Bool := false
  deriving Inhabited, BEq, Repr

/-- The options of a selected compiler/checker input. -/
def ClosureOptions.selected : ClosureOptions :=
  { recursors := true, units := true, checkerSupport := true }

/-- Collect the transitive closure of constants referenced by a set of seed
names: the one closure collector (R01-17) behind `ix compile --consts`/
`--module`/`--exclude`, the module scope of `defaultConstList`, `--local`,
`ix validate --ns`, `ix validate-lean --ns` and the closure suites.
(`Tests/Ix/Compile/ValidateAux.lean` keeps its own mirror;
`Lean.collectDependencies*` in `Ix/Common.lean` serve the `ixvm` claim
closures, whose costs are pinned, and stay raw.)

Walks each seed's type + value + recursor rules + ctor links + `all` links
(of inductives, recursors, definitions, theorems and opaques) + auxiliary
family siblings (`Lean.auxFamilySiblings`) until no new names are
discovered, plus what `opts` asks for at every visited declaration. With
`opts = {}` this is the raw collector of before, unchanged. The returned
list preserves the source environment's iteration order over the computed
name set. -/
partial def collectDeps (env : Lean.Environment) (seeds : List Lean.Name)
    (opts : ClosureOptions := {}) : List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let units : UnitIndex := if opts.units then unitIndex env.constants else {}
  let mut needed : Std.HashSet Lean.Name := {}
  let mut worklist := seeds
  while !worklist.isEmpty do
    match worklist with
    | [] => break
    | n :: rest =>
      worklist := rest
      if needed.contains n then continue
      needed := needed.insert n
      if let some ci := env.constants.find? n then
        let mut refs : Lean.NameSet := ci.type.getUsedConstantsAsSet
        -- An auxiliary's family (`A.brecOn`/`B.brecOn`/`A.brecOn_1`, …) is
        -- one compiled block: its other members, and their dependencies,
        -- must be in the closure or the block's address depends on it
        -- (`Lean.auxFamilySiblings`).
        for r in Lean.auxFamilySiblings env.constants n do refs := refs.insert r
        if opts.units then
          -- the whole logical unit of the declaration (§6.3)
          for r in unitMembers env.constants units n do refs := refs.insert r
        if opts.checkerSupport then
          for r in checkerSupportOf env.constants n do refs := refs.insert r
        match ci with
        -- A definition's `all` (its `mutual` siblings) is metadata the
        -- compiled entry names, and meta kernel ingress resolves each name
        -- through `named`: the sibling must be in the closure even when the
        -- value does not mention it (structural, well-founded and `partial`
        -- mutual definitions go through auxiliaries).
        | .defnInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do refs := refs.insert mutName
        | .thmInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do refs := refs.insert mutName
        | .opaqueInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do refs := refs.insert mutName
        | .inductInfo v =>
          if opts.recursors then
            for r in recursorsOf env.constants n do refs := refs.insert r
          for ctorName in v.ctors do
            refs := refs.insert ctorName
            if let some ctorCi := env.constants.find? ctorName then
              for r in ctorCi.type.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do
            refs := refs.insert mutName
        | .ctorInfo v =>
          refs := refs.insert v.induct
        | .recInfo v =>
          for mutName in v.all do
            refs := refs.insert mutName
          for rule in v.rules do
            for r in rule.rhs.getUsedConstantsAsSet do refs := refs.insert r
        | _ => pure ()
        for r in refs do
          if !needed.contains r then
            worklist := r :: worklist
  env.constants.toList.filter fun (n, _) => needed.contains n

/-- The closure of a selected compiler/checker input: `collectDeps` with
`ClosureOptions.selected`, so recursors, whole logical units and
checker-support ground close to the same fixed point as ordinary
references, mutual `all` members and auxiliary-family siblings. -/
def collectSelectedDeps (env : Lean.Environment) (seeds : List Lean.Name) :
    List (Lean.Name × Lean.ConstantInfo) :=
  collectDeps env seeds .selected

/-- Default (unfiltered) constant list for a file env. Classic files keep the
historical whole-import-env behavior (byte-identical artifacts). Module-mode
files seed from the module-visible surface — the `OLeanLevel.exported` name
set plus everything the file itself elaborates — closed over transitive deps
against the full-content env: referenced foreign `_private.*` proof
auxiliaries are pulled in (their content is mandatory for groundedness and
their named rows for decompile/tc lookups), while unreferenced foreign
privates stay out — the qualified-package isolation the `module` header asks
for. Content always comes from `fe.env` (full, private-level); the exported
view contributes names only. -/
def defaultConstList (fe : FileEnv) (pathStr : String)
    : IO (List (Lean.Name × Lean.ConstantInfo)) := do
  if !fe.isModule then
    return fe.env.constants.toList
  let some visible ← moduleVisibleNames pathStr
    | return fe.env.constants.toList
  let mut seeds : List Lean.Name := []
  for (n, _) in fe.env.constants.toList do
    if visible.contains n || (fe.env.getModuleIdxFor? n).isNone then
      seeds := n :: seeds
  let closed := collectDeps fe.env seeds
  IO.println s!"[env] module scope: {seeds.length} visible seed constant(s), \
{closed.length} after transitive-dep closure"
  return closed

/-- The constants the file itself elaborates (no imported module owns them),
closed as a selected input (`collectSelectedDeps`): the `--local` scope of
`ix compile` and `ix compile-lean`. A block's compiled form depends only on
its dependency closure, so on the file's own constants this scope compiles
what the whole import environment would, without recompiling the unrelated
imports. -/
def localConstList (fe : FileEnv) : List (Lean.Name × Lean.ConstantInfo) :=
  let env := fe.env
  let seeds := env.constants.toList.filterMap fun (n, _) =>
    if (env.getModuleIdxFor? n).isNone then some n else none
  collectSelectedDeps env seeds

end Ix.EnvScope

end
