module
public import IxC.Ixon.Types.Kinds
public import Lean.Data.Name
public import Lean.Expr
public import Lean.Declaration
public import Lean.Environment
public import Ix.Common.CheckerSupport
public import Lean.Elab.Frontend

public section

/-- The `ix` tool version string, `<lean version>|<ix version>` — e.g.
    `4.29.0|0.0.1`. Printed by `ix --version` and recorded in
    `ix compile --report`; external consumers gate their toolchain match
    on the Lean half, so keep the format stable. -/
def Ix.versionString : String :=
  s!"{Lean.versionString}|0.0.1"

def compareList [Ord α] : List α -> List α -> Ordering
| a::as, b::bs => match compare a b with
  | .eq => compareList as bs
  | x => x
| _::_, [] => .gt
| [], _::_ => .lt
| [], [] => .eq

def compareListM
  [Monad μ] (cmp: α -> α -> μ Ordering) : List α -> List α -> μ Ordering
| a::as, b::bs => do
  match (<- cmp a b) with
  | .eq => compareListM cmp as bs
  | x => pure x
| _::_, [] => pure .gt
| [], _::_ => pure .lt
| [], [] => pure .eq

instance [Ord α] : Ord (List α) where
  compare := compareList

instance [Ord α] [Ord β] : Ord (α × β) where
  compare a b := match compare a.fst b.fst with
    | .eq => compare a.snd b.snd
    | x => x

instance : Ord Lean.Name where
  compare := Lean.Name.cmp

deriving instance Ord for Lean.Literal
--deriving instance Ord for Lean.Expr
deriving instance Ord for Lean.BinderInfo
deriving instance BEq, Repr, Ord, Hashable for Lean.QuotKind
deriving instance BEq, Repr, Ord, Hashable for Lean.ReducibilityHints
deriving instance BEq, Repr, Ord, Hashable for Lean.DefinitionSafety
deriving instance BEq, Repr, Ord, Hashable for ByteArray

/-- The derived `BEq ByteArray` above shadows core's wherever this module is
imported. Its body compares `a.data == b.data`, and `ByteArray.data` copies the
bytes into a boxed `Array UInt8` on every call; core's `ByteArray.beq` is the
same function (`a.data == b.data`) implemented by `lean_sarray_dec_eq`
(`memcmp`). Compiled code runs core's. Audit root in
`Ix.Sharing.Verify.Audit.Statements` (`Audit.CompiledCode` requires it). -/
@[csimp] theorem instBEqByteArray_ix_beq_eq_core :
    @instBEqByteArray_ix.beq = @ByteArray.beq := by
  funext a b
  cases a; cases b; rfl
deriving instance BEq, Repr, Ord, Hashable for String.Pos.Raw
deriving instance BEq, Repr, Ord, Hashable for Substring.Raw
deriving instance BEq, Repr, Ord, Hashable for Lean.SourceInfo
deriving instance BEq, Repr, Ord, Hashable for Lean.Syntax.Preresolved
deriving instance BEq, Repr, Ord, Hashable for Lean.Syntax
deriving instance BEq, Repr, Ord, Hashable, Inhabited, Nonempty for Lean.DataValue
deriving instance BEq, Repr for Ordering
deriving instance BEq, Repr, Ord for Lean.FVarId
deriving instance BEq, Repr, Ord for Lean.MVarId
deriving instance BEq, Repr, Ord for Lean.DataValue
deriving instance BEq, Repr, Ord for Lean.KVMap
deriving instance BEq, Repr, Ord for Lean.LevelMVarId
deriving instance BEq, Repr, Ord for Lean.Level
deriving instance BEq, Repr, Ord for Lean.Expr
deriving instance BEq, Repr, Ord, Hashable, Inhabited, Nonempty for Lean.ConstantVal
deriving instance BEq, Repr, Ord, Hashable, Inhabited, Nonempty for Lean.QuotVal
deriving instance BEq, Repr, Ord, Hashable, Inhabited, Nonempty for Lean.AxiomVal
deriving instance BEq, Repr, Ord, Hashable, Inhabited, Nonempty for Lean.TheoremVal
deriving instance BEq, Repr, Ord, Hashable, Inhabited, Nonempty for Lean.DefinitionVal
deriving instance BEq, Repr, Ord, Hashable, Inhabited, Nonempty for Lean.OpaqueVal
deriving instance BEq, Repr, Ord, Hashable, Inhabited, Nonempty for Lean.RecursorRule
deriving instance BEq, Repr, Ord, Hashable, Inhabited, Nonempty for Lean.RecursorVal
deriving instance BEq, Repr, Ord, Hashable, Inhabited, Nonempty for Lean.ConstructorVal
deriving instance BEq, Repr, Ord, Hashable, Inhabited, Nonempty for Lean.InductiveVal
deriving instance BEq, Repr, Ord, Hashable, Inhabited, Nonempty for Lean.ConstantInfo

def UInt8.MAX : UInt64 := 0xFF
def UInt16.MAX : UInt64 := 0xFFFF
def UInt32.MAX : UInt64 := 0xFFFFFFFF
def UInt64.MAX : UInt64 := 0xFFFFFFFFFFFFFFFF

def UInt64.byteCount (x: UInt64) : UInt8 :=
  if      x < 0x0000000000000100 then 1
  else if x < 0x0000000000010000 then 2
  else if x < 0x0000000001000000 then 3
  else if x < 0x0000000100000000 then 4
  else if x < 0x0000010000000000 then 5
  else if x < 0x0001000000000000 then 6
  else if x < 0x0100000000000000 then 7
  else 8

def UInt64.trimmedLE (x: UInt64) : Array UInt8 :=
  if x == 0 then Array.mkArray1 0 else List.toArray (go 8 x)
  where
    go : Nat → UInt64 → List UInt8
    | _, 0 => []
    | 0, _ => []
    | Nat.succ f, x =>
      Nat.toUInt8 (UInt64.toNat x) :: go f (UInt64.shiftRight x 8)

def UInt64.fromTrimmedLE (xs: Array UInt8) : UInt64 := List.foldr step 0 xs.toList
  where
    step byte acc := UInt64.shiftLeft acc 8 + (UInt8.toUInt64 byte)

def Nat.toBytesLE (x: Nat) : Array UInt8 :=
  if x == 0 then Array.mkArray1 0 else List.toArray (go x x)
  where
    go : Nat -> Nat -> List UInt8
    | _, 0 => []
    | 0, _ => []
    | Nat.succ f, x => Nat.toUInt8 x:: go f (x / 256)

def Nat.fromBytesLE (xs: Array UInt8) : Nat :=
  (xs.toList.zipIdx 0).foldl (fun acc (b, i) => acc + (UInt8.toNat b) * 256 ^ i) 0


namespace List

def mergeM [Monad μ] (cmp : α → α → μ Ordering) :
    (as : List α) → (bs : List α) → μ (List α)
  | a::as, b::bs => do
    if (← cmp a b) == Ordering.gt
    then
      let merged ← mergeM cmp (a::as) bs
      pure (b :: merged)
    else
      let merged ← mergeM cmp as (b::bs)
      pure (a :: merged)
  | [], bs => return bs
  | as, [] => return as
termination_by as bs => as.length + bs.length
decreasing_by all_goals simp_wf

def mergePairsM [Monad μ] (cmp: α → α → μ Ordering) : List (List α) → μ (List (List α))
  | a::b::xs => do
    let merged ← mergeM cmp a b
    let rest ← mergePairsM cmp xs
    pure (merged :: rest)
  | xs => return xs

/-- Fuelled merge-round driver. `List.length` rounds are ample for every
nonempty run list; the zero case also makes the formerly divergent empty
input total while preserving all elements. -/
def mergeAllMFuel [Monad μ] (cmp : α → α → μ Ordering) :
    Nat → List (List α) → μ (List α)
  | 0, xs => return xs.flatten
  | _ + 1, [x] => return x
  | fuel + 1, xs => mergePairsM cmp xs >>= mergeAllMFuel cmp fuel

def mergeAllM [Monad μ] (cmp : α → α → μ Ordering)
    (xs : List (List α)) : μ (List α) :=
  mergeAllMFuel cmp xs.length xs

mutual
  def sequencesM [Monad μ] (cmp : α → α → μ Ordering) :
      (xs : List α) → μ (List (List α))
    | a::b::xs => do
      if (← cmp a b) == .gt
      then descendingM cmp b [a] xs
      else ascendingM cmp b (fun ys => a :: ys) xs
    | xs => return [xs]
  termination_by xs => 2 * xs.length
  decreasing_by all_goals (simp_wf <;> omega)

  def descendingM [Monad μ] (cmp : α → α → μ Ordering)
      (a : α) (as : List α) :
      (xs : List α) → μ (List (List α))
    | b::bs => do
      if (← cmp a b) == .gt
      then descendingM cmp b (a::as) bs
      else
        let rest ← sequencesM cmp (b::bs)
        pure ((a::as) :: rest)
    | [] => do
      let rest ← sequencesM cmp []
      pure ((a::as) :: rest)
  termination_by xs => 2 * xs.length + 1
  decreasing_by all_goals (simp_wf <;> omega)

  def ascendingM [Monad μ] (cmp : α → α → μ Ordering)
      (a : α) (as : List α → List α) :
      (xs : List α) → μ (List (List α))
    | b::bs => do
      if (← cmp a b) != .gt
      then ascendingM cmp b (fun ys => as (a :: ys)) bs
      else
        let rest ← sequencesM cmp (b::bs)
        pure (as [a] :: rest)
    | [] => do
      let rest ← sequencesM cmp []
      pure (as [a] :: rest)
  termination_by xs => 2 * xs.length + 1
  decreasing_by all_goals (simp_wf <;> omega)
end

def sortByM [Monad μ] (xs: List α) (cmp: α -> α -> μ Ordering) : μ (List α) :=
  sequencesM cmp xs >>= mergeAllM cmp

/--
Mergesort from least to greatest.
-/
def sortBy (cmp : α -> α -> Ordering) (xs: List α) : List α :=
  Id.run <| xs.sortByM (fun x y => pure <| cmp x y)


def sort [Ord α] (xs: List α) : List α := sortBy compare xs

def groupByMAux [Monad μ] (eq : α → α → μ Bool) : List α → List (List α) → μ (List (List α))
  | a::as, (ag::g)::gs => do match (← eq a ag) with
    | true  => groupByMAux eq as ((a::ag::g)::gs)
    | false => groupByMAux eq as ([a]::(ag::g).reverse::gs)
  | _, gs => return gs.reverse

def groupByM [Monad μ] (p : α → α → μ Bool) : List α → μ (List (List α))
  | []    => return []
  | a::as => groupByMAux p as [[a]]

def joinM [Monad μ] : List (List α) → μ (List α)
  | []      => return []
  | a :: as => do return a ++ (← joinM as)

end List

abbrev Ix.Map := Std.HashMap
abbrev Ix.Set := Std.HashSet

namespace Lean

def ConstantInfo.formatAll (c : ConstantInfo) : String :=
  match c.all with
  | [ ]
  | [_] => ""
  | all => " " ++ all.toString

def ConstantInfo.ctorName : ConstantInfo → String
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "definition"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "constructor"
  | .recInfo    _ => "recursor"

def ConstMap.childrenOfWith (map : ConstMap) (name : Name)
    (p : ConstantInfo → Bool) : List ConstantInfo :=
  map.fold (init := []) fun acc n c => match n with
  | .str n ..
  | .num n .. => if n == name && p c then c :: acc else acc
  | _ => acc

--def ConstMap.patchUnsafeRec (cs : ConstMap) : ConstMap :=
--  let unsafes : Batteries.RBSet Name compare := cs.fold (init := .empty)
--    fun acc n _ => match n with
--      | .str n "_unsafe_rec" => acc.insert n
--      | _ => acc
--  cs.map fun c => match c with
--    | .opaqueInfo o =>
--      if unsafes.contains o.name then
--        .opaqueInfo ⟨
--          o.toConstantVal, mkConst (o.name ++ `_unsafe_rec),
--          o.isUnsafe, o.levelParams ⟩
--      else .opaqueInfo o
--    | _ => c

def PersistentHashMap.filter [BEq α] [Hashable α]
    (map : PersistentHashMap α β) (p : α → β → Bool) : PersistentHashMap α β :=
  map.foldl (init := .empty) fun acc x y =>
    match p x y with
    | true => acc.insert x y
    | false => acc

def Environment.getDelta (env : Environment)
  : PersistentHashMap Name ConstantInfo :=
  env.constants.map₂.filter (fun n _ => !n.isInternal)

def Environment.getConstMap (env : Environment)
  : Std.HashMap Name ConstantInfo :=
  env.constants.map₁.filter (fun n _ => !n.isInternal)

/--
Sets the directories where `olean` files can be found.

This function must be called before `runFrontend` if the file to be compiled has
imports (the automatic imports from `Init` also count).
-/

-- TODO: parse JSON properly
-- TODO: Get import of Init and Std working
def setLibsPaths (s: String) : IO Unit := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["setup-file", s]
  }
  let split := out.stdout.splitOn "\"oleanPath\":[" |>.getD 1 ""
  let split := split.splitOn "],\"loadDynlibPaths\":[" |>.getD 0 ""
  let paths := split.replace "\"" "" |>.splitOn ","|>.map System.FilePath.mk
  Lean.initSearchPath (← Lean.findSysroot) paths

def runCmd' (cmd : String) (args : Array String) : IO $ Except String String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  return if out.exitCode != 0 then .error out.stderr
    else .ok out.stdout

def checkToolchain : IO Unit := do
  match ← runCmd' "lake" #["--version"] with
  | .error e => throw $ IO.userError e
  | .ok out =>
    let .some version := (out.splitOn "(Lean version ")[1]?
      | throw $ IO.userError s!"Could not parse Lean version from: {out}"
    let .some version := (version.splitOn ")").head?
      | throw $ IO.userError s!"Could not parse Lean version from: {out}"
    let expectedVersion := Lean.versionString
    if version != expectedVersion then
      IO.println s!"Warning: expected toolchain '{expectedVersion}' but got '{version}'"

open Elab in
open System (FilePath) in
def runFrontend (input : String) (filePath : FilePath) : IO Environment := do
  checkToolchain
  let inputCtx := Parser.mkInputContext input filePath.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  unsafe enableInitializersExecution  -- required for `processHeader`'s `loadExts := true` import
  let (env, messages) ← processHeader header default messages inputCtx 0
  let env := env.setMainModule default
  let commandState := Command.mkState env messages default
  let s ← IO.processCommands inputCtx parserState commandState
  let msgs := s.commandState.messages
  if msgs.hasErrors then
    throw $ IO.userError $ "\n\n".intercalate $
      (← msgs.toList.mapM (·.toString)).map (String.trimAscii · |>.toString)
  else return s.commandState.env

abbrev ConstList := List (Lean.Name × Lean.ConstantInfo)
private abbrev CollectM := StateM Lean.NameHashSet

/-- The other members of `name`'s auxiliary FAMILY, when `name` is one:
    `X.rec`/`.casesOn`/`.recOn`/`.below`/`.brecOn` (and `.brecOn.go`,
    `.brecOn.eq`) of an inductive `X`, or a nested auxiliary's
    `<all0>.rec_N`/`.below_N`/`.brecOn_N[.go|.eq]`. The members are the same
    suffix for every inductive in `X.all` plus, for `rec`/`below`/`brecOn`,
    every `<all0>.<suffix>_N`; only names in `consts` are returned.

    The compiler builds each family as ONE Ixon block (docs/ix_canonicity.md
    §6.0), so a dependency closure that holds one member must hold them all,
    and their dependencies: otherwise the block, and the address of every
    member, depends on the closure (a nested block's `T.brecOn.eq` shares a
    block with `T.brecOn_1.eq`, which needs `List.casesOn`). A family of a
    single (non-mutual, non-nested) inductive has no other member. A Prop
    `.below` is itself an inductive, so `X.below.casesOn` gets the other
    `.below.casesOn`s through the same rule. -/
def auxFamilySiblings (consts : Lean.ConstMap) (name : Lean.Name) :
    List Lean.Name := Id.run do
  let isBrecOnBase : Lean.Name → Bool
    | .str _ s => s == "brecOn" || s.startsWith "brecOn_"
    | _ => false
  let (base, sub) : Lean.Name × Option String := match name with
    | .str p s =>
      if (s == "go" || s == "eq") && isBrecOnBase p then (p, some s)
      else (name, none)
    | _ => (name, none)
  let .str owner last := base | return []
  let family : Option String :=
    if ["rec", "casesOn", "recOn", "below", "brecOn"].contains last then
      some last
    else
      ["rec", "below", "brecOn"].find? fun fam =>
        let rest := last.toList.drop (fam.length + 1)
        last.startsWith (fam ++ "_") && !rest.isEmpty && rest.all Char.isDigit
  let some fam := family | return []
  if sub.isSome && fam != "brecOn" then return []
  let some (.inductInfo v) := consts.find? owner | return []
  let withSub (n : Lean.Name) : Lean.Name := match sub with
    | some t => .str n t
    | none => n
  let mut out : List Lean.Name :=
    v.all.map fun m => withSub (.str m fam)
  if ["rec", "below", "brecOn"].contains fam then
    if let some all0 := v.all.head? then
      let mut i := 1
      while consts.contains (.str all0 s!"rec_{i}") do
        out := withSub (.str all0 s!"{fam}_{i}") :: out
        i := i + 1
  return out.filter fun n => n != name && consts.contains n

/-- Recursors owned by an explicit source inductive, including nested auxiliaries. -/
def sourceRecursorsOf (consts : Lean.ConstMap) (n : Lean.Name) : List Lean.Name := Id.run do
  let mut out := []
  if consts.contains (Lean.mkRecName n) then out := Lean.mkRecName n :: out
  let mut i := 1
  while consts.contains (n.str s!"rec_{i}") do
    out := n.str s!"rec_{i}" :: out
    i := i + 1
  return out

/-- Compiler support carried by a selected source declaration. A generated
`all₀._sizeOf_N` needs the existing instances of its owner's mutual family
and `SizeOf.sizeOf` after splitting. This is finite source-set completion,
not scheduler edges: source membership can cycle through an instance's own
function; O11a adds only precise cross-component scheduling dependencies.
The rest of the logical unit (equation lemmas, argument pushers, splitters)
is carried by `unitMembers` (§6.3); nothing is discovered from callers. -/
def compilerSupportOf (consts : Lean.ConstMap) (n : Lean.Name) : List Lean.Name := Id.run do
  let .str owner suffix := n | return []
  let digits := suffix.toList.drop "_sizeOf_".length
  unless suffix.startsWith "_sizeOf_" && !digits.isEmpty && digits.all Char.isDigit do return []
  let some (.inductInfo ind) := consts.find? owner | return []
  unless ind.all.head? == some owner do return []
  let some index := (String.ofList digits).toNat? | return []
  unless 0 < index && index <= ind.all.length + ind.numNested do return []
  let support := `SizeOf.sizeOf :: ind.all.map (·.str "_sizeOf_inst")
  return support.filter consts.contains

/-! ## Logical units (design document §6.2-§6.3)

The **logical unit** of a block is the block with all of its auxiliaries:
the constants Lean generates mechanically from it, eagerly (with the
declaration) or on demand (when a later declaration first asks for them).
A closure producer must carry, for every block in the closure, the whole
unit, on-demand auxiliaries included (§6.3, "On-demand auxiliaries"), so
that a block that reads its own unit (a clique its equation lemmas, O11a
its sibling's size instance) compiles in a closure as in the whole
environment.

Auxiliaries are recognised by name, under the declaration they belong to
(the **owner**): `X.s…` where `X` is a constant and the component `s` is one
Lean's generators use for `X`'s kind (`unitAuxComponent`), with anything
below it (`T.brecOn.go`, `f.match_1.splitter`, `f.match_1.eq_2`). Private
auxiliaries (`_private.M.0.f.match_1.eq_1`, `_private.M.0.T.casesOn._arg_pusher`)
are matched through their user name. The kinds are those Lean 4.34.1
generates: the inductive constructions (recursors, `casesOn`, `recOn`,
`below*`, `brecOn*`, `noConfusion*`, `ctorIdx`, `ctorElim*`, the size
functions and instances, `_sparseCasesOn_N`), the constructor theorems
(`inj`, `injEq`, `hinj`, `sizeOf_spec`, `elim`, `noConfusion`), the
encoding and equation constants of a definition (`_unary`, `_mutual`,
`_f`, `_sunfold`, `_unsafe_rec`, `_proof_N`/`proof_N`, `match_N`, `eq_N`,
`eq_def`, `eq_unfold`, the functional induction and fixpoint principles)
and the reserved names Lean realises on demand for any constant
(`congr_simp`, `hcongr_N`) or for a matcher (`splitter`, `congr_eq_N`,
`_arg_pusher`; the enum `BitVec` lemmas). The set is a name convention, so
a user declaration that happens to use one of these names under a
constant of the matching kind is carried too: a superset of the unit,
which only enlarges a closure. -/

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

/-- What a logical unit is read from (M1-h): the kind of a declaration as an
owner of auxiliaries, the roots of its unit, and the names of the
environment. The source is a Lean environment (`leanUnitView`), so that every
closure producer reads units by one definition. Units are for compilation only:
until M6R slice 6 `ix pack` also read them from a compiled environment's names
and metadata (`ixonUnitView`) to carry whole units, which it no longer does
(owner, 2026-10-07: a bundle is the root's reference closure). -/
structure UnitView where
  kind? : Lean.Name → Option UnitOwnerKind
  /-- The roots of the unit of a declaration (see `unitRoots`). -/
  roots : Lean.Name → List Lean.Name
  contains : Lean.Name → Bool
  /-- Every name, in the order the index is built in. -/
  names : Unit → List Lean.Name

/-- Is `s` a reserved component of Pass 3 (`_ix`, `_ix_retyped`, `_ix_rule`, …)?
A name with one is a compiler-generated auxiliary of the declaration it hangs
under (`c._ix`, `f._ix.fg`, `p._ix_retyped._f`, `x._ix._f`, `g._ix._mutual`) and
belongs to that declaration's logical unit (orchestrator's ruling, INT-fix,
2026-10-06). A Lean environment has no such name (the compiler refuses an
input with one), so only a compiled environment's view meets it. -/
def unitReservedComponent (s : String) : Bool :=
  s == "_ix" || s.startsWith "_ix_"

/-- The owner of `n` when `n` is an auxiliary by name: the shortest proper
prefix `X` of `n` that is a declaration and whose next component is an
auxiliary component for `X`'s kind, or a reserved component of Pass 3
(`unitReservedComponent`, any kind). A private name is tried as itself and
then through its user name. -/
def UnitView.auxOwner? (v : UnitView) (n : Lean.Name) : Option Lean.Name :=
  let walk (m : Lean.Name) : Option Lean.Name := Id.run do
    let comps := m.components
    let mut pre : Lean.Name := .anonymous
    for c in comps do
      if !pre.isAnonymous then
        if let .str .anonymous s := c then
          if let some k := v.kind? pre then
            if unitAuxComponent k s || unitReservedComponent s then return some pre
      -- component by component (`Name.append` would interpret macro scopes)
      pre := match c with
        | .str _ s => pre.str s
        | .num _ i => pre.num i
        | .anonymous => pre
    return none
  match walk n with
  | some o => some o
  | none => (Lean.privateToUserName? n).bind walk

/-- The key of the unit of a declaration `o` (the first root). -/
def UnitView.key (v : UnitView) (o : Lean.Name) : Lean.Name :=
  (v.roots o).head?.getD o

/-- Every auxiliary of the environment by the key of its owner's unit. Built
once per closure walk (a pass over the constants). -/
abbrev UnitIndex := Std.HashMap Lean.Name (Array Lean.Name)

def UnitView.index (v : UnitView) : UnitIndex := Id.run do
  let mut idx : UnitIndex := {}
  for n in v.names () do
    if let some o := v.auxOwner? n then
      let k := v.key o
      idx := idx.insert k ((idx.getD k #[]).push n)
  return idx

/-- The logical unit of `n`'s declaration: its roots and every auxiliary of
them, eager or on demand, that exists (an auxiliary stands for its owner's
unit). -/
def UnitView.members (v : UnitView) (idx : UnitIndex) (n : Lean.Name) : List Lean.Name :=
  let o := (v.auxOwner? n).getD n
  (v.roots o ++ (idx.getD (v.key o) #[]).toList).filter v.contains

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

/-- The units of a Lean environment. -/
def leanUnitView (consts : Lean.ConstMap) : UnitView where
  kind? n := (consts.find? n).bind unitOwnerKind?
  roots := unitRoots consts
  contains := consts.contains
  names _ := consts.toList.map (·.1)

def unitAuxOwner? (consts : Lean.ConstMap) (n : Lean.Name) : Option Lean.Name :=
  (leanUnitView consts).auxOwner? n

def unitKey (consts : Lean.ConstMap) (o : Lean.Name) : Lean.Name :=
  (leanUnitView consts).key o

def unitIndex (consts : Lean.ConstMap) : UnitIndex :=
  (leanUnitView consts).index

/-- The logical unit of `n`'s declaration in a Lean environment
(`UnitView.members`). -/
def unitMembers (consts : Lean.ConstMap) (idx : UnitIndex) (n : Lean.Name) : List Lean.Name :=
  (leanUnitView consts).members idx n

private partial def collectDependenciesAux (const : Lean.ConstantInfo)
    (consts : Lean.ConstMap) (acc : ConstList) (withCompilerSupport : Bool := false)
    (withCheckerSupport : Bool := false) (units : Option UnitIndex := none)
    : CollectM ConstList := do
  modify (·.insert const.name)
  -- An auxiliary's family is one compiled block: pull its other members.
  let acc ← collectNames (auxFamilySiblings consts const.name) acc
  let acc ← if withCompilerSupport then collectNames (compilerSupportOf consts const.name) acc else pure acc
  -- The whole logical unit of the declaration (§6.3): every block the
  -- closure reaches carries its eager and on-demand auxiliaries. Only for a
  -- selected scope (`withUnits`); raw collection, with or without compiler
  -- support, keeps its historical closure.
  let acc ← match units with
    | some idx => collectNames (unitMembers consts idx const.name) acc
    | none => pure acc
  let acc ← if withCheckerSupport then collectNames (checkerSupportOf consts const.name) acc else pure acc
  match const with
  | .ctorInfo val =>
    let acc ← collectNames [val.induct] acc
    goExpr consts acc val.type
  | .axiomInfo val | .quotInfo val => goExpr consts acc val.type
  | .inductInfo val =>
    let acc ← if withCompilerSupport then collectNames (sourceRecursorsOf consts val.name) acc else pure acc
    let acc ← collectNames val.all acc
    let acc ← collectNames val.ctors acc
    goExpr consts acc val.type
  | .defnInfo val | .thmInfo val | .opaqueInfo val =>
    let acc ← collectNames val.all acc
    let acc ← goExpr consts acc val.type
    goExpr consts acc val.value
  | .recInfo val =>
    let acc ← collectNames val.all acc
    -- The compiler processes a declaration's recursors as one block, and
    -- they cross-reference in rule RHSs (`A.rec`'s rule calls `A.rec_1`,
    -- `A.rec_2`'s calls `C.rec`), so the closure needs every sibling:
    -- `<ind>.rec` per block inductive plus the nested-aux `<all0>.rec_N`.
    let siblings := val.all.filterMap fun ind =>
      let n := Lean.mkRecName ind
      if consts.contains n then some n else none
    let auxSiblings : List Lean.Name := Id.run do
      let mut out := []
      let mut i := 1
      repeat
        match val.all.head? with
        | none => break
        | some base =>
          let n := Lean.Name.mkStr base s!"rec_{i}"
          if consts.contains n then
            out := n :: out
            i := i + 1
          else break
      return out
    let acc ← collectNames (siblings ++ auxSiblings) acc
    -- A nested-aux recursor's rules recurse via the external container's
    -- ctors; its evaporated form aliases that container's recursor
    -- (`List.rec`), which no collected expr mentions — pull it via each
    -- rule ctor's owning inductive.
    let extRecs := val.rules.filterMap fun rule =>
      match consts.find? rule.ctor with
      | some (.ctorInfo cv) =>
        if val.all.contains cv.induct then none
        else
          let n := Lean.mkRecName cv.induct
          if consts.contains n then some n else none
      | _ => none
    let acc ← collectNames extRecs acc
    let acc ← goExpr consts acc val.type
    val.rules.foldlM (init := acc) fun acc rule => goExpr consts acc rule.rhs
where
  collectNames all acc := do
    let visited ← get
    all.foldlM (init := acc) fun acc name => do
      -- Selected support can revisit this family through an instance's
      -- own function. Consult the live set after each recursive ingress;
      -- the raw collector retains its historical enumeration behavior.
      let visited ← if withCompilerSupport || withCheckerSupport || units.isSome then get else pure visited
      if visited.contains name then pure acc
      else
        let const := consts.find! name
        collectDependenciesAux const consts ((name, const) :: acc) withCompilerSupport withCheckerSupport units
  goExpr (consts : Lean.ConstMap) (acc : ConstList) : Lean.Expr → CollectM ConstList
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => pure acc
    | .const name _ => do
      let visited ← get
      if visited.contains name then pure acc
      else
        let const := consts.find! name
        collectDependenciesAux const consts ((name, const) :: acc) withCompilerSupport withCheckerSupport units
    | .app f a => do
      let acc ← goExpr consts acc f
      goExpr consts acc a
    | .lam _ t b _ | .forallE _ t b _ => do
      let acc ← goExpr consts acc t
      goExpr consts acc b
    | .letE _ t v b _ => do
      let acc ← goExpr consts acc t
      let acc ← goExpr consts acc v
      goExpr consts acc b
    | .mdata _ e => goExpr consts acc e
    | .proj typeName _ e => do
      let acc ← if withCompilerSupport then collectNames [typeName] acc else pure acc
      goExpr consts acc e

/-- Raw dependency closure by default. Selected compiler/checker consumers
can separately opt into source-owned compiler/recursor support and pinned-Nat
certificate ground, and `withUnits` into whole logical units (`unitMembers`,
§6.3; the selected scopes set all three). Raw callers retain the historical
closure by default. -/
def collectDependencies (name : Lean.Name) (consts : Lean.ConstMap)
    (withCompilerSupport : Bool := false) (withCheckerSupport : Bool := false)
    (withUnits : Bool := false) : ConstList :=
  let const := consts.find! name
  let units := if withUnits then some (unitIndex consts) else none
  let (constList, _) := collectDependenciesAux const consts [(name, const)] withCompilerSupport withCheckerSupport units default
  constList

/-- Bulk closure: `collectDependencies` over many roots SHARING one
    visited set, so overlapping closures walk once instead of once per
    root. For n roots over a common library the per-root variant is
    O(n × closure); this is O(union closure). -/
def collectDependenciesMany (names : Array Lean.Name)
    (consts : Lean.ConstMap) (withCompilerSupport : Bool := false)
    (withCheckerSupport : Bool := false) (withUnits : Bool := false) : ConstList := Id.run do
  let mut acc : ConstList := []
  let mut seen : Lean.NameHashSet := default
  let units := if withUnits then some (unitIndex consts) else none
  for n in names do
    if seen.contains n then continue
    let some const := consts.find? n | continue
    let (acc', seen') := collectDependenciesAux const consts ((n, const) :: acc) withCompilerSupport withCheckerSupport units seen
    acc := acc'
    seen := seen'
  return acc

end Lean

/-- Format a duration in milliseconds with appropriate unit suffix.
- `0` → `"< 1ms"`
- `1`–`999` → `"Xms"`
- `≥ 1000` → `"X.XXs"` (rounded to two decimal places) -/
def Nat.formatMs (ms : Nat) : String :=
  if ms ≥ 1000 then
    let centisecs := ms / 10
    let whole := centisecs / 100
    let frac := centisecs % 100
    let fracStr := if frac < 10 then s!"0{frac}" else s!"{frac}"
    s!"{whole}.{fracStr}s"
  else if ms > 0 then
    s!"{ms}ms"
  else
    "< 1ms"

/-- Bytes per GiB — the unit of the RAM-budget flags and every
    prover-peak log line. -/
def gibBytes : Nat := 1024 * 1024 * 1024

/-- Bytes rendered as GiB for log lines. -/
def toGib (bytes : Nat) : Float := bytes.toFloat / gibBytes.toFloat

/-- Format a byte count with appropriate unit suffix (B, kB, MB, GB). -/
def fmtBytes (n : Nat) : String :=
  if n < 1024 then s!"{n} B"
  else if n < 1024 * 1024 then
    let kb := n * 10 / 1024
    s!"{kb / 10}.{kb % 10} kB"
  else if n < gibBytes then
    let mb := n * 10 / (1024 * 1024)
    s!"{mb / 10}.{mb % 10} MB"
  else
    let gb := n * 10 / gibBytes
    s!"{gb / 10}.{gb % 10} GB"

/-- ` · rss X.Y GiB (hwm Z.W)` from `/proc/self/status`; empty where
    that file does not exist. For single-process passes VmRSS IS the
    pass's resident footprint — each progress line charts the memory
    trajectory, and the last line before a watchdog kill localizes the
    wall. -/
def Ix.rssSuffix : IO String := do
  let status ← try IO.FS.readFile "/proc/self/status" catch _ => pure ""
  if status.isEmpty then return ""
  let field (key : String) : Option Nat :=
    (status.splitOn "\n").findSome? fun line =>
      if line.startsWith key then
        ((line.splitOn " ").filter (· ≠ ""))[1]?.bind (·.toNat?)
      else none
  match field "VmRSS:", field "VmHWM:" with
  | some rss, some hwm =>
    let gib (kb : Nat) : String :=
      s!"{kb / (1024 * 1024)}.{kb * 10 / (1024 * 1024) % 10}"
    return s!" · rss {gib rss} GiB (hwm {gib hwm})"
  | _, _ => return ""

/-- Flushed progress line with the RSS trajectory: long streaming
    passes run for minutes-to-hours, and Lean's stdout block-buffers
    under redirection — an unflushed line is a line lost to a watchdog
    kill. -/
def Ix.progressLine (line : String) : IO Unit := do
  IO.println (line ++ (← Ix.rssSuffix))
  (← IO.getStdout).flush

end
