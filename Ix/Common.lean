import Lean
import Batteries
import Batteries.Data.RBMap

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
deriving instance BEq, Repr, Ord, Ord for Lean.QuotKind
deriving instance Ord, Repr for Lean.ReducibilityHints
deriving instance BEq, Ord, Ord, Repr for Lean.DefinitionSafety
deriving instance BEq, Repr, Ord for ByteArray
deriving instance BEq, Repr, Ord for String.Pos
deriving instance BEq, Repr, Ord for Substring
deriving instance BEq, Repr, Ord for Lean.SourceInfo
deriving instance BEq, Repr, Ord for Lean.Syntax.Preresolved
deriving instance BEq, Repr, Ord for Lean.Syntax
deriving instance BEq, Repr for Ordering
deriving instance BEq, Repr, Ord for Lean.FVarId
deriving instance BEq, Repr, Ord for Lean.MVarId
deriving instance BEq, Repr, Ord for Lean.DataValue
deriving instance BEq, Repr, Ord for Lean.KVMap
deriving instance BEq, Repr, Ord for Lean.LevelMVarId
deriving instance BEq, Repr, Ord for Lean.Level
deriving instance BEq, Repr, Ord for Lean.Expr
deriving instance BEq, Repr, Ord for Lean.ConstantVal
deriving instance BEq, Repr, Ord for Lean.QuotVal
deriving instance BEq, Repr, Ord for Lean.AxiomVal
deriving instance BEq, Repr, Ord for Lean.TheoremVal
deriving instance BEq, Repr, Ord for Lean.DefinitionVal
deriving instance BEq, Repr, Ord for Lean.OpaqueVal
deriving instance BEq, Repr, Ord for Lean.RecursorRule
deriving instance BEq, Repr, Ord for Lean.RecursorVal
deriving instance BEq, Repr, Ord for Lean.ConstructorVal
deriving instance BEq, Repr, Ord for Lean.InductiveVal
deriving instance BEq, Repr, Ord for Lean.ConstantInfo

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

/-- Distinguish different kinds of Ix definitions --/
inductive Ix.DefKind where
| «definition»
| «opaque»
| «theorem»
deriving BEq, Ord, Hashable, Repr, Nonempty, Inhabited

namespace List

partial def mergeM [Monad μ] (cmp : α → α → μ Ordering) : List α → List α → μ (List α)
  | as@(a::as'), bs@(b::bs') => do
    if (← cmp a b) == Ordering.gt
    then List.cons b <$> mergeM cmp as bs'
    else List.cons a <$> mergeM cmp as' bs
  | [], bs => return bs
  | as, [] => return as

def mergePairsM [Monad μ] (cmp: α → α → μ Ordering) : List (List α) → μ (List (List α))
  | a::b::xs => List.cons <$> (mergeM cmp a b) <*> mergePairsM cmp xs
  | xs => return xs

partial def mergeAllM [Monad μ] (cmp: α → α → μ Ordering) : List (List α) → μ (List α)
  | [x] => return x
  | xs => mergePairsM cmp xs >>= mergeAllM cmp

mutual
  partial def sequencesM [Monad μ] (cmp : α → α → μ Ordering) : List α → μ (List (List α))
    | a::b::xs => do
      if (← cmp a b) == .gt
      then descendingM cmp b [a] xs
      else ascendingM cmp b (fun ys => a :: ys) xs
    | xs => return [xs]

  partial def descendingM [Monad μ] (cmp : α → α → μ Ordering) (a : α) (as : List α) : List α → μ (List (List α))
    | b::bs => do
      if (← cmp a b) == .gt
      then descendingM cmp b (a::as) bs
      else List.cons (a::as) <$> sequencesM cmp (b::bs)
    | [] => List.cons (a::as) <$> sequencesM cmp []

  partial def ascendingM [Monad μ] (cmp : α → α → μ Ordering) (a : α) (as : List α → List α) : List α → μ (List (List α))
    | b::bs => do
      if (← cmp a b) != .gt
      then ascendingM cmp b (fun ys => as (a :: ys)) bs
      else List.cons (as [a]) <$> sequencesM cmp (b::bs)
    | [] => List.cons (as [a]) <$> sequencesM cmp []

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

-- Combined sort and group operations over (List (List α))

-- Merge two sorted lists of groups, combining groups with equal elements
partial def mergeGroupsM [Monad μ] (cmp : α → α → μ Ordering)
  : List (List α) → List (List α) → μ (List (List α))
  | gs@((g@(a::_))::gs'), hs@((h@(b::_))::hs') => do
    match (← cmp a b) with
    | Ordering.lt => List.cons g <$> mergeGroupsM cmp gs' hs
    | Ordering.gt => List.cons h <$> mergeGroupsM cmp gs hs'
    | Ordering.eq => List.cons (g ++ h) <$> mergeGroupsM cmp gs' hs'  -- Combine equal groups
  | [], hs => return hs
  | gs, [] => return gs
  | _, _ => return []

-- Merge pairs of grouped lists
def mergePairsGroupsM [Monad μ] (cmp: α → α → μ Ordering) 
  : List (List (List α)) → μ (List (List (List α)))
  | a::b::xs => List.cons <$> (mergeGroupsM cmp a b) <*> mergePairsGroupsM cmp xs
  | xs => return xs

-- Merge all grouped lists
partial def mergeAllGroupsM [Monad μ] (cmp: α → α → μ Ordering) 
  : List (List (List α)) → μ (List (List α))
  | [] => return []
  | [x] => return x
  | xs => mergePairsGroupsM cmp xs >>= mergeAllGroupsM cmp

-- Helper to collect equal consecutive elements into a group
def collectEqualM [Monad μ] (cmp : α → α → μ Ordering) (x : α)
  : List α → μ (List α × List α)
  | y::ys => do
    if (← cmp x y) == Ordering.eq
    then do
      let (group, rest) ← collectEqualM cmp x ys
      return (y::group, rest)
    else return ([x], y::ys)
  | [] => return ([x], [])

mutual
  -- Build sequences of groups (ascending/descending runs with grouping)
  partial def sequencesGroupedM [Monad μ] (cmp : α → α → μ Ordering)
    : List α → μ (List (List (List α)))
    | [] => return []
    | a::xs => do
      let (aGroup, rest) ← collectEqualM cmp a xs
      match rest with
      | [] => return [[aGroup]]
      | b::bs => do
        let (bGroup, rest') ← collectEqualM cmp b bs
        if (← cmp a b) == .gt
        then descendingGroupedM cmp b bGroup [aGroup] rest'
        else ascendingGroupedM cmp b bGroup (fun gs => aGroup :: gs) rest'

  partial def descendingGroupedM [Monad μ]
    (cmp : α → α → μ Ordering) (rep : α) (curr : List α) (acc : List (List α))
    : List α → μ (List (List (List α)))
    | [] => return [curr::acc]
    | x::xs => do
      let (xGroup, rest) ← collectEqualM cmp x xs
      if (← cmp rep x) == .gt
      then descendingGroupedM cmp x xGroup (curr::acc) rest
      else List.cons (curr::acc) <$> sequencesGroupedM cmp (x::xs)

  partial def ascendingGroupedM [Monad μ]
    (cmp : α → α → μ Ordering) (rep : α) (curr : List α)
    (acc : List (List α) → List (List α))
    : List α → μ (List (List (List α)))
    | [] => return [acc [curr]]
    | x::xs => do
      let (xGroup, rest) ← collectEqualM cmp x xs
      if (← cmp rep x) != .gt
      then ascendingGroupedM cmp x xGroup (fun gs => acc (curr :: gs)) rest
      else List.cons (acc [curr]) <$> sequencesGroupedM cmp (x::xs)
end

def sortAndGroupByM [Monad μ] (xs: List α) (cmp: α -> α -> μ Ordering)
  : μ (List (List α)) :=
  sequencesGroupedM cmp xs >>= mergeAllGroupsM cmp

def sortGroupsByM [Monad μ] (xs: List (List α)) (cmp: α -> α -> μ Ordering)
  : μ (List (List α)) := sortAndGroupByM xs.flatten cmp

end List

abbrev MutCtx := Batteries.RBMap Lean.Name Nat compare

instance : BEq MutCtx where
  beq a b := a.size == b.size && a.foldl
    (fun acc k v => acc && match b.find? k with
      | some v' => v == v'
      | none => false) true

-- TODO: incremental comparison with ForIn zip
instance : Ord MutCtx where
  compare a b := compare a.toList b.toList

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
  --IO.println s!"setup-file {out.stdout}"
  --IO.println s!"setup-file {out.stderr}"
  let split := out.stdout.splitOn "\"oleanPath\":[" |>.getD 1 ""
  let split := split.splitOn "],\"loadDynlibPaths\":[" |>.getD 0 ""
  let paths := split.replace "\"" "" |>.splitOn ","|>.map System.FilePath.mk
  --IO.println s!"paths {paths}"
  Lean.initSearchPath (← Lean.findSysroot) paths

def runCmd' (cmd : String) (args : Array String) : IO $ Except String String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  return if out.exitCode != 0 then .error out.stderr
    else .ok out.stdout

def checkToolchain : IO Unit := do
  match ← runCmd' "lake" #["--version"] with
  | .error e => throw $ IO.userError e
  | .ok out =>
    let version := (out.splitOn "(Lean version ")[1]!
    let version := version.splitOn ")" |>.head!
    let expectedVersion := Lean.versionString
    if version != expectedVersion then
      IO.println s!"Warning: expected toolchain '{expectedVersion}' but got '{version}'"

open Elab in
open System (FilePath) in
def runFrontend (input : String) (filePath : FilePath) : IO Environment := do
  checkToolchain
  let inputCtx := Parser.mkInputContext input filePath.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header default messages inputCtx 0
  let env := env.setMainModule default
  let commandState := Command.mkState env messages default
  let s ← IO.processCommands inputCtx parserState commandState
  let msgs := s.commandState.messages
  if msgs.hasErrors then
    throw $ IO.userError $ "\n\n".intercalate $
      (← msgs.toList.mapM (·.toString)).map String.trim
  else return s.commandState.env

--def Expr.size: Expr -> Nat
--| .mdata _ x => 1 + x.size
--| .app f a => 1 + f.size + a.size
--| .lam bn bt b bi => 1 + bt.size + b.size
--| .forallE bn bt b bi => 1 + bt.size + b.size
--| .letE ln t v b nd =>  1 + t.size + v.size + b.size
--| .proj tn i s => 1 + s.size
--| x => 1

--def Expr.size (e : Expr) : Nat :=
--  go e 0
--where
--  go e n := match e with
--    | .mdata _ x => go x n + 1
--    | .app f a => go a (go f n + 1)
--    | .lam bn bt b bi => go bt (go b n + 1)
--    | .forallE bn bt b bi => go bt (go b n + 1)
--    | .letE ln t v b nd => go b (go v (go t n + 1))
--    | .proj tn i s => go s n + 1
--    | x => n

--def Expr.msize: Expr -> Nat
--| .mdata _ x => 1 + x.msize
--| .app f a => f.msize + a.msize
--| .lam bn bt b bi => bt.msize + b.msize
--| .forallE bn bt b bi => bt.msize + b.msize
--| .letE ln t v b nd => t.msize + v.msize + b.msize
--| .proj tn i s => s.msize
--| x => 0
--
--def Expr.stripMData : Expr -> Expr
--| .mdata _ x => x.stripMData
--| .app f a => .app f.stripMData a.stripMData
--| .lam bn bt b bi => .lam bn bt.stripMData b.stripMData bi
--| .forallE bn bt b bi => .forallE bn bt.stripMData b.stripMData bi
--| .letE ln t v b nd => .letE ln t.stripMData v.stripMData b.stripMData nd
--| .proj tn i s => .proj tn i s.stripMData
--| x@(.lit ..) => x
--| x@(.const ..) => x
--| x@(.bvar ..) => x
--| x@(.fvar ..) => x
--| x@(.sort ..) => x
--| x@(.mvar ..) => x

--def RecursorRule.stripMData : RecursorRule -> RecursorRule
--| x =>
--  dbg_trace s!"RecursorRule.stripMData"
--  match x with
--  | ⟨c, nf, rhs⟩ => ⟨c, nf, rhs.stripMData⟩
--
--def RecursorRule.size : RecursorRule -> Nat
--| ⟨c, nf, rhs⟩ => rhs.size
--
--def RecursorRule.msize : RecursorRule -> Nat
--| ⟨c, nf, rhs⟩ => rhs.msize
--
--def ConstantInfo.stripMData : Lean.ConstantInfo -> Lean.ConstantInfo
--| x =>
--  dbg_trace s!"ConstantInfo.stripMData"
--  match x with
--  | .axiomInfo x => .axiomInfo { x with type := x.type.stripMData }
--  | .defnInfo x => .defnInfo { x with type := x.type.stripMData, value := x.value.stripMData }
--  | .thmInfo x => .thmInfo { x with type := x.type.stripMData, value := x.value.stripMData }
--  | .quotInfo x => .quotInfo { x with type := x.type.stripMData }
--  | .opaqueInfo x => .opaqueInfo { x with type := x.type.stripMData, value := x.value.stripMData }
--  | .inductInfo x => .inductInfo { x with type := x.type.stripMData }
--  | .ctorInfo x => .ctorInfo { x with type := x.type.stripMData }
--  | .recInfo x => .recInfo { x with type := x.type.stripMData, rules := x.rules.map (·.stripMData) }
--
--def ConstantInfo.size : Lean.ConstantInfo -> Nat
--| .axiomInfo x => x.type.size
--| .defnInfo x => x.type.size + x.value.size
--| .thmInfo x => x.type.size + x.value.size
--| .quotInfo x => x.type.size
--| .opaqueInfo x => x.type.size + x.value.size
--| .inductInfo x => x.type.size
--| .ctorInfo x => x.type.size
--| .recInfo x => x.type.size + x.rules.foldr (fun a acc => a.size + acc) 0
--
--def ConstantInfo.msize : Lean.ConstantInfo -> Nat
--| .axiomInfo x => x.type.msize
--| .defnInfo x => x.type.msize + x.value.msize
--| .thmInfo x => x.type.msize + x.value.msize
--| .quotInfo x => x.type.msize
--| .opaqueInfo x => x.type.msize + x.value.msize
--| .inductInfo x => x.type.msize
--| .ctorInfo x => x.type.msize
--| .recInfo x => x.type.msize + x.rules.foldr (fun a acc => a.msize + acc) 0
end Lean

