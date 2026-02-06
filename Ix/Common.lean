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
deriving instance BEq, Repr, Ord, Hashable for Lean.QuotKind
deriving instance BEq, Repr, Ord, Hashable for Lean.ReducibilityHints
deriving instance BEq, Repr, Ord, Hashable for Lean.DefinitionSafety
deriving instance BEq, Repr, Ord, Hashable for ByteArray
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
deriving instance Nonempty for Lean.Environment

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
| defn : Ix.DefKind
| opaq : Ix.DefKind
| thm : Ix.DefKind
deriving BEq, Ord, Hashable, Repr, Nonempty, Inhabited, DecidableEq

inductive Ix.DefinitionSafety where
  | unsaf : Ix.DefinitionSafety
  | safe : Ix.DefinitionSafety
  | part : Ix.DefinitionSafety
  deriving BEq, Ord, Hashable, Repr, Nonempty, Inhabited, DecidableEq

inductive Ix.QuotKind where
  | type : Ix.QuotKind
  | ctor : Ix.QuotKind
  | lift : Ix.QuotKind
  | ind : Ix.QuotKind
  deriving BEq, Ord, Hashable, Repr, Nonempty, Inhabited, DecidableEq

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

end List

def Std.HashMap.find? {A B} [BEq A] [Hashable A] (map: Std.HashMap A B) (a: A)
  := Std.HashMap.get? map a

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

end Lean
