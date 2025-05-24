import Lean
import Batteries

-- TODO: move to a utils namespace
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
  compare := Lean.Name.quickCmp

deriving instance Ord for Lean.Literal
--deriving instance Ord for Lean.Expr
deriving instance Ord for Lean.BinderInfo
deriving instance BEq, Repr, Hashable, Ord for Lean.QuotKind
deriving instance Hashable, Repr for Lean.ReducibilityHints
deriving instance BEq, Ord, Hashable, Repr for Lean.DefinitionSafety
deriving instance BEq, Repr for Lean.ConstantVal
deriving instance BEq, Repr for Lean.QuotVal
deriving instance BEq, Repr for Lean.AxiomVal
deriving instance BEq, Repr for Lean.TheoremVal
deriving instance BEq, Repr for Lean.DefinitionVal
deriving instance BEq, Repr for Lean.OpaqueVal
deriving instance BEq, Repr for Lean.RecursorRule
deriving instance BEq, Repr for Lean.RecursorVal
deriving instance BEq, Repr for Lean.ConstructorVal
deriving instance BEq, Repr for Lean.InductiveVal
deriving instance BEq, Repr for Lean.ConstantInfo
deriving instance BEq, Repr for Ordering

def UInt8.MAX : UInt64 := 0xFF
def UInt16.MAX : UInt64 := 0xFFFF
def UInt32.MAX : UInt64 := 0xFFFFFFFF
def UInt64.MAX : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Distinguish different kinds of Ix definitions --/
inductive Ix.DefMode where
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
Mergesort from least to greatest. To sort from greatest to least set `rev`
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

def Expr.stripMData : Expr -> Expr
| .mdata _ x => x.stripMData
| .app f a => .app f.stripMData a.stripMData
| .lam bn bt b bi => .lam bn bt.stripMData b.stripMData bi
| .forallE bn bt b bi => .forallE bn bt.stripMData b.stripMData bi
| .letE ln t v b nd => .letE ln t.stripMData v.stripMData b.stripMData nd
| .proj tn i s => .proj tn i s.stripMData
| x => x

def RecursorRule.stripMData : RecursorRule -> RecursorRule
| ⟨c, nf, rhs⟩ => ⟨c, nf, rhs.stripMData⟩

def ConstantInfo.stripMData : Lean.ConstantInfo -> Lean.ConstantInfo
| .axiomInfo x => .axiomInfo { x with type := x.type.stripMData }
| .defnInfo x => .defnInfo { x with type := x.type.stripMData, value := x.value.stripMData }
| .thmInfo x => .thmInfo { x with type := x.type.stripMData, value := x.value.stripMData }
| .quotInfo x => .quotInfo { x with type := x.type.stripMData }
| .opaqueInfo x => .opaqueInfo { x with type := x.type.stripMData, value := x.value.stripMData }
| .inductInfo x => .inductInfo { x with type := x.type.stripMData }
| .ctorInfo x => .ctorInfo { x with type := x.type.stripMData }
| .recInfo x => .recInfo { x with type := x.type.stripMData, rules := x.rules.map (·.stripMData) }
end Lean

