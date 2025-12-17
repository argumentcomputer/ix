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
deriving instance BEq, Repr, Ord, Hashable for String.Pos
deriving instance BEq, Repr, Ord, Hashable for Substring
deriving instance BEq, Repr, Ord, Hashable for Lean.SourceInfo
deriving instance BEq, Repr, Ord, Hashable for Lean.Syntax.Preresolved
deriving instance BEq, Repr, Ord, Hashable for Lean.Syntax
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

end List

def Std.HashMap.find? {A B} [BEq A] [Hashable A] (map: Std.HashMap A B) (a: A)
  := Std.HashMap.get? map a

abbrev Ix.Map := Std.HashMap
abbrev Ix.Set := Std.HashSet

abbrev MutCtx := Batteries.RBMap Lean.Name Nat compare

--instance : BEq MutCtx where
--  beq a b := a.size == b.size && a.fold
--    (fun acc k v => acc && match b.find? k with
--      | some v' => v == v'
--      | none => false) true

---- TODO: incremental comparison with ForIn zip
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

abbrev ConstList := List (Lean.Name × Lean.ConstantInfo)
private abbrev CollectM := StateM Lean.NameHashSet

private partial def collectDependenciesAux (const : Lean.ConstantInfo)
    (consts : Lean.ConstMap) (acc : ConstList) : CollectM ConstList := do
  modify (·.insert const.name)
  match const with
  | .axiomInfo val | .quotInfo val | .inductInfo val | .ctorInfo val =>
    goExpr consts acc val.type
  | .defnInfo val | .thmInfo val | .opaqueInfo val => do
    let acc ← goExpr consts acc val.type
    goExpr consts acc val.value
  | .recInfo val =>
    let acc ← goExpr consts acc val.type
    val.rules.foldlM (init := acc) fun acc rule => goExpr consts acc rule.rhs
where
  goExpr (consts : Lean.ConstMap) (acc : ConstList) : Lean.Expr → CollectM ConstList
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => pure acc
    | .const name _ => do
      let visited ← get
      if visited.contains name then pure acc
      else
        let const := consts.find! name
        collectDependenciesAux const consts $ (name, const) :: acc
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
    | .proj _ _ e => goExpr consts acc e

def collectDependencies (name : Lean.Name) (consts : Lean.ConstMap) : ConstList :=
  let const := consts.find! name
  let (constList, _) := collectDependenciesAux const consts [(name, const)] default
  constList

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
