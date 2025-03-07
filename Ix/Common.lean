import Lean

-- TODO: move to a utils namespace
def compareList [Ord α] : List α -> List α -> Ordering
| a::as, b::bs => match compare a b with
  | .eq => compareList as bs
  | x => x
| _::_, [] => .gt
| [], _::_ => .lt
| [], [] => .eq

instance [Ord α] : Ord (List α) where 
  compare := compareList

instance [Ord α] [Ord β] : Ord (α × β) where 
  compare a b := match compare a.fst b.fst with
    | .eq => compare a.snd b.snd
    | x => x

instance : Ord Lean.Name where
  compare := Lean.Name.quickCmp

deriving instance Ord for Lean.Literal
deriving instance Ord for Lean.BinderInfo
deriving instance Ord for Lean.QuotKind

def UInt8.MAX : UInt64 := 0xFF
def UInt16.MAX : UInt64 := 0xFFFF
def UInt32.MAX : UInt64 := 0xFFFFFFFF
def UInt64.MAX : UInt64 := 0xFFFFFFFFFFFFFFFF

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

def sortByM [Monad μ] (xs: List α) (cmp: α -> α -> μ Ordering) (rev := false) :
    μ (List α) := do
  if rev then
    let revCmp : _ → _ → μ Ordering := fun x y => do
      match (← cmp x y) with
      | .gt => return Ordering.lt
      | .eq => return Ordering.eq
      | .lt => return Ordering.gt
    sequencesM revCmp xs >>= mergeAllM revCmp
  else
    sequencesM cmp xs >>= mergeAllM cmp

/--
Mergesort from least to greatest. To sort from greatest to
-/
def sortBy (cmp : α -> α -> Ordering) (xs: List α) (rev := false) : List α :=
  Id.run do xs.sortByM (cmp <$> · <*> ·) rev

def sort [Ord α] (xs: List α) (rev := false) : List α :=
  sortBy compare xs rev

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

end Lean
