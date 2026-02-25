module

public section

/-- an Ordering with a boolean strength --/
structure SOrder where
  strong: Bool
  ord: Ordering

namespace SOrder

@[inline]
def cmp : SOrder -> SOrder -> SOrder
| ⟨true, .eq⟩, y => y
| ⟨false, .eq⟩, y => ⟨false, y.ord⟩
| x, _ => x

@[inline]
def cmpM [Monad μ] (x y: μ SOrder) : μ SOrder := do
  match <- x with
  | ⟨true, .eq⟩ => y
  | ⟨false, .eq⟩ => y >>= fun ⟨_, b⟩ => pure ⟨false, b⟩
  | x => pure x

@[inline]
def cmpMany : SOrder -> List SOrder -> SOrder
| a, [] => a
| a, b::[] => cmp a b
| a, b::bs => match cmp a b with
  | x@⟨_, .eq⟩ => cmpMany x bs
  | x => x

@[specialize]
def cmpManyM [Monad μ] : μ SOrder -> List (μ SOrder) -> μ SOrder
| ma, [] => ma
| ma, mb::[] => cmpM ma mb
| ma, mb::mbs => do match (<- cmpM ma mb) with
  | x@⟨_, .eq⟩ => cmpManyM (pure x) mbs
  | x => pure x

@[specialize, inline]
def zip (f: α -> α -> SOrder) : List α -> List α -> SOrder
| [] , [] => ⟨true, .eq⟩
| [], _ => ⟨true, .lt⟩
| _, [] => ⟨true, .gt⟩
| x::xs, y::ys =>
  match f x y with
  | a@⟨_, .eq⟩ => cmp a (zip f xs ys)
  | a => a

@[specialize, inline]
def zipM [Monad μ] (f: α -> α -> μ SOrder)
  : List α -> List α -> μ SOrder
  | [] , [] => pure ⟨true, .eq⟩
  | [], _ => pure ⟨true, .lt⟩
  | _, [] => pure ⟨true, .gt⟩
  | x::xs, y::ys => do match <- (f x y) with
    | a@⟨_, .eq⟩ => cmpM (pure a) (zipM f xs ys)
    | a => pure a

end SOrder

end
