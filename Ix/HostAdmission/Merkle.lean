module

public import Ix.Address.Admission

@[expose] public section

namespace Ix.HostAdmission.Merkle

def padding : Address := ⟨ByteArray.mk (Array.replicate 32 0)⟩
def leaf (a : Address) : Address := Address.admissionHash (ByteArray.mk #[0] ++ a.hash)
def node (a b : Address) : Address := Address.admissionHash (ByteArray.mk #[1] ++ a.hash ++ b.hash)

def nextSpec : List Address → List Address
  | [] => []
  | [a] => [node a padding]
  | a :: b :: rest => node a b :: nextSpec rest

def nextAux : List Address → List Address → List Address
  | [], out => out.reverse
  | [a], out => (node a padding :: out).reverse
  | a :: b :: rest, out => nextAux rest (node a b :: out)

theorem nextAux_eq : ∀ xs out, nextAux xs out = out.reverse ++ nextSpec xs
  | [], _ => by simp [nextAux, nextSpec]
  | [_], _ => by simp [nextAux, nextSpec]
  | _ :: _ :: rest, out => by simp [nextAux, nextAux_eq rest, nextSpec, List.append_assoc]

def next (xs : List Address) : List Address := nextAux xs []
theorem next_eq (xs : List Address) : next xs = nextSpec xs := by simp [next, nextAux_eq]

theorem nextSpec_length_le : ∀ xs, (nextSpec xs).length ≤ xs.length
  | [] => by simp [nextSpec]
  | [_] => by simp [nextSpec]
  | _ :: _ :: rest => by
    simpa [nextSpec] using Nat.succ_le_succ (Nat.le_trans (nextSpec_length_le rest) (Nat.le_succ _))

theorem next_length_lt (a b : Address) (rest : List Address) :
    (next (a :: b :: rest)).length < (a :: b :: rest).length := by
  simpa [next_eq, nextSpec] using Nat.lt_of_le_of_lt (Nat.succ_le_succ (nextSpec_length_le rest))
    (Nat.lt_succ_self (rest.length + 1))

/-- Total reduction of nonempty levels; a zero hash remains a genuine root. -/
def tree : List Address → Option Address
  | [] => none
  | [a] => some a
  | a :: b :: rest => tree (next (a :: b :: rest))
termination_by xs => xs.length
decreasing_by exact next_length_lt _ _ _

theorem tree_some_of_nonempty (xs : List Address) (nonempty : xs ≠ []) :
    ∃ root, tree xs = some root := by
  induction xs using tree.induct with
  | case1 => exact False.elim (nonempty rfl)
  | case2 a => exact ⟨a, by rw [tree]⟩
  | case3 a b rest ih =>
    obtain ⟨root, accepted⟩ := ih (by simp [next_eq, nextSpec])
    exact ⟨root, by rw [tree]; exact accepted⟩

/-- Existing canonical Merkle grammar: byte-lexical sort/dedup, leaf domain0,
node domain1, and32-zero odd padding. Empty input is represented only by none. -/
def root (addresses : Array Address) : Except String (Option Address) := do
  for address in addresses do
    unless address.hash.size == 32 do throw "host root: address width is not 32 bytes"
  let sorted := addresses.qsort fun a b => a.cmpBytes b == .lt
  let unique := sorted.foldl (fun (out : List Address) a =>
    if out.head? == some a then out else a :: out) [] |>.reverse
  return tree (unique.map leaf)

end Ix.HostAdmission.Merkle
