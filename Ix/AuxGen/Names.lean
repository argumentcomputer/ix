module
public import Ix.Environment
public section

namespace Ix.AuxGen

/-- Names of generated helpers, chosen at construction sites. The owner is
an inductive identity, not a prefix to replace in copied source expressions.
Nested indices are the source recursor's one-based slots. -/
structure AuxNames where
  privateHelpers : Bool := false
  representative : Name := Name.mkAnon
  perm : Array Nat := #[]

instance : Inhabited AuxNames := ⟨{}⟩

/-- Preserve primary recursor roles for the existing intrinsic-recursion
publication path. Derived helpers have their own reserved namespace. -/
def AuxNames.compiler (representative : Name) (perm : Array Nat) : AuxNames :=
  { privateHelpers := true, representative, perm }

def AuxNames.member (names : AuxNames) (owner : Name) (kind : String) : Name :=
  if !names.privateHelpers || kind == "rec" then Name.mkStr owner kind
  else Name.mkStr (Name.mkStr owner "_ix") kind

def AuxNames.nested (names : AuxNames) (owner : Name) (kind : String) (index : Nat) : Name :=
  if !names.privateHelpers || kind == "rec" then Name.mkStr owner s!"{kind}_{index}"
  else
    let (owner, index) := match names.perm[index - 1]? with
      | some slot => if slot != 0xFFFFFFFFFFFFFFFF then (names.representative, slot + 1)
        else (owner, index)
      | none => (owner, index)
    Name.mkStr (Name.mkStr owner "_ix") s!"{kind}_{index}"

end Ix.AuxGen
