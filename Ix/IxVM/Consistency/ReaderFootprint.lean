import Ix.IxVM.Refinement.Claim
import IxC.Kernel.Ixon.Prelude

/-! # Fixed projection images used by reader reconstruction

The footprint depends only on exact raw decoding of the view and the committed record rows.
It does not inspect lazy decoded caches or depend on a chosen admission witness's limits.
-/

namespace IxVM.Consistency

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Refinement (View)

def memberProjection (owner : _root_.Address) (i : Nat) (member : Ixon.MutConst) : Ixon.Constant :=
  ⟨match member with
    | .defn _ => .dPrj ⟨i.toUInt64, owner⟩
    | .indc _ => .iPrj ⟨i.toUInt64, owner⟩
    | .recr _ => .rPrj ⟨i.toUInt64, owner⟩,
    #[], #[], #[], #[]⟩

def constructorProjection (owner : _root_.Address) (i j : Nat) : Ixon.Constant :=
  ⟨.cPrj ⟨i.toUInt64, j.toUInt64, owner⟩, #[], #[], #[], #[]⟩

def memberProjectionImages (owner : _root_.Address) (member : Ixon.MutConst) (i : Nat) : List ByteArray :=
  Ixon.serConstant (memberProjection owner i member) ::
    match member with
    | .indc ind => (List.range ind.ctors.size).map fun j => Ixon.serConstant (constructorProjection owner i j)
    | _ => []

def recordProjectionImages (owner : _root_.Address) (constant : Ixon.Constant) : List ByteArray :=
  match constant.info with
  | .muts members => members.toList.zipIdx.flatMap fun (member, i) => memberProjectionImages owner member i
  | _ => []

/-- Exact raw decoding, independent of the lazy cache and of any fixed admission limit. -/
def rawProjectionImages (owner : _root_.Address) (bytes : ByteArray) : List ByteArray :=
  match Ixon.deConstantExact bytes with
  | .ok constant => recordProjectionImages owner constant
  | .error _ => []

def derivedProjImages (V : View) : List ByteArray :=
  V.env.consts.toList.flatMap fun (owner, lc) => rawProjectionImages owner lc.rawBytes

/-- The same finite construction on committed record rows, including constructor wrappers.
Blobs are not decoded as records. -/
def committedProjImages : List ByteArray :=
  (RoleData.prelude ++ RoleData.evidence).toList.flatMap fun row =>
    match addressOfHex row.1, bytesOfHex row.2 with
    | some owner, some bytes => rawProjectionImages owner bytes
    | _, _ => []

end IxVM.Consistency
