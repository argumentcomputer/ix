import IxCC.Ixon.V3.Wire
import IxCC.Ixon.Hash

/-! # Block-member keys

The address by which a member of a mutual block, or a constructor of one of its
inductives, is named: the BLAKE3 hash (`Address.blake3`, pure BLAKE3) of the
canonical bytes of its projection record, `⟨.dPrj ⟨idx, block⟩, #[], #[], #[]⟩`
and its siblings, the record `ix compile` stores for it. Ingress keys each
member and constructor by it (`Src.Ingress`), and the kernel front end checks
that the address the certified kernel's reader keys each of them by is this
one (`Src.KernelFront.Reading`). Not typing: these were kept with the erased
type checker (`IxCC.Ixon.V3.Tc`) and moved here
(`docs/kernel-front-end-design.md`, "The switch", step 2). -/

namespace IxCC.Ixon.V3

/-- The key of definition `idx` of the block at `block`. -/
def defnProjAddr (block : Address) (idx : UInt64) : Address :=
  Address.blake3 (constantBytes ⟨.dPrj ⟨idx, block⟩, #[], #[], #[]⟩)

/-- The key of inductive `idx` of the block at `block`. -/
def indcProjAddr (block : Address) (idx : UInt64) : Address :=
  Address.blake3 (constantBytes ⟨.iPrj ⟨idx, block⟩, #[], #[], #[]⟩)

/-- The key of recursor `idx` of the block at `block`. -/
def recrProjAddr (block : Address) (idx : UInt64) : Address :=
  Address.blake3 (constantBytes ⟨.rPrj ⟨idx, block⟩, #[], #[], #[]⟩)

/-- The key of constructor `cidx` of inductive `idx` of the block at `block`. -/
def ctorProjAddr (block : Address) (idx cidx : UInt64) : Address :=
  Address.blake3 (constantBytes ⟨.cPrj ⟨idx, cidx, block⟩, #[], #[], #[]⟩)

end IxCC.Ixon.V3
