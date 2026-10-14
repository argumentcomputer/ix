module
public import Ix.Address
public import Ix.Address.Pure

public section

/-! # The admission hash

`Address.admissionHash` is the content hash the root library instantiates
the certified Ixon entries at (`Ixon.Authenticated`). Logically it is pure
BLAKE3, `Address.blake3Pure`, so every theorem about an instantiated entry is
a theorem about pure BLAKE3 (`admissionHash_eq`). It executes as the Rust
BLAKE3, `Address.blake3`, through `@[implemented_by]`: the owner approved
(2026-10-13) that substitution on the explicit, unproved assumption that the
two implementations agree on every input; `Tests.Ix.Kernel.AddressPure`
compares them on fixture inputs. It is the one such substitution the
authenticated entries admit, enumerated by name in the runtime audit
(`Ix.Kernel.Audit.assumedSubstitutions`) and in the trust-surface fence
(`Tests/Ix/Kernel/TrustSurface.lean`). It is a wrapper so that
`Address.blake3Pure` itself keeps executing as pure Lean. -/

/-- BLAKE3 for admission: pure BLAKE3, executed by the Rust backend. -/
@[expose, implemented_by Address.blake3]
def Address.admissionHash (x : ByteArray) : Address := Address.blake3Pure x

/-- The admission hash is pure BLAKE3. -/
theorem Address.admissionHash_eq : Address.admissionHash = Address.blake3Pure := rfl

end
