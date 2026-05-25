module
public import Ix.Aiur.Meta
public import Ix.MultiStark.Deserialize

/-!
# PCS verification stub

`multi-stark/src/verifier.rs` calls `pcs.verify(coms_to_verify, opening_proof,
&mut challenger)` (a `TwoAdicFriPcs` FRI verification: query openings, Merkle
authentication paths, FRI folding consistency). That is the heaviest part of
the verifier and is **stubbed** here — `pcs_verify` accepts any opening proof
unconditionally.

Replacing this stub with a real FRI verifier (against the keccak Merkle commits
and the Fiat-Shamir challenger) is the remaining work for a sound recursive
verifier.
-/

public section

namespace MultiStark

def pcs := ⟦
  -- STUB: accept any FRI opening proof. Returns 1 ("accepted"). The argument is
  -- ignored; a real implementation would check query openings, Merkle paths and
  -- the FRI folding against the committed roots and sampled challenges.
  fn pcs_verify(opening: FriProof) -> G {
    1
  }
⟧

end MultiStark

end
