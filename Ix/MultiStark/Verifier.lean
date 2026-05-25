module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.MultiStark.Deserialize
public import Ix.MultiStark.Keccak
public import Ix.MultiStark.Pcs

/-!
# Multi-STARK verifier (Aiur)

Reimplementation of `multi-stark/src/verifier.rs` (`System::verify_multiple_claims`)
over the deserialized `Proof` (`Ix/MultiStark/Deserialize.lean`).

The Rust verifier runs these steps:

1. **Shape check** — proof array dimensions match the system's circuit count and
   column widths.
2. **Accumulator balance** — the last intermediate accumulator is zero (all
   lookup pushes/pulls cancel).
3. **Fiat-Shamir replay** — reconstruct the Keccak challenger: observe
   commitments / trace heights / claims, sample (lookup, fingerprint, α, ζ).
4. **PCS verification** — FRI opening proofs (see `Ix/MultiStark/Pcs.lean`).
5. **OOD evaluation** — recompute the composition polynomial at ζ and check
   `composition(ζ) · inv_vanishing(ζ) == quotient(ζ)`.

### Implemented here
* Step 1 (the system-independent part): the proof is internally consistent —
  `stage_1`, `stage_2` and `intermediate_accumulators` all have the same length
  (the circuit count) and it is non-zero.
* Step 2: accumulator balance — the last `intermediate_accumulator` is the zero
  extension element.
* Step 4: the PCS check, via the accept-stub `pcs_verify`.

### Stubbed / TODO
* Steps 3 and 5 need extension-field (`GoldilocksExt2`) arithmetic, evaluation
  domains (vanishing polynomials, subgroup generators), the Keccak Fiat-Shamir
  challenger (`SerializingChallenger64<HashChallenger<u8, Keccak256Hash, 32>>`,
  which our `keccak256` can drive), and the per-circuit AIR constraint folder.
  None of that infrastructure exists in Aiur yet, so these steps are left as the
  next milestone. With the PCS stubbed and steps 3/5 absent, this verifier is a
  **structural** verifier, not yet sound.
-/

public section

namespace MultiStark

def verifier := ⟦
  -- An extension element `[c0, c1]` (`= c0 + c1·X`) is zero iff both Goldilocks
  -- coefficients are zero. (`read_ext` already reduced the limbs mod p.)
  fn ext_is_zero(e: Ext) -> G {
    eq_zero(e[0]) * eq_zero(e[1])
  }

  -- 1 iff the LAST element of the accumulator list is the zero extension
  -- element (Rust: `intermediate_accumulators.last() == Some(ExtVal::ZERO)`).
  -- The empty list returns 0 (there is no last element to balance).
  fn last_acc_is_zero(accs: List‹Ext›) -> G {
    match load(accs) {
      ListNode.Nil => 0,
      ListNode.Cons(e, rest) =>
        match load(rest) {
          ListNode.Nil => ext_is_zero(e),
          _ => last_acc_is_zero(rest),
        },
    }
  }

  -- Structural + accumulator verification of a deserialized proof.
  --
  -- Returns 1 on success; `assert_eq!` aborts the (proof) execution on any
  -- failed check, exactly as the Rust verifier returns `Err`.
  fn verify(proof: Proof) -> G {
    match proof {
      Proof.Mk(_commitments, accs, _log_degrees, opening,
               _quotient, _preprocessed, stage_1, stage_2) =>
        -- Step 1 (shape, system-independent): the per-round opened-value lists
        -- and the accumulator list all have the same length = the circuit count.
        let num_circuits = list_length(accs);
        -- there must be at least one circuit (Rust: InvalidSystem)
        assert_eq!(eq_zero(num_circuits), 0);
        assert_eq!(list_length(stage_1), num_circuits);
        assert_eq!(list_length(stage_2), num_circuits);

        -- Step 2: accumulator balance — the last accumulator must be zero.
        assert_eq!(last_acc_is_zero(accs), 1);

        -- Step 4: PCS opening proof (stubbed — accepts; see Pcs.lean).
        let _pcs = pcs_verify(opening);

        -- Steps 3 (Fiat-Shamir challenger replay over keccak) and 5 (OOD
        -- composition/quotient check) are TODO — they need ExtVal/domain math,
        -- the Keccak challenger, and the per-circuit AIR folder.
        1,
    }
  }
⟧

end MultiStark

end
