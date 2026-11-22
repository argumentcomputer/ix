// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

interface IPlonkVerifier {
    function Verify(bytes calldata proof, uint256[] calldata publicInputs) external view returns (bool);
}

/// The verifier address and code hash fix the wrapper circuit and its aggregation-program prefix.
contract IxPlonkVerifier {
    // Malformed pairing inputs can consume all gas forwarded to a precompile.
    uint256 public constant VERIFICATION_GAS = 1_000_000;
    IPlonkVerifier public immutable verifier;
    bytes32 public immutable verifierCodeHash;

    constructor(IPlonkVerifier trustedVerifier, bytes32 trustedCodeHash) {
        require(address(trustedVerifier).code.length != 0, "missing verifier code");
        require(address(trustedVerifier).codehash == trustedCodeHash, "verifier code differs");
        verifier = trustedVerifier;
        verifierCodeHash = trustedCodeHash;
    }

    /// The caller obtains expectedClaimDigest independently of the proof.
    function verify(bytes calldata proof, bytes32 expectedClaimDigest) external view returns (bool) {
        if (address(verifier).codehash != verifierCodeHash) return false;
        uint256[] memory publicInputs = new uint256[](2);
        publicInputs[0] = _reverse128(uint128(uint256(expectedClaimDigest) >> 128));
        publicInputs[1] = _reverse128(uint128(uint256(expectedClaimDigest)));
        // EIP-150 forwards at most 63/64 of remaining gas; require enough caller gas
        // for the full VERIFICATION_GAS stipend so gas starvation reverts instead of
        // returning false on a valid proof via catch.
        require(gasleft() >= (VERIFICATION_GAS * 64) / 63 + 10_000, "insufficient gas");
        try verifier.Verify{gas: VERIFICATION_GAS}(proof, publicInputs) returns (bool valid) {
            return valid;
        } catch {
            return false;
        }
    }

    function _reverse128(uint128 value) private pure returns (uint128) {
        value = ((value >> 8) & 0x00ff00ff00ff00ff00ff00ff00ff00ff) |
            ((value & 0x00ff00ff00ff00ff00ff00ff00ff00ff) << 8);
        value = ((value >> 16) & 0x0000ffff0000ffff0000ffff0000ffff) |
            ((value & 0x0000ffff0000ffff0000ffff0000ffff) << 16);
        value = ((value >> 32) & 0x00000000ffffffff00000000ffffffff) |
            ((value & 0x00000000ffffffff00000000ffffffff) << 32);
        return (value >> 64) | (value << 64);
    }
}
