// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

interface IGroth16Verifier {
    function verifyProof(bytes calldata proof, uint256[2] calldata publicInputs) external view;
}

/// The verifier address and code hash fix the circuit, setup and aggregation program.
contract IxGroth16Verifier {
    // Malformed pairing inputs can consume all gas forwarded to a precompile.
    uint256 public constant VERIFICATION_GAS = 1_000_000;
    IGroth16Verifier public immutable verifier;
    bytes32 public immutable verifierCodeHash;

    constructor(IGroth16Verifier trustedVerifier, bytes32 trustedCodeHash) {
        require(address(trustedVerifier).code.length != 0, "missing verifier code");
        require(address(trustedVerifier).codehash == trustedCodeHash, "verifier code differs");
        verifier = trustedVerifier;
        verifierCodeHash = trustedCodeHash;
    }

    /// The caller derives expectedClaimDigest independently of the proof.
    function verify(bytes calldata proof, bytes32 expectedClaimDigest) external view returns (bool) {
        if (proof.length != 256 && proof.length != 384) return false;
        if (address(verifier).codehash != verifierCodeHash) return false;
        uint256[2] memory publicInputs = [
            uint256(_reverse128(uint128(uint256(expectedClaimDigest) >> 128))),
            uint256(_reverse128(uint128(uint256(expectedClaimDigest))))
        ];
        try verifier.verifyProof{gas: VERIFICATION_GAS}(proof, publicInputs) {
            return true;
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
