// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

interface IPlonkVerifier {
    function Verify(bytes calldata proof, uint256[] calldata publicInputs) external view returns (bool);
}

/// The verifier address fixes the wrapper circuit and its aggregation-program prefix.
contract IxPlonkVerifier {
    IPlonkVerifier public immutable verifier;

    constructor(IPlonkVerifier trustedVerifier) {
        require(address(trustedVerifier).code.length != 0, "missing verifier code");
        verifier = trustedVerifier;
    }

    /// The caller obtains expectedClaimDigest independently of the proof.
    function verify(bytes calldata proof, bytes32 expectedClaimDigest) external view returns (bool) {
        uint256[] memory publicInputs = new uint256[](2);
        publicInputs[0] = _reverse128(uint128(uint256(expectedClaimDigest) >> 128));
        publicInputs[1] = _reverse128(uint128(uint256(expectedClaimDigest)));
        return verifier.Verify(proof, publicInputs);
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
