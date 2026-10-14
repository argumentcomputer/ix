// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

/// @notice BLS12-381 encodings and EIP-2537 precompile operations.
library Bls12381 {
    error InvalidLength();
    error InvalidEncoding();
    error NonCanonicalScalar();
    error PrecompileFailure(address precompile);

    uint256 private constant P_HI = 0x1a0111ea397fe69a4b1ba7b6434bacd7;
    uint256 private constant P_LO = 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab;
    uint256 private constant R = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;
    uint256 private constant G1_ADD_GAS = 375;
    uint256 private constant G1_MUL_GAS = 12_000;
    uint256 private constant PAIRING2_GAS = 102_900;
    uint256 private constant GAS_HEADROOM = 1_000;

    /// @notice Expand a canonical compressed G1 point using a supplied y-coordinate.
    /// @dev Only encoding, infinity, and the lexicographic y sign are checked here.
    /// Every variable point must subsequently enter MSM or pairing to validate its
    /// curve and subgroup membership. G1 addition alone does not check subgroups.
    /// The hint is a 48-byte big-endian field element; the result is EIP-2537's
    /// 128-byte encoding, with each coordinate padded to 64 bytes.
    function decodeG1(bytes memory compressed48, bytes memory yHint48) internal pure returns (bytes memory point128) {
        if (compressed48.length != 48 || yHint48.length != 48) revert InvalidLength();
        uint8 flags = uint8(compressed48[0]);
        (uint256 xHi, uint256 xLo) = _load48(compressed48);
        (uint256 yHi, uint256 yLo) = _load48(yHint48);
        xHi &= (uint256(1) << 125) - 1;
        _validateG1(flags, xHi, xLo, yHi, yLo);
        return abi.encode(xHi, xLo, yHi, yLo);
    }

    function decodeG1Into(bytes calldata compressed48, bytes calldata yHint48, bytes memory destination, uint256 offset)
        internal
        pure
    {
        if (compressed48.length != 48 || yHint48.length != 48 || offset + 128 > destination.length) {
            revert InvalidLength();
        }
        uint8 flags;
        uint256 xHi;
        uint256 xLo;
        uint256 yHi;
        uint256 yLo;
        assembly ("memory-safe") {
            let x := calldataload(compressed48.offset)
            flags := shr(248, x)
            xHi := and(shr(128, x), 0x1fffffffffffffffffffffffffffffff)
            xLo := calldataload(add(compressed48.offset, 16))
            yHi := shr(128, calldataload(yHint48.offset))
            yLo := calldataload(add(yHint48.offset, 16))
        }
        _validateG1(flags, xHi, xLo, yHi, yLo);
        assembly ("memory-safe") {
            let target := add(add(destination, 32), offset)
            mstore(target, xHi)
            mstore(add(target, 32), xLo)
            mstore(add(target, 64), yHi)
            mstore(add(target, 96), yLo)
        }
    }

    function _validateG1(uint8 flags, uint256 xHi, uint256 xLo, uint256 yHi, uint256 yLo) private pure {
        if ((flags & 0x80) == 0) revert InvalidEncoding();
        if ((flags & 0x40) != 0) {
            if (flags != 0xc0 || xHi != 0 || xLo != 0 || yHi != 0 || yLo != 0) revert InvalidEncoding();
        } else {
            if (!_canonical(xHi, xLo) || !_canonical(yHi, yLo)) revert InvalidEncoding();
            // EIP-2537 reserves (0, 0) for infinity; finite encodings cannot alias it.
            if (xHi == 0 && xLo == 0 && yHi == 0 && yLo == 0) revert InvalidEncoding();
            (uint256 negHi, uint256 negLo) = _negatedY(yHi, yLo);
            bool largest = yHi > negHi || (yHi == negHi && yLo > negLo);
            if (((flags & 0x20) != 0) != largest) revert InvalidEncoding();
        }
    }

    /// @notice Compute the MSM of concatenated 128-byte G1 points and canonical scalars.
    /// @dev Every input, including points with scalar zero, is passed to the precompile
    /// and receives its mandatory curve and subgroup checks.
    function msm(bytes memory concatenatedPoints128, uint256[] memory scalars)
        internal
        view
        returns (bytes memory point128)
    {
        uint256 n = scalars.length;
        if (n == 0 || concatenatedPoints128.length != n * 128) revert InvalidLength();
        bytes memory input = new bytes(n * 160);
        for (uint256 i; i < n; ++i) {
            uint256 scalar = scalars[i];
            if (scalar >= R) revert NonCanonicalScalar();
            assembly ("memory-safe") {
                let source := add(add(concatenatedPoints128, 32), mul(i, 128))
                let destination := add(add(input, 32), mul(i, 160))
                mstore(destination, mload(source))
                mstore(add(destination, 32), mload(add(source, 32)))
                mstore(add(destination, 64), mload(add(source, 64)))
                mstore(add(destination, 96), mload(add(source, 96)))
                mstore(add(destination, 128), scalar)
            }
        }
        // The undiscounted cost bounds every EIP-2537 MSM discount tier.
        return _call(address(0x0c), input, 128, G1_MUL_GAS * n);
    }

    function copyPointsInto(bytes memory points128, bytes memory records160, uint256 first) internal pure {
        if (points128.length % 128 != 0 || records160.length % 160 != 0) revert InvalidLength();
        uint256 count = points128.length / 128;
        uint256 capacity = records160.length / 160;
        if (first > capacity || count > capacity - first) revert InvalidLength();
        assembly ("memory-safe") {
            let source := add(points128, 32)
            let destination := add(add(records160, 32), mul(first, 160))
            let end := add(source, mul(count, 128))
            for {} lt(source, end) {
                source := add(source, 128)
                destination := add(destination, 160)
            } {
                mcopy(destination, source, 128)
            }
        }
    }

    /// @dev Scalars are written in place. Each selected point is passed to the
    /// precompile even when its scalar is zero. Point coordinates remain intact.
    function msmPrepared(bytes memory records160, uint256 first, uint256[] memory scalars)
        internal
        view
        returns (bytes memory point128)
    {
        uint256 n = scalars.length;
        uint256 capacity = records160.length / 160;
        if (n == 0 || records160.length % 160 != 0 || first > capacity || n > capacity - first) {
            revert InvalidLength();
        }
        uint256 errorSelector = uint32(NonCanonicalScalar.selector);
        assembly ("memory-safe") {
            let source := add(scalars, 32)
            let destination := add(add(records160, 160), mul(first, 160))
            let end := add(source, mul(n, 32))
            for {} lt(source, end) {
                source := add(source, 32)
                destination := add(destination, 160)
            } {
                let scalar := mload(source)
                if iszero(lt(scalar, R)) {
                    mstore(0, errorSelector)
                    revert(28, 4)
                }
                mstore(destination, scalar)
            }
        }
        point128 = new bytes(128);
        uint256 gasBudget = G1_MUL_GAS * n + GAS_HEADROOM;
        bool success;
        assembly ("memory-safe") {
            success := staticcall(
                gasBudget,
                0x0c,
                add(add(records160, 32), mul(first, 160)),
                mul(n, 160),
                add(point128, 32),
                128
            )
            success := and(success, eq(returndatasize(), 128))
        }
        if (!success) revert PrecompileFailure(address(0x0c));
    }

    /// @dev Addition validates curve membership but does not validate subgroups.
    function add(bytes memory a128, bytes memory b128) internal view returns (bytes memory point128) {
        if (a128.length != 128 || b128.length != 128) revert InvalidLength();
        return _call(address(0x0b), bytes.concat(a128, b128), 128, G1_ADD_GAS);
    }

    /// @dev Validates coordinate encodings, preserving infinity. Membership must be
    /// established by MSM or pairing, as for decodeG1.
    function negate(bytes memory point128) internal pure returns (bytes memory negated128) {
        if (point128.length != 128) revert InvalidLength();
        uint256 xHi;
        uint256 xLo;
        uint256 yHi;
        uint256 yLo;
        assembly ("memory-safe") {
            xHi := mload(add(point128, 32))
            xLo := mload(add(point128, 64))
            yHi := mload(add(point128, 96))
            yLo := mload(add(point128, 128))
        }
        if (!_canonical(xHi, xLo) || !_canonical(yHi, yLo)) revert InvalidEncoding();
        (yHi, yLo) = _negatedY(yHi, yLo);
        return abi.encode(xHi, xLo, yHi, yLo);
    }

    /// @notice Check e(a, h) * e(b, tau) == 1, validating all four points.
    /// @dev A well-formed but false equation returns false; malformed points revert.
    function pairing2(bytes memory a128, bytes memory h256, bytes memory b128, bytes memory tau256)
        internal
        view
        returns (bool)
    {
        if (a128.length != 128 || h256.length != 256 || b128.length != 128 || tau256.length != 256) {
            revert InvalidLength();
        }
        bytes memory output = _call(address(0x0f), bytes.concat(a128, h256, b128, tau256), 32, PAIRING2_GAS);
        uint256 result;
        assembly ("memory-safe") {
            result := mload(add(output, 32))
        }
        if (result > 1) revert PrecompileFailure(address(0x0f));
        return result == 1;
    }

    function _load48(bytes memory value) private pure returns (uint256 hi, uint256 lo) {
        assembly ("memory-safe") {
            hi := shr(128, mload(add(value, 32)))
            lo := mload(add(value, 48))
        }
    }

    function _canonical(uint256 hi, uint256 lo) private pure returns (bool) {
        return hi < P_HI || (hi == P_HI && lo < P_LO);
    }

    function _negatedY(uint256 hi, uint256 lo) private pure returns (uint256 negHi, uint256 negLo) {
        if (hi == 0 && lo == 0) return (0, 0);
        unchecked {
            negLo = P_LO - lo;
            negHi = P_HI - hi - (lo > P_LO ? 1 : 0);
        }
    }

    function _call(address precompile, bytes memory input, uint256 expectedLength, uint256 gasBudget)
        private
        view
        returns (bytes memory output)
    {
        bool success;
        // Invalid inputs consume all forwarded gas. Bound that loss by the public
        // EIP-2537 operation cost, leaving the caller gas to handle the failure.
        (success, output) = precompile.staticcall{gas: gasBudget + GAS_HEADROOM}(input);
        if (!success || output.length != expectedLength) revert PrecompileFailure(precompile);
    }
}
