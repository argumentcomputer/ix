// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

library Scalar {
    uint256 internal constant MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513;

    // EIP-7883 charges 4,064 gas for this inversion with fixed 32-byte operands.
    uint256 private constant MODEXP_GAS = 5_064;

    error NonCanonicalScalar();
    error ZeroDenominator();

    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return addmod(a, MODULUS - b, MODULUS);
    }

    function negate(uint256 a) internal pure returns (uint256) {
        return a == 0 ? 0 : MODULUS - a;
    }

    function inverse(uint256 a) internal view returns (uint256 result) {
        if (a == 0) revert ZeroDenominator();
        uint256 p = MODULUS;
        uint256[6] memory input = [uint256(32), 32, 32, a, p - 2, p];
        bool ok;
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            ok := staticcall(MODEXP_GAS, 5, input, 192, ptr, 32)
            ok := and(ok, eq(returndatasize(), 32))
            result := mload(ptr)
        }
        require(ok, "modexp failure");
    }

    function inverseBatch6(uint256[6] memory values) internal view returns (uint256[6] memory result) {
        uint256 product = 1;
        for (uint256 i; i < 6; ++i) {
            result[i] = product;
            product = mulmod(product, values[i], MODULUS);
        }
        uint256 productInverse = inverse(product);
        for (uint256 i = 6; i > 0;) {
            --i;
            result[i] = mulmod(result[i], productInverse, MODULUS);
            productInverse = mulmod(productInverse, values[i], MODULUS);
        }
    }

    function power(uint256 a, uint256 exponent) internal pure returns (uint256 result) {
        result = 1;
        while (exponent != 0) {
            if ((exponent & 1) != 0) result = mulmod(result, a, MODULUS);
            a = mulmod(a, a, MODULUS);
            exponent >>= 1;
        }
    }

    function powerOfTwo(uint256 a, uint256 logExponent) internal pure returns (uint256) {
        for (uint256 i; i < logExponent; ++i) {
            a = mulmod(a, a, MODULUS);
        }
        return a;
    }

    function littleEndian(uint256 value, uint256 length) internal pure returns (bytes memory result) {
        result = new bytes(length);
        if (length <= 32) {
            require(length == 32 || value >> (length * 8) == 0, "integer encoding overflow");
            uint256 swapped = reverseBytes(value);
            if (length != 0) {
                assembly ("memory-safe") { mstore(add(result, 32), swapped) }
            }
        } else {
            for (uint256 i; i < length; ++i) {
                result[i] = bytes1(uint8(value));
                value >>= 8;
            }
            require(value == 0, "integer encoding overflow");
        }
    }

    function readLittleEndian(bytes calldata input, uint256 offset, uint256 length)
        internal
        pure
        returns (uint256 result)
    {
        require(length <= 32 && offset + length <= input.length, "truncated integer");
        assembly ("memory-safe") { result := calldataload(add(input.offset, offset)) }
        result = reverseBytes(result);
        if (length < 32) result &= (uint256(1) << (length * 8)) - 1;
    }

    function reverseBytes(uint256 value) internal pure returns (uint256) {
        uint256 m = 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff;
        value = ((value >> 8) & m) | ((value & m) << 8);
        m = 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff;
        value = ((value >> 16) & m) | ((value & m) << 16);
        m = 0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff;
        value = ((value >> 32) & m) | ((value & m) << 32);
        m = 0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff;
        value = ((value >> 64) & m) | ((value & m) << 64);
        return (value >> 128) | (value << 128);
    }

    function reverseBytes64(uint64 value) internal pure returns (uint64) {
        uint256 word = value;
        word = ((word >> 8) & 0x00ff00ff00ff00ff) | ((word & 0x00ff00ff00ff00ff) << 8);
        word = ((word >> 16) & 0x0000ffff0000ffff) | ((word & 0x0000ffff0000ffff) << 16);
        return uint64((word >> 32) | (word << 32));
    }

    function readCanonicalRange(bytes calldata input, uint256 offset, uint256 count)
        internal
        pure
        returns (uint256[] memory values)
    {
        require(offset <= input.length && count <= (input.length - offset) / 32, "truncated integer");
        values = new uint256[](count);
        for (uint256 i; i < count; ++i) {
            uint256 value;
            assembly ("memory-safe") {
                value := calldataload(add(add(input.offset, offset), mul(i, 32)))
            }
            value = reverseBytes(value);
            if (value >= MODULUS) revert NonCanonicalScalar();
            assembly ("memory-safe") {
                mstore(add(add(values, 32), mul(i, 32)), value)
            }
        }
    }

    function readCanonical(bytes calldata input, uint256 offset) internal pure returns (uint256 value) {
        value = readLittleEndian(input, offset, 32);
        if (value >= MODULUS) revert NonCanonicalScalar();
    }
}
