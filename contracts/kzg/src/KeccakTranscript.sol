// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {Scalar} from "./Scalar.sol";

library KeccakTranscript {
    uint256 internal constant TWO_256_MOD_R =
        10920338887063814464675503992315976177888879664585288394250266608035967270910;
    uint256 internal constant PREFIX = 61;

    struct State {
        bytes32 chain;
        bytes observations;
        uint256 used;
    }

    function reserve(State memory self, uint256 additional) private pure {
        uint256 needed = PREFIX + self.used + additional;
        if (needed <= self.observations.length) return;
        uint256 capacity = self.observations.length;
        if (capacity < 1024) capacity = 1024;
        while (capacity < needed) capacity *= 2;
        bytes memory next = new bytes(capacity);
        bytes memory previous = self.observations;
        uint256 length = self.used;
        assembly ("memory-safe") {
            mcopy(add(next, 93), add(previous, 93), length)
        }
        self.observations = next;
    }

    function observe(State memory self, bytes memory data) internal pure {
        observeRange(self, data, 0, data.length);
    }

    function observeRange(State memory self, bytes memory data, uint256 offset, uint256 length) internal pure {
        require(offset <= data.length && length <= data.length - offset, "truncated bytes");
        reserve(self, length);
        bytes memory buffer = self.observations;
        uint256 used = self.used;
        assembly ("memory-safe") {
            mcopy(add(add(buffer, 93), used), add(add(data, 32), offset), length)
        }
        self.used += length;
    }

    function integer64(State memory self, uint256 value) internal pure {
        require(value <= type(uint64).max, "integer encoding overflow");
        reserve(self, 32);
        value = ((value >> 8) & 0x00ff00ff00ff00ff) | ((value & 0x00ff00ff00ff00ff) << 8);
        value = ((value >> 16) & 0x0000ffff0000ffff) | ((value & 0x0000ffff0000ffff) << 16);
        value = ((value >> 32) | (value << 32)) << 192;
        bytes memory buffer = self.observations;
        uint256 used = self.used;
        assembly ("memory-safe") {
            mstore(add(add(buffer, 93), used), value)
        }
        self.used += 8;
    }

    function publicTuples(State memory self, uint256[23] memory values) internal pure {
        reserve(self, 23 * 160);
        bytes memory buffer = self.observations;
        uint256 used = self.used;
        for (uint256 i; i < 23; ++i) {
            require(values[i] < Scalar.MODULUS, "noncanonical observation");
            uint256 encodedValue = Scalar.reverseBytes(values[i]);
            assembly ("memory-safe") {
                let start := add(add(buffer, 93), add(used, mul(i, 160)))
                mstore(start, shl(248, 4))
                mstore(add(start, 32), shl(248, 94))
                mstore(add(start, 64), shl(248, 1))
                mstore(add(start, 96), shl(248, i))
                mstore(add(start, 128), encodedValue)
            }
        }
        self.used += 23 * 160;
    }

    function fieldsRange(State memory self, uint256[] memory values, uint256 offset, uint256 length) internal pure {
        require(offset <= values.length && length <= values.length - offset, "truncated fields");
        reserve(self, length * 32);
        bytes memory buffer = self.observations;
        uint256 used = self.used;
        for (uint256 i; i < length; ++i) {
            uint256 value = values[offset + i];
            require(value < Scalar.MODULUS, "noncanonical observation");
            uint256 encodedValue = Scalar.reverseBytes(value);
            assembly ("memory-safe") {
                mstore(add(add(buffer, 93), add(used, mul(i, 32))), encodedValue)
            }
        }
        self.used += length * 32;
    }

    function field(State memory self, uint256 value) internal pure {
        require(value < Scalar.MODULUS, "noncanonical observation");
        reserve(self, 32);
        uint256 encoded = Scalar.reverseBytes(value);
        bytes memory buffer = self.observations;
        uint256 used = self.used;
        assembly ("memory-safe") {
            mstore(add(add(buffer, 93), used), encoded)
        }
        self.used += 32;
    }

    function sample(State memory self) internal pure returns (uint256 challenge) {
        reserve(self, 0);
        bytes memory buffer = self.observations;
        bytes32 chain = self.chain;
        uint256 length = PREFIX + self.used;
        bytes32 high;
        bytes32 low;
        bytes32 next;
        assembly ("memory-safe") {
            let start := add(buffer, 32)
            mstore(start, "multi-stark/kzg/keccak256/v1")
            mstore(add(start, 29), chain)
            mstore8(add(start, 28), 0)
            high := keccak256(start, length)
            mstore8(add(start, 28), 1)
            low := keccak256(start, length)
            mstore8(add(start, 28), 2)
            next := keccak256(start, length)
        }
        challenge = addmod(mulmod(uint256(high), TWO_256_MOD_R, Scalar.MODULUS), uint256(low), Scalar.MODULUS);
        self.chain = next;
        self.used = 0;
    }
}
