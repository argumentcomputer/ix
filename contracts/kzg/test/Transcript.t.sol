// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;
import {KeccakTranscript} from "../src/KeccakTranscript.sol";
import {Scalar} from "../src/Scalar.sol";

contract TranscriptTest {
    using KeccakTranscript for KeccakTranscript.State;

    function _le(uint256 value, uint256 length) private pure returns (bytes memory result) {
        result = new bytes(length);
        for (uint256 i; i < length; ++i) {
            result[i] = bytes1(uint8(value));
            value >>= 8;
        }
        require(value == 0);
    }

    function _reference(bytes32 chain, bytes memory observations)
        private
        pure
        returns (uint256 challenge, bytes32 next)
    {
        bytes memory domain = "multi-stark/kzg/keccak256/v1";
        bytes32 high = keccak256(abi.encodePacked(domain, bytes1(0), chain, observations));
        bytes32 low = keccak256(abi.encodePacked(domain, bytes1(uint8(1)), chain, observations));
        next = keccak256(abi.encodePacked(domain, bytes1(uint8(2)), chain, observations));
        challenge = addmod(
            mulmod(
                uint256(high),
                10920338887063814464675503992315976177888879664585288394250266608035967270910,
                Scalar.MODULUS
            ),
            uint256(low),
            Scalar.MODULUS
        );
    }

    function testDirectAppendersPreserveBytesGrowthAndReset() public pure {
        KeccakTranscript.State memory t;
        bytes memory source = new bytes(2050);
        for (uint256 i; i < source.length; ++i) {
            source[i] = bytes1(uint8(i));
        }
        t.observeRange(source, 1, 2048);
        bytes memory expected = new bytes(2048);
        for (uint256 i; i < expected.length; ++i) {
            expected[i] = source[i + 1];
        }
        t.integer64(type(uint64).max);
        expected = bytes.concat(expected, _le(type(uint64).max, 8));
        uint256[23] memory publics;
        for (uint256 i; i < 23; ++i) {
            publics[i] = i == 22 ? Scalar.MODULUS - 1 : i * 0x123456789;
            expected = bytes.concat(expected, _le(4, 32), _le(94, 32), _le(1, 32), _le(i, 32), _le(publics[i], 32));
        }
        t.publicTuples(publics);
        uint256[] memory values = new uint256[](6);
        for (uint256 i; i < values.length; ++i) {
            values[i] = i * 1234567;
        }
        values[4] = Scalar.MODULUS - 1;
        t.fieldsRange(values, 1, 4);
        for (uint256 i = 1; i < 5; ++i) {
            expected = bytes.concat(expected, _le(values[i], 32));
        }
        (uint256 first, bytes32 chain) = _reference(bytes32(0), expected);
        require(t.sample() == first && t.chain == chain, "batched observation differs");
        t.observeRange(source, source.length, 0);
        t.fieldsRange(values, values.length, 0);
        t.integer64(0);
        t.integer64(1 << 63);
        expected = bytes.concat(_le(0, 8), _le(1 << 63, 8));
        (uint256 second, bytes32 next) = _reference(chain, expected);
        require(t.sample() == second && t.chain == next, "reuse differs");
        (uint256 third, bytes32 finalChain) = _reference(next, new bytes(0));
        require(t.sample() == third && t.chain == finalChain, "empty sample differs");
    }

    function malformed(uint256 which) external pure {
        KeccakTranscript.State memory t;
        if (which == 0) {
            t.integer64(uint256(1) << 64);
        } else if (which == 1) {
            t.observeRange(new bytes(1), 1, 1);
        } else if (which == 2) {
            t.observeRange(new bytes(1), 2, 0);
        } else if (which == 3) {
            uint256[] memory values = new uint256[](1);
            values[0] = Scalar.MODULUS;
            t.fieldsRange(values, 0, 1);
        } else if (which == 4) {
            uint256[23] memory values;
            values[22] = Scalar.MODULUS;
            t.publicTuples(values);
        } else {
            t.fieldsRange(new uint256[](1), 1, 1);
        }
    }

    function testDirectAppendersRejectOverflowAndNoncanonicalInputs() public view {
        for (uint256 i; i < 6; ++i) {
            bool rejected;
            try this.malformed(i) {
                rejected = false;
            } catch {
                rejected = true;
            }
            require(rejected, "malformed observation accepted");
        }
    }
}
