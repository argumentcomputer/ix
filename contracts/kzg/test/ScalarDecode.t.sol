// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;
import {Scalar} from "../src/Scalar.sol";

contract ScalarDecodeTest {
    function bulk(bytes calldata input, uint256 offset, uint256 count) external pure returns (uint256[] memory) {
        return Scalar.readCanonicalRange(input, offset, count);
    }

    function previous(bytes calldata input, uint256 offset, uint256 count)
        external
        pure
        returns (uint256[] memory values)
    {
        values = new uint256[](count);
        for (uint256 i; i < count; ++i) {
            values[i] = Scalar.readCanonical(input, offset + i * 32);
        }
    }

    function _writeLe(bytes memory output, uint256 offset, uint256 value, uint256 length) private pure {
        for (uint256 i; i < length; ++i) {
            output[offset + i] = bytes1(uint8(value));
            value >>= 8;
        }
        require(value == 0);
    }

    function testFuzzBulkMatchesPreviousAndBytewiseEncoding(uint256[4] memory values, uint8 padding) public view {
        uint256 prefix = padding % 32;
        bytes memory encoded = new bytes(prefix + 128 + 3);
        for (uint256 i; i < 4; ++i) {
            values[i] %= Scalar.MODULUS;
            _writeLe(encoded, prefix + i * 32, values[i], 32);
        }
        uint256[] memory got = this.bulk(encoded, prefix, 4);
        uint256[] memory prior = this.previous(encoded, prefix, 4);
        for (uint256 i; i < 4; ++i) {
            require(got[i] == values[i] && got[i] == prior[i], "bulk decoder mismatch");
        }
    }

    function testFuzzReverse64MatchesBytewiseDecoder(uint64 value) public pure {
        uint256 result;
        uint256 v = value;
        for (uint256 i; i < 8; ++i) {
            result = (result << 8) | (v & 255);
            v >>= 8;
        }
        require(Scalar.reverseBytes64(value) == result, "64-bit reversal mismatch");
        require(Scalar.reverseBytes64(Scalar.reverseBytes64(value)) == value, "64-bit reversal not involution");
    }

    function testBulkBoundaryAndCanonicalityChecks() public view {
        require(this.bulk(new bytes(0), 0, 0).length == 0, "empty decode");
        require(this.bulk(new bytes(7), 7, 0).length == 0, "empty final range");
        _reject(new bytes(31), 0, 1, false);
        _reject(new bytes(32), 1, 1, false);
        _reject(new bytes(32), 33, 0, false);
        _reject(new bytes(32), type(uint256).max, 1, false);
        _reject(new bytes(32), 0, type(uint256).max, false);
        for (uint256 bad; bad < 4; ++bad) {
            bytes memory encoded = new bytes(128);
            for (uint256 i; i < 4; ++i) {
                _writeLe(encoded, i * 32, i == bad ? Scalar.MODULUS : Scalar.MODULUS - 1, 32);
            }
            _reject(encoded, 0, 4, true);
        }
        bytes memory good = new bytes(64);
        _writeLe(good, 32, Scalar.MODULUS - 1, 32);
        uint256[] memory values = this.bulk(good, 0, 2);
        require(values[0] == 0 && values[1] == Scalar.MODULUS - 1, "canonical boundary rejected");
    }

    function _reject(bytes memory input, uint256 offset, uint256 count, bool canonicality) private view {
        (bool success, bytes memory output) =
            address(this).staticcall(abi.encodeCall(this.bulk, (input, offset, count)));
        require(!success, "invalid range accepted");
        if (canonicality) {
            bytes4 selector;
            assembly ("memory-safe") { selector := mload(add(output, 32)) }
            require(selector == Scalar.NonCanonicalScalar.selector, "wrong canonicality error");
        }
    }
}
