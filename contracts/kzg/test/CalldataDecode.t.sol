// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

import {Bls12381} from "../src/Bls12381.sol";

contract CalldataDecodeTest {
    function memoryDecode(bytes memory point, bytes memory hint) external pure returns (bytes memory) {
        return Bls12381.decodeG1(point, hint);
    }

    function directDecode(bytes calldata point, bytes calldata hint, uint256 offset)
        external
        pure
        returns (bytes memory result)
    {
        bytes memory destination = new bytes(256);
        for (uint256 i; i < destination.length; ++i) {
            destination[i] = 0xa5;
        }
        Bls12381.decodeG1Into(point, hint, destination, offset);
        for (uint256 i; i < destination.length; ++i) {
            if (i < offset || i >= offset + 128) require(destination[i] == 0xa5, "out-of-range write");
        }
        result = new bytes(128);
        assembly ("memory-safe") { mcopy(add(result, 32), add(add(destination, 32), offset), 128) }
    }

    function _compare(bytes memory point, bytes memory hint, uint256 offset) private view {
        (bool expected, bytes memory expectedOutput) =
            address(this).staticcall(abi.encodeCall(this.memoryDecode, (point, hint)));
        (bool actual, bytes memory direct) =
            address(this).staticcall(abi.encodeCall(this.directDecode, (point, hint, offset)));
        require(actual == expected, "decode acceptance mismatch");
        require(keccak256(expectedOutput) == keccak256(direct), "decode output mismatch");
    }

    function testFuzzDirectMatchesMemory(uint128 xHi, uint256 xLo, uint128 yHi, uint256 yLo, uint8 offset) public view {
        _compare(abi.encodePacked(xHi, xLo), abi.encodePacked(yHi, yLo), uint256(offset) % 129);
    }

    function testDirectValidAndMalformedBoundaries() public view {
        bytes memory point =
            hex"97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb";
        bytes memory hint =
            hex"08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1";
        _compare(point, hint, 0);
        _compare(point, hint, 1);
        _compare(point, hint, 128);
        point[0] = 0xb7;
        _compare(point, hint, 13);
        _compare(new bytes(47), hint, 0);
        _compare(point, new bytes(47), 0);
        point = new bytes(48);
        hint = new bytes(48);
        point[0] = 0xc0;
        _compare(point, hint, 17);
        point[0] = 0x80;
        _compare(point, hint, 17);
        (bool success,) = address(this).staticcall(abi.encodeCall(this.directDecode, (point, hint, 129)));
        require(!success, "short destination accepted");
    }
}
