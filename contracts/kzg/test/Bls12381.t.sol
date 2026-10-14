// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

import {Bls12381} from "../src/Bls12381.sol";

contract Bls12381Test {
    uint256 private constant R = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;

    function testDecodeGeneratorAndLexicographicSign() public pure {
        bytes memory generator = _generator();
        _equal(Bls12381.decodeG1(_compressedGenerator(), _generatorY()), generator);

        bytes memory negativeCompressed = _compressedGenerator();
        negativeCompressed[0] = 0xb7;
        bytes memory negativeY =
            hex"114d1d6855d545a8aa7d76c8cf2e21f267816aef1db507c96655b9d5caac42364e6f38ba0ecb751bad54dcd6b939c2ca";
        _equal(Bls12381.decodeG1(negativeCompressed, negativeY), Bls12381.negate(generator));
        _equal(Bls12381.negate(Bls12381.negate(generator)), generator);
    }

    function testGeneratorAdditionAndMsm() public view {
        bytes memory generator = _generator();
        bytes memory twice =
            hex"000000000000000000000000000000000572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e00000000000000000000000000000000166a9d8cabc673a322fda673779d8e3822ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d28";
        bytes memory five =
            hex"0000000000000000000000000000000010e7791fb972fe014159aa33a98622da3cdc98ff707965e536d8636b5fcc5ac7a91a8c46e59a00dca575af0f18fb13dc0000000000000000000000000000000016ba437edcc6551e30c10512367494bfb6b01cc6681e8a4c3cd2501832ab5c4abc40b4578b85cbaffbf0bcd70d67c6e2";
        _equal(Bls12381.add(generator, generator), twice);
        _equal(Bls12381.msm(generator, _oneScalar(2)), twice);
        uint256[] memory scalars = new uint256[](2);
        scalars[0] = 2;
        scalars[1] = 3;
        _equal(Bls12381.msm(bytes.concat(generator, generator), scalars), five);
        _equal(Bls12381.add(generator, Bls12381.negate(generator)), new bytes(128));
    }

    function testInfinityIsCanonicalAndAccepted() public view {
        bytes memory infinity = new bytes(48);
        infinity[0] = 0xc0;
        bytes memory zero = Bls12381.decodeG1(infinity, new bytes(48));
        _equal(zero, new bytes(128));
        _equal(Bls12381.negate(zero), zero);
        _equal(Bls12381.add(_generator(), zero), _generator());
        _equal(Bls12381.msm(zero, _oneScalar(1)), zero);
        _equal(Bls12381.msm(_generator(), _oneScalar(0)), zero);
        require(Bls12381.pairing2(zero, _g2(), zero, _g2()), "infinity pairing");
    }

    function testTwoPairCheck() public view {
        bytes memory generator = _generator();
        bytes memory h = _g2();
        require(Bls12381.pairing2(generator, h, Bls12381.negate(generator), h), "valid pairing");
        require(!Bls12381.pairing2(generator, h, generator, h), "invalid pairing accepted");
    }

    function testRejectCompressedFlagsAndSign() public view {
        bytes memory compressed = _compressedGenerator();
        compressed[0] = 0x17;
        _expectRevert(abi.encodeCall(this.decode, (compressed, _generatorY())), Bls12381.InvalidEncoding.selector);
        compressed[0] = 0xb7;
        _expectRevert(abi.encodeCall(this.decode, (compressed, _generatorY())), Bls12381.InvalidEncoding.selector);
        compressed[0] = 0xd7;
        _expectRevert(abi.encodeCall(this.decode, (compressed, _generatorY())), Bls12381.InvalidEncoding.selector);
    }

    function testRejectNonCanonicalFields() public view {
        bytes memory modulus =
            hex"1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";
        _expectRevert(abi.encodeCall(this.decode, (_compressedGenerator(), modulus)), Bls12381.InvalidEncoding.selector);
        modulus[0] = 0x9a;
        _expectRevert(abi.encodeCall(this.decode, (modulus, _generatorY())), Bls12381.InvalidEncoding.selector);

        bytes memory unpadded = abi.encode(uint256(1) << 128, uint256(0), uint256(0), uint256(2));
        _expectRevert(abi.encodeCall(this.negate, (unpadded)), Bls12381.InvalidEncoding.selector);
        _expectRevert(abi.encodeCall(this.msm, (unpadded, _oneScalar(1))), Bls12381.PrecompileFailure.selector);
    }

    function testRejectInfinityAliases() public view {
        bytes memory compressed = new bytes(48);
        bytes memory hint = new bytes(48);
        compressed[0] = 0xe0;
        _expectRevert(abi.encodeCall(this.decode, (compressed, hint)), Bls12381.InvalidEncoding.selector);
        compressed[0] = 0xc0;
        compressed[47] = 0x01;
        _expectRevert(abi.encodeCall(this.decode, (compressed, hint)), Bls12381.InvalidEncoding.selector);
        compressed[47] = 0;
        hint[47] = 0x01;
        _expectRevert(abi.encodeCall(this.decode, (compressed, hint)), Bls12381.InvalidEncoding.selector);
        hint[47] = 0;
        compressed[0] = 0x80;
        _expectRevert(abi.encodeCall(this.decode, (compressed, hint)), Bls12381.InvalidEncoding.selector);
    }

    function testMsmRejectsWrongSubgroupEvenForZeroScalar() public view {
        // (0, 2) is on y^2 = x^3 + 4 and has order 3, outside the prime-order G1 subgroup.
        bytes memory compressed = new bytes(48);
        compressed[0] = 0x80;
        bytes memory hint = new bytes(48);
        hint[47] = 0x02;
        bytes memory point = Bls12381.decodeG1(compressed, hint);
        _equal(Bls12381.add(point, new bytes(128)), point);
        _expectRevert(abi.encodeCall(this.msm, (point, _oneScalar(1))), Bls12381.PrecompileFailure.selector);
        _expectRevert(abi.encodeCall(this.msm, (point, _oneScalar(0))), Bls12381.PrecompileFailure.selector);
        _expectRevert(
            abi.encodeCall(this.pairing2, (point, _g2(), new bytes(128), _g2())), Bls12381.PrecompileFailure.selector
        );
    }

    function testRejectOffCurveAndNonCanonicalScalar() public view {
        bytes memory offCurve = abi.encode(uint256(0), uint256(0), uint256(0), uint256(3));
        _expectRevert(abi.encodeCall(this.msm, (offCurve, _oneScalar(1))), Bls12381.PrecompileFailure.selector);
        _expectRevert(abi.encodeCall(this.add, (offCurve, new bytes(128))), Bls12381.PrecompileFailure.selector);
        _expectRevert(abi.encodeCall(this.msm, (_generator(), _oneScalar(R))), Bls12381.NonCanonicalScalar.selector);
    }

    function testRejectMalformedLengths() public view {
        _expectRevert(abi.encodeCall(this.decode, (new bytes(47), new bytes(48))), Bls12381.InvalidLength.selector);
        _expectRevert(abi.encodeCall(this.decode, (new bytes(48), new bytes(47))), Bls12381.InvalidLength.selector);
        _expectRevert(abi.encodeCall(this.msm, (new bytes(0), new uint256[](0))), Bls12381.InvalidLength.selector);
        _expectRevert(abi.encodeCall(this.msm, (new bytes(129), _oneScalar(1))), Bls12381.InvalidLength.selector);
        _expectRevert(abi.encodeCall(this.msm, (_generator(), new uint256[](0))), Bls12381.InvalidLength.selector);
        _expectRevert(abi.encodeCall(this.add, (new bytes(0), _generator())), Bls12381.InvalidLength.selector);
        _expectRevert(abi.encodeCall(this.negate, (new bytes(127))), Bls12381.InvalidLength.selector);
        _expectRevert(
            abi.encodeCall(this.pairing2, (_generator(), new bytes(255), _generator(), _g2())),
            Bls12381.InvalidLength.selector
        );
    }

    function testMalformedPointsHaveBoundedGasCost() public view {
        bytes memory offCurve = abi.encode(uint256(0), uint256(0), uint256(0), uint256(3));
        _expectRevertWithin(abi.encodeCall(this.add, (offCurve, new bytes(128))), 20_000);
        _expectRevertWithin(abi.encodeCall(this.msm, (offCurve, _oneScalar(1))), 35_000);
        uint256[] memory scalars = new uint256[](4);
        scalars[0] = 1;
        _expectRevertWithin(
            abi.encodeCall(this.msm, (bytes.concat(offCurve, _generator(), _generator(), _generator()), scalars)),
            70_000
        );
        _expectRevertWithin(abi.encodeCall(this.pairing2, (offCurve, _g2(), new bytes(128), _g2())), 140_000);
    }

    function testPreparedMsmReusesBufferWithoutAliasingOutputs() public view {
        bytes memory generator = _generator();
        bytes memory original = bytes.concat(generator, generator, generator);
        bytes memory records = new bytes(3 * 160);
        Bls12381.copyPointsInto(original, records, 0);
        uint256[] memory scalars = new uint256[](2);
        scalars[0] = 2;
        scalars[1] = 3;
        bytes memory left = Bls12381.msmPrepared(records, 1, scalars);
        bytes32 leftDigest = keccak256(left);
        _equal(left, Bls12381.msm(generator, _oneScalar(5)));
        bytes memory right = Bls12381.msmPrepared(records, 2, _oneScalar(4));
        _equal(right, Bls12381.msm(generator, _oneScalar(4)));
        require(keccak256(left) == leftDigest, "second MSM overwrote first output");
        uint256 untouched;
        uint256 firstScalar;
        uint256 lastScalar;
        assembly ("memory-safe") {
            untouched := mload(add(records, 160))
            firstScalar := mload(add(records, 320))
            lastScalar := mload(add(records, 480))
        }
        require(untouched == 0 && firstScalar == 2 && lastScalar == 4, "wrong scalar record changed");
        bytes memory preserved = new bytes(3 * 128);
        assembly ("memory-safe") {
            mcopy(add(preserved, 32), add(records, 32), 128)
            mcopy(add(preserved, 160), add(records, 192), 128)
            mcopy(add(preserved, 288), add(records, 352), 128)
        }
        _equal(preserved, original);
        right[0] ^= 0x01;
        require(keccak256(left) == leftDigest, "MSM outputs alias");
        scalars = new uint256[](3);
        scalars[1] = 1;
        _equal(Bls12381.msmPrepared(records, 0, scalars), generator);
        require(keccak256(left) == leftDigest, "buffer reuse overwrote output");
    }

    function testPreparedMsmChecksBoundsScalarsAndAliases() public view {
        bytes memory records = new bytes(160);
        Bls12381.copyPointsInto(_generator(), records, 0);
        _expectRevert(abi.encodeCall(this.preparedMsm, (records, 1, _oneScalar(1))), Bls12381.InvalidLength.selector);
        _expectRevert(
            abi.encodeCall(this.preparedMsm, (records, type(uint256).max, _oneScalar(1))),
            Bls12381.InvalidLength.selector
        );
        _expectRevert(abi.encodeCall(this.preparedMsm, (records, 0, new uint256[](0))), Bls12381.InvalidLength.selector);
        _expectRevert(
            abi.encodeCall(this.preparedMsm, (new bytes(161), 0, _oneScalar(1))), Bls12381.InvalidLength.selector
        );
        _expectRevert(
            abi.encodeCall(this.preparedMsm, (records, 0, _oneScalar(R))), Bls12381.NonCanonicalScalar.selector
        );
        _expectRevert(abi.encodeCall(this.copyRecords, (_generator(), records, 1)), Bls12381.InvalidLength.selector);
        _expectRevert(abi.encodeCall(this.copyRecords, (new bytes(129), records, 0)), Bls12381.InvalidLength.selector);
        _expectRevert(
            abi.encodeCall(this.copyRecords, (_generator(), new bytes(161), 0)), Bls12381.InvalidLength.selector
        );
        _expectRevert(abi.encodeCall(this.copyAlias, ()), Bls12381.InvalidLength.selector);
        _equal(this.copyRecords(new bytes(0), records, 1), records);
    }

    function testPreparedMsmChecksWrongSubgroupAtZeroWeightWithinBound() public view {
        bytes memory orderThree = abi.encode(uint256(0), uint256(0), uint256(0), uint256(2));
        bytes memory records = new bytes(2 * 160);
        Bls12381.copyPointsInto(bytes.concat(_generator(), orderThree), records, 0);
        uint256[] memory scalars = new uint256[](2);
        scalars[0] = 1;
        _expectRevertWithin(abi.encodeCall(this.preparedMsm, (records, 0, scalars)), 70_000);
        _expectRevertWithin(abi.encodeCall(this.preparedMsm, (records, 1, _oneScalar(0))), 35_000);
    }

    function preparedMsm(bytes memory records, uint256 first, uint256[] memory scalars)
        external
        view
        returns (bytes memory)
    {
        return Bls12381.msmPrepared(records, first, scalars);
    }

    function copyRecords(bytes memory points, bytes memory records, uint256 first)
        external
        pure
        returns (bytes memory)
    {
        Bls12381.copyPointsInto(points, records, first);
        return records;
    }

    function copyAlias() external pure {
        bytes memory records = new bytes(640);
        Bls12381.copyPointsInto(records, records, 0);
    }

    function decode(bytes memory compressed, bytes memory hint) external pure returns (bytes memory) {
        return Bls12381.decodeG1(compressed, hint);
    }

    function msm(bytes memory points, uint256[] memory scalars) external view returns (bytes memory) {
        return Bls12381.msm(points, scalars);
    }

    function add(bytes memory a, bytes memory b) external view returns (bytes memory) {
        return Bls12381.add(a, b);
    }

    function negate(bytes memory point) external pure returns (bytes memory) {
        return Bls12381.negate(point);
    }

    function pairing2(bytes memory a, bytes memory h, bytes memory b, bytes memory tau) external view returns (bool) {
        return Bls12381.pairing2(a, h, b, tau);
    }

    function _expectRevert(bytes memory data, bytes4 expected) private view {
        // Invalid precompile inputs burn the forwarded gas; cap only these deliberately invalid calls.
        (bool success, bytes memory result) = address(this).staticcall{gas: 1_000_000}(data);
        require(!success && result.length >= 4, "expected revert data");
        bytes4 actual;
        assembly ("memory-safe") {
            actual := mload(add(result, 32))
        }
        require(actual == expected, "unexpected revert");
    }

    function _expectRevertWithin(bytes memory data, uint256 maxGas) private view {
        uint256 before = gasleft();
        _expectRevert(data, Bls12381.PrecompileFailure.selector);
        require(before - gasleft() < maxGas, "malformed point consumed caller gas");
    }

    function _equal(bytes memory a, bytes memory b) private pure {
        require(a.length == b.length && keccak256(a) == keccak256(b), "bytes differ");
    }

    function _oneScalar(uint256 scalar) private pure returns (uint256[] memory values) {
        values = new uint256[](1);
        values[0] = scalar;
    }

    function _compressedGenerator() private pure returns (bytes memory) {
        return hex"97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb";
    }

    function _generatorY() private pure returns (bytes memory) {
        return hex"08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1";
    }

    function _generator() private pure returns (bytes memory) {
        return abi.encode(
            uint256(0x17f1d3a73197d7942695638c4fa9ac0f),
            uint256(0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb),
            uint256(0x08b3f481e3aaa0f1a09e30ed741d8ae4),
            uint256(0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
        );
    }

    function _g2() private pure returns (bytes memory) {
        return abi.encode(
            uint256(0x024aa2b2f08f0a91260805272dc51051),
            uint256(0xc6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8),
            uint256(0x13e02b6052719f607dacd3a088274f65),
            uint256(0x596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e),
            uint256(0x0ce5d527727d6e118cc9cdc6da2e351a),
            uint256(0xadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801),
            uint256(0x0606c4a02ea734cc32acd2b02bc28b99),
            uint256(0xcb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)
        );
    }
}
