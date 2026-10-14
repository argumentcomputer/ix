// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;
import {KzgVerifier} from "../src/KzgVerifier.sol";
import {Scalar} from "../src/Scalar.sol";

abstract contract OpeningDifferentialBase is KzgVerifier {
    function _evaluateGraph(Circuit memory, Proof memory, uint256, EvaluationView memory)
        internal
        pure
        override
        returns (uint256[] memory)
    {
        return new uint256[](0);
    }

    function compare(uint256 zeta, uint256 v, uint256 r, uint256 count) external pure returns (bool) {
        Profile memory p = _profile();
        Proof memory generated;
        Proof memory interpreted;
        generated.openingCount = count;
        interpreted.openingCount = count;
        (uint256 generatedFields, uint256 generatedFixed) = _proofLayout(p, generated);
        (uint256 interpretedFields, uint256 interpretedFixed) = _referenceLayout(p, interpreted);
        require(generatedFields == interpretedFields && generatedFixed == interpretedFixed, "layout counts differ");
        require(
            generated.pointCount == interpreted.pointCount && generated.witnessOffset == interpreted.witnessOffset,
            "point offsets differ"
        );
        require(
            keccak256(abi.encode(generated.matrices)) == keccak256(abi.encode(interpreted.matrices)),
            "matrix layout differs"
        );
        generated.values = new uint256[](generatedFields);
        for (uint256 i; i < generatedFields; ++i) {
            generated.values[i] = mulmod(i + 1, R - 1, R);
        }
        interpreted.values = generated.values;
        uint256[6] memory ch;
        ch[3] = zeta;
        ch[4] = v;
        ch[5] = r;
        (uint256[] memory a, uint256[] memory b) = _openingCoefficients(p, generated, ch);
        (uint256[] memory c, uint256[] memory d) = _referenceCoefficients(p, interpreted, ch);
        require(keccak256(abi.encode(a)) == keccak256(abi.encode(c)), "commitment coefficients differ");
        require(keccak256(abi.encode(b)) == keccak256(abi.encode(d)), "witness coefficients differ");
        return true;
    }

    function _referenceLayout(Profile memory profile, Proof memory proof)
        private
        pure
        returns (uint256 fieldCount, uint256 fixedCount)
    {
        uint256 commitmentCount;
        fieldCount = 1;
        for (uint256 round; round < 4; ++round) {
            for (uint256 ci; ci < 2; ++ci) {
                Circuit memory c = profile.circuits[ci];
                if (
                    c.logDegree == 0 || c.logDegree > 28 || c.preprocessedWidth == 0 || c.stage2Width == 0
                        || c.lookupGroupSize == 0 || c.lookupGroupSize > 8
                ) {
                    revert InvalidProfile();
                }
                Matrix memory m;
                if (round == 0) {
                    m.width = c.mainWidth;
                    m.rows = c.mainNext ? 2 : 1;
                } else if (round == 1) {
                    m.width = c.stage2Width;
                    m.rows = 2;
                } else if (round == 2) {
                    m.width = c.quotientDegree;
                    m.rows = 1;
                } else {
                    m.width = c.preprocessedWidth;
                    m.rows = c.preprocessedNext ? 2 : 1;
                }
                m.valueOffset = fieldCount;
                fieldCount += m.width * m.rows;
                if (round == 3) {
                    m.pointOffset = commitmentCount + proof.openingCount + fixedCount;
                    fixedCount += m.width;
                } else {
                    m.pointOffset = commitmentCount;
                    commitmentCount += m.width;
                }
                proof.matrices[round * 2 + ci] = m;
            }
        }
        proof.witnessOffset = commitmentCount;
        proof.pointCount = commitmentCount + proof.openingCount;
    }

    function _referenceBatches(Profile memory profile, Proof memory proof, uint256 zeta)
        private
        pure
        returns (Batches memory batches)
    {
        for (uint256 i; i < 8; ++i) {
            Matrix memory m = proof.matrices[i];
            for (uint256 row; row < m.rows; ++row) {
                uint256 point = row == 0 ? zeta : mulmod(zeta, profile.circuits[i % 2].omega, R);
                uint256 group;
                while (group < batches.count && batches.points[group] != point) ++group;
                if (group == batches.count) {
                    if (batches.count == 3) revert InvalidProfile();
                    batches.points[group] = point;
                    ++batches.count;
                }
                batches.group[i * 2 + row] = group;
            }
        }
        if (batches.count != proof.openingCount) revert InvalidPacket();
    }

    function _referenceCoefficients(Profile memory profile, Proof memory proof, uint256[6] memory ch)
        private
        pure
        returns (uint256[] memory coefficients, uint256[] memory witnessCoefficients)
    {
        Batches memory batches = _referenceBatches(profile, proof, ch[3]);
        uint256 fixedCount = profile.fixedPoints.length / 128;
        uint256 generatorIndex = proof.pointCount + fixedCount;
        coefficients = new uint256[](generatorIndex + 1);
        uint256[3] memory vPowers = [uint256(1), uint256(1), uint256(1)];
        uint256[3] memory rPowers = [uint256(1), ch[5], mulmod(ch[5], ch[5], R)];
        for (uint256 i; i < 8; ++i) {
            Matrix memory m = proof.matrices[i];
            for (uint256 row; row < m.rows; ++row) {
                uint256 group = batches.group[i * 2 + row];
                for (uint256 column; column < m.width; ++column) {
                    uint256 weight = mulmod(rPowers[group], vPowers[group], R);
                    uint256 pointIndex = m.pointOffset + column;
                    coefficients[pointIndex] = addmod(coefficients[pointIndex], weight, R);
                    coefficients[generatorIndex] = Scalar.sub(
                        coefficients[generatorIndex],
                        mulmod(weight, proof.values[m.valueOffset + row * m.width + column], R)
                    );
                    vPowers[group] = mulmod(vPowers[group], ch[4], R);
                }
            }
        }
        witnessCoefficients = new uint256[](proof.openingCount);
        for (uint256 i; i < proof.openingCount; ++i) {
            coefficients[proof.witnessOffset + i] = mulmod(rPowers[i], batches.points[i], R);
            witnessCoefficients[i] = rPowers[i];
        }
    }
}

contract OpeningCase0 is OpeningDifferentialBase {
    function _profile() internal pure override returns (Profile memory p) {
        p.circuits[0].logDegree = 5;
        p.circuits[0].mainWidth = 3;
        p.circuits[0].stage2Width = 4;
        p.circuits[0].preprocessedWidth = 15;
        p.circuits[0].quotientDegree = 2;
        p.circuits[0].lookupGroupSize = 2;
        p.circuits[0].mainNext = false;
        p.circuits[0].preprocessedNext = false;
        p.circuits[0].omega = 36581797046584068049060372878520385032448812009597153775348195406694427778894;
        p.circuits[1].logDegree = 4;
        p.circuits[1].mainWidth = 1;
        p.circuits[1].stage2Width = 1;
        p.circuits[1].preprocessedWidth = 4;
        p.circuits[1].quotientDegree = 1;
        p.circuits[1].lookupGroupSize = 1;
        p.circuits[1].mainNext = false;
        p.circuits[1].preprocessedNext = false;
        p.circuits[1].omega = 14788168760825820622209131888203028446852016562542525606630160374691593895118;
        p.fixedPoints = new bytes(2432);
    }

    function _proofLayout(Profile memory, Proof memory proof)
        internal
        pure
        override
        returns (uint256 fieldCount, uint256 fixedCount)
    {
        if (proof.openingCount != 3) revert InvalidPacket();
        proof.matrices[0] = Matrix(3, 1, 0, 1);
        proof.matrices[1] = Matrix(1, 1, 3, 4);
        proof.matrices[2] = Matrix(4, 2, 4, 5);
        proof.matrices[3] = Matrix(1, 2, 8, 13);
        proof.matrices[4] = Matrix(2, 1, 9, 15);
        proof.matrices[5] = Matrix(1, 1, 11, 17);
        proof.matrices[6] = Matrix(15, 1, 15, 18);
        proof.matrices[7] = Matrix(4, 1, 30, 33);
        proof.witnessOffset = 12;
        proof.pointCount = 15;
        return (37, 19);
    }

    function _openingCoefficients(Profile memory, Proof memory proof, uint256[6] memory ch)
        internal
        pure
        override
        returns (uint256[] memory coefficients, uint256[] memory witnessCoefficients)
    {
        if (ch[3] == 0) revert InvalidChallenge();
        if (proof.openingCount != 3 || proof.values.length != 37) revert InvalidPacket();
        coefficients = new uint256[](35);
        witnessCoefficients = new uint256[](3);
        uint256[] memory values = proof.values;
        assembly ("memory-safe") {
            let modulus := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
            let zeta := mload(add(ch, 96))
            let v := mload(add(ch, 128))
            let r := mload(add(ch, 160))
            let generatorSum := 0
            let rSquared := mulmod(r, r, modulus)
            let weight0 := 1
            let weight1 := r
            let weight2 := rSquared
            mstore(add(coefficients, 32), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 64)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 64), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 96)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 96), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 128)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 128), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 160)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 160), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 192)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 192), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 224)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 224), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 256)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 256), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 288)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 160), addmod(mload(add(coefficients, 160)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 320)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 192), addmod(mload(add(coefficients, 192)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 352)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 224), addmod(mload(add(coefficients, 224)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 384)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 256), addmod(mload(add(coefficients, 256)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 416)), modulus), modulus)
            mstore(add(coefficients, 288), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 448)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 288), addmod(mload(add(coefficients, 288)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 480)), modulus), modulus)
            mstore(add(coefficients, 320), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 512)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 352), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 544)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 384), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 576)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 512), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 608)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 544), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 640)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 576), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 672)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 608), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 704)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 640), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 736)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 672), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 768)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 704), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 800)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 736), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 832)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 768), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 864)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 800), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 896)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 832), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 928)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 864), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 960)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 896), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 992)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 928), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1024)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 960), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1056)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 992), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1088)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 1024), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1120)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 1056), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1152)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 1088), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1184)), modulus), modulus)
            mstore(add(coefficients, 1120), mod(sub(modulus, generatorSum), modulus))
            mstore(add(coefficients, 416), zeta)
            mstore(add(witnessCoefficients, 32), 1)
            mstore(
                add(coefficients, 448),
                mulmod(
                    r,
                    mulmod(zeta, 0x50e0903a157988bab4bcd40e22f55448bf6e88fb4c38fb8a360c60997369df4e, modulus),
                    modulus
                )
            )
            mstore(add(witnessCoefficients, 64), r)
            mstore(
                add(coefficients, 480),
                mulmod(
                    rSquared,
                    mulmod(zeta, 0x20b1ce9140267af9dd1c0af834cec32c17beb312f20b6f7653ea61d87742bcce, modulus),
                    modulus
                )
            )
            mstore(add(witnessCoefficients, 96), rSquared)
        }
    }
}

contract OpeningCase1 is OpeningDifferentialBase {
    function _profile() internal pure override returns (Profile memory p) {
        p.circuits[0].logDegree = 5;
        p.circuits[0].mainWidth = 3;
        p.circuits[0].stage2Width = 4;
        p.circuits[0].preprocessedWidth = 15;
        p.circuits[0].quotientDegree = 2;
        p.circuits[0].lookupGroupSize = 2;
        p.circuits[0].mainNext = true;
        p.circuits[0].preprocessedNext = false;
        p.circuits[0].omega = 36581797046584068049060372878520385032448812009597153775348195406694427778894;
        p.circuits[1].logDegree = 5;
        p.circuits[1].mainWidth = 1;
        p.circuits[1].stage2Width = 1;
        p.circuits[1].preprocessedWidth = 4;
        p.circuits[1].quotientDegree = 1;
        p.circuits[1].lookupGroupSize = 1;
        p.circuits[1].mainNext = false;
        p.circuits[1].preprocessedNext = true;
        p.circuits[1].omega = 36581797046584068049060372878520385032448812009597153775348195406694427778894;
        p.fixedPoints = new bytes(2432);
    }

    function _proofLayout(Profile memory, Proof memory proof)
        internal
        pure
        override
        returns (uint256 fieldCount, uint256 fixedCount)
    {
        if (proof.openingCount != 2) revert InvalidPacket();
        proof.matrices[0] = Matrix(3, 2, 0, 1);
        proof.matrices[1] = Matrix(1, 1, 3, 7);
        proof.matrices[2] = Matrix(4, 2, 4, 8);
        proof.matrices[3] = Matrix(1, 2, 8, 16);
        proof.matrices[4] = Matrix(2, 1, 9, 18);
        proof.matrices[5] = Matrix(1, 1, 11, 20);
        proof.matrices[6] = Matrix(15, 1, 14, 21);
        proof.matrices[7] = Matrix(4, 2, 29, 36);
        proof.witnessOffset = 12;
        proof.pointCount = 14;
        return (44, 19);
    }

    function _openingCoefficients(Profile memory, Proof memory proof, uint256[6] memory ch)
        internal
        pure
        override
        returns (uint256[] memory coefficients, uint256[] memory witnessCoefficients)
    {
        if (ch[3] == 0) revert InvalidChallenge();
        if (proof.openingCount != 2 || proof.values.length != 44) revert InvalidPacket();
        coefficients = new uint256[](34);
        witnessCoefficients = new uint256[](2);
        uint256[] memory values = proof.values;
        assembly ("memory-safe") {
            let modulus := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
            let zeta := mload(add(ch, 96))
            let v := mload(add(ch, 128))
            let r := mload(add(ch, 160))
            let generatorSum := 0
            let weight0 := 1
            let weight1 := r
            mstore(add(coefficients, 32), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 64)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 64), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 96)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 96), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 128)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 32), addmod(mload(add(coefficients, 32)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 160)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 64), addmod(mload(add(coefficients, 64)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 192)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 96), addmod(mload(add(coefficients, 96)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 224)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 128), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 256)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 160), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 288)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 192), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 320)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 224), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 352)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 256), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 384)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 160), addmod(mload(add(coefficients, 160)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 416)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 192), addmod(mload(add(coefficients, 192)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 448)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 224), addmod(mload(add(coefficients, 224)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 480)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 256), addmod(mload(add(coefficients, 256)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 512)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 288), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 544)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 288), addmod(mload(add(coefficients, 288)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 576)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 320), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 608)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 352), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 640)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 384), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 672)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 480), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 704)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 512), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 736)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 544), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 768)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 576), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 800)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 608), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 832)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 640), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 864)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 672), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 896)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 704), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 928)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 736), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 960)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 768), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 992)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 800), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1024)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 832), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1056)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 864), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1088)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 896), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1120)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 928), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1152)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 960), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1184)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 992), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1216)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 1024), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1248)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 1056), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1280)), modulus), modulus)
            mstore(add(coefficients, 960), addmod(mload(add(coefficients, 960)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1312)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 992), addmod(mload(add(coefficients, 992)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1344)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 1024), addmod(mload(add(coefficients, 1024)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1376)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 1056), addmod(mload(add(coefficients, 1056)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1408)), modulus), modulus)
            mstore(add(coefficients, 1088), mod(sub(modulus, generatorSum), modulus))
            mstore(add(coefficients, 416), zeta)
            mstore(add(witnessCoefficients, 32), 1)
            mstore(
                add(coefficients, 448),
                mulmod(
                    r,
                    mulmod(zeta, 0x50e0903a157988bab4bcd40e22f55448bf6e88fb4c38fb8a360c60997369df4e, modulus),
                    modulus
                )
            )
            mstore(add(witnessCoefficients, 64), r)
        }
    }
}

contract OpeningCase2 is OpeningDifferentialBase {
    function _profile() internal pure override returns (Profile memory p) {
        p.circuits[0].logDegree = 5;
        p.circuits[0].mainWidth = 3;
        p.circuits[0].stage2Width = 4;
        p.circuits[0].preprocessedWidth = 15;
        p.circuits[0].quotientDegree = 2;
        p.circuits[0].lookupGroupSize = 2;
        p.circuits[0].mainNext = false;
        p.circuits[0].preprocessedNext = true;
        p.circuits[0].omega = 36581797046584068049060372878520385032448812009597153775348195406694427778894;
        p.circuits[1].logDegree = 4;
        p.circuits[1].mainWidth = 1;
        p.circuits[1].stage2Width = 1;
        p.circuits[1].preprocessedWidth = 4;
        p.circuits[1].quotientDegree = 1;
        p.circuits[1].lookupGroupSize = 1;
        p.circuits[1].mainNext = true;
        p.circuits[1].preprocessedNext = true;
        p.circuits[1].omega = 14788168760825820622209131888203028446852016562542525606630160374691593895118;
        p.fixedPoints = new bytes(2432);
    }

    function _proofLayout(Profile memory, Proof memory proof)
        internal
        pure
        override
        returns (uint256 fieldCount, uint256 fixedCount)
    {
        if (proof.openingCount != 3) revert InvalidPacket();
        proof.matrices[0] = Matrix(3, 1, 0, 1);
        proof.matrices[1] = Matrix(1, 2, 3, 4);
        proof.matrices[2] = Matrix(4, 2, 4, 6);
        proof.matrices[3] = Matrix(1, 2, 8, 14);
        proof.matrices[4] = Matrix(2, 1, 9, 16);
        proof.matrices[5] = Matrix(1, 1, 11, 18);
        proof.matrices[6] = Matrix(15, 2, 15, 19);
        proof.matrices[7] = Matrix(4, 2, 30, 49);
        proof.witnessOffset = 12;
        proof.pointCount = 15;
        return (57, 19);
    }

    function _openingCoefficients(Profile memory, Proof memory proof, uint256[6] memory ch)
        internal
        pure
        override
        returns (uint256[] memory coefficients, uint256[] memory witnessCoefficients)
    {
        if (ch[3] == 0) revert InvalidChallenge();
        if (proof.openingCount != 3 || proof.values.length != 57) revert InvalidPacket();
        coefficients = new uint256[](35);
        witnessCoefficients = new uint256[](3);
        uint256[] memory values = proof.values;
        assembly ("memory-safe") {
            let modulus := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
            let zeta := mload(add(ch, 96))
            let v := mload(add(ch, 128))
            let r := mload(add(ch, 160))
            let generatorSum := 0
            let rSquared := mulmod(r, r, modulus)
            let weight0 := 1
            let weight1 := r
            let weight2 := rSquared
            mstore(add(coefficients, 32), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 64)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 64), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 96)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 96), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 128)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 128), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 160)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 128), addmod(mload(add(coefficients, 128)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 192)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 160), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 224)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 192), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 256)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 224), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 288)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 256), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 320)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 160), addmod(mload(add(coefficients, 160)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 352)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 192), addmod(mload(add(coefficients, 192)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 384)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 224), addmod(mload(add(coefficients, 224)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 416)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 256), addmod(mload(add(coefficients, 256)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 448)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 288), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 480)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 288), addmod(mload(add(coefficients, 288)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 512)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 320), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 544)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 352), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 576)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 384), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 608)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 512), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 640)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 544), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 672)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 576), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 704)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 608), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 736)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 640), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 768)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 672), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 800)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 704), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 832)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 736), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 864)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 768), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 896)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 800), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 928)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 832), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 960)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 864), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 992)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 896), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1024)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 928), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1056)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 960), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1088)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 512), addmod(mload(add(coefficients, 512)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1120)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 544), addmod(mload(add(coefficients, 544)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1152)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 576), addmod(mload(add(coefficients, 576)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1184)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 608), addmod(mload(add(coefficients, 608)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1216)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 640), addmod(mload(add(coefficients, 640)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1248)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 672), addmod(mload(add(coefficients, 672)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1280)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 704), addmod(mload(add(coefficients, 704)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1312)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 736), addmod(mload(add(coefficients, 736)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1344)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 768), addmod(mload(add(coefficients, 768)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1376)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 800), addmod(mload(add(coefficients, 800)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1408)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 832), addmod(mload(add(coefficients, 832)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1440)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 864), addmod(mload(add(coefficients, 864)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1472)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 896), addmod(mload(add(coefficients, 896)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1504)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 928), addmod(mload(add(coefficients, 928)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1536)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 960), addmod(mload(add(coefficients, 960)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 1568)), modulus), modulus)
            mstore(add(coefficients, 992), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1600)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 1024), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1632)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 1056), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1664)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 1088), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1696)), modulus), modulus)
            mstore(add(coefficients, 992), addmod(mload(add(coefficients, 992)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1728)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 1024), addmod(mload(add(coefficients, 1024)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1760)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 1056), addmod(mload(add(coefficients, 1056)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1792)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 1088), addmod(mload(add(coefficients, 1088)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1824)), modulus), modulus)
            mstore(add(coefficients, 1120), mod(sub(modulus, generatorSum), modulus))
            mstore(add(coefficients, 416), zeta)
            mstore(add(witnessCoefficients, 32), 1)
            mstore(
                add(coefficients, 448),
                mulmod(
                    r,
                    mulmod(zeta, 0x20b1ce9140267af9dd1c0af834cec32c17beb312f20b6f7653ea61d87742bcce, modulus),
                    modulus
                )
            )
            mstore(add(witnessCoefficients, 64), r)
            mstore(
                add(coefficients, 480),
                mulmod(
                    rSquared,
                    mulmod(zeta, 0x50e0903a157988bab4bcd40e22f55448bf6e88fb4c38fb8a360c60997369df4e, modulus),
                    modulus
                )
            )
            mstore(add(witnessCoefficients, 96), rSquared)
        }
    }
}

contract OpeningCase3 is OpeningDifferentialBase {
    function _profile() internal pure override returns (Profile memory p) {
        p.circuits[0].logDegree = 5;
        p.circuits[0].mainWidth = 0;
        p.circuits[0].stage2Width = 4;
        p.circuits[0].preprocessedWidth = 15;
        p.circuits[0].quotientDegree = 0;
        p.circuits[0].lookupGroupSize = 2;
        p.circuits[0].mainNext = true;
        p.circuits[0].preprocessedNext = true;
        p.circuits[0].omega = 36581797046584068049060372878520385032448812009597153775348195406694427778894;
        p.circuits[1].logDegree = 4;
        p.circuits[1].mainWidth = 2;
        p.circuits[1].stage2Width = 1;
        p.circuits[1].preprocessedWidth = 4;
        p.circuits[1].quotientDegree = 3;
        p.circuits[1].lookupGroupSize = 1;
        p.circuits[1].mainNext = true;
        p.circuits[1].preprocessedNext = false;
        p.circuits[1].omega = 14788168760825820622209131888203028446852016562542525606630160374691593895118;
        p.fixedPoints = new bytes(2432);
    }

    function _proofLayout(Profile memory, Proof memory proof)
        internal
        pure
        override
        returns (uint256 fieldCount, uint256 fixedCount)
    {
        if (proof.openingCount != 3) revert InvalidPacket();
        proof.matrices[0] = Matrix(0, 2, 0, 1);
        proof.matrices[1] = Matrix(2, 2, 0, 1);
        proof.matrices[2] = Matrix(4, 2, 2, 5);
        proof.matrices[3] = Matrix(1, 2, 6, 13);
        proof.matrices[4] = Matrix(0, 1, 7, 15);
        proof.matrices[5] = Matrix(3, 1, 7, 15);
        proof.matrices[6] = Matrix(15, 2, 13, 18);
        proof.matrices[7] = Matrix(4, 1, 28, 48);
        proof.witnessOffset = 10;
        proof.pointCount = 13;
        return (52, 19);
    }

    function _openingCoefficients(Profile memory, Proof memory proof, uint256[6] memory ch)
        internal
        pure
        override
        returns (uint256[] memory coefficients, uint256[] memory witnessCoefficients)
    {
        if (ch[3] == 0) revert InvalidChallenge();
        if (proof.openingCount != 3 || proof.values.length != 52) revert InvalidPacket();
        coefficients = new uint256[](33);
        witnessCoefficients = new uint256[](3);
        uint256[] memory values = proof.values;
        assembly ("memory-safe") {
            let modulus := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
            let zeta := mload(add(ch, 96))
            let v := mload(add(ch, 128))
            let r := mload(add(ch, 160))
            let generatorSum := 0
            let rSquared := mulmod(r, r, modulus)
            let weight0 := 1
            let weight1 := r
            let weight2 := rSquared
            mstore(add(coefficients, 32), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 64)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 64), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 96)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 32), addmod(mload(add(coefficients, 32)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 128)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 64), addmod(mload(add(coefficients, 64)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 160)), modulus), modulus)
            weight2 := mulmod(weight2, v, modulus)
            mstore(add(coefficients, 96), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 192)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 128), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 224)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 160), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 256)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 192), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 288)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 96), addmod(mload(add(coefficients, 96)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 320)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 128), addmod(mload(add(coefficients, 128)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 352)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 160), addmod(mload(add(coefficients, 160)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 384)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 192), addmod(mload(add(coefficients, 192)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 416)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 224), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 448)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 224), addmod(mload(add(coefficients, 224)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 480)), modulus), modulus)
            mstore(add(coefficients, 256), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 512)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 288), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 544)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 320), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 576)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 448), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 608)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 480), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 640)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 512), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 672)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 544), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 704)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 576), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 736)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 608), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 768)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 640), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 800)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 672), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 832)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 704), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 864)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 736), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 896)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 768), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 928)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 800), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 960)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 832), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 992)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 864), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1024)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 896), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1056)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 448), addmod(mload(add(coefficients, 448)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1088)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 480), addmod(mload(add(coefficients, 480)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1120)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 512), addmod(mload(add(coefficients, 512)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1152)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 544), addmod(mload(add(coefficients, 544)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1184)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 576), addmod(mload(add(coefficients, 576)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1216)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 608), addmod(mload(add(coefficients, 608)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1248)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 640), addmod(mload(add(coefficients, 640)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1280)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 672), addmod(mload(add(coefficients, 672)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1312)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 704), addmod(mload(add(coefficients, 704)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1344)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 736), addmod(mload(add(coefficients, 736)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1376)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 768), addmod(mload(add(coefficients, 768)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1408)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 800), addmod(mload(add(coefficients, 800)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1440)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 832), addmod(mload(add(coefficients, 832)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1472)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 864), addmod(mload(add(coefficients, 864)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1504)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 896), addmod(mload(add(coefficients, 896)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 1536)), modulus), modulus)
            mstore(add(coefficients, 928), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1568)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 960), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1600)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 992), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1632)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 1024), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1664)), modulus), modulus)
            mstore(add(coefficients, 1056), mod(sub(modulus, generatorSum), modulus))
            mstore(add(coefficients, 352), zeta)
            mstore(add(witnessCoefficients, 32), 1)
            mstore(
                add(coefficients, 384),
                mulmod(
                    r,
                    mulmod(zeta, 0x50e0903a157988bab4bcd40e22f55448bf6e88fb4c38fb8a360c60997369df4e, modulus),
                    modulus
                )
            )
            mstore(add(witnessCoefficients, 64), r)
            mstore(
                add(coefficients, 416),
                mulmod(
                    rSquared,
                    mulmod(zeta, 0x20b1ce9140267af9dd1c0af834cec32c17beb312f20b6f7653ea61d87742bcce, modulus),
                    modulus
                )
            )
            mstore(add(witnessCoefficients, 96), rSquared)
        }
    }
}

contract OpeningLayoutTest {
    OpeningDifferentialBase[4] private harnesses;

    function setUp() public {
        harnesses[0] = new OpeningCase0();
        harnesses[1] = new OpeningCase1();
        harnesses[2] = new OpeningCase2();
        harnesses[3] = new OpeningCase3();
    }

    function testGeneratedLayoutsAndCoefficientsAcrossDomainsAndRows() public view {
        uint256[4] memory counts = [uint256(3), 2, 3, 3];
        uint256[4] memory zetas = [uint256(1), 7, Scalar.MODULUS - 1, 19];
        uint256[4] memory vs = [uint256(0), 1, 7, Scalar.MODULUS - 1];
        uint256[4] memory rs = [uint256(0), 1, Scalar.MODULUS - 1, 13];
        for (uint256 profile; profile < 4; ++profile) {
            for (uint256 sample; sample < 4; ++sample) {
                require(
                    harnesses[profile].compare(zetas[sample], vs[sample], rs[sample], counts[profile]),
                    "opening differs"
                );
            }
        }
    }

    function testGeneratedOpeningRejectsWrongCountAndZeroChallenge() public view {
        uint256[4] memory counts = [uint256(3), 2, 3, 3];
        for (uint256 profile; profile < 4; ++profile) {
            (bool ok,) = address(harnesses[profile])
                .staticcall(abi.encodeCall(OpeningDifferentialBase.compare, (7, 3, 5, counts[profile] == 2 ? 3 : 2)));
            require(!ok, "wrong opening count accepted");
            (ok,) = address(harnesses[profile])
                .staticcall(abi.encodeCall(OpeningDifferentialBase.compare, (0, 3, 5, counts[profile])));
            require(!ok, "zero zeta accepted");
        }
    }
}
