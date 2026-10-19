// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {Bls12381} from "./Bls12381.sol";
import {Scalar} from "./Scalar.sol";
import {KeccakTranscript} from "./KeccakTranscript.sol";

/// @notice Fixed-verifying key verifier for the two-circuit ix v5 KZG packet.
/// @dev The verifying key is authenticated contract code. Pairing operands deferred
/// by the recursive circuit are bound as four 192-bit public scalar values.
abstract contract KzgVerifier {
    using KeccakTranscript for KeccakTranscript.State;

    uint256 internal constant R = Scalar.MODULUS;
    uint256 internal constant PACKET_PREFIX = 272;
    uint256 internal constant POINT_START = PACKET_PREFIX + 5;

    struct Lookup {
        uint256 multiplicity;
        uint256[] args;
    }

    struct Circuit {
        uint256 logDegree;
        uint256 mainWidth;
        uint256 stage2Width;
        uint256 preprocessedWidth;
        uint256 quotientDegree;
        uint256 constraintCount;
        uint256 maxConstraintDegree;
        uint256 lookupGroupSize;
        bool mainNext;
        bool preprocessedNext;
        uint256 omega;
        // [op,a,b,c]: Const(a), Var(source=a,row=b,column=c), Public(a),
        // First, Last, Transition, Add(a,b), Sub(a,b), Mul(a,b), Neg(a).
        // Variable sources are Main=0, Preprocessed=1, Stage2=2.
        uint256[4][] nodes;
        uint256[] zeros;
        Lookup[] lookups;
    }

    struct VerifyingKey {
        bytes32 id;
        bytes seed;
        Circuit[2] circuits;
        bytes fixedCompressed;
        bytes fixedPoints;
        bytes generator;
        bytes outerH;
        bytes outerTauH;
        bytes innerH;
        bytes innerTauH;
    }

    struct Matrix {
        uint256 width;
        uint256 rows;
        uint256 pointOffset;
        uint256 valueOffset;
    }

    struct Proof {
        uint256 pointCount;
        uint256 openingCount;
        uint256 witnessOffset;
        bytes compressed;
        bytes msmInput;
        uint256[] values;
        uint256[23] publicValues;
        Matrix[8] matrices;
        bytes innerA;
        bytes innerB;
    }

    struct Prepared {
        uint256[6] challenges;
        bytes left;
        bytes right;
        bytes innerA;
        bytes innerB;
    }

    struct Batches {
        uint256 count;
        uint256[3] points;
        uint256[16] group;
    }

    struct EvaluationView {
        uint256[4] publics;
        uint256 first;
        uint256 last;
        uint256 transition;
    }

    error InvalidPacket();
    error InvalidVerifyingKey();
    error InvalidChallenge();
    error ConstraintMismatch(uint256 circuit);

    function _vk() internal pure virtual returns (VerifyingKey memory);

    /// @param packet Native packet, beginning with the 32-byte verifying key ID.
    /// @param yHints 48-byte big-endian y values in packet order: deferred A,
    /// deferred B, then main, LogUp, quotient and opening-witness points.
    /// @param expectedClaim The application's independently expected library claim.
    /// @dev Malformed encodings and violated scalar identities revert. The
    /// authenticated verifying key must describe the computation being proved.
    function verify(bytes calldata packet, bytes calldata yHints, uint64[18] calldata expectedClaim)
        external
        view
        returns (bool)
    {
        VerifyingKey memory vk = _vk();
        Prepared memory result = _prepareWithVerifyingKey(vk, packet, yHints, expectedClaim);
        if (!Bls12381.pairing2(result.left, vk.outerH, Bls12381.negate(result.right), vk.outerTauH)) {
            return false;
        }
        return Bls12381.pairing2(result.innerA, vk.innerH, result.innerB, vk.innerTauH);
    }

    function _prepare(bytes calldata packet, bytes calldata yHints, uint64[18] calldata expectedClaim)
        internal
        view
        returns (Prepared memory result)
    {
        return _prepareWithVerifyingKey(_vk(), packet, yHints, expectedClaim);
    }

    function _prepareWithVerifyingKey(
        VerifyingKey memory vk,
        bytes calldata packet,
        bytes calldata yHints,
        uint64[18] calldata expectedClaim
    ) private view returns (Prepared memory result) {
        Proof memory proof = _decode(vk, packet, yHints, expectedClaim);
        result.challenges = _challenges(vk, proof);
        _checkConstraints(vk, proof, result.challenges);
        (result.left, result.right) = _foldOpenings(vk, proof, result.challenges);
        result.innerA = proof.innerA;
        result.innerB = proof.innerB;
    }

    function _decode(
        VerifyingKey memory vk,
        bytes calldata packet,
        bytes calldata hints,
        uint64[18] calldata expectedClaim
    ) internal pure returns (Proof memory proof) {
        if (
            packet.length < POINT_START || bytes32(packet[:32]) != vk.id
                || bytes4(packet[PACKET_PREFIX:PACKET_PREFIX + 4]) != bytes4("KQP4")
        ) {
            revert InvalidPacket();
        }
        proof.openingCount = uint8(packet[PACKET_PREFIX + 4]);
        if (proof.openingCount == 0 || proof.openingCount > 3) revert InvalidPacket();
        (uint256 fieldCount, uint256 fixedCount) = _proofLayout(vk, proof);
        if (
            packet.length != POINT_START + proof.pointCount * 48 + fieldCount * 32
                || hints.length != (proof.pointCount + 2) * 48
        ) revert InvalidPacket();
        if (
            vk.fixedCompressed.length != fixedCount * 48 || vk.fixedPoints.length != fixedCount * 128
                || vk.generator.length != 128
        ) {
            revert InvalidVerifyingKey();
        }
        for (uint256 i; i < 18; ++i) {
            uint64 encodedWord;
            // The packet header length check covers the complete fixed-width claim.
            assembly ("memory-safe") {
                encodedWord := shr(192, calldataload(add(add(packet.offset, 32), mul(i, 8))))
            }
            uint256 word = Scalar.reverseBytes64(encodedWord);
            if (word != expectedClaim[i]) revert InvalidPacket();
            proof.publicValues[i + 1] = word;
        }
        for (uint256 i; i < 4; ++i) {
            proof.publicValues[19 + i] = Scalar.readLittleEndian(packet, 176 + i * 24, 24);
        }
        proof.innerA = new bytes(128);
        proof.innerB = new bytes(128);
        Bls12381.decodeG1Into(packet[176:224], hints[:48], proof.innerA, 0);
        Bls12381.decodeG1Into(packet[224:272], hints[48:96], proof.innerB, 0);
        proof.compressed = packet[POINT_START:POINT_START + proof.pointCount * 48];
        proof.msmInput = new bytes((proof.pointCount + fixedCount + 1) * 160);
        for (uint256 i; i < proof.pointCount; ++i) {
            uint256 offset = POINT_START + i * 48;
            Bls12381.decodeG1Into(packet[offset:offset + 48], hints[(i + 2) * 48:(i + 3) * 48], proof.msmInput, i * 160);
        }
        Bls12381.copyPointsInto(vk.fixedPoints, proof.msmInput, proof.pointCount);
        Bls12381.copyPointsInto(vk.generator, proof.msmInput, proof.pointCount + fixedCount);
        uint256 scalarStart = POINT_START + proof.pointCount * 48;
        proof.values = Scalar.readCanonicalRange(packet, scalarStart, fieldCount);
    }

    function _challenges(VerifyingKey memory vk, Proof memory proof)
        internal
        pure
        returns (uint256[6] memory challenges)
    {
        KeccakTranscript.State memory t;
        t.observe(vk.seed);
        t.field(2);
        for (uint256 ci; ci < 2; ++ci) {
            Circuit memory c = vk.circuits[ci];
            t.field(c.constraintCount);
            t.field(c.maxConstraintDegree);
            t.field(uint256(1) << c.logDegree);
            t.field(c.preprocessedWidth);
            t.field(c.mainWidth);
            t.field(c.stage2Width);
            t.field(c.lookupGroupSize);
        }
        t.field(1);
        t.field(1);
        _observeCommitment(t, vk, proof, 3);
        _observeCommitment(t, vk, proof, 0);
        t.field(vk.circuits[0].logDegree);
        t.field(vk.circuits[1].logDegree);
        t.field(23);
        t.publicTuples(proof.publicValues);
        challenges[0] = t.sample();
        t.field(challenges[0]);
        challenges[1] = t.sample();
        t.field(challenges[1]);
        _observeCommitment(t, vk, proof, 1);
        t.field(proof.values[0]);
        t.field(0);
        challenges[2] = t.sample();
        _observeCommitment(t, vk, proof, 2);
        challenges[3] = t.sample();
        if (challenges[3] == 0) revert InvalidChallenge();
        for (uint256 round; round < 4; ++round) {
            _observeCommitment(t, vk, proof, round);
            t.integer64(vk.circuits[0].logDegree);
            t.integer64(vk.circuits[1].logDegree);
        }
        t.fieldsRange(proof.values, 1, proof.values.length - 1);
        challenges[4] = t.sample();
        t.observeRange(proof.compressed, proof.witnessOffset * 48, proof.openingCount * 48);
        challenges[5] = t.sample();
    }

    function _observeCommitment(
        KeccakTranscript.State memory t,
        VerifyingKey memory vk,
        Proof memory proof,
        uint256 round
    ) private pure {
        t.integer64(2);
        for (uint256 ci; ci < 2; ++ci) {
            Matrix memory m = proof.matrices[round * 2 + ci];
            t.integer64(m.width);
            if (round == 3) {
                t.observeRange(vk.fixedCompressed, (m.pointOffset - proof.pointCount) * 48, m.width * 48);
            } else {
                t.observeRange(proof.compressed, m.pointOffset * 48, m.width * 48);
            }
        }
    }

    function _publicAccumulator(Proof memory proof, uint256 beta, uint256 gamma)
        internal
        view
        returns (uint256 accumulator)
    {
        (uint256 numerator, uint256 product) = _publicFraction(proof, beta, gamma);
        return mulmod(numerator, Scalar.inverse(product), R);
    }

    function _publicFraction(Proof memory proof, uint256 beta, uint256 gamma)
        private
        pure
        returns (uint256 numerator, uint256 product)
    {
        product = 1;
        uint256 gammaSquared = mulmod(gamma, gamma, R);
        uint256 gammaCubed = mulmod(gammaSquared, gamma, R);
        uint256 offset = addmod(addmod(beta, gamma, R), 94, R);
        for (uint256 i; i < 23; ++i) {
            uint256 denominator = addmod(mulmod(proof.publicValues[i], gammaCubed, R), offset, R);
            numerator = addmod(mulmod(numerator, denominator, R), product, R);
            product = mulmod(product, denominator, R);
            offset = addmod(offset, gammaSquared, R);
        }
    }

    function _checkConstraints(VerifyingKey memory vk, Proof memory proof, uint256[6] memory ch) private view {
        (uint256 publicNumerator, uint256 publicProduct) = _publicFraction(proof, ch[0], ch[1]);
        uint256[6] memory denominators;
        denominators[0] = publicProduct;
        denominators[1] = Scalar.sub(ch[3], 1);
        for (uint256 ci; ci < 2; ++ci) {
            denominators[2 + ci] = vk.circuits[ci].omega;
            denominators[4 + ci] = Scalar.sub(mulmod(vk.circuits[ci].omega, ch[3], R), 1);
        }
        uint256[6] memory inverses = Scalar.inverseBatch6(denominators);
        uint256 accumulator = mulmod(publicNumerator, inverses[0], R);
        for (uint256 ci; ci < 2; ++ci) {
            Circuit memory c = vk.circuits[ci];
            uint256 zN = Scalar.powerOfTwo(ch[3], c.logDegree);
            if (zN == 1) revert InvalidChallenge();
            uint256 vanishing = Scalar.sub(zN, 1);
            uint256 nextAccumulator = ci == 0 ? proof.values[0] : 0;
            EvaluationView memory view_;
            view_.publics = [ch[0], ch[1], accumulator, nextAccumulator];
            view_.first = mulmod(vanishing, inverses[1], R);
            view_.transition = Scalar.sub(ch[3], inverses[2 + ci]);
            uint256 normalizedLast = mulmod(vanishing, inverses[4 + ci], R);
            view_.last = mulmod(normalizedLast, c.omega, R);
            uint256[] memory nodes = _evaluateGraph(c, proof, ci, view_);
            uint256 composition;
            for (uint256 i; i < c.zeros.length; ++i) {
                composition = addmod(mulmod(composition, ch[2], R), nodes[c.zeros[i]], R);
            }
            uint256 inverseDegree = R - ((R - 1) >> c.logDegree);
            uint256 injection =
                mulmod(mulmod(normalizedLast, Scalar.sub(nextAccumulator, accumulator), R), inverseDegree, R);
            composition = _foldLookups(c, proof, ci, nodes, view_.publics, injection, ch[2], composition);
            Matrix memory q = proof.matrices[4 + ci];
            uint256 quotient;
            for (uint256 i = q.width; i > 0; --i) {
                quotient = addmod(mulmod(quotient, zN, R), proof.values[q.valueOffset + i - 1], R);
            }
            if (composition != mulmod(vanishing, quotient, R)) revert ConstraintMismatch(ci);
            accumulator = nextAccumulator;
        }
    }

    function _evaluateGraph(Circuit memory c, Proof memory proof, uint256 ci, EvaluationView memory view_)
        internal
        pure
        virtual
        returns (uint256[] memory values);

    function _foldLookups(
        Circuit memory c,
        Proof memory proof,
        uint256 ci,
        uint256[] memory nodes,
        uint256[4] memory publics,
        uint256 injection,
        uint256 alpha,
        uint256 composition
    ) private pure returns (uint256) {
        Matrix memory m = proof.matrices[2 + ci];
        uint256 groups = c.lookups.length == 0 ? 1 : (c.lookups.length + c.lookupGroupSize - 1) / c.lookupGroupSize;
        if (groups != m.width || c.constraintCount != c.zeros.length + groups) revert InvalidVerifyingKey();
        for (uint256 g; g < groups; ++g) {
            uint256 target = g + 1 < groups
                ? proof.values[m.valueOffset + g + 1]
                : addmod(proof.values[m.valueOffset + m.width], injection, R);
            uint256 difference = Scalar.sub(target, proof.values[m.valueOffset + g]);
            uint256 start = g * c.lookupGroupSize;
            uint256 end = start + c.lookupGroupSize;
            if (end > c.lookups.length) end = c.lookups.length;
            uint256 length = end - start;
            uint256 product = 1;
            uint256 weightedNumerator;
            for (uint256 j; j < length; ++j) {
                Lookup memory lookup = c.lookups[start + j];
                uint256 message;
                for (uint256 k = lookup.args.length; k > 0; --k) {
                    message = addmod(mulmod(message, publics[1], R), nodes[lookup.args[k - 1]], R);
                }
                message = addmod(message, publics[0], R);
                weightedNumerator =
                    addmod(mulmod(weightedNumerator, message, R), mulmod(nodes[lookup.multiplicity], product, R), R);
                product = mulmod(product, message, R);
            }
            uint256 value = Scalar.sub(mulmod(product, difference, R), weightedNumerator);
            composition = addmod(mulmod(composition, alpha, R), value, R);
        }
        return composition;
    }

    function _proofLayout(VerifyingKey memory vk, Proof memory proof)
        internal
        pure
        virtual
        returns (uint256 fieldCount, uint256 fixedCount);

    function _openingCoefficients(VerifyingKey memory vk, Proof memory proof, uint256[6] memory ch)
        internal
        pure
        virtual
        returns (uint256[] memory coefficients, uint256[] memory witnessCoefficients);

    function _foldOpenings(VerifyingKey memory vk, Proof memory proof, uint256[6] memory ch)
        private
        view
        returns (bytes memory left, bytes memory right)
    {
        (uint256[] memory coefficients, uint256[] memory witnessCoefficients) = _openingCoefficients(vk, proof, ch);
        // Retain every point in the MSM, including zero-weight terms: the
        // precompile must validate each supplied point's subgroup membership.
        left = Bls12381.msmPrepared(proof.msmInput, 0, coefficients);
        right = Bls12381.msmPrepared(proof.msmInput, proof.witnessOffset, witnessCoefficients);
    }
}
