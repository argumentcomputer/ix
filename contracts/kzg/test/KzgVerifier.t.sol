// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {Bls12381} from "../src/Bls12381.sol";
import {GeneratedVerifier} from "../src/GeneratedVerifier.sol";
import {KzgVerifier} from "../src/KzgVerifier.sol";

interface Vm {
    function projectRoot() external view returns (string memory);
    function readFile(string calldata path) external view returns (string memory);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
    function parseJsonBytes32(string calldata json, string calldata key) external pure returns (bytes32);
    function parseJsonUintArray(string calldata json, string calldata key) external pure returns (uint256[] memory);
}

contract VerifierDiagnostics is GeneratedVerifier {
    function prepare(bytes calldata packet, bytes calldata yHints, uint64[18] calldata expectedClaim)
        external
        view
        returns (Prepared memory)
    {
        return _prepare(packet, yHints, expectedClaim);
    }

    function pairingResults(bytes calldata packet, bytes calldata yHints, uint64[18] calldata expectedClaim)
        external
        view
        returns (bool outer, bool inner)
    {
        Prepared memory result = _prepare(packet, yHints, expectedClaim);
        Profile memory profile = _profile();
        outer = Bls12381.pairing2(result.left, profile.outerH, Bls12381.negate(result.right), profile.outerTauH);
        inner = Bls12381.pairing2(result.innerA, profile.innerH, result.innerB, profile.innerTauH);
    }
}

contract KzgVerifierTest {
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 private constant POINT_START = 277;
    // Invalid precompile inputs can exhaust forwarded gas. The positive
    // fixture shares this test budget, so it also checks that the bound suffices.
    uint256 private constant VERIFY_GAS_LIMIT = 10_000_000;

    GeneratedVerifier private verifier;
    VerifierDiagnostics private diagnostics;
    string private fixture;
    bytes private packet;
    bytes private yHints;
    uint64[18] private expectedClaim;

    event log_named_uint(string key, uint256 value);

    function setUp() public {
        fixture = _readFixture("fixture.json");
        packet = vm.parseJsonBytes(fixture, ".packet");
        yHints = vm.parseJsonBytes(fixture, ".yHints");
        expectedClaim = _readExpectedClaim(fixture);
        require(packet.length > POINT_START, "fixture packet is too short");
        require(yHints.length >= 144 && yHints.length % 48 == 0, "invalid fixture hint layout");
        verifier = new GeneratedVerifier();
        diagnostics = new VerifierDiagnostics();
    }

    function testValidFilecoinPacket() public {
        bytes memory proof = packet;
        bytes memory hints = yHints;
        uint64[18] memory claim = expectedClaim;
        uint256 before = gasleft();
        bool valid = verifier.verify{gas: VERIFY_GAS_LIMIT}(proof, hints, claim);
        uint256 verificationGas = before - gasleft();
        require(valid, "valid Filecoin proof rejected");
        emit log_named_uint("verify external call gas", verificationGas);
        emit log_named_uint("packet bytes", proof.length);
        emit log_named_uint("y hint bytes", hints.length);
        emit log_named_uint(
            "verify ABI calldata bytes", abi.encodeWithSelector(KzgVerifier.verify.selector, proof, hints, claim).length
        );
    }

    function testVerifierRuntimeFitsEip170() public view {
        require(address(verifier).code.length <= 24576, "verifier exceeds EIP-170 runtime limit");
    }

    function testChallengesAndFoldedPointsMatchRust() public view {
        KzgVerifier.Prepared memory prepared = diagnostics.prepare{gas: VERIFY_GAS_LIMIT}(packet, yHints, expectedClaim);
        string[6] memory keys = [
            ".challenges[0]", ".challenges[1]", ".challenges[2]", ".challenges[3]", ".challenges[4]", ".challenges[5]"
        ];
        for (uint256 i; i < 6; ++i) {
            require(
                prepared.challenges[i] == uint256(vm.parseJsonBytes32(fixture, keys[i])),
                "Fiat-Shamir challenge differs from Rust"
            );
        }
        require(keccak256(prepared.left) == keccak256(vm.parseJsonBytes(fixture, ".outerL")), "outer L differs");
        require(keccak256(prepared.right) == keccak256(vm.parseJsonBytes(fixture, ".outerR")), "outer R differs");
        (bool outer, bool inner) = diagnostics.pairingResults{gas: VERIFY_GAS_LIMIT}(packet, yHints, expectedClaim);
        require(outer && inner, "valid fixture must satisfy both pairings");
    }

    function testRejectsBadDeferredPairingWithValidOuterProof() public view {
        string memory badFixture = _readFixture("fixture-bad-pairing.json");
        require(
            vm.parseJsonBytes32(badFixture, ".profileId") == vm.parseJsonBytes32(fixture, ".profileId"),
            "negative fixture must use the same profile"
        );
        bytes memory badPacket = vm.parseJsonBytes(badFixture, ".packet");
        bytes memory badHints = vm.parseJsonBytes(badFixture, ".yHints");
        uint64[18] memory badExpected = _readExpectedClaim(badFixture);
        (bool outer, bool inner) = diagnostics.pairingResults{gas: VERIFY_GAS_LIMIT}(badPacket, badHints, badExpected);
        require(outer, "negative fixture must have a valid outer KZG proof");
        require(!inner, "negative fixture must fail its deferred pairing");
        require(
            !verifier.verify{gas: VERIFY_GAS_LIMIT}(badPacket, badHints, badExpected),
            "deferred pairing failure accepted"
        );
    }

    function testRejectsChangedOpeningWitnessWithValidDeferredPairing() public view {
        bytes memory badPacket = packet;
        bytes memory hints = yHints;
        uint256 pointCount = hints.length / 48 - 2;
        uint256 witness = pointCount - uint8(badPacket[276]);
        uint256 replacement;
        while (_pointHash(badPacket, replacement) == _pointHash(badPacket, witness)) {
            ++replacement;
            require(replacement < witness, "fixture needs distinct commitment and witness points");
        }
        for (uint256 i; i < 48; ++i) {
            badPacket[POINT_START + witness * 48 + i] = badPacket[POINT_START + replacement * 48 + i];
            hints[(witness + 2) * 48 + i] = hints[(replacement + 2) * 48 + i];
        }
        (bool outer, bool inner) = diagnostics.pairingResults{gas: VERIFY_GAS_LIMIT}(badPacket, hints, expectedClaim);
        require(!outer, "changed opening witness must fail the outer pairing");
        require(inner, "opening mutation must preserve the deferred pairing");
        require(
            !verifier.verify{gas: VERIFY_GAS_LIMIT}(badPacket, hints, expectedClaim), "invalid outer pairing accepted"
        );
    }

    function testSameVerifierAcceptsDifferentLibraryStatements() public view {
        (bytes memory otherPacket, bytes memory otherHints, uint64[18] memory otherClaim) = _otherStatement();
        require(verifier.verify{gas: VERIFY_GAS_LIMIT}(packet, yHints, expectedClaim), "first statement rejected");
        require(
            verifier.verify{gas: VERIFY_GAS_LIMIT}(otherPacket, otherHints, otherClaim), "second statement rejected"
        );
    }

    function testRejectsCrossedExpectedClaims() public view {
        (bytes memory otherPacket, bytes memory otherHints, uint64[18] memory otherClaim) = _otherStatement();
        _assertRejected(packet, yHints, otherClaim);
        _assertRejected(otherPacket, otherHints, expectedClaim);
    }

    function testRejectsEveryMutatedExpectedClaimWord() public view {
        for (uint256 i; i < 18; ++i) {
            uint64[18] memory badClaim = expectedClaim;
            badClaim[i] ^= 1;
            _assertRejected(packet, yHints, badClaim);
        }
    }

    function testRejectsNoncanonicalAbiClaimWords() public view {
        for (uint256 i; i < 18; ++i) {
            bytes memory encoded = abi.encodeCall(KzgVerifier.verify, (packet, yHints, expectedClaim));
            encoded[4 + 64 + i * 32 + 23] = bytes1(uint8(1));
            (bool success,) = address(verifier).staticcall{gas: VERIFY_GAS_LIMIT}(encoded);
            require(!success, "noncanonical ABI claim accepted");
        }
    }

    function testRejectsChangedProfile() public view {
        bytes memory bad = packet;
        bad[0] ^= 0x01;
        _assertRejected(bad, yHints, expectedClaim);
    }

    function testRejectsChangedPublicClaim() public view {
        bytes memory bad = packet;
        bad[32] ^= 0x01;
        _assertRejected(bad, yHints, expectedClaim);
    }

    function testRejectsChangedClaimEvenWhenExpectedClaimMatches() public view {
        bytes memory bad = packet;
        uint64[18] memory changedClaim = expectedClaim;
        bad[32] ^= 0x01;
        changedClaim[0] ^= 1;
        _assertRejected(bad, yHints, changedClaim);
    }

    function testRejectsChangedOpenedValue() public view {
        bytes memory bad = packet;
        uint256 scalarStart = POINT_START + (yHints.length / 48 - 2) * 48;
        bad[scalarStart + 32] ^= 0x01;
        _assertRejected(bad, yHints, expectedClaim);
    }

    function testRejectsNonCanonicalScalar() public view {
        bytes memory bad = packet;
        uint256 scalarStart = POINT_START + (yHints.length / 48 - 2) * 48;
        for (uint256 i; i < 32; ++i) {
            bad[scalarStart + i] = 0xff;
        }
        _assertRejected(bad, yHints, expectedClaim);
    }

    function testRejectsChangedDeferredOperand() public view {
        bytes memory bad = packet;
        bad[176] ^= 0x01;
        _assertRejected(bad, yHints, expectedClaim);
    }

    function testRejectsMalformedPointEncoding() public view {
        bytes memory bad = packet;
        for (uint256 i; i < 48; ++i) {
            bad[POINT_START + i] = 0xff;
        }
        _assertRejected(bad, yHints, expectedClaim);
    }

    function testRejectsChangedHint() public view {
        bytes memory bad = yHints;
        bad[47] ^= 0x01;
        _assertRejected(packet, bad, expectedClaim);
    }

    function testRejectsNonCanonicalHint() public view {
        bytes memory bad = yHints;
        for (uint256 i; i < 48; ++i) {
            bad[i] = 0xff;
        }
        _assertRejected(packet, bad, expectedClaim);
    }

    function testRejectsWrongCompactMagicAndOpeningCount() public view {
        bytes memory bad = packet;
        bad[272] ^= 0x01;
        _assertRejected(bad, yHints, expectedClaim);
        bad = packet;
        bad[276] = 0x00;
        _assertRejected(bad, yHints, expectedClaim);
        bad[276] = 0x04;
        _assertRejected(bad, yHints, expectedClaim);
    }

    function testRejectsTrailingPacketAndHintBytes() public view {
        _assertRejected(bytes.concat(packet, hex"00"), yHints, expectedClaim);
        _assertRejected(packet, bytes.concat(yHints, hex"00"), expectedClaim);
    }

    function testRejectsTruncatedPacketsAndHints() public view {
        bytes memory proof = packet;
        bytes memory hints = yHints;
        uint256[7] memory lengths = [uint256(0), 31, 175, 223, 271, 276, proof.length - 1];
        for (uint256 i; i < lengths.length; ++i) {
            _assertRejected(_prefix(proof, lengths[i]), hints, expectedClaim);
        }
        _assertRejected(proof, _prefix(hints, hints.length - 1), expectedClaim);
    }

    function _assertRejected(bytes memory proof, bytes memory hints, uint64[18] memory claim) private view {
        (bool success, bytes memory result) = address(verifier).staticcall{gas: VERIFY_GAS_LIMIT}(
            abi.encodeWithSelector(KzgVerifier.verify.selector, proof, hints, claim)
        );
        require(!success || (result.length == 32 && !abi.decode(result, (bool))), "invalid proof accepted");
    }

    function _otherStatement()
        private
        view
        returns (bytes memory otherPacket, bytes memory otherHints, uint64[18] memory otherClaim)
    {
        string memory otherFixture = _readFixture("fixture-other-statement.json");
        require(
            vm.parseJsonBytes32(otherFixture, ".profileId") == vm.parseJsonBytes32(fixture, ".profileId"),
            "statements must use the same verifier profile"
        );
        otherPacket = vm.parseJsonBytes(otherFixture, ".packet");
        otherHints = vm.parseJsonBytes(otherFixture, ".yHints");
        otherClaim = _readExpectedClaim(otherFixture);
        require(keccak256(abi.encode(otherClaim)) != keccak256(abi.encode(expectedClaim)), "claims must differ");
    }

    function _readExpectedClaim(string memory json) private pure returns (uint64[18] memory claim) {
        uint256[] memory words = vm.parseJsonUintArray(json, ".expectedClaim");
        require(words.length == 18, "expected claim must have 18 words");
        for (uint256 i; i < 18; ++i) {
            require(words[i] <= type(uint64).max, "expected claim word exceeds uint64");
            claim[i] = uint64(words[i]);
        }
    }

    function _readFixture(string memory filename) private view returns (string memory) {
        return vm.readFile(string.concat(vm.projectRoot(), "/testdata/", filename));
    }

    function _pointHash(bytes memory proof, uint256 point) private pure returns (bytes32) {
        bytes memory encoded = new bytes(48);
        for (uint256 i; i < 48; ++i) {
            encoded[i] = proof[POINT_START + point * 48 + i];
        }
        return keccak256(encoded);
    }

    function _prefix(bytes memory data, uint256 length) private pure returns (bytes memory result) {
        result = new bytes(length);
        for (uint256 i; i < length; ++i) {
            result[i] = data[i];
        }
    }
}
