// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

import {IGroth16Verifier} from "../src/IxGroth16Verifier.sol";
import {IxBls12381Groth16Verifier} from "../src/IxBls12381Groth16Verifier.sol";
import {Verifier as BlsPlainVerifier} from "../testdata/bls12-381/plain/Groth16Verifier.sol";
import {Verifier as BlsCommittedVerifier} from "../testdata/bls12-381/committed/Groth16Verifier.sol";

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
    function parseJsonBytes32(string calldata json, string calldata key) external pure returns (bytes32);
}

contract GasGriefBlsGroth16Verifier is IGroth16Verifier {
    function verifyProof(bytes calldata, uint256[2] calldata) external pure {
        uint256 i;
        while (true) {
            unchecked {
                ++i;
            }
        }
    }
}

contract IxBls12381Groth16VerifierTest {
    event log_named_uint(string key, uint256 val);
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function vector(string memory name) private view returns (bytes memory proof, bytes32 claim) {
        string memory data = vm.readFile(string.concat("testdata/bls12-381/", name, "/proof.json"));
        return (vm.parseJsonBytes(data, ".proof"), vm.parseJsonBytes32(data, ".digest"));
    }

    function facade(address verifier) private returns (IxBls12381Groth16Verifier) {
        return new IxBls12381Groth16Verifier(IGroth16Verifier(verifier), verifier.codehash);
    }

    function testBls12381PlainProofAndClaimBinding() public {
        BlsPlainVerifier inner = new BlsPlainVerifier();
        IxBls12381Groth16Verifier verifier = facade(address(inner));
        (bytes memory proof, bytes32 claim) = vector("plain");
        require(proof.length == 384, "unexpected BLS12-381 plain encoding");
        uint256 before = gasleft();
        require(verifier.verify(proof, claim), "valid BLS12-381 plain proof rejected");
        uint256 used = before - gasleft();
        emit log_named_uint("BLS12-381 EIP-2537 Groth16 plain verification gas", used);
        require(used < verifier.VERIFICATION_GAS(), "verification exceeds its gas budget");
        require(!verifier.verify(proof, claim ^ bytes32(uint256(1))), "wrong low claim half accepted");
        require(!verifier.verify(proof, claim ^ bytes32(uint256(1) << 128)), "wrong high claim half accepted");
        require(!verifier.verify(bytes.concat(proof, hex"00"), claim), "trailing bytes accepted");
        require(!verifier.verify(new bytes(256), claim), "BN254-length proof accepted");
        proof[0] = 0xff;
        require(!verifier.verify(proof, claim), "invalid point accepted");
    }

    function testBls12381CommittedProofAndClaimBinding() public {
        BlsCommittedVerifier inner = new BlsCommittedVerifier();
        IxBls12381Groth16Verifier verifier = facade(address(inner));
        (bytes memory proof, bytes32 claim) = vector("committed");
        require(proof.length == 576, "unexpected BLS12-381 committed encoding");
        uint256 before = gasleft();
        require(verifier.verify(proof, claim), "valid BLS12-381 committed proof rejected");
        uint256 used = before - gasleft();
        emit log_named_uint("BLS12-381 EIP-2537 Groth16 committed verification gas", used);
        require(used < verifier.VERIFICATION_GAS(), "verification exceeds its gas budget");
        require(!verifier.verify(proof, claim ^ bytes32(uint256(1))), "wrong low claim half accepted");
        require(!verifier.verify(proof, claim ^ bytes32(uint256(1) << 128)), "wrong high claim half accepted");
        proof[384] ^= bytes1(0x01);
        require(!verifier.verify(proof, claim), "changed commitment accepted");
        proof[384] ^= bytes1(0x01);
        proof[575] ^= bytes1(0x01);
        require(!verifier.verify(proof, claim), "changed commitment proof accepted");
    }

    function testBls12381DifferentVerifierRejectsProof() public {
        IxBls12381Groth16Verifier verifier = facade(address(new BlsPlainVerifier()));
        (bytes memory proof, bytes32 claim) = vector("committed");
        require(!verifier.verify(proof, claim), "proof for another key accepted");
    }

    function testBls12381GasGriefingBounded() public {
        GasGriefBlsGroth16Verifier grief = new GasGriefBlsGroth16Verifier();
        IxBls12381Groth16Verifier griefAdapter = facade(address(grief));
        (bytes memory proof, bytes32 claim) = vector("plain");
        uint256 start = gasleft();
        require(!griefAdapter.verify{gas: 2_000_000}(proof, claim), "griefing verifier accepted");
        uint256 used = start - gasleft();
        require(used < 1_500_000, "griefing verifier exhausted caller gas");
    }

    function testBls12381InsufficientGasRevertsOnValidProof() public {
        IxBls12381Groth16Verifier plainVerifier = facade(address(new BlsPlainVerifier()));
        (bytes memory plainProof, bytes32 plainClaim) = vector("plain");
        _assertLowGasReverts(plainVerifier, plainProof, plainClaim);

        IxBls12381Groth16Verifier committedVerifier = facade(address(new BlsCommittedVerifier()));
        (bytes memory committedProof, bytes32 committedClaim) = vector("committed");
        _assertLowGasReverts(committedVerifier, committedProof, committedClaim);
    }

    function _assertLowGasReverts(IxBls12381Groth16Verifier verifier, bytes memory proof, bytes32 claim) private view {
        uint256 threshold = (verifier.VERIFICATION_GAS() * 64) / 63 + 10_000;
        uint256[4] memory lowBudgets = [uint256(100_000), uint256(200_000), verifier.VERIFICATION_GAS(), threshold - 1];
        for (uint256 i; i < lowBudgets.length; ++i) {
            try verifier.verify{gas: lowBudgets[i]}(proof, claim) returns (bool) {
                revert("low-gas verify returned instead of reverting");
            } catch Error(string memory reason) {
                require(
                    keccak256(bytes(reason)) == keccak256(bytes("insufficient gas")),
                    "unexpected revert reason"
                );
            } catch {
                revert("expected insufficient gas revert");
            }
        }
        require(verifier.verify{gas: threshold + 20_000}(proof, claim), "valid BLS12-381 proof rejected above threshold");
    }

    function testBls12381MissingOrDifferentVerifierCodeRejected() public {
        try new IxBls12381Groth16Verifier(IGroth16Verifier(address(1)), bytes32(0)) {
            revert("missing verifier accepted");
        } catch {}
        address verifier = address(new BlsPlainVerifier());
        try new IxBls12381Groth16Verifier(IGroth16Verifier(verifier), bytes32(0)) {
            revert("different code accepted");
        } catch {}
    }

    function testBls12381DeploymentLimits() public {
        BlsPlainVerifier plain = new BlsPlainVerifier();
        BlsCommittedVerifier committed = new BlsCommittedVerifier();
        IxBls12381Groth16Verifier adapter = facade(address(committed));
        require(address(plain).code.length <= 24576, "BLS12-381 plain Groth16 verifier exceeds EIP-170");
        require(address(committed).code.length <= 24576, "BLS12-381 committed Groth16 verifier exceeds EIP-170");
        require(address(adapter).code.length <= 24576, "adapter exceeds EIP-170");
        require(type(BlsCommittedVerifier).creationCode.length <= 49152, "BLS12-381 Groth16 initcode exceeds EIP-3860");
    }

    function testRawBls12381VerifierNegativeControls() public {
        _assertRawBlsNegativeControls(IGroth16Verifier(address(new BlsPlainVerifier())), "plain", false);
        _assertRawBlsNegativeControls(IGroth16Verifier(address(new BlsCommittedVerifier())), "committed", true);
    }

    function _assertRawBlsNegativeControls(IGroth16Verifier raw, string memory name, bool committed) private {
        uint256 BLS12_381_R_MOD = 52435875175126190479447740508185965837690552500527637822603658699938581184513;
        IxBls12381Groth16Verifier adapter = facade(address(raw));
        (bytes memory proof, bytes32 claim) = vector(name);
        uint256[2] memory validInputs = _digestToInputs(claim);

        // Sanity: raw verifier accepts the valid fixture proof.
        raw.verifyProof{gas: 2_000_000}(proof, validInputs);

        // Unreduced public inputs (`input + R_MOD` and exact `R_MOD`) must revert on raw verifier.
        _assertRawReverts(raw, proof, [validInputs[0] + BLS12_381_R_MOD, validInputs[1]], "raw BLS12-381 verifier accepted input[0] + R_MOD");
        _assertRawReverts(raw, proof, [validInputs[0], validInputs[1] + BLS12_381_R_MOD], "raw BLS12-381 verifier accepted input[1] + R_MOD");
        _assertRawReverts(raw, proof, [BLS12_381_R_MOD, validInputs[1]], "raw BLS12-381 verifier accepted input[0] == R_MOD");

        // All-zero proof of expected length must revert on raw verifier and return false via adapter.
        bytes memory allZero = new bytes(proof.length);
        _assertRawReverts(raw, allZero, validInputs, "raw BLS12-381 verifier accepted all-zero proof");
        require(!adapter.verify(allZero, claim), "adapter accepted all-zero BLS12-381 proof");

        // BLS12-381 on-curve non-subgroup torsion point (0, 2) (y^2 = 4 = x^3 + 4,
        // outside prime-order G1 subgroup r) injected into A (0x00) and C (0x120),
        // plus commitment (0x180) and PoK (0x1e0) for committed proofs.
        bytes memory torsionA = _withBlsTorsionG1(proof, 0x00);
        _assertRawReverts(raw, torsionA, validInputs, "raw BLS12-381 verifier accepted torsion point (0, 2) in A");
        require(!adapter.verify(torsionA, claim), "adapter accepted torsion point (0, 2) in A");

        bytes memory torsionC = _withBlsTorsionG1(proof, 0x120);
        _assertRawReverts(raw, torsionC, validInputs, "raw BLS12-381 verifier accepted torsion point (0, 2) in C");
        require(!adapter.verify(torsionC, claim), "adapter accepted torsion point (0, 2) in C");

        if (committed) {
            bytes memory torsionCom = _withBlsTorsionG1(proof, 0x180);
            _assertRawReverts(raw, torsionCom, validInputs, "raw BLS12-381 verifier accepted torsion point (0, 2) in commitment");
            require(!adapter.verify(torsionCom, claim), "adapter accepted torsion point (0, 2) in commitment");

            bytes memory torsionPok = _withBlsTorsionG1(proof, 0x1e0);
            _assertRawReverts(raw, torsionPok, validInputs, "raw BLS12-381 verifier accepted torsion point (0, 2) in PoK");
            require(!adapter.verify(torsionPok, claim), "adapter accepted torsion point (0, 2) in PoK");
        }
    }

    function _withBlsTorsionG1(bytes memory base, uint256 offset) private pure returns (bytes memory mutated) {
        mutated = bytes.concat(base);
        for (uint256 i; i < 96; ++i) {
            mutated[offset + i] = bytes1(0x00);
        }
        mutated[offset + 95] = bytes1(0x02);
    }

    function _digestToInputs(bytes32 expectedClaimDigest) private pure returns (uint256[2] memory inputs) {
        inputs = [
            uint256(_reverse128(uint128(uint256(expectedClaimDigest) >> 128))),
            uint256(_reverse128(uint128(uint256(expectedClaimDigest))))
        ];
    }

    function _reverse128(uint128 value) private pure returns (uint128) {
        value = ((value >> 8) & 0x00ff00ff00ff00ff00ff00ff00ff00ff) |
            ((value & 0x00ff00ff00ff00ff00ff00ff00ff00ff) << 8);
        value = ((value >> 16) & 0x0000ffff0000ffff0000ffff0000ffff) |
            ((value & 0x0000ffff0000ffff0000ffff0000ffff) << 16);
        value = ((value >> 32) & 0x00000000ffffffff00000000ffffffff) |
            ((value & 0x00000000ffffffff00000000ffffffff) << 32);
        return (value >> 64) | (value << 64);
    }

    function _assertRawReverts(
        IGroth16Verifier raw,
        bytes memory p,
        uint256[2] memory inputs,
        string memory errMsg
    ) private view {
        try raw.verifyProof{gas: 2_000_000}(p, inputs) {
            revert(errMsg);
        } catch {}
    }
}
