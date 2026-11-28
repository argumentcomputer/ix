// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

import {IxPlonkVerifier, IPlonkVerifier} from "../src/IxPlonkVerifier.sol";
import {PlonkVerifier as Bls12381PlonkVerifier} from "../testdata/bls12-381/Bls12381PlonkVerifier.sol";

interface Vm {
    function projectRoot() external view returns (string memory);
    function readFile(string calldata path) external view returns (string memory);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
    function parseJsonBytes32(string calldata json, string calldata key) external pure returns (bytes32);
    function parseJsonString(string calldata json, string calldata key) external pure returns (string memory);
}

contract GasGriefBls12381PlonkVerifier is IPlonkVerifier {
    function Verify(bytes calldata, uint256[] calldata) external pure returns (bool) {
        uint256 i;
        while (true) {
            unchecked {
                ++i;
            }
        }
        return i == 0;
    }
}

contract IxBls12381PlonkVerifierTest {
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    IxPlonkVerifier private adapter;
    Bls12381PlonkVerifier private plonk;
    bytes private proof;
    bytes32 private digest;
    event log_named_uint(string key, uint256 value);

    function setUp() public {
        string memory fixture = vm.readFile(string.concat(vm.projectRoot(), "/testdata/bls12-381/proof.json"));
        require(
            keccak256(bytes(vm.parseJsonString(fixture, ".curve"))) == keccak256(bytes("bls12-381")),
            "fixture is not BLS12-381"
        );
        proof = vm.parseJsonBytes(fixture, ".proof");
        digest = vm.parseJsonBytes32(fixture, ".claimDigest");
        plonk = new Bls12381PlonkVerifier();
        adapter = new IxPlonkVerifier(IPlonkVerifier(address(plonk)), address(plonk).codehash);
    }

    function testValidBls12381Proof() public {
        bytes memory bytes_ = proof;
        require(bytes_.length == 1184, "unexpected BLS12-381 PLONK Solidity proof length");
        uint256 start = gasleft();
        require(adapter.verify{gas: 2_000_000}(bytes_, digest), "valid BLS12-381 EIP-2537 proof rejected");
        uint256 used = start - gasleft();
        emit log_named_uint("BLS12-381 EIP-2537 PLONK external call gas", used);
        emit log_named_uint("BLS12-381 PLONK proof bytes", bytes_.length);
        emit log_named_uint("BLS12-381 PLONK ABI calldata bytes", abi.encodeCall(adapter.verify, (bytes_, digest)).length);
        require(used < adapter.VERIFICATION_GAS(), "BLS12-381 verification exceeds its gas budget");
    }

    function testBls12381BothDigestHalvesAreBound() public view {
        _reject(proof, digest ^ bytes32(uint256(1)));
        _reject(proof, digest ^ bytes32(uint256(1) << 128));
    }

    function testBls12381MalformedProofs() public view {
        _reject(new bytes(proof.length - 1), digest);
        _reject(bytes.concat(proof, hex"00"), digest);
        bytes memory wrong = proof;
        wrong[0] ^= bytes1(0x01);
        _reject(wrong, digest);
        for (uint256 i; i < 96; ++i) wrong[i] = 0xff;
        _reject(wrong, digest);
    }

    function testBls12381MissingOrDifferentVerifierCodeRejected() public {
        try new IxPlonkVerifier(IPlonkVerifier(address(1)), bytes32(0)) {
            revert("missing verifier accepted");
        } catch {}
        try new IxPlonkVerifier(IPlonkVerifier(address(plonk)), bytes32(0)) {
            revert("different code accepted");
        } catch {}
    }

    function testBls12381GasGriefingBounded() public {
        GasGriefBls12381PlonkVerifier grief = new GasGriefBls12381PlonkVerifier();
        IxPlonkVerifier griefAdapter = new IxPlonkVerifier(IPlonkVerifier(address(grief)), address(grief).codehash);
        uint256 start = gasleft();
        require(!griefAdapter.verify{gas: 2_000_000}(proof, digest), "griefing verifier accepted");
        uint256 used = start - gasleft();
        require(used < 1_500_000, "griefing verifier exhausted caller gas");
    }

    function testBls12381InsufficientGasRevertsOnValidProof() public view {
        uint256 threshold = (adapter.VERIFICATION_GAS() * 64) / 63 + 10_000;
        uint256[4] memory lowBudgets = [uint256(100_000), uint256(200_000), adapter.VERIFICATION_GAS(), threshold - 1];
        for (uint256 i; i < lowBudgets.length; ++i) {
            try adapter.verify{gas: lowBudgets[i]}(proof, digest) returns (bool) {
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
        require(adapter.verify{gas: threshold + 20_000}(proof, digest), "valid BLS12-381 proof rejected above threshold");
    }

    function testBls12381DeploymentLimits() public view {
        require(address(plonk).code.length <= 24576, "BLS12-381 PLONK verifier exceeds EIP-170");
        require(address(adapter).code.length <= 24576, "adapter exceeds EIP-170");
        require(type(Bls12381PlonkVerifier).creationCode.length <= 49152, "BLS12-381 PLONK initcode exceeds EIP-3860");
    }

    function testRawBls12381VerifierNegativeControls() public view {
        uint256 BLS12_381_R_MOD = 52435875175126190479447740508185965837690552500527637822603658699938581184513;
        uint256[] memory validInputs = _digestToInputs(digest);
        require(plonk.Verify{gas: 2_000_000}(proof, validInputs), "raw valid BLS12-381 PLONK proof rejected");

        // Unreduced public inputs (`input + R_MOD` and exact `R_MOD`) must revert on raw verifier.
        uint256[] memory bad0 = new uint256[](2);
        bad0[0] = validInputs[0] + BLS12_381_R_MOD;
        bad0[1] = validInputs[1];
        _assertRawReverts(proof, bad0, "raw BLS12-381 verifier accepted input[0] + R_MOD");

        uint256[] memory bad1 = new uint256[](2);
        bad1[0] = validInputs[0];
        bad1[1] = validInputs[1] + BLS12_381_R_MOD;
        _assertRawReverts(proof, bad1, "raw BLS12-381 verifier accepted input[1] + R_MOD");

        uint256[] memory exactR = new uint256[](2);
        exactR[0] = BLS12_381_R_MOD;
        exactR[1] = validInputs[1];
        _assertRawReverts(proof, exactR, "raw BLS12-381 verifier accepted input[0] == R_MOD");

        // All-zero proof of expected length (1184 bytes) must be rejected.
        bytes memory allZero = new bytes(proof.length);
        _assertRawRejected(allZero, validInputs, "raw BLS12-381 verifier accepted all-zero proof");
        _reject(allZero, digest);

        // BLS12-381 on-curve non-subgroup torsion point (0, 2) (y^2 = 4 = x^3 + 4,
        // outside prime-order G1 subgroup r) injected into L, Z, W_zeta, and BSB22 slots.
        uint256[4] memory g1Offsets = [uint256(0x00), uint256(0x2e0), uint256(0x360), uint256(0x440)];
        for (uint256 i; i < g1Offsets.length; ++i) {
            bytes memory torsionProof = _withBlsTorsionG1(proof, g1Offsets[i]);
            _assertRawRejected(torsionProof, validInputs, "raw BLS12-381 verifier accepted torsion point (0, 2)");
            _reject(torsionProof, digest);
        }
    }

    function _withBlsTorsionG1(bytes memory base, uint256 offset) private pure returns (bytes memory mutated) {
        mutated = bytes.concat(base);
        for (uint256 i; i < 96; ++i) {
            mutated[offset + i] = bytes1(0x00);
        }
        mutated[offset + 95] = bytes1(0x02);
    }

    function _digestToInputs(bytes32 expectedClaimDigest) private pure returns (uint256[] memory inputs) {
        inputs = new uint256[](2);
        inputs[0] = _reverse128(uint128(uint256(expectedClaimDigest) >> 128));
        inputs[1] = _reverse128(uint128(uint256(expectedClaimDigest)));
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

    function _assertRawReverts(bytes memory p, uint256[] memory inputs, string memory errMsg) private view {
        try plonk.Verify{gas: 2_000_000}(p, inputs) returns (bool) {
            revert(errMsg);
        } catch {}
    }

    function _assertRawRejected(bytes memory p, uint256[] memory inputs, string memory errMsg) private view {
        try plonk.Verify{gas: 2_000_000}(p, inputs) returns (bool valid) {
            require(!valid, errMsg);
        } catch {}
    }

    function _reject(bytes memory badProof, bytes32 badDigest) private view {
        require(!adapter.verify{gas: 2_000_000}(badProof, badDigest), "invalid BLS12-381 proof accepted");
    }
}
