// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

import {IxPlonkVerifier, IPlonkVerifier} from "../src/IxPlonkVerifier.sol";
import {PlonkVerifier} from "../src/PlonkVerifier.sol";

interface Vm {
    function projectRoot() external view returns (string memory);
    function readFile(string calldata path) external view returns (string memory);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
    function parseJsonBytes32(string calldata json, string calldata key) external pure returns (bytes32);
    function parseJsonString(string calldata json, string calldata key) external pure returns (string memory);
}

contract GasGriefPlonkVerifier is IPlonkVerifier {
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

contract IxPlonkVerifierTest {
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    /// SHA-256 of crates/proof-compression/verifying-keys/0.4/plonk-verifying-key.bin,
    /// the key src/PlonkVerifier.sol is generated from.
    string private constant RELEASE_KEY_SHA256 = "032ff41ec34de4488553485a361d80d23e0dde1e8acbb07457e4625c85aa324b";
    IxPlonkVerifier private adapter;
    PlonkVerifier private plonk;
    bytes private proof;
    bytes32 private digest;
    event log_named_uint(string key, uint256 value);

    function setUp() public {
        string memory fixture = vm.readFile(string.concat(vm.projectRoot(), "/testdata/nat-add-comm.json"));
        require(
            keccak256(bytes(vm.parseJsonString(fixture, ".verifyingKeySHA256"))) == keccak256(bytes(RELEASE_KEY_SHA256)),
            "fixture proof is not under the release PLONK key"
        );
        proof = vm.parseJsonBytes(fixture, ".proof");
        digest = vm.parseJsonBytes32(fixture, ".claimDigest");
        plonk = new PlonkVerifier();
        adapter = new IxPlonkVerifier(IPlonkVerifier(address(plonk)), address(plonk).codehash);
    }

    function testValidProof() public {
        bytes memory bytes_ = proof;
        uint256 start = gasleft();
        require(adapter.verify{gas: 2_000_000}(bytes_, digest), "valid proof rejected");
        uint256 used = start - gasleft();
        emit log_named_uint("external call gas excluding transaction intrinsic", used);
        emit log_named_uint("proof bytes", bytes_.length);
        emit log_named_uint("ABI calldata bytes", abi.encodeCall(adapter.verify, (bytes_, digest)).length);
        require(used < adapter.VERIFICATION_GAS(), "verification exceeds its gas budget");
    }

    function testBothDigestHalvesAreBound() public view {
        _reject(proof, digest ^ bytes32(uint256(1)));
        _reject(proof, digest ^ bytes32(uint256(1) << 128));
    }

    function testMalformedProofs() public view {
        _reject(new bytes(proof.length - 1), digest);
        _reject(bytes.concat(proof, hex"00"), digest);
        bytes memory wrong = proof;
        wrong[0] ^= bytes1(0x01);
        _reject(wrong, digest);
        for (uint256 i; i < 96; ++i) wrong[i] = 0xff;
        _reject(wrong, digest);
    }

    function testMissingOrDifferentVerifierCodeRejected() public {
        try new IxPlonkVerifier(IPlonkVerifier(address(1)), bytes32(0)) {
            revert("missing verifier accepted");
        } catch {}
        try new IxPlonkVerifier(IPlonkVerifier(address(plonk)), bytes32(0)) {
            revert("different code accepted");
        } catch {}
    }

    function testGasGriefingBounded() public {
        GasGriefPlonkVerifier grief = new GasGriefPlonkVerifier();
        IxPlonkVerifier griefAdapter = new IxPlonkVerifier(IPlonkVerifier(address(grief)), address(grief).codehash);
        uint256 start = gasleft();
        require(!griefAdapter.verify{gas: 2_000_000}(proof, digest), "griefing verifier accepted");
        uint256 used = start - gasleft();
        require(used < 1_500_000, "griefing verifier exhausted caller gas");
    }

    function testInsufficientGasRevertsOnValidProof() public view {
        uint256 threshold = (adapter.VERIFICATION_GAS() * 64) / 63 + 10_000;
        // Both realistic starvation (~200k gas, below inner verification cost) and
        // boundary gas (VERIFICATION_GAS, where EIP-150 forwards only 63/64) must revert
        // rather than silently returning false on a valid proof.
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
        // Full gas above the EIP-150 threshold still accepts the valid proof.
        require(adapter.verify{gas: threshold + 20_000}(proof, digest), "valid proof rejected above threshold");
    }

    function testDeploymentLimits() public view {
        require(address(plonk).code.length <= 24576, "PLONK verifier exceeds EIP-170");
        require(address(adapter).code.length <= 24576, "adapter exceeds EIP-170");
        require(type(PlonkVerifier).creationCode.length <= 49152, "PLONK initcode exceeds EIP-3860");
    }

    function _reject(bytes memory badProof, bytes32 badDigest) private view {
        require(!adapter.verify{gas: 2_000_000}(badProof, badDigest), "invalid proof accepted");
    }
}
