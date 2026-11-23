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

    function _reject(bytes memory badProof, bytes32 badDigest) private view {
        require(!adapter.verify{gas: 2_000_000}(badProof, badDigest), "invalid BLS12-381 proof accepted");
    }
}
