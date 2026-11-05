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

contract IxPlonkVerifierTest {
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    /// SHA-256 of crates/proof-compression/verifying-keys/0.1/plonk-verifying-key.bin,
    /// the key src/PlonkVerifier.sol is generated from.
    string private constant RELEASE_KEY_SHA256 = "7123a80f9c56b25138ffe8ec47a53c6b0b22b64bf183380d63e5c80a7e3144a9";
    IxPlonkVerifier private adapter;
    PlonkVerifier private plonk;
    bytes private proof;
    bytes32 private digest;
    event log_named_uint(string key, uint256 value);

    function setUp() public {
        string memory fixture = vm.readFile(string.concat(vm.projectRoot(), "/testdata/init.json"));
        require(
            keccak256(bytes(vm.parseJsonString(fixture, ".verifyingKeySHA256"))) == keccak256(bytes(RELEASE_KEY_SHA256)),
            "fixture proof is not under the release PLONK key"
        );
        proof = vm.parseJsonBytes(fixture, ".proof");
        digest = vm.parseJsonBytes32(fixture, ".claimDigest");
        plonk = new PlonkVerifier();
        adapter = new IxPlonkVerifier(IPlonkVerifier(address(plonk)));
    }

    function testValidInitProof() public {
        bytes memory bytes_ = proof;
        uint256 start = gasleft();
        require(adapter.verify{gas: 2_000_000}(bytes_, digest), "valid proof rejected");
        emit log_named_uint("external call gas excluding transaction intrinsic", start - gasleft());
        emit log_named_uint("proof bytes", bytes_.length);
        emit log_named_uint("ABI calldata bytes", abi.encodeCall(adapter.verify, (bytes_, digest)).length);
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

    function testDeploymentLimits() public view {
        require(address(plonk).code.length <= 24576, "PLONK verifier exceeds EIP-170");
        require(address(adapter).code.length <= 24576, "adapter exceeds EIP-170");
        require(type(PlonkVerifier).creationCode.length <= 49152, "PLONK initcode exceeds EIP-3860");
    }

    function _reject(bytes memory badProof, bytes32 badDigest) private view {
        (bool success, bytes memory result) = address(adapter).staticcall{gas: 2_000_000}(
            abi.encodeCall(adapter.verify, (badProof, badDigest))
        );
        require(!success || !abi.decode(result, (bool)), "invalid proof accepted");
    }
}
