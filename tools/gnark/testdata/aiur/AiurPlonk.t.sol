// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

import {PlonkVerifier} from "../src/PlonkVerifier.sol";

interface VmAiur {
    function projectRoot() external view returns (string memory);
    function readFile(string calldata path) external view returns (string memory);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
}

contract AiurPlonkTest {
    VmAiur private constant vm = VmAiur(address(uint160(uint256(keccak256("hevm cheat code")))));
    PlonkVerifier private verifier;
    bytes private proof;
    event log_named_uint(string key, uint256 value);

    function setUp() public {
        verifier = new PlonkVerifier();
        proof = vm.parseJsonBytes(vm.readFile(string.concat(vm.projectRoot(), "/proof.json")), ".proof");
    }

    function expectedCall() private pure returns (uint256[] memory values) {
        // BN254Trace::run(3, -1) returns 9. The callable and channel are fixed
        // in the compiler schema; this array contains its typed public fields.
        values = new uint256[](3);
        values[0] = 3;
        values[1] = 21888242871839275222246405745257275088548364400416034343698204186575808495616;
        values[2] = 9;
    }

    function testExpectedCall() public {
        uint256[] memory expected = expectedCall();
        uint256 start = gasleft();
        require(verifier.Verify(proof, expected), "valid Aiur execution rejected");
        emit log_named_uint("external verifier call gas", start-gasleft());
        emit log_named_uint("Solidity proof bytes", proof.length);
        emit log_named_uint("ABI calldata bytes", abi.encodeCall(verifier.Verify, (proof, expected)).length);
    }

    function reject(bytes memory candidate, uint256[] memory expected) private view {
        (bool ok, bytes memory result) = address(verifier).staticcall{gas: 2_000_000}(abi.encodeCall(verifier.Verify, (candidate, expected)));
        require(!ok || !abi.decode(result, (bool)), "invalid execution accepted");
    }

    function testEveryPublicFieldIsBound() public view {
        for (uint256 i; i < 3; ++i) {
            uint256[] memory expected = expectedCall();
            expected[i] ^= 1;
            reject(proof, expected);
        }
    }

    function testMalformedProofsAreRejected() public view {
        bytes memory wrong = proof;
        wrong[0] ^= bytes1(0x01);
        reject(wrong, expectedCall());
        reject(new bytes(proof.length - 1), expectedCall());
        reject(bytes.concat(proof, hex"00"), expectedCall());
    }

    function testDeploymentLimits() public view {
        require(address(verifier).code.length <= 24576, "runtime exceeds EIP-170");
        require(type(PlonkVerifier).creationCode.length <= 49152, "initcode exceeds EIP-3860");
    }
}
