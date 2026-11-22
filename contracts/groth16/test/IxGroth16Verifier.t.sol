// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

import {IxGroth16Verifier, IGroth16Verifier} from "../src/IxGroth16Verifier.sol";
import {Verifier as PlainVerifier} from "../testdata/plain/Verifier.sol";
import {Verifier as WrapperVerifier} from "../testdata/wrapper/Verifier.sol";

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
    function parseJsonBytes32(string calldata json, string calldata key) external pure returns (bytes32);
}

contract IxGroth16VerifierTest {
    event log_named_uint(string key, uint256 val);
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function vector(string memory name) private view returns (bytes memory proof, bytes32 claim) {
        string memory data = vm.readFile(string.concat("testdata/", name, "/proof.json"));
        return (vm.parseJsonBytes(data, ".proof"), vm.parseJsonBytes32(data, ".digest"));
    }

    function facade(address verifier) private returns (IxGroth16Verifier) {
        return new IxGroth16Verifier(IGroth16Verifier(verifier), verifier.codehash);
    }

    function testPlainProofAndClaimBinding() public {
        IxGroth16Verifier verifier = facade(address(new PlainVerifier()));
        (bytes memory proof, bytes32 claim) = vector("plain");
        require(proof.length == 256, "unexpected plain encoding");
        require(verifier.verify(proof, claim), "valid plain proof rejected");
        require(!verifier.verify(proof, bytes32(uint256(claim) ^ 1)), "wrong claim accepted");
        require(!verifier.verify(bytes.concat(proof, hex"00"), claim), "trailing bytes accepted");
        require(!verifier.verify(hex"00", claim), "short proof accepted");
        proof[0] = 0xff;
        require(!verifier.verify(proof, claim), "invalid point accepted");
    }

    function testDifferentVerifierRejectsProof() public {
        IxGroth16Verifier verifier = facade(address(new PlainVerifier()));
        (bytes memory proof, bytes32 claim) = vector("wrapper");
        require(!verifier.verify(proof, claim), "proof for another key accepted");
    }

    function testRealKzgWrapperProof() public {
        IxGroth16Verifier verifier = facade(address(new WrapperVerifier()));
        (bytes memory proof, bytes32 claim) = vector("wrapper");
        uint256 before = gasleft();
        require(verifier.verify(proof, claim), "valid KZG wrapper proof rejected");
        uint256 used = before - gasleft();
        emit log_named_uint("KZG wrapper verification gas", used);
        require(used < verifier.VERIFICATION_GAS(), "verification exceeds its gas budget");
        require(!verifier.verify(proof, bytes32(uint256(claim) ^ 1)), "wrong KZG claim accepted");
        require(proof.length == 384, "unexpected committed encoding");
        require(!verifier.verify(proof, bytes32(uint256(claim) ^ (1 << 128))), "wrong claim half accepted");
        proof[256] ^= bytes1(0x01);
        require(!verifier.verify(proof, claim), "changed commitment accepted");
        proof[256] ^= bytes1(0x01);
        proof[383] ^= bytes1(0x01);
        require(!verifier.verify(proof, claim), "changed commitment proof accepted");
    }

    function testInsufficientGasRevertsOnValidProof() public {
        IxGroth16Verifier plainVerifier = facade(address(new PlainVerifier()));
        (bytes memory plainProof, bytes32 plainClaim) = vector("plain");
        _assertLowGasReverts(plainVerifier, plainProof, plainClaim);

        IxGroth16Verifier wrapperVerifier = facade(address(new WrapperVerifier()));
        (bytes memory wrapperProof, bytes32 wrapperClaim) = vector("wrapper");
        _assertLowGasReverts(wrapperVerifier, wrapperProof, wrapperClaim);
    }

    function _assertLowGasReverts(IxGroth16Verifier verifier, bytes memory proof, bytes32 claim) private view {
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
        require(verifier.verify{gas: threshold + 20_000}(proof, claim), "valid proof rejected above threshold");
    }

    function testMissingOrDifferentVerifierCodeRejected() public {
        try new IxGroth16Verifier(IGroth16Verifier(address(1)), bytes32(0)) {
            revert("missing verifier accepted");
        } catch {}
        address verifier = address(new PlainVerifier());
        try new IxGroth16Verifier(IGroth16Verifier(verifier), bytes32(0)) {
            revert("different code accepted");
        } catch {}
    }
}
