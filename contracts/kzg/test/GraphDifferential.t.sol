// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;
import {KzgVerifier} from "../src/KzgVerifier.sol";
import {Scalar} from "../src/Scalar.sol";

contract GraphDifferentialHarness is KzgVerifier {
    function _proofLayout(Profile memory, Proof memory) internal pure override returns (uint256, uint256) {
        return (0, 0);
    }

    function _openingCoefficients(Profile memory, Proof memory, uint256[6] memory)
        internal
        pure
        override
        returns (uint256[] memory, uint256[] memory)
    {
        return (new uint256[](0), new uint256[](0));
    }
    function _profile() internal pure override returns (Profile memory profile) {}

    function evaluateBoth(uint256 trial) external pure returns (uint256[] memory direct, uint256[] memory interpreted) {
        Proof memory proof;
        proof.values = new uint256[](18);
        for (uint256 i; i < 18; ++i) {
            proof.values[i] = mulmod(i + trial, R - 1, R);
        }
        proof.matrices[0] = Matrix(3, 2, 0, 0);
        proof.matrices[6] = Matrix(3, 2, 0, 6);
        proof.matrices[2] = Matrix(3, 2, 0, 12);
        EvaluationView memory view_;
        view_.publics = [trial, addmod(trial, 1, R), addmod(trial, 2, R), addmod(trial, 3, R)];
        view_.first = addmod(trial, 5, R);
        view_.last = addmod(trial, 7, R);
        view_.transition = addmod(trial, 9, R);
        Circuit memory c;
        c.nodes = new uint256[4][](18);
        c.nodes[0] = [uint256(0), 52435875175126190479447740508185965837690552500527637822603658699938581184512, 0, 0];
        c.nodes[1] = [uint256(1), 0, 0, 0];
        c.nodes[2] = [uint256(1), 0, 1, 2];
        c.nodes[3] = [uint256(1), 1, 0, 1];
        c.nodes[4] = [uint256(1), 1, 1, 0];
        c.nodes[5] = [uint256(1), 2, 0, 1];
        c.nodes[6] = [uint256(1), 2, 1, 2];
        c.nodes[7] = [uint256(2), 0, 0, 0];
        c.nodes[8] = [uint256(2), 1, 0, 0];
        c.nodes[9] = [uint256(2), 2, 0, 0];
        c.nodes[10] = [uint256(2), 3, 0, 0];
        c.nodes[11] = [uint256(3), 0, 0, 0];
        c.nodes[12] = [uint256(4), 0, 0, 0];
        c.nodes[13] = [uint256(5), 0, 0, 0];
        c.nodes[14] = [uint256(6), 0, 1, 0];
        c.nodes[15] = [uint256(7), 1, 2, 0];
        c.nodes[16] = [uint256(8), 14, 15, 0];
        c.nodes[17] = [uint256(9), 16, 0, 0];
        direct = _evaluateGraph(c, proof, 0, view_);
        interpreted = _referenceGraph(c, proof, 0, view_);
    }

    function _referenceGraph(Circuit memory c, Proof memory proof, uint256 ci, EvaluationView memory view_)
        private
        pure
        returns (uint256[] memory values)
    {
        values = new uint256[](c.nodes.length);
        for (uint256 i; i < values.length; ++i) {
            uint256[4] memory node = c.nodes[i];
            uint256 op = node[0];
            uint256 a = node[1];
            uint256 b = node[2];
            if (op == 0) {
                if (a >= R) revert InvalidProfile();
                values[i] = a;
            } else if (op == 1) {
                uint256 index = a == 0 ? ci : (a == 1 ? 6 + ci : 2 + ci);
                Matrix memory m = proof.matrices[index];
                if (a > 2 || b >= m.rows || node[3] >= m.width) revert InvalidProfile();
                values[i] = proof.values[m.valueOffset + b * m.width + node[3]];
            } else if (op == 2) {
                values[i] = view_.publics[a];
            } else if (op == 3) {
                values[i] = view_.first;
            } else if (op == 4) {
                values[i] = view_.last;
            } else if (op == 5) {
                values[i] = view_.transition;
            } else {
                if (a >= i || (op != 9 && b >= i)) revert InvalidProfile();
                if (op == 6) values[i] = addmod(values[a], values[b], R);
                else if (op == 7) values[i] = Scalar.sub(values[a], values[b]);
                else if (op == 8) values[i] = mulmod(values[a], values[b], R);
                else if (op == 9) values[i] = Scalar.negate(values[a]);
                else revert InvalidProfile();
            }
        }
    }

    function _evaluateGraph(Circuit memory, Proof memory proof, uint256 ci, EvaluationView memory view_)
        internal
        pure
        override
        returns (uint256[] memory values)
    {
        if (ci == 0) return _evaluateCircuit0(proof, view_);
        revert InvalidProfile();
    }

    function _evaluateCircuit0(Proof memory proof, EvaluationView memory view_)
        private
        pure
        returns (uint256[] memory values)
    {
        values = new uint256[](18);
        values[0] = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000;
        values[1] = proof.values[proof.matrices[0].valueOffset];
        values[2] = proof.values[proof.matrices[0].valueOffset + 5];
        values[3] = proof.values[proof.matrices[6].valueOffset + 1];
        values[4] = proof.values[proof.matrices[6].valueOffset + 3];
        values[5] = proof.values[proof.matrices[2].valueOffset + 1];
        values[6] = proof.values[proof.matrices[2].valueOffset + 5];
        values[7] = view_.publics[0];
        values[8] = view_.publics[1];
        values[9] = view_.publics[2];
        values[10] = view_.publics[3];
        values[11] = view_.first;
        values[12] = view_.last;
        values[13] = view_.transition;
        values[14] = addmod(values[0], values[1], R);
        values[15] = Scalar.sub(values[1], values[2]);
        values[16] = mulmod(values[14], values[15], R);
        values[17] = Scalar.negate(values[16]);
    }
}

contract GraphDifferentialTest {
    GraphDifferentialHarness private harness = new GraphDifferentialHarness();

    function testEveryGraphOpcodeAndVariableRowMatchesInterpreter() public view {
        for (uint256 trial; trial < 4; ++trial) {
            (uint256[] memory direct, uint256[] memory interpreted) = harness.evaluateBoth(trial * 19);
            require(keccak256(abi.encode(direct)) == keccak256(abi.encode(interpreted)), "generated graph differs");
        }
    }
}
