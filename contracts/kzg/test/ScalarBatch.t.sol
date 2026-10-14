// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;
import {Scalar} from "../src/Scalar.sol";

contract ScalarBatchHarness {
    function batch(uint256[6] memory values) external view returns (uint256[6] memory) {
        return Scalar.inverseBatch6(values);
    }
}

contract ScalarBatchTest {
    ScalarBatchHarness private harness = new ScalarBatchHarness();

    function testBatchInversesAndAllSupportedDegreeNormalizations() public view {
        uint256[6] memory values = [uint256(1), 3, 7, 17, 257, Scalar.MODULUS - 1];
        uint256[6] memory results = harness.batch(values);
        for (uint256 i; i < 6; ++i) {
            require(mulmod(values[i], results[i], Scalar.MODULUS) == 1, "inverse differs");
        }
        for (uint256 d = 1; d <= 28; ++d) {
            uint256 inverseDegree = Scalar.MODULUS - ((Scalar.MODULUS - 1) >> d);
            require(mulmod(uint256(1) << d, inverseDegree, Scalar.MODULUS) == 1, "degree inverse differs");
        }
    }

    function testBatchRejectsEveryZeroDenominatorPosition() public view {
        for (uint256 i; i < 6; ++i) {
            uint256[6] memory values = [uint256(1), 3, 7, 17, 257, Scalar.MODULUS - 1];
            values[i] = 0;
            (bool ok, bytes memory reason) =
                address(harness).staticcall(abi.encodeCall(ScalarBatchHarness.batch, (values)));
            require(!ok && bytes4(reason) == Scalar.ZeroDenominator.selector, "zero denominator accepted");
        }
    }
}
