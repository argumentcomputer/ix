// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

import {KzgVerifier} from "./KzgVerifier.sol";
import {Scalar} from "./Scalar.sol";

/// Test-only conformance circuit; this does not prove a Lean library computation or an inner recursive proof.
contract GeneratedVerifier is KzgVerifier {
    function _profile() internal pure override returns (Profile memory p) {
        p.id = hex"0deb36de58d4c36e4c50b8aca00870e2247446b5d0388232bac081e7a80a3ecb";
        p.seed =
            hex"6d756c74692d737461726b2f6b7a672f6b656363616b3235362f763105000000000000000200000000000000feffff0f0000000048b74609da5ec9a9d59efb1d4c9d91d81815a304a8baab8ba35af4fe0145239f97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8ae3f321e2ba24e302542a3ecf8847e8e820f9ca1b3a6a63bae25140f215344314e1bfc9c36bf2c3dcbe94dec33d71f3cb16010f1b3d33aa5f3f608c385400979ed36dc3fab53d3626f519c74d7e1ebef62c9ad35796404ce2fc3ebb42167b5a1050ac27c3527072b81af0fa9a683e226da79275f2985c9e89a0db969b76e0b6be94fee874c48586737ad5588cf1e1041";
        p.circuits[0] = _circuit0();
        p.circuits[1] = _circuit1();
        p.fixedCompressed =
            hex"823222a72009debb870a4830d1f575665569f38d3030cf3e858a0ed5d292670975f87a6782dd13694b35ded2aa7b1efa893b681bc453d6d641af75548dd948d53b02f4285fcd99928df36f3fc34a778ad6ec52eb4f87cb945b135fa3cf04cbf6abba37ac925569b9f873a311358c021843481ba455d85838893703cedf84f94119ceb6127977d3720047fdbf5864c19fa23222a72009debb870a4830d1f575665569f38d3030cf3e858a0ed5d292670975f87a6782dd13694b35ded2aa7b1efab802d2cc7d74da1faf3968a046aa6197e0b909d29eb20fdb1c6f64c137e06b35ff15e27ba8bba7b26a84d8918ac96c968906b8c938bff29972815c38a95fa420b11d8aee2a238e4731cb4c3dd2a40c3c68f0eb8efb4e160ef586bda285cda9ca80703bbc36c7da9cbc446661ccd0dcd04e77d9ab140eba09f541ef30d9ea589ecbcdd332f507ad907abb4b4aec6cde38b338c799859ef33570c600e98a3c5c9f206f6f32b42d56daa2495f70a799c1ff5ffd57a8610ad0196409711852f361a5807a4def0a190d3633050f0324d1c84a45c71dc9323f7f3bc710705075ebb4d2c5dfdf44a7b7cceaa2170171897e97ec8a88b437486141d78116be238ab3799408e4e29d2c9d717562d3e3afec74f347851c8b9d6332ad98cf19186b53299a1ca96590a931e18e5597187a0ae5e2bab8263471b3d6ef25f2dbdb96f2c016c56dd57b1a70428a9462f5ab1296d8b04c138640c13a05c48547bfdf83485a2c9ba5f0fda9506fa6f63bc5183550d8f0cee8046dc13bd6396eec200b626f130eb44e931b89882a84baee00dcb44c42e27dcff024e1dafaebd919f939a8c4a8a1e140d8a0886aea9c0067f868591d44383a5caf0c818c2064ed5736e915a0a4ab5fee73c0ebd837fa82e9d5915531de15fe6b0eedd2525a429e00d1fcc0b0fe01919dc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008f72ed474f2e94bc70a03fa7a44b8ecc1cac4a0160c242b5be45ca2072e9c1928915e7cdaa9043c24e4e0de71efadb76c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
        p.fixedPoints =
            hex"00000000000000000000000000000000023222a72009debb870a4830d1f575665569f38d3030cf3e858a0ed5d292670975f87a6782dd13694b35ded2aa7b1efa00000000000000000000000000000000059a5cd6a6c06eb274060f8163d32ce1e8d20a93281c3509aee2286a8a628be43aa4f9a4b736ba6fca4b4c904e6a362000000000000000000000000000000000093b681bc453d6d641af75548dd948d53b02f4285fcd99928df36f3fc34a778ad6ec52eb4f87cb945b135fa3cf04cbf6000000000000000000000000000000000663f77b4b3ccd0c9798fbf487ffa5557e8f20a3488c8eea002b5755ce4e57633723393543b26bcb88e27961cd076fb9000000000000000000000000000000000bba37ac925569b9f873a311358c021843481ba455d85838893703cedf84f94119ceb6127977d3720047fdbf5864c19f0000000000000000000000000000000019167223bf1539e9313b1eb613671e1a26f2577f34dba9d69bed058be5288d60e0c403af470ba7ea3efe5a450c0df0a100000000000000000000000000000000023222a72009debb870a4830d1f575665569f38d3030cf3e858a0ed5d292670975f87a6782dd13694b35ded2aa7b1efa000000000000000000000000000000001466b51392bf77e7d7159834df787ff57ba540f1cb68ddb5b84eaa366c4e6a3fe4070659fa1d458fefb3b36fb195748b000000000000000000000000000000001802d2cc7d74da1faf3968a046aa6197e0b909d29eb20fdb1c6f64c137e06b35ff15e27ba8bba7b26a84d8918ac96c9600000000000000000000000000000000105179ec7364256efd4c5027cacb8bf0f2a31d1ffa4495932cc1c6d747acd96b3cd885084176380bbb6c38b54dee0ab6000000000000000000000000000000000906b8c938bff29972815c38a95fa420b11d8aee2a238e4731cb4c3dd2a40c3c68f0eb8efb4e160ef586bda285cda9ca000000000000000000000000000000000c5d5001cf20a09f34e516ab738849f41a57c6f00f5973d308a3bce44c96023541d8bc243756068e7ee85c4c003921780000000000000000000000000000000000703bbc36c7da9cbc446661ccd0dcd04e77d9ab140eba09f541ef30d9ea589ecbcdd332f507ad907abb4b4aec6cde380000000000000000000000000000000001f05e929a402b0931531cf4f69d4021f7015d1a61ef0b8963fad53bdd1f865e348c8ffdb7f3f6db658f2660d778d60b000000000000000000000000000000001338c799859ef33570c600e98a3c5c9f206f6f32b42d56daa2495f70a799c1ff5ffd57a8610ad0196409711852f361a50000000000000000000000000000000018a2847bff0940919da2b8e454db85f017bf161ef743a139d41744179ffe4123d3ea2cf989ff0374c97fc93646f8831e00000000000000000000000000000000007a4def0a190d3633050f0324d1c84a45c71dc9323f7f3bc710705075ebb4d2c5dfdf44a7b7cceaa2170171897e97ec0000000000000000000000000000000009f0c2d419d483817f7c17a298c36e79273d151d36cb306fc0da721a10ebbbab0098719c486a748ed3963fbb3d87529a000000000000000000000000000000000a88b437486141d78116be238ab3799408e4e29d2c9d717562d3e3afec74f347851c8b9d6332ad98cf19186b53299a1c000000000000000000000000000000000173fdab5ff8e932752eebd75a444f824dadf786de1d4c9f8c94083f5450ae828ade841ad893c056666d24d00f403dfd00000000000000000000000000000000096590a931e18e5597187a0ae5e2bab8263471b3d6ef25f2dbdb96f2c016c56dd57b1a70428a9462f5ab1296d8b04c1300000000000000000000000000000000153e9400d0aed3b6e396fe72fea540304a27ef2f649923e359383705dfdde860e6cce8714d39f10ab3b454644c4b3acd000000000000000000000000000000000640c13a05c48547bfdf83485a2c9ba5f0fda9506fa6f63bc5183550d8f0cee8046dc13bd6396eec200b626f130eb44e000000000000000000000000000000000c01f6de10de2001f7903ed92dacf7ea9c6e6376e607ecf274c27dd0ca8f84734e4b7d7b0d367b181303a408e6912fc500000000000000000000000000000000131b89882a84baee00dcb44c42e27dcff024e1dafaebd919f939a8c4a8a1e140d8a0886aea9c0067f868591d44383a5c000000000000000000000000000000000744b1babe423ba9aa5755ae1a4fa2352e3325b3ed8ec5972a8e810bc9daa443617673570494ebe2060c29191f10ec48000000000000000000000000000000000f0c818c2064ed5736e915a0a4ab5fee73c0ebd837fa82e9d5915531de15fe6b0eedd2525a429e00d1fcc0b0fe01919d0000000000000000000000000000000018b62234d86e87a88a141b9ada6e0cc97af1c4de346cf50cb240838438f95fb3a91748ebf0be81c52c89f3e54eb9684700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f72ed474f2e94bc70a03fa7a44b8ecc1cac4a0160c242b5be45ca2072e9c1928915e7cdaa9043c24e4e0de71efadb760000000000000000000000000000000009fb2f189de5c25026eb0288625fc6bb2cb714732cd1bb515b5c1d5a0a201ffa7cdbbeabe25e4cb4ca1870aa825593d900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
        p.generator =
            hex"0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1";
        p.outerH =
            hex"00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be";
        p.outerTauH =
            hex"00000000000000000000000000000000050ac27c3527072b81af0fa9a683e226da79275f2985c9e89a0db969b76e0b6be94fee874c48586737ad5588cf1e104100000000000000000000000000000000116010f1b3d33aa5f3f608c385400979ed36dc3fab53d3626f519c74d7e1ebef62c9ad35796404ce2fc3ebb42167b5a100000000000000000000000000000000044eda01714f357cb8c41b01f89b0398130096fb654a9d23b03528ba2d79a2e376038aa70dbfc979b08149726eb1841d000000000000000000000000000000001993b9f29f67c48d2cbcb76a6e31c341c9da846f9fc99ca4130e2bea5f95805b4b42a404a99b9e3b0835a725bd90ae66";
        p.innerH =
            hex"00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be";
        p.innerTauH =
            hex"00000000000000000000000000000000050ac27c3527072b81af0fa9a683e226da79275f2985c9e89a0db969b76e0b6be94fee874c48586737ad5588cf1e104100000000000000000000000000000000116010f1b3d33aa5f3f608c385400979ed36dc3fab53d3626f519c74d7e1ebef62c9ad35796404ce2fc3ebb42167b5a100000000000000000000000000000000044eda01714f357cb8c41b01f89b0398130096fb654a9d23b03528ba2d79a2e376038aa70dbfc979b08149726eb1841d000000000000000000000000000000001993b9f29f67c48d2cbcb76a6e31c341c9da846f9fc99ca4130e2bea5f95805b4b42a404a99b9e3b0835a725bd90ae66";
    }

    function _circuit0() private pure returns (Circuit memory c) {
        c.logDegree = 5;
        c.mainWidth = 3;
        c.stage2Width = 4;
        c.preprocessedWidth = 15;
        c.quotientDegree = 2;
        c.constraintCount = 5;
        c.maxConstraintDegree = 3;
        c.lookupGroupSize = 2;
        c.mainNext = false;
        c.preprocessedNext = false;
        c.omega = 0x50e0903a157988bab4bcd40e22f55448bf6e88fb4c38fb8a360c60997369df4e;
        c.zeros = new uint256[](1);
        c.zeros[0] = 33;
        c.lookups = new Lookup[](8);
        c.lookups[0].multiplicity = 0;
        c.lookups[0].args = new uint256[](4);
        c.lookups[0].args[0] = 1;
        c.lookups[0].args[1] = 2;
        c.lookups[0].args[2] = 3;
        c.lookups[0].args[3] = 4;
        c.lookups[1].multiplicity = 5;
        c.lookups[1].args = new uint256[](4);
        c.lookups[1].args[0] = 1;
        c.lookups[1].args[1] = 2;
        c.lookups[1].args[2] = 6;
        c.lookups[1].args[3] = 4;
        c.lookups[2].multiplicity = 0;
        c.lookups[2].args = new uint256[](4);
        c.lookups[2].args[0] = 1;
        c.lookups[2].args[1] = 2;
        c.lookups[2].args[2] = 7;
        c.lookups[2].args[3] = 8;
        c.lookups[3].multiplicity = 5;
        c.lookups[3].args = new uint256[](4);
        c.lookups[3].args[0] = 1;
        c.lookups[3].args[1] = 2;
        c.lookups[3].args[2] = 9;
        c.lookups[3].args[3] = 8;
        c.lookups[4].multiplicity = 0;
        c.lookups[4].args = new uint256[](4);
        c.lookups[4].args[0] = 1;
        c.lookups[4].args[1] = 2;
        c.lookups[4].args[2] = 10;
        c.lookups[4].args[3] = 11;
        c.lookups[5].multiplicity = 5;
        c.lookups[5].args = new uint256[](4);
        c.lookups[5].args[0] = 1;
        c.lookups[5].args[1] = 2;
        c.lookups[5].args[2] = 12;
        c.lookups[5].args[3] = 11;
        c.lookups[6].multiplicity = 14;
        c.lookups[6].args = new uint256[](4);
        c.lookups[6].args[0] = 1;
        c.lookups[6].args[1] = 0;
        c.lookups[6].args[2] = 15;
        c.lookups[6].args[3] = 4;
        c.lookups[7].multiplicity = 17;
        c.lookups[7].args = new uint256[](6);
        c.lookups[7].args[0] = 1;
        c.lookups[7].args[1] = 18;
        c.lookups[7].args[2] = 19;
        c.lookups[7].args[3] = 4;
        c.lookups[7].args[4] = 8;
        c.lookups[7].args[5] = 11;
    }

    function _circuit1() private pure returns (Circuit memory c) {
        c.logDegree = 4;
        c.mainWidth = 1;
        c.stage2Width = 1;
        c.preprocessedWidth = 4;
        c.quotientDegree = 1;
        c.constraintCount = 1;
        c.maxConstraintDegree = 2;
        c.lookupGroupSize = 1;
        c.mainNext = false;
        c.preprocessedNext = false;
        c.omega = 0x20b1ce9140267af9dd1c0af834cec32c17beb312f20b6f7653ea61d87742bcce;
        c.zeros = new uint256[](0);
        c.lookups = new Lookup[](1);
        c.lookups[0].multiplicity = 0;
        c.lookups[0].args = new uint256[](6);
        c.lookups[0].args[0] = 1;
        c.lookups[0].args[1] = 2;
        c.lookups[0].args[2] = 3;
        c.lookups[0].args[3] = 4;
        c.lookups[0].args[4] = 5;
        c.lookups[0].args[5] = 6;
    }

    function _evaluateGraph(Circuit memory, Proof memory proof, uint256 ci, EvaluationView memory view_)
        internal
        pure
        override
        returns (uint256[] memory values)
    {
        if (ci == 0) return _evaluateCircuit0(proof, view_);
        if (ci == 1) return _evaluateCircuit1(proof, view_);
        revert InvalidProfile();
    }

    function _evaluateCircuit0(Proof memory proof, EvaluationView memory)
        private
        pure
        returns (uint256[] memory values)
    {
        values = new uint256[](34);
        values[0] = 0x0000000000000000000000000000000000000000000000000000000000000001;
        values[1] = 0x000000000000000000000000000000000000000000000000000000000000005e;
        values[2] = 0x0000000000000000000000000000000000000000000000000000000000000000;
        values[3] = proof.values[proof.matrices[6].valueOffset + 5];
        values[4] = proof.values[proof.matrices[0].valueOffset];
        values[5] = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000;
        values[6] = proof.values[proof.matrices[6].valueOffset + 8];
        values[7] = proof.values[proof.matrices[6].valueOffset + 6];
        values[8] = proof.values[proof.matrices[0].valueOffset + 1];
        values[9] = proof.values[proof.matrices[6].valueOffset + 9];
        values[10] = proof.values[proof.matrices[6].valueOffset + 7];
        values[11] = proof.values[proof.matrices[0].valueOffset + 2];
        values[12] = proof.values[proof.matrices[6].valueOffset + 10];
        values[13] = proof.values[proof.matrices[6].valueOffset + 11];
        values[14] = Scalar.negate(values[13]);
        values[15] = proof.values[proof.matrices[6].valueOffset + 12];
        values[16] = proof.values[proof.matrices[6].valueOffset + 13];
        values[17] = Scalar.negate(values[16]);
        values[18] = 0x0000000000000000000000000000000000000000000000000000000000000002;
        values[19] = proof.values[proof.matrices[6].valueOffset + 14];
        values[20] = proof.values[proof.matrices[6].valueOffset];
        values[21] = mulmod(values[4], values[20], R);
        values[22] = mulmod(values[8], values[21], R);
        values[23] = proof.values[proof.matrices[6].valueOffset + 1];
        values[24] = mulmod(values[4], values[23], R);
        values[25] = addmod(values[22], values[24], R);
        values[26] = proof.values[proof.matrices[6].valueOffset + 2];
        values[27] = mulmod(values[8], values[26], R);
        values[28] = addmod(values[25], values[27], R);
        values[29] = proof.values[proof.matrices[6].valueOffset + 3];
        values[30] = mulmod(values[11], values[29], R);
        values[31] = addmod(values[28], values[30], R);
        values[32] = proof.values[proof.matrices[6].valueOffset + 4];
        values[33] = addmod(values[31], values[32], R);
    }

    function _evaluateCircuit1(Proof memory proof, EvaluationView memory)
        private
        pure
        returns (uint256[] memory values)
    {
        values = new uint256[](7);
        values[0] = proof.values[proof.matrices[1].valueOffset];
        values[1] = 0x000000000000000000000000000000000000000000000000000000000000005e;
        values[2] = 0x0000000000000000000000000000000000000000000000000000000000000002;
        values[3] = proof.values[proof.matrices[7].valueOffset];
        values[4] = proof.values[proof.matrices[7].valueOffset + 1];
        values[5] = proof.values[proof.matrices[7].valueOffset + 2];
        values[6] = proof.values[proof.matrices[7].valueOffset + 3];
    }

    function _proofLayout(Profile memory, Proof memory proof)
        internal
        pure
        override
        returns (uint256 fieldCount, uint256 fixedCount)
    {
        if (proof.openingCount != 3) revert InvalidPacket();
        proof.matrices[0] = Matrix(3, 1, 0, 1);
        proof.matrices[1] = Matrix(1, 1, 3, 4);
        proof.matrices[2] = Matrix(4, 2, 4, 5);
        proof.matrices[3] = Matrix(1, 2, 8, 13);
        proof.matrices[4] = Matrix(2, 1, 9, 15);
        proof.matrices[5] = Matrix(1, 1, 11, 17);
        proof.matrices[6] = Matrix(15, 1, 15, 18);
        proof.matrices[7] = Matrix(4, 1, 30, 33);
        proof.witnessOffset = 12;
        proof.pointCount = 15;
        return (37, 19);
    }

    function _openingCoefficients(Profile memory, Proof memory proof, uint256[6] memory ch)
        internal
        pure
        override
        returns (uint256[] memory coefficients, uint256[] memory witnessCoefficients)
    {
        if (ch[3] == 0) revert InvalidChallenge();
        if (proof.openingCount != 3 || proof.values.length != 37) revert InvalidPacket();
        coefficients = new uint256[](35);
        witnessCoefficients = new uint256[](3);
        uint256[] memory values = proof.values;
        assembly ("memory-safe") {
            let modulus := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
            let zeta := mload(add(ch, 96))
            let v := mload(add(ch, 128))
            let r := mload(add(ch, 160))
            let generatorSum := 0
            let rSquared := mulmod(r, r, modulus)
            let weight0 := 1
            let weight1 := r
            let weight2 := rSquared
            mstore(add(coefficients, 32), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 64)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 64), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 96)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 96), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 128)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 128), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 160)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 160), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 192)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 192), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 224)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 224), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 256)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 256), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 288)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 160), addmod(mload(add(coefficients, 160)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 320)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 192), addmod(mload(add(coefficients, 192)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 352)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 224), addmod(mload(add(coefficients, 224)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 384)), modulus), modulus)
            weight1 := mulmod(weight1, v, modulus)
            mstore(add(coefficients, 256), addmod(mload(add(coefficients, 256)), weight1, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight1, mload(add(values, 416)), modulus), modulus)
            mstore(add(coefficients, 288), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 448)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 288), addmod(mload(add(coefficients, 288)), weight2, modulus))
            generatorSum := addmod(generatorSum, mulmod(weight2, mload(add(values, 480)), modulus), modulus)
            mstore(add(coefficients, 320), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 512)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 352), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 544)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 384), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 576)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 512), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 608)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 544), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 640)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 576), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 672)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 608), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 704)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 640), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 736)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 672), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 768)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 704), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 800)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 736), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 832)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 768), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 864)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 800), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 896)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 832), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 928)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 864), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 960)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 896), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 992)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 928), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1024)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 960), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1056)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 992), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1088)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 1024), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1120)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 1056), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1152)), modulus), modulus)
            weight0 := mulmod(weight0, v, modulus)
            mstore(add(coefficients, 1088), weight0)
            generatorSum := addmod(generatorSum, mulmod(weight0, mload(add(values, 1184)), modulus), modulus)
            mstore(add(coefficients, 1120), mod(sub(modulus, generatorSum), modulus))
            mstore(add(coefficients, 416), zeta)
            mstore(add(witnessCoefficients, 32), 1)
            mstore(
                add(coefficients, 448),
                mulmod(
                    r,
                    mulmod(zeta, 0x50e0903a157988bab4bcd40e22f55448bf6e88fb4c38fb8a360c60997369df4e, modulus),
                    modulus
                )
            )
            mstore(add(witnessCoefficients, 64), r)
            mstore(
                add(coefficients, 480),
                mulmod(
                    rSquared,
                    mulmod(zeta, 0x20b1ce9140267af9dd1c0af834cec32c17beb312f20b6f7653ea61d87742bcce, modulus),
                    modulus
                )
            )
            mstore(add(witnessCoefficients, 96), rSquared)
        }
    }
}
