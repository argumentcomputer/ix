// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

import {IxL3PlonkVerifier} from "../src/IxL3PlonkVerifier.sol";
import {IPlonkVerifier} from "../src/IxPlonkVerifier.sol";

interface Vm {
    function etch(address target, bytes calldata newRuntimeBytecode) external;
}

/// Deterministic mock terminal PLONK verifier that accepts registered
/// `(proof, stmtLow, stmtHigh)` tuples, modeling a real terminal circuit that
/// validates any well-formed two-limb statement regardless of which inner STARK
/// key produced it.
contract MockL3PlonkVerifier is IPlonkVerifier {
    mapping(bytes32 => bool) public accepted;

    function accept(bytes calldata proof, uint256 stmtLow, uint256 stmtHigh) external {
        accepted[keccak256(abi.encode(proof, stmtLow, stmtHigh))] = true;
    }

    function Verify(bytes calldata proof, uint256[] calldata publicInputs) external view returns (bool) {
        if (publicInputs.length != 2) return false;
        return accepted[keccak256(abi.encode(proof, publicInputs[0], publicInputs[1]))];
    }
}

contract GasGriefL3PlonkVerifier is IPlonkVerifier {
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

contract IxL3PlonkVerifierTest {
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    // Shared test vector pinned identically in Rust (`l3_verifier::tests::deterministic_solidity_parity_vector`).
    bytes32 private constant ROOT_VK_BLAKE3 =
        0xd3813ae554af0aa6a24c5c72c796e17403756aa1f9cabbb08519ed4d767c9f13;
    bytes32 private constant WRAP_KEY_BLAKE3 =
        0x1bc0cd05e3d1ad8d0102030405060708090a0b0c0d0e0f101112131415161718;
    bytes32 private constant WRAP_LAYOUT_BLAKE3 =
        0x81b62471a48b5ec8000000000000000000000000000000000000000000000001;
    bytes32 private constant CLAIM_DIGEST =
        0x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef;

    // Expected 2-layer terminal statement and LE 128-bit limbs (cross-checked against Rust blake3).
    bytes32 private constant EXPECTED_TERMINAL_STATEMENT =
        0x4ff9237e250652a41232734d32290ff46ccc00f54cccafeb52cf50c6f985da51;
    uint256 private constant EXPECTED_STMT_LOW = 0xf40f29324d733212a45206257e23f94f;
    uint256 private constant EXPECTED_STMT_HIGH = 0x51da85f9c650cf52ebafcc4cf500cc6c;

    MockL3PlonkVerifier private plonk;
    IxL3PlonkVerifier private adapter;
    bytes private honestProof;

    event log_named_uint(string key, uint256 value);
    event log_named_bytes32(string key, bytes32 value);

    function _release05Prefix() private pure returns (uint64[10] memory p) {
        p[0] = 1;
        p[1] = 0;
        p[2] = 2736370005;
        p[3] = 1983549104;
        p[4] = 896032380;
        p[5] = 1564468090;
        p[6] = 1137178757;
        p[7] = 4223943773;
        p[8] = 1723211272;
        p[9] = 3024343524;
    }

    function _defaultConfig(IPlonkVerifier v) private view returns (IxL3PlonkVerifier.Config memory) {
        return IxL3PlonkVerifier.Config({
            verifier: v,
            verifierCodeHash: address(v).codehash,
            rootVkBlake3: ROOT_VK_BLAKE3,
            rootStatementPrefix: _release05Prefix(),
            wrapKeyBlake3: WRAP_KEY_BLAKE3,
            wrapClaimPrefix: [uint64(1), uint64(0)],
            wrapLayoutBlake3: WRAP_LAYOUT_BLAKE3
        });
    }

    function setUp() public {
        plonk = new MockL3PlonkVerifier();
        adapter = new IxL3PlonkVerifier(_defaultConfig(IPlonkVerifier(address(plonk))));
        honestProof = hex"deadbeef0102030405060708090a0b0c";
        (uint256 low, uint256 high) = adapter.derivePublicInputs(CLAIM_DIGEST);
        plonk.accept(honestProof, low, high);
    }

    function testExactTwoLayerStatementMatchesRustVector() public {
        uint256 start = gasleft();
        bytes32 stmt = adapter.deriveTerminalStatement(CLAIM_DIGEST);
        (uint256 low, uint256 high) = adapter.derivePublicInputs(CLAIM_DIGEST);
        uint256 deriveGas = start - gasleft();
        emit log_named_bytes32("terminal_statement", stmt);
        emit log_named_uint("stmt_low", low);
        emit log_named_uint("stmt_high", high);
        emit log_named_uint("derive_gas", deriveGas);
        require(stmt == EXPECTED_TERMINAL_STATEMENT, "terminal statement mismatch");
        require(low == EXPECTED_STMT_LOW, "stmtLow mismatch");
        require(high == EXPECTED_STMT_HIGH, "stmtHigh mismatch");
        // Verify getter round-trip on immutable rootStatementPrefix.
        uint64[10] memory gotPrefix = adapter.rootStatementPrefix();
        uint64[10] memory wantPrefix = _release05Prefix();
        for (uint256 i; i < 10; ++i) {
            require(gotPrefix[i] == wantPrefix[i], "rootStatementPrefix mismatch");
        }
    }

    function testPositiveVerificationAcceptsHonestProof() public {
        uint256 start = gasleft();
        require(adapter.verify{gas: 2_000_000}(honestProof, CLAIM_DIGEST), "valid L3 proof rejected");
        uint256 used = start - gasleft();
        emit log_named_uint("verify_gas_with_mock_plonk", used);
        require(used < adapter.VERIFICATION_GAS(), "verification exceeds gas stipend");
    }

    function testNegativeControlWrongClaimDigestRejected() public view {
        require(!adapter.verify{gas: 2_000_000}(honestProof, CLAIM_DIGEST ^ bytes32(uint256(1))), "flipped low bit accepted");
        require(
            !adapter.verify{gas: 2_000_000}(honestProof, CLAIM_DIGEST ^ bytes32(uint256(1) << 128)),
            "flipped high bit accepted"
        );
        require(!adapter.verify{gas: 2_000_000}(honestProof, bytes32(0)), "zero claim digest accepted");
    }

    /// Critical negative control: a valid terminal PLONK proof under the SAME
    /// underlying PLONK verifier for a non-IxVM wrapper STARK key K* MUST be rejected.
    function testNegativeControlForeignWrapperKeyKStarRejected() public {
        IxL3PlonkVerifier.Config memory rogueCfg = _defaultConfig(IPlonkVerifier(address(plonk)));
        rogueCfg.wrapKeyBlake3 = bytes32(uint256(0xDEADBEEF));
        IxL3PlonkVerifier rogueAdapter = new IxL3PlonkVerifier(rogueCfg);

        bytes memory rogueProof = hex"cafe000102030405060708090a0b0c0d";
        (uint256 rogueLow, uint256 rogueHigh) = rogueAdapter.derivePublicInputs(CLAIM_DIGEST);
        plonk.accept(rogueProof, rogueLow, rogueHigh);

        // Underlying PLONK verifier and rogue adapter accept rogueProof on S*...
        require(rogueAdapter.verify{gas: 2_000_000}(rogueProof, CLAIM_DIGEST), "sanity: rogue adapter accepts");
        // ...but the honest IxL3PlonkVerifier MUST reject it!
        require(
            !adapter.verify{gas: 2_000_000}(rogueProof, CLAIM_DIGEST),
            "valid L3 proof for foreign wrapper key K* was accepted"
        );
    }

    /// Critical negative control: a valid terminal PLONK proof under the SAME
    /// underlying PLONK verifier for a non-IxVM root STARK key K_root* MUST be rejected.
    function testNegativeControlForeignRootKeyKRootStarRejected() public {
        IxL3PlonkVerifier.Config memory rogueCfg = _defaultConfig(IPlonkVerifier(address(plonk)));
        rogueCfg.rootVkBlake3 = bytes32(uint256(0xBAD0C0DE));
        IxL3PlonkVerifier rogueAdapter = new IxL3PlonkVerifier(rogueCfg);

        bytes memory rogueProof = hex"feed000102030405060708090a0b0c0d";
        (uint256 rogueLow, uint256 rogueHigh) = rogueAdapter.derivePublicInputs(CLAIM_DIGEST);
        plonk.accept(rogueProof, rogueLow, rogueHigh);

        require(rogueAdapter.verify{gas: 2_000_000}(rogueProof, CLAIM_DIGEST), "sanity: rogue root adapter accepts");
        require(
            !adapter.verify{gas: 2_000_000}(rogueProof, CLAIM_DIGEST),
            "valid L3 proof for foreign root key K_root* was accepted"
        );
    }

    /// Negative control: different root or wrapper claim prefixes under the same
    /// underlying PLONK verifier MUST be rejected.
    function testNegativeControlForeignPrefixesRejected() public {
        // Swapped root statement prefix.
        IxL3PlonkVerifier.Config memory altRoot = _defaultConfig(IPlonkVerifier(address(plonk)));
        altRoot.rootStatementPrefix[1] = 1;
        IxL3PlonkVerifier altRootAdapter = new IxL3PlonkVerifier(altRoot);
        bytes memory p1 = hex"aa01";
        (uint256 l1, uint256 h1) = altRootAdapter.derivePublicInputs(CLAIM_DIGEST);
        plonk.accept(p1, l1, h1);
        require(!adapter.verify{gas: 2_000_000}(p1, CLAIM_DIGEST), "swapped root prefix accepted");

        // Swapped wrap claim prefix.
        IxL3PlonkVerifier.Config memory altWrap = _defaultConfig(IPlonkVerifier(address(plonk)));
        altWrap.wrapClaimPrefix[1] = 7;
        IxL3PlonkVerifier altWrapAdapter = new IxL3PlonkVerifier(altWrap);
        bytes memory p2 = hex"bb02";
        (uint256 l2, uint256 h2) = altWrapAdapter.derivePublicInputs(CLAIM_DIGEST);
        plonk.accept(p2, l2, h2);
        require(!adapter.verify{gas: 2_000_000}(p2, CLAIM_DIGEST), "swapped wrap prefix accepted");
    }

    function testConstructorValidationAndWrongCodehashRejected() public {
        // Missing verifier code.
        IxL3PlonkVerifier.Config memory c1 = _defaultConfig(IPlonkVerifier(address(plonk)));
        c1.verifier = IPlonkVerifier(address(1));
        c1.verifierCodeHash = bytes32(0);
        try new IxL3PlonkVerifier(c1) {
            revert("missing verifier code accepted");
        } catch {}

        // Mismatched verifier code hash.
        IxL3PlonkVerifier.Config memory c2 = _defaultConfig(IPlonkVerifier(address(plonk)));
        c2.verifierCodeHash = bytes32(uint256(1));
        try new IxL3PlonkVerifier(c2) {
            revert("wrong verifier codehash accepted");
        } catch {}

        // Zero rootVkBlake3, wrapKeyBlake3, or wrapLayoutBlake3.
        IxL3PlonkVerifier.Config memory c3 = _defaultConfig(IPlonkVerifier(address(plonk)));
        c3.rootVkBlake3 = bytes32(0);
        try new IxL3PlonkVerifier(c3) {
            revert("zero rootVkBlake3 accepted");
        } catch {}

        IxL3PlonkVerifier.Config memory c4 = _defaultConfig(IPlonkVerifier(address(plonk)));
        c4.wrapKeyBlake3 = bytes32(0);
        try new IxL3PlonkVerifier(c4) {
            revert("zero wrapKeyBlake3 accepted");
        } catch {}

        IxL3PlonkVerifier.Config memory c5 = _defaultConfig(IPlonkVerifier(address(plonk)));
        c5.wrapLayoutBlake3 = bytes32(0);
        try new IxL3PlonkVerifier(c5) {
            revert("zero wrapLayoutBlake3 accepted");
        } catch {}

        // Non-canonical Goldilocks prefix words.
        IxL3PlonkVerifier.Config memory c6 = _defaultConfig(IPlonkVerifier(address(plonk)));
        c6.rootStatementPrefix[9] = adapter.GOLDILOCKS_MODULUS();
        try new IxL3PlonkVerifier(c6) {
            revert("noncanonical rootStatementPrefix accepted");
        } catch {}

        IxL3PlonkVerifier.Config memory c7 = _defaultConfig(IPlonkVerifier(address(plonk)));
        c7.wrapClaimPrefix[0] = adapter.GOLDILOCKS_MODULUS();
        try new IxL3PlonkVerifier(c7) {
            revert("noncanonical wrapClaimPrefix accepted");
        } catch {}

        // Runtime codehash mutation at verifier address must fail closed.
        MockL3PlonkVerifier mutablePlonk = new MockL3PlonkVerifier();
        IxL3PlonkVerifier checkedAdapter =
            new IxL3PlonkVerifier(_defaultConfig(IPlonkVerifier(address(mutablePlonk))));
        (uint256 low, uint256 high) = checkedAdapter.derivePublicInputs(CLAIM_DIGEST);
        mutablePlonk.accept(honestProof, low, high);
        require(checkedAdapter.verify{gas: 2_000_000}(honestProof, CLAIM_DIGEST), "sanity: passes before etch");
        vm.etch(address(mutablePlonk), hex"600160005260206000f3");
        require(!checkedAdapter.verify{gas: 2_000_000}(honestProof, CLAIM_DIGEST), "mutated verifier code accepted");
    }

    function testGasGriefingBounded() public {
        GasGriefL3PlonkVerifier grief = new GasGriefL3PlonkVerifier();
        IxL3PlonkVerifier griefAdapter = new IxL3PlonkVerifier(_defaultConfig(IPlonkVerifier(address(grief))));
        uint256 start = gasleft();
        require(!griefAdapter.verify{gas: 2_000_000}(honestProof, CLAIM_DIGEST), "griefing verifier accepted");
        uint256 used = start - gasleft();
        require(used < 1_500_000, "griefing verifier exhausted caller gas");
    }

    function testInsufficientGasRevertsOnValidProof() public view {
        uint256 threshold = (adapter.VERIFICATION_GAS() * 64) / 63 + 10_000;
        // Include enough gas for derivePublicInputs (~150k) but still below the EIP-150 threshold.
        uint256[3] memory lowBudgets = [uint256(500_000), adapter.VERIFICATION_GAS(), threshold - 1];
        for (uint256 i; i < lowBudgets.length; ++i) {
            try adapter.verify{gas: lowBudgets[i]}(honestProof, CLAIM_DIGEST) returns (bool) {
                revert("low-gas verify returned instead of reverting");
            } catch Error(string memory reason) {
                require(
                    keccak256(bytes(reason)) == keccak256(bytes("insufficient gas")),
                    "unexpected revert reason"
                );
            } catch {
                // Out-of-gas inside derivePublicInputs also reverts cleanly (never returns false).
            }
        }
        require(adapter.verify{gas: threshold + 500_000}(honestProof, CLAIM_DIGEST), "valid proof rejected above threshold");
    }

    function testDeploymentLimits() public view {
        require(address(adapter).code.length <= 24576, "IxL3PlonkVerifier exceeds EIP-170");
        require(type(IxL3PlonkVerifier).creationCode.length <= 49152, "IxL3PlonkVerifier initcode exceeds EIP-3860");
    }

    /// Real cryptographic BN254 PLONK verification on-chain (EVM ecPairing precompile)
    /// against a deterministic test-only domain-8 gnark PLONK verifier (1 BSB22 commitment,
    /// 2 public inputs):
    /// - Honest L3 proof for pinned (rootVk, rootPrefix, wrapKey, wrapPrefix, claimDigest) PASSES.
    /// - Foreign wrapper STARK key K* proof passes raw realPlonk.Verify on S* yet is REJECTED by IxL3PlonkVerifier.
    /// - Foreign root STARK key K_root* proof passes raw realPlonk.Verify on S_root* yet is REJECTED by IxL3PlonkVerifier.
    function testRealBn254PlonkAcceptsHonestAndRejectsForeignStarkKeys() public {
        Domain8L3FixturePlonkVerifier realPlonk = new Domain8L3FixturePlonkVerifier();
        IxL3PlonkVerifier realAdapter = new IxL3PlonkVerifier(_defaultConfig(IPlonkVerifier(address(realPlonk))));
        bytes32 fxClaim = 0x255390a2578251f5cdf9f90c0577458924f5a2b7a2f761413b9a0f20b30d07db;

        bytes memory honestSolProof = hex"13db1bfabf1bf8738ef59db69073c931b0aa7d67ebaa6675a3b05b7ffd45369704bf97564da6d9993c0a5e5b527f6da557fd45b1ae1f1a51d15bee1a8286403420b52bcaa67ebe840398bb533ce5c2205ef249caf88757bd4e6824662971f1b7300df33c01c4fe36b52dc42eddafbd0a590766ac32234d71cdd9044bc7b33d9e1caf3f5d4b615156f2d378c5a9ca9a3fe6219e9f9d1b384c3a9149e5301874de10f87a28e6dfebafc82e28ed9ea30c731ce0536a37b84b4e38bdf2b70052504a1abfd53ac4eaa5ef0152717b2788fdc369c60b180f0e54796bdc2ca1cadc0ea900716a710a61d19d2924c8fb1efb8fd1cd5575a04e3622fb975e2d1cd5b79adc1d47478777a57bbd5267b98623bd010aed1b06032843db80881eb3e1a6cf68041490f527d56831ef49f595db6c0a5c567296c6776b7296b841d5992abb04f9af039a7daff1bd23065d4ce3fe1e6e118596a9411aa4780ccca37a20c5ef31f6930f93ec1c70ee8d3c381318b80c1b73b85eab221391163702174bc2e57d35bdba0011f703afcac65c3c1deb8c0a7982f033964101b9a4a4ae3e3e1354fed0f0a2103c4e22820f2ef086e9825904da4ca655f2548692b9bd7adf00459b8191fc792e33307cef7cae7bfed225e70dc6221c1dfc3e0ad28399875bbbcf3b634e07452f656f26f5d4372dd15fa1a6c9c918ee340fc2c8c528fe7fb79f653e84a14f362d463bfd85249691dac6e6ff08f717e9f505960c0101a5913c4194568bb2029a068d767f7e3cc9f8d91850e1928cbb459de099b2a09817384b159615935b33782020079f77bb23e8cea9a00be44abeeb125098d94cc0475ccd54cd6d59700a5f22881d9cab99ad4df322c4378eac25cc6def99b95b5c1702c7e89014e488ae722135bb6b5752d354312ef9574fb92a44d15ec90555cd70a0e626e3215cd8322b134d7ed7f1f65a9c83c8c42e187a8dffea4f09e582b17df438d2f64e510b4df61eaa053b470f8ac433f76c7f805cab2560f6bcd8397100684b021bae689f07622844e2fe58541663974decbaf688a436fbfc77726756041889abe01d9b9e09750b69d0b98d1bcd6e893ea133f7b9771012e331243018b2d162fff60761ad946100d0ed90edf5f0828262e5e4e51e9e9480caaabf51daf6870d7e2f43092c46540aa543b8fd7eee287ad319577e77408b70612804fd1f1b0ea96ae2a68032a078";
        bytes memory rogueWrapSolProof = hex"038d7ed0183e7869ac5666c4eba751472c84ff6d0af3d48ec47549bce1ffa5550cb51a9bf4647dd8c3f023cf5791f2e5a4d8528f41148082b611ab325d5e7245224f456a23f0088c8f66a2ce89686dbab81e328761b7d9ef6b8ef4bb2403d03c2a09b3cc0a6c0d8d4b221d7617bf5ec0fff45bde5633ea5c22931993ca92b4691b8c9392a7e76362005bc16e0bbad75e8280a7b0ae1901e3ac37d58c6fb8ceba0ad294b93fe77e5888a23ad7aee236c3559cefe5e1530a774e1750edbb3b76b930348ca57179cebc8cd19b8c91442027da29e210b94c4b36a84eb35f1f0d267c10a8113d6c1a8aac4dd1b7c1de445a4201f6c9d2d348ff7f785601eba416a50f203f7d62a025a3d4d8bb8bbbacc81413dfea0bdad5eb328642d196079aff8f971245394d1cfbb63793295ad41b9583cc13c93ab4210e5a9cc9fcc071ce572b2e03a399df2b053a7db016e7257dd045a8fdbf36805ff1ee19478fe68f76306ea218739599409c83256b889a9b3f04814aee7209a2385b6212451549ada0428e1b009e44073f90919e3e2af7801bf40e2b66b1159c3cd76b0c539e5a3ac81a50d52a17047203ada5c3b06dac37750b26fac7e63406d0a0fa954949257a3c5f82c10f4d9d5f4e1d0ba1954737b387b341c4213c8d712825493b1f9f7dbcf96886b7168d572621c5cb9ee20e06e215875bd69af6370908d67a62753ec7e13cd16f800021223c60ba09d80c1b7981127703b22d7594bfdd92be67de01db901fdd226e1a3317c6bdf54d37e40e1237d12f6d7c83ae56dc113189a7d7e7d28e0ddcb66522e60af0e48eee8599b707a1376771050d545f457460b399d14c4507360e0a310bbe1a2e07852d9cf39384e302669c16e04c0aa561cc2589684a1fd1ce0496e808fcf15f3326ff4cd800ae289fbc070e381b7d27fde3039a0ed648383db03c4a281e8d754d4ec2bae919f10f2eeef5d7afa0535d600d85d109a48b56fcbcfffa169625c2c8e85258fe3e56b98243efb7245a5ad493d12422ac3d2a96fcfa6b262d87bc5ee68325a810e93f0c8740efb0b76252b6976e7aa6fc77e56f48f11f28068e0deda49093c094b3d74657bf2ad32f148050e7c073930a42dea4618eebcf266f3123039d2755b740eb1e039eec8b0cb3e5e5ebfaac9940d57a5f6571b29a01672b9d23950fdd6f51e76f04f1e7756698ad499c5eb2da00e17cecca2974f7";
        bytes memory rogueRootSolProof = hex"0866535db3f2cb09d2b21e9da4210b6c19b5a192c60a448827224f525088d2a9230adf0762b534bca283ded11c213003b34b58f649729e44082766801c5c6f32048435e42de997b963bdf69942ac06d98a698c1bc4920e97a1d4a09f06a9bac11c9ea00220a571b71444f6630204844d8bb69a0006ac97c359e927affaefcf37161105c6304c060d9bcbf76cb59e5c30af1b81ae6138484ae3a581038209f893301de51c3085accedc4ef43d93b669685ed94bca3ab63b027b8f5fef8a8be61c1f1b51f74af0f6e0b880bf7b217c226e741485decc86fa17a5c99f08e70022c10293f435ad9f6f92ce9c7102bc087c352678f5feba1173412b0f54641a1ec08a303cba94b1f854c99c27a2ee39426451adc7215dbc126d3df54bc741cf5cae1e0c70a099a4aa8f28cd09d3df42b8f31e705a7704e889c99c1782a9ca84e5db940204c6398382ad68aa6323308f8deddeccbb8f870bfcd9c70d24ec34b11583c323333d2a2d4ca0edd62afb080594aca45848e5e9b0d21a58ee7bf881c5b3c13a0a4fde68935f9c74af1233a4e5b4fb0c008a57e2b50cee848060658851859692059e0e56df718d26034b15b11f7108e933901b6e7e6f7237de18d957ad224f811642113af28dbc017616acb1910fd046dc3f84f4fb87ddc7a6550b7fe5b8f51515c1330f6b75f83ae2f5364ceca07dfa48c8afe245f25adaf45a503e501eee591a11a6713146122156188421059aed9498b4e6740ee0d727a93e21d01de39e1724f1121e106c46247fd91d7a450a0264caa76d9df343b1e2f1336c7f585fd2711d404e8a2907fb810f84bc4920e284cf90698e2bb140b8668b46f4c9510582331bf62ad037b4b8d963697e988e58b1e65c027dda616a829d94e5cb5efca292e223899b11b8c7dfc5538bfc19c4eedd2e9d220dcfb74d908e042fad1b0ec29acd0ea900507e2aa0296ace7dec409bf1f48ab8a3876d28bc89eaf7e86c7ca2995d2cfe334f31d85c1747109f0a4f37ee7a972b5cc0518d196446501c4ef87acdd4188a590d1b43ce58a94ca7ff0581534379972fbd6a831f1a793ce20eb6332d9020b8cab54fafaa5f05ae2442cd588424d93f7d8286d632818ce6e154b818859e1c7db7a7383b963cd0e3e027d10fb94a87814e73d63bf6d10cad3123c6e6ebd623959b74cd37a395f56adc30d8bbba3c09fd99ff386262eb35e2246f317d6cd3";

        // 1. Positive control: honest real BN254 PLONK proof verifies on-chain!
        uint256 start = gasleft();
        require(realAdapter.verify{gas: 2_000_000}(honestSolProof, fxClaim), "honest real BN254 L3 proof rejected");
        uint256 used = start - gasleft();
        emit log_named_uint("real_bn254_l3_verify_gas", used);

        // 2. Wrong claim digest rejected on real BN254 PLONK proof.
        require(
            !realAdapter.verify{gas: 2_000_000}(honestSolProof, fxClaim ^ bytes32(uint256(1))),
            "honest proof accepted on mutated claim digest"
        );

        // 3. Critical negative control A: valid real BN254 PLONK proof under the SAME
        // terminal verifier for foreign wrapper STARK key K* MUST be rejected.
        uint256[] memory rogueWrapPub = new uint256[](2);
        rogueWrapPub[0] = 0x3ed5d5119d24e279c37d11494399e137;
        rogueWrapPub[1] = 0x3ee81547719f5e44e5342876258ea8cf;
        require(realPlonk.Verify(rogueWrapSolProof, rogueWrapPub), "sanity: raw PLONK accepts K* proof on S*");
        require(
            !realAdapter.verify{gas: 2_000_000}(rogueWrapSolProof, fxClaim),
            "real BN254 L3 proof for foreign wrapper key K* accepted"
        );

        // 4. Critical negative control B: valid real BN254 PLONK proof under the SAME
        // terminal verifier for foreign root STARK key K_root* MUST be rejected.
        uint256[] memory rogueRootPub = new uint256[](2);
        rogueRootPub[0] = 0x432ef71a715a1666c30c4e25fff7068d;
        rogueRootPub[1] = 0x2426f0b9622ac17c108f8405056932c0;
        require(realPlonk.Verify(rogueRootSolProof, rogueRootPub), "sanity: raw PLONK accepts K_root* proof on S_root*");
        require(
            !realAdapter.verify{gas: 2_000_000}(rogueRootSolProof, fxClaim),
            "real BN254 L3 proof for foreign root key K_root* accepted"
        );
    }
}

/// Test-only domain-8 BN254 PLONK verifier exported by gnark under a
/// known-trapdoor development SRS (1 BSB22 commitment, 2 public inputs).
/// Not a production verifier key; used solely to execute real ecPairing
/// positive and negative controls inside Foundry tests.
contract Domain8L3FixturePlonkVerifier {

  uint256 private constant R_MOD = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
  uint256 private constant R_MOD_MINUS_ONE = 21888242871839275222246405745257275088548364400416034343698204186575808495616;
  uint256 private constant P_MOD = 21888242871839275222246405745257275088696311157297823662689037894645226208583;
  
  uint256 private constant G2_SRS_0_X_0 = 11559732032986387107991004021392285783925812861821192530917403151452391805634;
  uint256 private constant G2_SRS_0_X_1 = 10857046999023057135944570762232829481370756359578518086990519993285655852781;
  uint256 private constant G2_SRS_0_Y_0 = 4082367875863433681332203403145435568316851327593401208105741076214120093531;
  uint256 private constant G2_SRS_0_Y_1 = 8495653923123431417604973247489272438418190587263600148770280649306958101930;
  
  uint256 private constant G2_SRS_1_X_0 = 8346649071297262948544714173736482699128410021416543801035997871711276407441;
  uint256 private constant G2_SRS_1_X_1 = 7883069657575422103991939149663123175414599384626279795595310520790051448551;
  uint256 private constant G2_SRS_1_Y_0 = 16795962876692295166012804782785252840345796645199573986777498170046508450267;
  uint256 private constant G2_SRS_1_Y_1 = 3343323372806643151863786479815504460125163176086666838570580800830972412274;
  
  uint256 private constant G1_SRS_X = 1;
  uint256 private constant G1_SRS_Y = 2;

  // ----------------------- vk ---------------------
  uint256 private constant VK_NB_PUBLIC_INPUTS = 2;
  uint256 private constant VK_DOMAIN_SIZE = 8;
  uint256 private constant VK_INV_DOMAIN_SIZE = 19152212512859365819465605027100115702479818850364030050735928663253832433665;
  uint256 private constant VK_OMEGA = 19540430494807482326159819597004422086093766032135589407132600596362845576832;
  uint256 private constant VK_QL_COM_X = 18406815422122669819032823958442783706250645482260737478889639007988320782617;
  uint256 private constant VK_QL_COM_Y = 13299474223547282337869814706068974042083372231288005728086347169826307287823;
  uint256 private constant VK_QR_COM_X = 7310393856872782849918609323851186948917725248112043056197623196284105212222;
  uint256 private constant VK_QR_COM_Y = 7621945421149498404664979503386535615870914992560393187047879690467368017729;
  uint256 private constant VK_QM_COM_X = 0;
  uint256 private constant VK_QM_COM_Y = 0;
  uint256 private constant VK_QO_COM_X = 0;
  uint256 private constant VK_QO_COM_Y = 0;
  uint256 private constant VK_QK_COM_X = 0;
  uint256 private constant VK_QK_COM_Y = 0;
  
  uint256 private constant VK_S1_COM_X = 11705101854728991708171984490382371248437128941297146184935499596999756048137;
  uint256 private constant VK_S1_COM_Y = 12082008332698508636972474331815145209505485258761960602468398959584055513780;
  
  uint256 private constant VK_S2_COM_X = 19092345157656690987704474625230804916727165447615384635737533638589724999708;
  uint256 private constant VK_S2_COM_Y = 11384624068592907767587491540206094320468955024781151051352505649669193661065;
  
  uint256 private constant VK_S3_COM_X = 8440516769630238978446145696636865675782750737783278729082704209122477099662;
  uint256 private constant VK_S3_COM_Y = 2171149670287868664868824566264189636297308723736019572783679218080973140021;
  
  uint256 private constant VK_COSET_SHIFT = 5;
  
  
  uint256 private constant VK_QCP_0_X = 10109423277056731460791102629139983954247383883523276863579508597236463526434;
  uint256 private constant VK_QCP_0_Y = 16876934767796764791531439280241538267215851609965253952711246716109273626568;
  
  
  uint256 private constant VK_INDEX_COMMIT_API_0 = 4;
  uint256 private constant VK_NB_CUSTOM_GATES = 1;

  // ------------------------------------------------

  // size of the proof without call custom gate
  uint256 private constant FIXED_PROOF_SIZE = 0x300;

  // offset proof
  
  uint256 private constant PROOF_L_COM_X = 0x0;
  uint256 private constant PROOF_L_COM_Y = 0x20;
  uint256 private constant PROOF_R_COM_X = 0x40;
  uint256 private constant PROOF_R_COM_Y = 0x60;
  uint256 private constant PROOF_O_COM_X = 0x80;
  uint256 private constant PROOF_O_COM_Y = 0xa0;

  // h = h_0 + x^{n+2}h_1 + x^{2(n+2)}h_2
  uint256 private constant PROOF_H_0_COM_X = 0xc0;
  uint256 private constant PROOF_H_0_COM_Y = 0xe0;
  uint256 private constant PROOF_H_1_COM_X = 0x100;
  uint256 private constant PROOF_H_1_COM_Y = 0x120;
  uint256 private constant PROOF_H_2_COM_X = 0x140;
  uint256 private constant PROOF_H_2_COM_Y = 0x160;

  // "evaluations of wire polynomials at zeta
  uint256 private constant PROOF_L_AT_ZETA = 0x180;
  uint256 private constant PROOF_R_AT_ZETA = 0x1a0;
  uint256 private constant PROOF_O_AT_ZETA = 0x1c0;

  // S1(zeta),S2(zeta)
  uint256 private constant PROOF_S1_AT_ZETA = 0x1e0; // Sσ1(zeta)
  uint256 private constant PROOF_S2_AT_ZETA = 0x200; // Sσ2(zeta)

  // [Z]
  uint256 private constant PROOF_GRAND_PRODUCT_COMMITMENT_X = 0x220;
  uint256 private constant PROOF_GRAND_PRODUCT_COMMITMENT_Y = 0x240;

  uint256 private constant PROOF_GRAND_PRODUCT_AT_ZETA_OMEGA = 0x260; // z(w*zeta)

  // Folded proof for the opening of linearised poly, l, r, o, s_1, s_2, qcp
  uint256 private constant PROOF_BATCH_OPENING_AT_ZETA_X = 0x280;
  uint256 private constant PROOF_BATCH_OPENING_AT_ZETA_Y = 0x2a0;

  uint256 private constant PROOF_OPENING_AT_ZETA_OMEGA_X = 0x2c0;
  uint256 private constant PROOF_OPENING_AT_ZETA_OMEGA_Y = 0x2e0;

  uint256 private constant PROOF_OPENING_QCP_AT_ZETA = 0x300;
  uint256 private constant PROOF_BSB_COMMITMENTS = 0x320;

  // -------- offset state

  // challenges to check the claimed quotient
  
  uint256 private constant STATE_ALPHA = 0x0;
  uint256 private constant STATE_BETA = 0x20;
  uint256 private constant STATE_GAMMA = 0x40;
  uint256 private constant STATE_ZETA = 0x60;
  uint256 private constant STATE_ALPHA_SQUARE_LAGRANGE_0 = 0x80;
  uint256 private constant STATE_FOLDED_H_X = 0xa0;
  uint256 private constant STATE_FOLDED_H_Y = 0xc0;
  uint256 private constant STATE_LINEARISED_POLYNOMIAL_X = 0xe0;
  uint256 private constant STATE_LINEARISED_POLYNOMIAL_Y = 0x100;
  uint256 private constant STATE_OPENING_LINEARISED_POLYNOMIAL_ZETA = 0x120;
  uint256 private constant STATE_FOLDED_CLAIMED_VALUES = 0x140; // Folded proof for the opening of H, linearised poly, l, r, o, s_1, s_2, qcp
  uint256 private constant STATE_FOLDED_DIGESTS_X = 0x160; // linearised poly, l, r, o, s_1, s_2, qcp
  uint256 private constant STATE_FOLDED_DIGESTS_Y = 0x180;
  uint256 private constant STATE_PI = 0x1a0;
  uint256 private constant STATE_ZETA_POWER_N_MINUS_ONE = 0x1c0;
  uint256 private constant STATE_GAMMA_KZG = 0x1e0;
  uint256 private constant STATE_SUCCESS = 0x200;
  uint256 private constant STATE_CHECK_VAR = 0x220; // /!\ this slot is used for debugging only
  uint256 private constant STATE_LAST_MEM = 0x240;

  // -------- utils (for Fiat Shamir)
  uint256 private constant FS_ALPHA = 0x616C706861; // "alpha"
  uint256 private constant FS_BETA = 0x62657461; // "beta"
  uint256 private constant FS_GAMMA = 0x67616d6d61; // "gamma"
  uint256 private constant FS_ZETA = 0x7a657461; // "zeta"
  uint256 private constant FS_GAMMA_KZG = 0x67616d6d61; // "gamma"

  // -------- errors
  uint256 private constant ERROR_STRING_ID = 0x08c379a000000000000000000000000000000000000000000000000000000000; // selector for function Error(string)

  
  // -------- utils (for hash_fr)
	uint256 private constant HASH_FR_BB = 340282366920938463463374607431768211456; // 2**128
	uint256 private constant HASH_FR_ZERO_UINT256 = 0;
	uint8 private constant HASH_FR_LEN_IN_BYTES = 48;
	uint8 private constant HASH_FR_SIZE_DOMAIN = 11;
	uint8 private constant HASH_FR_ONE = 1;
	uint8 private constant HASH_FR_TWO = 2;
  

  // -------- precompiles
  uint8 private constant SHA2 = 0x2;
  uint8 private constant MOD_EXP = 0x5;
  uint8 private constant EC_ADD = 0x6;
  uint8 private constant EC_MUL = 0x7;
  uint8 private constant EC_PAIR = 0x8;
  
  /// Verify a Plonk proof.
  /// Reverts if the proof or the public inputs are malformed.
  /// @param proof serialised plonk proof (using gnark's MarshalSolidity)
  /// @param public_inputs (must be reduced)
  /// @return success true if the proof passes false otherwise
  function Verify(bytes calldata proof, uint256[] calldata public_inputs) 
  public view returns(bool success) {

    assembly {

      let mem := mload(0x40)
      let freeMem := add(mem, STATE_LAST_MEM)

      // sanity checks
      check_number_of_public_inputs(public_inputs.length)
      check_inputs_size(public_inputs.length, public_inputs.offset)
      check_proof_size(proof.length)
      check_proof_openings_size(proof.offset)

      // compute the challenges
      let prev_challenge_non_reduced
      prev_challenge_non_reduced := derive_gamma(proof.offset, public_inputs.length, public_inputs.offset)
      prev_challenge_non_reduced := derive_beta(prev_challenge_non_reduced)
      prev_challenge_non_reduced := derive_alpha(proof.offset, prev_challenge_non_reduced)
      derive_zeta(proof.offset, prev_challenge_non_reduced)

      // evaluation of Z=Xⁿ-1 at ζ, we save this value
      let zeta := mload(add(mem, STATE_ZETA))
      let zeta_power_n_minus_one := addmod(pow(zeta, VK_DOMAIN_SIZE, freeMem), sub(R_MOD, 1), R_MOD)
      mstore(add(mem, STATE_ZETA_POWER_N_MINUS_ONE), zeta_power_n_minus_one)

      // public inputs contribution
      let l_pi := sum_pi_wo_api_commit(public_inputs.offset, public_inputs.length, freeMem)
      let l_pi_commit := sum_pi_commit(proof.offset, public_inputs.length, freeMem)
      l_pi := addmod(l_pi_commit, l_pi, R_MOD)
      mstore(add(mem, STATE_PI), l_pi)

      compute_alpha_square_lagrange_0()
      compute_opening_linearised_polynomial(proof.offset)
      fold_h(proof.offset)
      compute_commitment_linearised_polynomial(proof.offset)
      compute_gamma_kzg(proof.offset)
      fold_state(proof.offset)
      batch_verify_multi_points(proof.offset)

      success := mload(add(mem, STATE_SUCCESS))

      // Beginning errors -------------------------------------------------

      function error_nb_public_inputs() {
        let ptError := mload(0x40)
        mstore(ptError, ERROR_STRING_ID) // selector for function Error(string)
        mstore(add(ptError, 0x4), 0x20)
        mstore(add(ptError, 0x24), 0x1d)
        mstore(add(ptError, 0x44), "wrong number of public inputs")
        revert(ptError, 0x64)
      }

      /// Called when an exponentiation mod r fails
      function error_mod_exp() {
        let ptError := mload(0x40)
        mstore(ptError, ERROR_STRING_ID) // selector for function Error(string)
        mstore(add(ptError, 0x4), 0x20)
        mstore(add(ptError, 0x24), 0xc)
        mstore(add(ptError, 0x44), "error mod exp")
        revert(ptError, 0x64)
      }

      /// Called when an operation on Bn254 fails
      /// @dev for instance when calling EcMul on a point not on Bn254.
      function error_ec_op() {
        let ptError := mload(0x40)
        mstore(ptError, ERROR_STRING_ID) // selector for function Error(string)
        mstore(add(ptError, 0x4), 0x20)
        mstore(add(ptError, 0x24), 0x12)
        mstore(add(ptError, 0x44), "error ec operation")
        revert(ptError, 0x64)
      }

      /// Called when one of the public inputs is not reduced.
      function error_inputs_size() {
        let ptError := mload(0x40)
        mstore(ptError, ERROR_STRING_ID) // selector for function Error(string)
        mstore(add(ptError, 0x4), 0x20)
        mstore(add(ptError, 0x24), 0x18)
        mstore(add(ptError, 0x44), "inputs are bigger than r")
        revert(ptError, 0x64)
      }

      /// Called when the size proof is not as expected
      /// @dev to avoid overflow attack for instance
      function error_proof_size() {
        let ptError := mload(0x40)
        mstore(ptError, ERROR_STRING_ID) // selector for function Error(string)
        mstore(add(ptError, 0x4), 0x20)
        mstore(add(ptError, 0x24), 0x10)
        mstore(add(ptError, 0x44), "wrong proof size")
        revert(ptError, 0x64)
      }

      /// Called when one the openings is bigger than r
      /// The openings are the claimed evalutions of a polynomial
      /// in a Kzg proof.
      function error_proof_openings_size() {
        let ptError := mload(0x40)
        mstore(ptError, ERROR_STRING_ID) // selector for function Error(string)
        mstore(add(ptError, 0x4), 0x20)
        mstore(add(ptError, 0x24), 0x16)
        mstore(add(ptError, 0x44), "openings bigger than r")
        revert(ptError, 0x64)
      }

      function error_pairing() {
        let ptError := mload(0x40)
        mstore(ptError, ERROR_STRING_ID) // selector for function Error(string)
        mstore(add(ptError, 0x4), 0x20)
        mstore(add(ptError, 0x24), 0xd)
        mstore(add(ptError, 0x44), "error pairing")
        revert(ptError, 0x64)
      }

      function error_verify() {
        let ptError := mload(0x40)
        mstore(ptError, ERROR_STRING_ID) // selector for function Error(string)
        mstore(add(ptError, 0x4), 0x20)
        mstore(add(ptError, 0x24), 0xc)
        mstore(add(ptError, 0x44), "error verify")
        revert(ptError, 0x64)
      }

      function error_random_generation() {
        let ptError := mload(0x40)
        mstore(ptError, ERROR_STRING_ID) // selector for function Error(string)
        mstore(add(ptError, 0x4), 0x20)
        mstore(add(ptError, 0x24), 0x14)
        mstore(add(ptError, 0x44), "error random gen kzg")
        revert(ptError, 0x64)
      }
      // end errors -------------------------------------------------

      // Beginning checks -------------------------------------------------
      
      /// @param s actual number of public inputs
      function check_number_of_public_inputs(s) {
        if iszero(eq(s, VK_NB_PUBLIC_INPUTS)) {
          error_nb_public_inputs()
        }
      }
    
      /// Checks that the public inputs are < R_MOD.
      /// @param s number of public inputs
      /// @param p pointer to the public inputs array
      function check_inputs_size(s, p) {
        for {let i} lt(i, s) {i:=add(i,1)}
        {
          if gt(calldataload(p), R_MOD_MINUS_ONE) {
            error_inputs_size()
          }
          p := add(p, 0x20)
        }
      }

      /// Checks if the proof is of the correct size
      /// @param actual_proof_size size of the proof (not the expected size)
      function check_proof_size(actual_proof_size) {
        let expected_proof_size := add(FIXED_PROOF_SIZE, mul(VK_NB_CUSTOM_GATES,0x60))
        if iszero(eq(actual_proof_size, expected_proof_size)) {
         error_proof_size() 
        }
      }
    
      /// Checks if the multiple openings of the polynomials are < R_MOD.
      /// @param aproof pointer to the beginning of the proof
      /// @dev the 'a' prepending proof is to have a local name
      function check_proof_openings_size(aproof) {
        
        // PROOF_L_AT_ZETA
        let p := add(aproof, PROOF_L_AT_ZETA)
        if gt(calldataload(p), R_MOD_MINUS_ONE) {
          error_proof_openings_size()
        }

        // PROOF_R_AT_ZETA
        p := add(aproof, PROOF_R_AT_ZETA)
        if gt(calldataload(p), R_MOD_MINUS_ONE) {
          error_proof_openings_size()
        }

        // PROOF_O_AT_ZETA
        p := add(aproof, PROOF_O_AT_ZETA)
        if gt(calldataload(p), R_MOD_MINUS_ONE) {
          error_proof_openings_size()
        }

        // PROOF_S1_AT_ZETA
        p := add(aproof, PROOF_S1_AT_ZETA)
        if gt(calldataload(p), R_MOD_MINUS_ONE) {
          error_proof_openings_size()
        }
        
        // PROOF_S2_AT_ZETA
        p := add(aproof, PROOF_S2_AT_ZETA)
        if gt(calldataload(p), R_MOD_MINUS_ONE) {
          error_proof_openings_size()
        }

        // PROOF_GRAND_PRODUCT_AT_ZETA_OMEGA
        p := add(aproof, PROOF_GRAND_PRODUCT_AT_ZETA_OMEGA)
        if gt(calldataload(p), R_MOD_MINUS_ONE) {
          error_proof_openings_size()
        }

        // PROOF_OPENING_QCP_AT_ZETA
        
        p := add(aproof, PROOF_OPENING_QCP_AT_ZETA)
        for {let i:=0} lt(i, VK_NB_CUSTOM_GATES) {i:=add(i,1)}
        {
          if gt(calldataload(p), R_MOD_MINUS_ONE) {
            error_proof_openings_size()
          }
          p := add(p, 0x20)
        }

      }
      // end checks -------------------------------------------------

      // Beginning challenges -------------------------------------------------

      /// Derive gamma as Sha256(<transcript>)
      /// @param aproof pointer to the proof
      /// @param nb_pi number of public inputs
      /// @param pi pointer to the array of public inputs
      /// @return the challenge gamma, not reduced
      /// @notice The transcript is the concatenation (in this order) of:
      /// * the word "gamma" in ascii, equal to [0x67,0x61,0x6d, 0x6d, 0x61] and encoded as a uint256.
      /// * the commitments to the permutation polynomials S1, S2, S3, where we concatenate the coordinates of those points
      /// * the commitments of Ql, Qr, Qm, Qo, Qk
      /// * the public inputs
      /// * the commitments of the wires related to the custom gates (commitments_wires_commit_api)
      /// * commitments to L, R, O (proof_<l,r,o>_com_<x,y>)
      /// The data described above is written starting at mPtr. "gamma" lies on 5 bytes,
      /// and is encoded as a uint256 number n. In basis b = 256, the number looks like this
      /// [0 0 0 .. 0x67 0x61 0x6d, 0x6d, 0x61]. The first non zero entry is at position 27=0x1b
      /// Gamma reduced (the actual challenge) is stored at add(state, state_gamma)
      function derive_gamma(aproof, nb_pi, pi)->gamma_not_reduced {
        
        let state := mload(0x40)
        let mPtr := add(state, STATE_LAST_MEM)

        mstore(mPtr, FS_GAMMA) // "gamma"

        
        mstore(add(mPtr, 0x20), VK_S1_COM_X) 
        mstore(add(mPtr, 0x40), VK_S1_COM_Y) 
        mstore(add(mPtr, 0x60), VK_S2_COM_X) 
        mstore(add(mPtr, 0x80), VK_S2_COM_Y) 
        mstore(add(mPtr, 0xa0), VK_S3_COM_X) 
        mstore(add(mPtr, 0xc0), VK_S3_COM_Y) 
        mstore(add(mPtr, 0xe0), VK_QL_COM_X) 
        mstore(add(mPtr, 0x100), VK_QL_COM_Y) 
        mstore(add(mPtr, 0x120), VK_QR_COM_X) 
        mstore(add(mPtr, 0x140), VK_QR_COM_Y) 
        mstore(add(mPtr, 0x160), VK_QM_COM_X) 
        mstore(add(mPtr, 0x180), VK_QM_COM_Y) 
        mstore(add(mPtr, 0x1a0), VK_QO_COM_X) 
        mstore(add(mPtr, 0x1c0), VK_QO_COM_Y) 
        mstore(add(mPtr, 0x1e0), VK_QK_COM_X) 
        mstore(add(mPtr, 0x200), VK_QK_COM_Y) 
        
        mstore(add(mPtr, 0x220), VK_QCP_0_X) 
        mstore(add(mPtr, 0x240), VK_QCP_0_Y) 
        
        // public inputs
        let _mPtr := add(mPtr, 0x260)
        let size_pi_in_bytes := mul(nb_pi, 0x20)
        calldatacopy(_mPtr, pi, size_pi_in_bytes)
        _mPtr := add(_mPtr, size_pi_in_bytes)

        // commitments to l, r, o
        let size_commitments_lro_in_bytes := 0xc0
        calldatacopy(_mPtr, aproof, size_commitments_lro_in_bytes)
        _mPtr := add(_mPtr, size_commitments_lro_in_bytes)

        // total size is :
        // sizegamma(=0x5) + 11*64(=0x2c0)
        // + nb_public_inputs*0x20
        // + nb_custom gates*0x40
        let size := add(0x2c5, size_pi_in_bytes)
        
        size := add(size, mul(VK_NB_CUSTOM_GATES, 0x40))
        let l_success := staticcall(gas(), SHA2, add(mPtr, 0x1b), size, mPtr, 0x20) //0x1b -> 000.."gamma"
        if iszero(l_success) {
          error_verify()
        }
        gamma_not_reduced := mload(mPtr)
        mstore(add(state, STATE_GAMMA), mod(gamma_not_reduced, R_MOD))
      }

      /// derive beta as Sha256<transcript>
      /// @param gamma_not_reduced the previous challenge (gamma) not reduced
      /// @return beta_not_reduced the next challenge, beta, not reduced
      /// @notice the transcript consists of the previous challenge only.
      /// The reduced version of beta is stored at add(state, state_beta)
      function derive_beta(gamma_not_reduced)->beta_not_reduced{
        
        let state := mload(0x40)
        let mPtr := add(mload(0x40), STATE_LAST_MEM)

        // beta
        mstore(mPtr, FS_BETA) // "beta"
        mstore(add(mPtr, 0x20), gamma_not_reduced)
        let l_success := staticcall(gas(), SHA2, add(mPtr, 0x1c), 0x24, mPtr, 0x20) //0x1b -> 000.."gamma"
        if iszero(l_success) {
          error_verify()
        }
        beta_not_reduced := mload(mPtr)
        mstore(add(state, STATE_BETA), mod(beta_not_reduced, R_MOD))
      }

      /// derive alpha as sha256<transcript>
      /// @param aproof pointer to the proof object
      /// @param beta_not_reduced the previous challenge (beta) not reduced
      /// @return alpha_not_reduced the next challenge, alpha, not reduced
      /// @notice the transcript consists of the previous challenge (beta)
      /// not reduced, the commitments to the wires associated to the QCP_i,
      /// and the commitment to the grand product polynomial 
      function derive_alpha(aproof, beta_not_reduced)->alpha_not_reduced {
        
        let state := mload(0x40)
        let mPtr := add(mload(0x40), STATE_LAST_MEM)
        let full_size := 0x65 // size("alpha") + 0x20 (previous challenge)

        // alpha
        mstore(mPtr, FS_ALPHA) // "alpha"
        let _mPtr := add(mPtr, 0x20)
        mstore(_mPtr, beta_not_reduced)
        _mPtr := add(_mPtr, 0x20)
        
        // Bsb22Commitments
        let proof_bsb_commitments := add(aproof, PROOF_BSB_COMMITMENTS)
        let size_bsb_commitments := mul(0x40, VK_NB_CUSTOM_GATES)
        calldatacopy(_mPtr, proof_bsb_commitments, size_bsb_commitments)
        _mPtr := add(_mPtr, size_bsb_commitments)
        full_size := add(full_size, size_bsb_commitments)
        
        // [Z], the commitment to the grand product polynomial
        calldatacopy(_mPtr, add(aproof, PROOF_GRAND_PRODUCT_COMMITMENT_X), 0x40)
        let l_success := staticcall(gas(), SHA2, add(mPtr, 0x1b), full_size, mPtr, 0x20)
        if iszero(l_success) {
          error_verify()
        }

        alpha_not_reduced := mload(mPtr)
        mstore(add(state, STATE_ALPHA), mod(alpha_not_reduced, R_MOD))
      }

      /// derive zeta as sha256<transcript>
      /// @param aproof pointer to the proof object
      /// @param alpha_not_reduced the previous challenge (alpha) not reduced
      /// The transcript consists of the previous challenge and the commitment to
      /// the quotient polynomial h.
      function derive_zeta(aproof, alpha_not_reduced) {
        
        let state := mload(0x40)
        let mPtr := add(mload(0x40), STATE_LAST_MEM)

        // zeta
        mstore(mPtr, FS_ZETA) // "zeta"
        mstore(add(mPtr, 0x20), alpha_not_reduced)
        calldatacopy(add(mPtr, 0x40), add(aproof, PROOF_H_0_COM_X), 0xc0)
        let l_success := staticcall(gas(), SHA2, add(mPtr, 0x1c), 0xe4, mPtr, 0x20)
        if iszero(l_success) {
          error_verify()
        }
        let zeta_not_reduced := mload(mPtr)
        mstore(add(state, STATE_ZETA), mod(zeta_not_reduced, R_MOD))
      }
      // END challenges -------------------------------------------------

      // BEGINNING compute_pi -------------------------------------------------

      /// sum_pi_wo_api_commit computes the public inputs contributions,
      /// except for the public inputs coming from the custom gate
      /// @param ins pointer to the public inputs
      /// @param n number of public inputs
      /// @param mPtr free memory
      /// @return pi_wo_commit public inputs contribution (except the public inputs coming from the custom gate)
      function sum_pi_wo_api_commit(ins, n, mPtr)->pi_wo_commit {
        
        let state := mload(0x40)
        let z := mload(add(state, STATE_ZETA))
        let zpnmo := mload(add(state, STATE_ZETA_POWER_N_MINUS_ONE))

        let li := mPtr
        batch_compute_lagranges_at_z(z, zpnmo, n, li)

        let tmp := 0
        for {let i:=0} lt(i,n) {i:=add(i,1)}
        {
          tmp := mulmod(mload(li), calldataload(ins), R_MOD)
          pi_wo_commit := addmod(pi_wo_commit, tmp, R_MOD)
          li := add(li, 0x20)
          ins := add(ins, 0x20)
        }
        
      }

      /// batch_compute_lagranges_at_z computes [L_0(z), .., L_{n-1}(z)]
      /// @param z point at which the Lagranges are evaluated
      /// @param zpnmo ζⁿ-1
      /// @param n_pub number of public inputs (number of Lagranges to compute)
      /// @param mPtr pointer to which the results are stored
      function batch_compute_lagranges_at_z(z, zpnmo, n_pub, mPtr) {

        let zn := mulmod(zpnmo, VK_INV_DOMAIN_SIZE, R_MOD) // 1/n * (ζⁿ - 1)
        
        let _w := 1
        let _mPtr := mPtr
        for {let i:=0} lt(i,n_pub) {i:=add(i,1)}
        {
          mstore(_mPtr, addmod(z,sub(R_MOD, _w), R_MOD))
          _w := mulmod(_w, VK_OMEGA, R_MOD)
          _mPtr := add(_mPtr, 0x20)
        }
        batch_invert(mPtr, n_pub, _mPtr)
        _mPtr := mPtr
        _w := 1
        for {let i:=0} lt(i,n_pub) {i:=add(i,1)}
        {
          mstore(_mPtr, mulmod(mulmod(mload(_mPtr), zn , R_MOD), _w, R_MOD))
          _mPtr := add(_mPtr, 0x20)
          _w := mulmod(_w, VK_OMEGA, R_MOD)
        }
      } 

      /// @notice Montgomery trick for batch inversion mod R_MOD
      /// @param ins pointer to the data to batch invert
      /// @param number of elements to batch invert
      /// @param mPtr free memory
      function batch_invert(ins, nb_ins, mPtr) {
        mstore(mPtr, 1)
        let offset := 0
        for {let i:=0} lt(i, nb_ins) {i:=add(i,1)}
        {
          let prev := mload(add(mPtr, offset))
          let cur := mload(add(ins, offset))
          cur := mulmod(prev, cur, R_MOD)
          offset := add(offset, 0x20)
          mstore(add(mPtr, offset), cur)
        }
        ins := add(ins, sub(offset, 0x20))
        mPtr := add(mPtr, offset)
        let inv := pow(mload(mPtr), sub(R_MOD,2), add(mPtr, 0x20))
        for {let i:=0} lt(i, nb_ins) {i:=add(i,1)}
        {
          mPtr := sub(mPtr, 0x20)
          let tmp := mload(ins)
          let cur := mulmod(inv, mload(mPtr), R_MOD)
          mstore(ins, cur)
          inv := mulmod(inv, tmp, R_MOD)
          ins := sub(ins, 0x20)
        }
      }

      
      /// Public inputs (the ones coming from the custom gate) contribution
      /// @param aproof pointer to the proof
      /// @param nb_public_inputs number of public inputs
      /// @param mPtr pointer to free memory
      /// @return pi_commit custom gate public inputs contribution
      function sum_pi_commit(aproof, nb_public_inputs, mPtr)->pi_commit {

        let state := mload(0x40)
        let z := mload(add(state, STATE_ZETA))
        let zpnmo := mload(add(state, STATE_ZETA_POWER_N_MINUS_ONE))

        let p := add(aproof, PROOF_BSB_COMMITMENTS)

        let h_fr, ith_lagrange
       
        
        h_fr := hash_fr(calldataload(p), calldataload(add(p, 0x20)), mPtr)
        ith_lagrange := compute_ith_lagrange_at_z(z, zpnmo, add(nb_public_inputs, VK_INDEX_COMMIT_API_0), mPtr)
        pi_commit := addmod(pi_commit, mulmod(h_fr, ith_lagrange, R_MOD), R_MOD)
        
        

      }

      /// Computes L_i(zeta) =  ωⁱ/n * (ζⁿ-1)/(ζ-ωⁱ) where:
      /// @param z zeta
      /// @param zpmno ζⁿ-1
      /// @param i i-th lagrange
      /// @param mPtr free memory
      /// @return res = ωⁱ/n * (ζⁿ-1)/(ζ-ωⁱ) 
      function compute_ith_lagrange_at_z(z, zpnmo, i, mPtr)->res {

        let w := pow(VK_OMEGA, i, mPtr) // w**i
        i := addmod(z, sub(R_MOD, w), R_MOD) // z-w**i
        w := mulmod(w, VK_INV_DOMAIN_SIZE, R_MOD) // w**i/n
        i := pow(i, sub(R_MOD,2), mPtr) // (z-w**i)**-1
        w := mulmod(w, i, R_MOD) // w**i/n*(z-w)**-1
        res := mulmod(w, zpnmo, R_MOD)
      
      }

      /// @dev https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06#section-5.2
      /// @param x x coordinate of a point on Bn254(𝔽_p)
      /// @param y y coordinate of a point on Bn254(𝔽_p)
      /// @param mPtr free memory
      /// @return res an element mod R_MOD
      function hash_fr(x, y, mPtr)->res {

        // [0x00, .. , 0x00 || x, y, || 0, 48, 0, dst, HASH_FR_SIZE_DOMAIN]
        // <-  64 bytes  ->  <-64b -> <-       1 bytes each     ->

        // [0x00, .., 0x00] 64 bytes of zero
        mstore(mPtr, HASH_FR_ZERO_UINT256)
        mstore(add(mPtr, 0x20), HASH_FR_ZERO_UINT256)
    
        // msg =  x || y , both on 32 bytes
        mstore(add(mPtr, 0x40), x)
        mstore(add(mPtr, 0x60), y)

        // 0 || 48 || 0 all on 1 byte
        mstore8(add(mPtr, 0x80), 0)
        mstore8(add(mPtr, 0x81), HASH_FR_LEN_IN_BYTES)
        mstore8(add(mPtr, 0x82), 0)

        // "BSB22-Plonk" = [42, 53, 42, 32, 32, 2d, 50, 6c, 6f, 6e, 6b,]
        mstore8(add(mPtr, 0x83), 0x42)
        mstore8(add(mPtr, 0x84), 0x53)
        mstore8(add(mPtr, 0x85), 0x42)
        mstore8(add(mPtr, 0x86), 0x32)
        mstore8(add(mPtr, 0x87), 0x32)
        mstore8(add(mPtr, 0x88), 0x2d)
        mstore8(add(mPtr, 0x89), 0x50)
        mstore8(add(mPtr, 0x8a), 0x6c)
        mstore8(add(mPtr, 0x8b), 0x6f)
        mstore8(add(mPtr, 0x8c), 0x6e)
        mstore8(add(mPtr, 0x8d), 0x6b)

        // size domain
        mstore8(add(mPtr, 0x8e), HASH_FR_SIZE_DOMAIN)

        let l_success := staticcall(gas(), SHA2, mPtr, 0x8f, mPtr, 0x20)
        if iszero(l_success) {
          error_verify()
        }

        let b0 := mload(mPtr)

        // [b0         || one || dst || HASH_FR_SIZE_DOMAIN]
        // <-64bytes ->  <-    1 byte each      ->
        mstore8(add(mPtr, 0x20), HASH_FR_ONE) // 1
        
        mstore8(add(mPtr, 0x21), 0x42) // dst
        mstore8(add(mPtr, 0x22), 0x53)
        mstore8(add(mPtr, 0x23), 0x42)
        mstore8(add(mPtr, 0x24), 0x32)
        mstore8(add(mPtr, 0x25), 0x32)
        mstore8(add(mPtr, 0x26), 0x2d)
        mstore8(add(mPtr, 0x27), 0x50)
        mstore8(add(mPtr, 0x28), 0x6c)
        mstore8(add(mPtr, 0x29), 0x6f)
        mstore8(add(mPtr, 0x2a), 0x6e)
        mstore8(add(mPtr, 0x2b), 0x6b)

        mstore8(add(mPtr, 0x2c), HASH_FR_SIZE_DOMAIN) // size domain
        l_success := staticcall(gas(), SHA2, mPtr, 0x2d, mPtr, 0x20)
        if iszero(l_success) {
          error_verify()
        }

        // b1 is located at mPtr. We store b2 at add(mPtr, 0x20)

        // [b0^b1      || two || dst || HASH_FR_SIZE_DOMAIN]
        // <-64bytes ->  <-    1 byte each      ->
        mstore(add(mPtr, 0x20), xor(mload(mPtr), b0))
        mstore8(add(mPtr, 0x40), HASH_FR_TWO)

        mstore8(add(mPtr, 0x41), 0x42) // dst
        mstore8(add(mPtr, 0x42), 0x53)
        mstore8(add(mPtr, 0x43), 0x42)
        mstore8(add(mPtr, 0x44), 0x32)
        mstore8(add(mPtr, 0x45), 0x32)
        mstore8(add(mPtr, 0x46), 0x2d)
        mstore8(add(mPtr, 0x47), 0x50)
        mstore8(add(mPtr, 0x48), 0x6c)
        mstore8(add(mPtr, 0x49), 0x6f)
        mstore8(add(mPtr, 0x4a), 0x6e)
        mstore8(add(mPtr, 0x4b), 0x6b)

        mstore8(add(mPtr, 0x4c), HASH_FR_SIZE_DOMAIN) // size domain

        let offset := add(mPtr, 0x20)
        l_success := staticcall(gas(), SHA2, offset, 0x2d, offset, 0x20)
        if iszero(l_success) {
          error_verify()
        }

        // at this point we have mPtr = [ b1 || b2] where b1 is on 32byes and b2 in 16bytes.
        // we interpret it as a big integer mod r in big endian (similar to regular decimal notation)
        // the result is then 2**(8*16)*mPtr[:32] + mPtr[32:48]
        res := mulmod(mload(mPtr), HASH_FR_BB, R_MOD) // <- res = 2**128 * mPtr[:32]
        let b1 := shr(128, mload(add(mPtr, 0x20))) // b1 <- [0, 0, .., 0 ||  b2[:16] ]
        res := addmod(res, b1, R_MOD)

      }
      
      // END compute_pi -------------------------------------------------

      /// @notice compute α² * 1/n * (ζ{n}-1)/(ζ - 1) where
      /// *  α = challenge derived in derive_gamma_beta_alpha_zeta
      /// * n = vk_domain_size
      /// * ω = vk_omega (generator of the multiplicative cyclic group of order n in (ℤ/rℤ)*)
      /// * ζ = zeta (challenge derived with Fiat Shamir)
      function compute_alpha_square_lagrange_0() {   
        let state := mload(0x40)
        let mPtr := add(mload(0x40), STATE_LAST_MEM)

        let res := mload(add(state, STATE_ZETA_POWER_N_MINUS_ONE))
        let den := addmod(mload(add(state, STATE_ZETA)), sub(R_MOD, 1), R_MOD)
        den := pow(den, sub(R_MOD, 2), mPtr)
        den := mulmod(den, VK_INV_DOMAIN_SIZE, R_MOD)
        res := mulmod(den, res, R_MOD)

        let l_alpha := mload(add(state, STATE_ALPHA))
        res := mulmod(res, l_alpha, R_MOD)
        res := mulmod(res, l_alpha, R_MOD)
        mstore(add(state, STATE_ALPHA_SQUARE_LAGRANGE_0), res)
      }

      /// @notice follows alg. p.13 of https://eprint.iacr.org/2019/953.pdf
      /// with t₁ = t₂ = 1, and the proofs are ([digest] + [quotient] +purported evaluation):
      /// * [state_folded_state_digests], [proof_batch_opening_at_zeta_x], state_folded_evals
      /// * [proof_grand_product_commitment], [proof_opening_at_zeta_omega_x], [proof_grand_product_at_zeta_omega]
      /// @param aproof pointer to the proof
      function batch_verify_multi_points(aproof) {
        let state := mload(0x40)
        let mPtr := add(state, STATE_LAST_MEM)

        // derive a random number. As there is no random generator, we
        // do an FS like challenge derivation, depending on both digests and
        // ζ to ensure that the prover cannot control the random number.
        // Note: adding the other point ζω is not needed, as ω is known beforehand.
        mstore(mPtr, mload(add(state, STATE_FOLDED_DIGESTS_X)))
        mstore(add(mPtr, 0x20), mload(add(state, STATE_FOLDED_DIGESTS_Y)))
        mstore(add(mPtr, 0x40), calldataload(add(aproof, PROOF_BATCH_OPENING_AT_ZETA_X)))
        mstore(add(mPtr, 0x60), calldataload(add(aproof, PROOF_BATCH_OPENING_AT_ZETA_Y)))
        mstore(add(mPtr, 0x80), calldataload(add(aproof, PROOF_GRAND_PRODUCT_COMMITMENT_X)))
        mstore(add(mPtr, 0xa0), calldataload(add(aproof, PROOF_GRAND_PRODUCT_COMMITMENT_Y)))
        mstore(add(mPtr, 0xc0), calldataload(add(aproof, PROOF_OPENING_AT_ZETA_OMEGA_X)))
        mstore(add(mPtr, 0xe0), calldataload(add(aproof, PROOF_OPENING_AT_ZETA_OMEGA_Y)))
        mstore(add(mPtr, 0x100), mload(add(state, STATE_ZETA)))
        mstore(add(mPtr, 0x120), mload(add(state, STATE_GAMMA_KZG)))
        let random := staticcall(gas(), SHA2, mPtr, 0x140, mPtr, 0x20)
        if iszero(random){
          error_random_generation()
        }
        random := mod(mload(mPtr), R_MOD) // use the same variable as we are one variable away from getting stack-too-deep error...

        let folded_quotients := mPtr
        mPtr := add(folded_quotients, 0x40)
        mstore(folded_quotients, calldataload(add(aproof, PROOF_BATCH_OPENING_AT_ZETA_X)))
        mstore(add(folded_quotients, 0x20), calldataload(add(aproof, PROOF_BATCH_OPENING_AT_ZETA_Y)))
        point_acc_mul_calldata(folded_quotients, add(aproof, PROOF_OPENING_AT_ZETA_OMEGA_X), random, mPtr)

        let folded_digests := add(state, STATE_FOLDED_DIGESTS_X)
        point_acc_mul_calldata(folded_digests, add(aproof, PROOF_GRAND_PRODUCT_COMMITMENT_X), random, mPtr)

        let folded_evals := add(state, STATE_FOLDED_CLAIMED_VALUES)
        fr_acc_mul_calldata(folded_evals, add(aproof, PROOF_GRAND_PRODUCT_AT_ZETA_OMEGA), random)

        let folded_evals_commit := mPtr
        mPtr := add(folded_evals_commit, 0x40)
        mstore(folded_evals_commit, G1_SRS_X)
        mstore(add(folded_evals_commit, 0x20), G1_SRS_Y)
        mstore(add(folded_evals_commit, 0x40), mload(folded_evals))
        let check_staticcall := staticcall(gas(), 7, folded_evals_commit, 0x60, folded_evals_commit, 0x40)
        if iszero(check_staticcall) {
          error_verify()
        }

        let folded_evals_commit_y := add(folded_evals_commit, 0x20)
        mstore(folded_evals_commit_y, sub(P_MOD, mload(folded_evals_commit_y)))
        point_add(folded_digests, folded_digests, folded_evals_commit, mPtr)

        let folded_points_quotients := mPtr
        mPtr := add(mPtr, 0x40)
        point_mul_calldata(
          folded_points_quotients,
          add(aproof, PROOF_BATCH_OPENING_AT_ZETA_X),
          mload(add(state, STATE_ZETA)),
          mPtr
        )
        let zeta_omega := mulmod(mload(add(state, STATE_ZETA)), VK_OMEGA, R_MOD)
        random := mulmod(random, zeta_omega, R_MOD)
        point_acc_mul_calldata(folded_points_quotients, add(aproof, PROOF_OPENING_AT_ZETA_OMEGA_X), random, mPtr)

        point_add(folded_digests, folded_digests, folded_points_quotients, mPtr)

        let folded_quotients_y := add(folded_quotients, 0x20)
        mstore(folded_quotients_y, sub(P_MOD, mload(folded_quotients_y)))

        mstore(mPtr, mload(folded_digests))
        
        mstore(add(mPtr, 0x20), mload(add(folded_digests, 0x20))) 
        mstore(add(mPtr, 0x40), G2_SRS_0_X_0)  // the 4 lines are the canonical G2 point on BN254
        mstore(add(mPtr, 0x60), G2_SRS_0_X_1) 
        mstore(add(mPtr, 0x80), G2_SRS_0_Y_0) 
        mstore(add(mPtr, 0xa0), G2_SRS_0_Y_1) 
        mstore(add(mPtr, 0xc0), mload(folded_quotients)) 
        mstore(add(mPtr, 0xe0), mload(add(folded_quotients, 0x20))) 
        mstore(add(mPtr, 0x100), G2_SRS_1_X_0) 
        mstore(add(mPtr, 0x120), G2_SRS_1_X_1) 
        mstore(add(mPtr, 0x140), G2_SRS_1_Y_0) 
        mstore(add(mPtr, 0x160), G2_SRS_1_Y_1) 
        check_pairing_kzg(mPtr)
      }

      /// @notice check_pairing_kzg checks the result of the final pairing product of the batched
      /// kzg verification. The purpose of this function is to avoid exhausting the stack
      /// in the function batch_verify_multi_points.
      /// @param mPtr pointer storing the tuple of pairs
      function check_pairing_kzg(mPtr) {
        let state := mload(0x40)

        let l_success := staticcall(gas(), 8, mPtr, 0x180, 0x00, 0x20)
        if iszero(l_success) {
          error_pairing()
        }
        let res_pairing := mload(0x00)
        mstore(add(state, STATE_SUCCESS), res_pairing)
      }

      /// @notice Fold the opening proofs at ζ:
      /// * at state+state_folded_digest we store: [Linearised_polynomial]+γ[L] + γ²[R] + γ³[O] + γ⁴[S₁] +γ⁵[S₂] + ∑ᵢγ⁵⁺ⁱ[Pi_{i}]
      /// * at state+state_folded_claimed_values we store: Linearised_polynomial(ζ)+γL(ζ) + γ²R(ζ)+ γ³O(ζ) + γ⁴S₁(ζ) +γ⁵S₂(ζ) + ∑ᵢγ⁵⁺ⁱPi_{i}(ζ)
      /// @param aproof pointer to the proof
      /// acc_gamma stores the γⁱ
      function fold_state(aproof) {

        let state := mload(0x40)
        let mPtr := add(mload(0x40), STATE_LAST_MEM)
        let mPtr20 := add(mPtr, 0x20)
        let mPtr40 := add(mPtr, 0x40)

        let l_gamma_kzg := mload(add(state, STATE_GAMMA_KZG))
        let acc_gamma := l_gamma_kzg
        let state_folded_digests := add(state, STATE_FOLDED_DIGESTS_X)

        mstore(state_folded_digests, mload(add(state, STATE_LINEARISED_POLYNOMIAL_X)))
        mstore(add(state, STATE_FOLDED_DIGESTS_Y), mload(add(state, STATE_LINEARISED_POLYNOMIAL_Y)))
        mstore(add(state, STATE_FOLDED_CLAIMED_VALUES), mload(add(state, STATE_OPENING_LINEARISED_POLYNOMIAL_ZETA)))

        point_acc_mul_calldata(state_folded_digests, add(aproof, PROOF_L_COM_X), acc_gamma, mPtr)
        fr_acc_mul_calldata(add(state, STATE_FOLDED_CLAIMED_VALUES), add(aproof, PROOF_L_AT_ZETA), acc_gamma)

        acc_gamma := mulmod(acc_gamma, l_gamma_kzg, R_MOD)
        point_acc_mul_calldata(state_folded_digests, add(aproof, PROOF_R_COM_X), acc_gamma, mPtr)
        fr_acc_mul_calldata(add(state, STATE_FOLDED_CLAIMED_VALUES), add(aproof, PROOF_R_AT_ZETA), acc_gamma)

        acc_gamma := mulmod(acc_gamma, l_gamma_kzg, R_MOD)
        point_acc_mul_calldata(state_folded_digests, add(aproof, PROOF_O_COM_X), acc_gamma, mPtr)
        fr_acc_mul_calldata(add(state, STATE_FOLDED_CLAIMED_VALUES), add(aproof, PROOF_O_AT_ZETA), acc_gamma)

        acc_gamma := mulmod(acc_gamma, l_gamma_kzg, R_MOD)
        mstore(mPtr, VK_S1_COM_X)
        mstore(mPtr20, VK_S1_COM_Y)
        point_acc_mul(state_folded_digests, mPtr, acc_gamma, mPtr40)
        fr_acc_mul_calldata(add(state, STATE_FOLDED_CLAIMED_VALUES), add(aproof, PROOF_S1_AT_ZETA), acc_gamma)

        acc_gamma := mulmod(acc_gamma, l_gamma_kzg, R_MOD)
        mstore(mPtr, VK_S2_COM_X)
        mstore(mPtr20, VK_S2_COM_Y)
        point_acc_mul(state_folded_digests, mPtr, acc_gamma, mPtr40)
        fr_acc_mul_calldata(add(state, STATE_FOLDED_CLAIMED_VALUES), add(aproof, PROOF_S2_AT_ZETA), acc_gamma)
        let poqaz := add(aproof, PROOF_OPENING_QCP_AT_ZETA)
        
        acc_gamma := mulmod(acc_gamma, l_gamma_kzg, R_MOD)
        mstore(mPtr, VK_QCP_0_X)
        mstore(mPtr20, VK_QCP_0_Y)
        point_acc_mul(state_folded_digests, mPtr, acc_gamma, mPtr40)
        fr_acc_mul_calldata(add(state, STATE_FOLDED_CLAIMED_VALUES), poqaz, acc_gamma)
        poqaz := add(poqaz, 0x20)
        
        }

      /// @notice generate the challenge (using Fiat Shamir) to fold the opening proofs
      /// at ζ.
      /// The process for deriving γ is the same as in derive_gamma but this time the inputs are
      /// in this order (the [] means it's a commitment):
      /// * ζ
      /// * [Linearised polynomial]
      /// * [L], [R], [O]
      /// * [S₁] [S₂]
      /// * [Pi_{i}] (wires associated to custom gates)
      /// Then there are the purported evaluations of the previous committed polynomials:
      /// * Linearised_polynomial(ζ)
      /// * L(ζ), R(ζ), O(ζ), S₁(ζ), S₂(ζ)
      /// * Pi_{i}(ζ)
      /// * Z(ζω)
      /// @param aproof pointer to the proof
      function compute_gamma_kzg(aproof) {

        let state := mload(0x40)
        let mPtr := add(mload(0x40), STATE_LAST_MEM)
        mstore(mPtr, FS_GAMMA_KZG) // "gamma"
        mstore(add(mPtr, 0x20), mload(add(state, STATE_ZETA)))
        mstore(add(mPtr,0x40), mload(add(state, STATE_LINEARISED_POLYNOMIAL_X)))
        mstore(add(mPtr,0x60), mload(add(state, STATE_LINEARISED_POLYNOMIAL_Y)))
        calldatacopy(add(mPtr, 0x80), add(aproof, PROOF_L_COM_X), 0xc0)
        mstore(add(mPtr,0x140), VK_S1_COM_X)
        mstore(add(mPtr,0x160), VK_S1_COM_Y)
        mstore(add(mPtr,0x180), VK_S2_COM_X)
        mstore(add(mPtr,0x1a0), VK_S2_COM_Y)
        
        let offset := 0x1c0
        
        mstore(add(mPtr,offset), VK_QCP_0_X)
        mstore(add(mPtr,add(offset, 0x20)), VK_QCP_0_Y)
        offset := add(offset, 0x40)
        mstore(add(mPtr, offset), mload(add(state, STATE_OPENING_LINEARISED_POLYNOMIAL_ZETA)))
        mstore(add(mPtr, add(offset, 0x20)), calldataload(add(aproof, PROOF_L_AT_ZETA)))
        mstore(add(mPtr, add(offset, 0x40)), calldataload(add(aproof, PROOF_R_AT_ZETA)))
        mstore(add(mPtr, add(offset, 0x60)), calldataload(add(aproof, PROOF_O_AT_ZETA)))
        mstore(add(mPtr, add(offset, 0x80)), calldataload(add(aproof, PROOF_S1_AT_ZETA)))
        mstore(add(mPtr, add(offset, 0xa0)), calldataload(add(aproof, PROOF_S2_AT_ZETA)))

        let _mPtr := add(mPtr, add(offset, 0xc0))

        
        let _poqaz := add(aproof, PROOF_OPENING_QCP_AT_ZETA)
        calldatacopy(_mPtr, _poqaz, mul(VK_NB_CUSTOM_GATES, 0x20))
        _mPtr := add(_mPtr, mul(VK_NB_CUSTOM_GATES, 0x20))
        

        mstore(_mPtr, calldataload(add(aproof, PROOF_GRAND_PRODUCT_AT_ZETA_OMEGA)))

        let start_input := 0x1b // 00.."gamma"
        let size_input := add(0x14, mul(VK_NB_CUSTOM_GATES,3)) // number of 32bytes elmts = 0x14 (zeta+3*6 for the digests+openings) + 3*VK_NB_CUSTOM_GATES (for the commitments of the selectors) + 1 (opening of Z at ζω)
        size_input := add(0x5, mul(size_input, 0x20)) // size in bytes: 15*32 bytes + 5 bytes for gamma
        let check_staticcall := staticcall(gas(), SHA2, add(mPtr,start_input), size_input, add(state, STATE_GAMMA_KZG), 0x20)
        if iszero(check_staticcall) {
          error_verify()
        }
        mstore(add(state, STATE_GAMMA_KZG), mod(mload(add(state, STATE_GAMMA_KZG)), R_MOD))
      }

      function compute_commitment_linearised_polynomial_ec(aproof, s1, s2) {
        
        let state := mload(0x40)
        let mPtr := add(mload(0x40), STATE_LAST_MEM)

        mstore(mPtr, VK_QL_COM_X)
        mstore(add(mPtr, 0x20), VK_QL_COM_Y)
        point_mul(
          add(state, STATE_LINEARISED_POLYNOMIAL_X),
          mPtr,
          calldataload(add(aproof, PROOF_L_AT_ZETA)),
          add(mPtr, 0x40)
        )

        mstore(mPtr, VK_QR_COM_X)
        mstore(add(mPtr, 0x20), VK_QR_COM_Y)
        point_acc_mul(
          add(state, STATE_LINEARISED_POLYNOMIAL_X),
          mPtr,
          calldataload(add(aproof, PROOF_R_AT_ZETA)),
          add(mPtr, 0x40)
        )

        let rl := mulmod(calldataload(add(aproof, PROOF_L_AT_ZETA)), calldataload(add(aproof, PROOF_R_AT_ZETA)), R_MOD)
        mstore(mPtr, VK_QM_COM_X)
        mstore(add(mPtr, 0x20), VK_QM_COM_Y)
        point_acc_mul(add(state, STATE_LINEARISED_POLYNOMIAL_X), mPtr, rl, add(mPtr, 0x40))

        mstore(mPtr, VK_QO_COM_X)
        mstore(add(mPtr, 0x20), VK_QO_COM_Y)
        point_acc_mul(
          add(state, STATE_LINEARISED_POLYNOMIAL_X),
          mPtr,
          calldataload(add(aproof, PROOF_O_AT_ZETA)),
          add(mPtr, 0x40)
        )

        mstore(mPtr, VK_QK_COM_X)
        mstore(add(mPtr, 0x20), VK_QK_COM_Y)
        point_add(
          add(state, STATE_LINEARISED_POLYNOMIAL_X),
          add(state, STATE_LINEARISED_POLYNOMIAL_X),
          mPtr,
          add(mPtr, 0x40)
        )

        
        let qcp_opening_at_zeta := add(aproof, PROOF_OPENING_QCP_AT_ZETA)
        let bsb_commitments := add(aproof, PROOF_BSB_COMMITMENTS)
        for {
          let i := 0
        } lt(i, VK_NB_CUSTOM_GATES) {
          i := add(i, 1)
        } {
          mstore(mPtr, calldataload(bsb_commitments))
          mstore(add(mPtr, 0x20), calldataload(add(bsb_commitments, 0x20)))
          point_acc_mul(
            add(state, STATE_LINEARISED_POLYNOMIAL_X),
            mPtr,
            calldataload(qcp_opening_at_zeta),
            add(mPtr, 0x40)
          )
          qcp_opening_at_zeta := add(qcp_opening_at_zeta, 0x20)
          bsb_commitments := add(bsb_commitments, 0x40)
        }
        

        mstore(mPtr, VK_S3_COM_X)
        mstore(add(mPtr, 0x20), VK_S3_COM_Y)
        point_acc_mul(add(state, STATE_LINEARISED_POLYNOMIAL_X), mPtr, s1, add(mPtr, 0x40))

        mstore(mPtr, calldataload(add(aproof, PROOF_GRAND_PRODUCT_COMMITMENT_X)))
        mstore(add(mPtr, 0x20), calldataload(add(aproof, PROOF_GRAND_PRODUCT_COMMITMENT_Y)))
        point_acc_mul(add(state, STATE_LINEARISED_POLYNOMIAL_X), mPtr, s2, add(mPtr, 0x40))

        point_add(
          add(state, STATE_LINEARISED_POLYNOMIAL_X), 
          add(state, STATE_LINEARISED_POLYNOMIAL_X), 
          add(state, STATE_FOLDED_H_X), 
          mPtr)
      }

      /// @notice Compute the commitment to the linearized polynomial equal to
      ///	L(ζ)[Qₗ]+r(ζ)[Qᵣ]+R(ζ)L(ζ)[Qₘ]+O(ζ)[Qₒ]+[Qₖ]+Σᵢqc'ᵢ(ζ)[BsbCommitmentᵢ] +
      ///	α*( Z(μζ)(L(ζ)+β*S₁(ζ)+γ)*(R(ζ)+β*S₂(ζ)+γ)[S₃]-[Z](L(ζ)+β*id_{1}(ζ)+γ)*(R(ζ)+β*id_{2}(ζ)+γ)*(O(ζ)+β*id_{3}(ζ)+γ) ) +
      ///	α²*L₁(ζ)[Z] - Z_{H}(ζ)*(([H₀] + ζᵐ⁺²*[H₁] + ζ²⁽ᵐ⁺²⁾*[H₂])
      /// where
      /// * id_1 = id, id_2 = vk_coset_shift*id, id_3 = vk_coset_shift^{2}*id
      /// * the [] means that it's a commitment (i.e. a point on Bn254(F_p))
      /// * Z_{H}(ζ) = ζ^n-1
      /// @param aproof pointer to the proof
      function compute_commitment_linearised_polynomial(aproof) {
        let state := mload(0x40)
        let l_beta := mload(add(state, STATE_BETA))
        let l_gamma := mload(add(state, STATE_GAMMA))
        let l_zeta := mload(add(state, STATE_ZETA))
        let l_alpha := mload(add(state, STATE_ALPHA))

        let u := mulmod(calldataload(add(aproof, PROOF_GRAND_PRODUCT_AT_ZETA_OMEGA)), l_beta, R_MOD)
        let v := mulmod(l_beta, calldataload(add(aproof, PROOF_S1_AT_ZETA)), R_MOD)
        v := addmod(v, calldataload(add(aproof, PROOF_L_AT_ZETA)), R_MOD)
        v := addmod(v, l_gamma, R_MOD)

        let w := mulmod(l_beta, calldataload(add(aproof, PROOF_S2_AT_ZETA)), R_MOD)
        w := addmod(w, calldataload(add(aproof, PROOF_R_AT_ZETA)), R_MOD)
        w := addmod(w, l_gamma, R_MOD)

        let s1 := mulmod(u, v, R_MOD)
        s1 := mulmod(s1, w, R_MOD)
        s1 := mulmod(s1, l_alpha, R_MOD)

        let coset_square := mulmod(VK_COSET_SHIFT, VK_COSET_SHIFT, R_MOD)
        let betazeta := mulmod(l_beta, l_zeta, R_MOD)
        u := addmod(betazeta, calldataload(add(aproof, PROOF_L_AT_ZETA)), R_MOD)
        u := addmod(u, l_gamma, R_MOD)

        v := mulmod(betazeta, VK_COSET_SHIFT, R_MOD)
        v := addmod(v, calldataload(add(aproof, PROOF_R_AT_ZETA)), R_MOD)
        v := addmod(v, l_gamma, R_MOD)

        w := mulmod(betazeta, coset_square, R_MOD)
        w := addmod(w, calldataload(add(aproof, PROOF_O_AT_ZETA)), R_MOD)
        w := addmod(w, l_gamma, R_MOD)

        let s2 := mulmod(u, v, R_MOD)
        s2 := mulmod(s2, w, R_MOD)
        s2 := sub(R_MOD, s2)
        s2 := mulmod(s2, l_alpha, R_MOD)
        s2 := addmod(s2, mload(add(state, STATE_ALPHA_SQUARE_LAGRANGE_0)), R_MOD)

        // at this stage:
        // * s₁ = α*Z(μζ)(l(ζ)+β*s₁(ζ)+γ)*(r(ζ)+β*s₂(ζ)+γ)*β
        // * s₂ = -α*(l(ζ)+β*ζ+γ)*(r(ζ)+β*u*ζ+γ)*(o(ζ)+β*u²*ζ+γ) + α²*L₁(ζ)

        compute_commitment_linearised_polynomial_ec(aproof, s1, s2)
      }

      /// @notice compute -z_h(ζ)*([H₁] + ζⁿ⁺²[H₂] + ζ²⁽ⁿ⁺²⁾[H₃]) and store the result at
      /// state + state_folded_h
      /// @param aproof pointer to the proof
      function fold_h(aproof) {
        let state := mload(0x40)
        let n_plus_two := add(VK_DOMAIN_SIZE, 2)
        let mPtr := add(mload(0x40), STATE_LAST_MEM)
        let zeta_power_n_plus_two := pow(mload(add(state, STATE_ZETA)), n_plus_two, mPtr)
        point_mul_calldata(add(state, STATE_FOLDED_H_X), add(aproof, PROOF_H_2_COM_X), zeta_power_n_plus_two, mPtr)
        point_add_calldata(add(state, STATE_FOLDED_H_X), add(state, STATE_FOLDED_H_X), add(aproof, PROOF_H_1_COM_X), mPtr)
        point_mul(add(state, STATE_FOLDED_H_X), add(state, STATE_FOLDED_H_X), zeta_power_n_plus_two, mPtr)
        point_add_calldata(add(state, STATE_FOLDED_H_X), add(state, STATE_FOLDED_H_X), add(aproof, PROOF_H_0_COM_X), mPtr)
          point_mul(add(state, STATE_FOLDED_H_X), add(state, STATE_FOLDED_H_X), mload(add(state, STATE_ZETA_POWER_N_MINUS_ONE)), mPtr)
        let folded_h_y := mload(add(state, STATE_FOLDED_H_Y))
        folded_h_y := sub(P_MOD, folded_h_y)
        mstore(add(state, STATE_FOLDED_H_Y), folded_h_y)
      }

      /// @notice check that the opening of the linearised polynomial at zeta is equal to
      /// - [ PI(ζ) - α²*L₁(ζ) + α(l(ζ)+β*s1(ζ)+γ)(r(ζ)+β*s2(ζ)+γ)(o(ζ)+γ)*z(ωζ) ]
      /// @param aproof pointer to the proof
      function compute_opening_linearised_polynomial(aproof) {
        
        let state := mload(0x40)

        // (l(ζ)+β*s1(ζ)+γ)
        let s1
        s1 := mulmod(calldataload(add(aproof, PROOF_S1_AT_ZETA)), mload(add(state, STATE_BETA)), R_MOD)
        s1 := addmod(s1, mload(add(state, STATE_GAMMA)), R_MOD)
        s1 := addmod(s1, calldataload(add(aproof, PROOF_L_AT_ZETA)), R_MOD)

        // (r(ζ)+β*s2(ζ)+γ)
        let s2
        s2 := mulmod(calldataload(add(aproof, PROOF_S2_AT_ZETA)), mload(add(state, STATE_BETA)), R_MOD)
        s2 := addmod(s2, mload(add(state, STATE_GAMMA)), R_MOD)
        s2 := addmod(s2, calldataload(add(aproof, PROOF_R_AT_ZETA)), R_MOD)

        // (o(ζ)+γ)
        let o
        o := addmod(calldataload(add(aproof, PROOF_O_AT_ZETA)), mload(add(state, STATE_GAMMA)), R_MOD)

        //  α*Z(μζ)*(l(ζ)+β*s1(ζ)+γ)*(r(ζ)+β*s2(ζ)+γ)*(o(ζ)+γ)
        s1 := mulmod(s1, s2, R_MOD)
        s1 := mulmod(s1, o, R_MOD)
        s1 := mulmod(s1, mload(add(state, STATE_ALPHA)), R_MOD)
        s1 := mulmod(s1, calldataload(add(aproof, PROOF_GRAND_PRODUCT_AT_ZETA_OMEGA)), R_MOD)

        // PI(ζ) - α²*L₁(ζ) + α(l(ζ)+β*s1(ζ)+γ)(r(ζ)+β*s2(ζ)+γ)(o(ζ)+γ)*z(ωζ)
        s1 := addmod(s1, mload(add(state, STATE_PI)), R_MOD)
        s2 := mload(add(state, STATE_ALPHA_SQUARE_LAGRANGE_0))
        s2 := sub(R_MOD, s2)
        s1 := addmod(s1, s2, R_MOD)
        s1 := sub(R_MOD, s1)

        mstore(add(state, STATE_OPENING_LINEARISED_POLYNOMIAL_ZETA), s1)
      }

      // BEGINNING utils math functions -------------------------------------------------
      
      /// @param dst pointer storing the result
      /// @param p pointer to the first point
      /// @param q pointer to the second point
      /// @param mPtr pointer to free memory
      function point_add(dst, p, q, mPtr) {
        mstore(mPtr, mload(p))
        mstore(add(mPtr, 0x20), mload(add(p, 0x20)))
        mstore(add(mPtr, 0x40), mload(q))
        mstore(add(mPtr, 0x60), mload(add(q, 0x20)))
        let l_success := staticcall(gas(),EC_ADD,mPtr,0x80,dst,0x40)
        if iszero(l_success) {
          error_ec_op()
        }
      }

      /// @param dst pointer storing the result
      /// @param p pointer to the first point (calldata)
      /// @param q pointer to the second point (calladata)
      /// @param mPtr pointer to free memory
      function point_add_calldata(dst, p, q, mPtr) {
        mstore(mPtr, mload(p))
        mstore(add(mPtr, 0x20), mload(add(p, 0x20)))
        mstore(add(mPtr, 0x40), calldataload(q))
        mstore(add(mPtr, 0x60), calldataload(add(q, 0x20)))
        let l_success := staticcall(gas(), EC_ADD, mPtr, 0x80, dst, 0x40)
        if iszero(l_success) {
          error_ec_op()
        }
      }

      /// @parma dst pointer storing the result
      /// @param src pointer to a point on Bn254(𝔽_p)
      /// @param s scalar
      /// @param mPtr free memory
      function point_mul(dst,src,s, mPtr) {
        mstore(mPtr,mload(src))
        mstore(add(mPtr,0x20),mload(add(src,0x20)))
        mstore(add(mPtr,0x40),s)
        let l_success := staticcall(gas(),EC_MUL,mPtr,0x60,dst,0x40)
        if iszero(l_success) {
          error_ec_op()
        }
      }

      /// @parma dst pointer storing the result
      /// @param src pointer to a point on Bn254(𝔽_p) on calldata
      /// @param s scalar
      /// @param mPtr free memory
      function point_mul_calldata(dst, src, s, mPtr) {
        mstore(mPtr, calldataload(src))
        mstore(add(mPtr, 0x20), calldataload(add(src, 0x20)))
        mstore(add(mPtr, 0x40), s)
        let l_success := staticcall(gas(), EC_MUL, mPtr, 0x60, dst, 0x40)
        if iszero(l_success) {
          error_ec_op()
        }
      }

      /// @notice dst <- dst + [s]src (Elliptic curve)
      /// @param dst pointer accumulator point storing the result
      /// @param src pointer to the point to multiply and add
      /// @param s scalar
      /// @param mPtr free memory
      function point_acc_mul(dst,src,s, mPtr) {
        mstore(mPtr,mload(src))
        mstore(add(mPtr,0x20),mload(add(src,0x20)))
        mstore(add(mPtr,0x40),s)
        let l_success := staticcall(gas(),7,mPtr,0x60,mPtr,0x40)
        mstore(add(mPtr,0x40),mload(dst))
        mstore(add(mPtr,0x60),mload(add(dst,0x20)))
        l_success := and(l_success, staticcall(gas(),EC_ADD,mPtr,0x80,dst, 0x40))
        if iszero(l_success) {
          error_ec_op()
        }
      }

      /// @notice dst <- dst + [s]src (Elliptic curve)
      /// @param dst pointer accumulator point storing the result
      /// @param src pointer to the point to multiply and add (on calldata)
      /// @param s scalar
      /// @mPtr free memory
      function point_acc_mul_calldata(dst, src, s, mPtr) {
        mstore(mPtr, calldataload(src))
        mstore(add(mPtr, 0x20), calldataload(add(src, 0x20)))
        mstore(add(mPtr, 0x40), s)
        let l_success := staticcall(gas(), 7, mPtr, 0x60, mPtr, 0x40)
        mstore(add(mPtr, 0x40), mload(dst))
        mstore(add(mPtr, 0x60), mload(add(dst, 0x20)))
        l_success := and(l_success, staticcall(gas(), EC_ADD, mPtr, 0x80, dst, 0x40))
        if iszero(l_success) {
          error_ec_op()
        }
      }

      /// @notice dst <- dst + src*s (Fr) dst,src are addresses, s is a value
      /// @param dst pointer storing the result
      /// @param src pointer to the scalar to multiply and add (on calldata)
      /// @param s scalar
      function fr_acc_mul_calldata(dst, src, s) {
        let tmp :=  mulmod(calldataload(src), s, R_MOD)
        mstore(dst, addmod(mload(dst), tmp, R_MOD))
      }

      /// @param x element to exponentiate
      /// @param e exponent
      /// @param mPtr free memory
      /// @return res x ** e mod r
      function pow(x, e, mPtr)->res {
        mstore(mPtr, 0x20)
        mstore(add(mPtr, 0x20), 0x20)
        mstore(add(mPtr, 0x40), 0x20)
        mstore(add(mPtr, 0x60), x)
        mstore(add(mPtr, 0x80), e)
        mstore(add(mPtr, 0xa0), R_MOD)
        let check_staticcall := staticcall(gas(),MOD_EXP,mPtr,0xc0,mPtr,0x20)
        if eq(check_staticcall, 0) {
            error_mod_exp()
        }
        res := mload(mPtr)
      }
    }
  }
}
