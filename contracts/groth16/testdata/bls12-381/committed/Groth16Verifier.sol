
// SPDX-License-Identifier: MIT

pragma solidity ^0.8.28;

/// @title Groth16 verifier template.
/// @notice Supports verifying Groth16 proofs over BLS12-381 using EIP-2537 precompiles.
contract Verifier {

    /// Some of the provided public input values are larger than the field modulus.
    /// @dev Public input elements are not automatically reduced, as this is can be
    /// a dangerous source of bugs.
    error PublicInputNotInField();

    /// The proof is invalid.
    /// @dev This can mean that provided Groth16 proof points are not on their
    /// curves, that pairing equation fails, or that the proof is not for the
    /// provided public input.
    error ProofInvalid();
    /// The commitment is invalid
    /// @dev This can mean that provided commitment points and/or proof of knowledge are not on their
    /// curves, that pairing equation fails, or that the commitment and/or proof of knowledge is not for the
    /// commitment key.
    error CommitmentInvalid();

    // Addresses of precompiles
    uint256 constant PRECOMPILE_MODEXP = 0x05;
    uint256 constant PRECOMPILE_BLS12_G1MSM = 0x0c;
    uint256 constant PRECOMPILE_BLS12_PAIR = 0x0f;

    // BLS12-381 scalar field Fr order R.
    uint256 constant R = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;

    // Groth16 alpha point in G1
    uint256 constant ALPHA_X_HI = 26302528495642575669953178747056896702;
    uint256 constant ALPHA_X_LO = 38146388479751963515161769874255128608954776684794616093928424447589489872121;
    uint256 constant ALPHA_Y_HI = 15256377294816697271435346419190525225;
    uint256 constant ALPHA_Y_LO = 1918652605853749177334637575657585995311742577474935407913554718700536092775;

    // Groth16 beta point in G2 (negated)
    uint256 constant BETA_NEG_X_0_HI = 29813768965579309020998481064825572004;
    uint256 constant BETA_NEG_X_0_LO = 53949785715337812718816498759315852867294724499634239267875618868975547660822;
    uint256 constant BETA_NEG_X_1_HI = 9063795565038624912281420860419769493;
    uint256 constant BETA_NEG_X_1_LO = 23539521931112333485289759001917908129556613746229113119778345454367323948583;
    uint256 constant BETA_NEG_Y_0_HI = 26095945774010128199738284810341228904;
    uint256 constant BETA_NEG_Y_0_LO = 26820492510500449842124204094463527246347175326108189735599359469725489652645;
    uint256 constant BETA_NEG_Y_1_HI = 4412180150292104630134858837859180378;
    uint256 constant BETA_NEG_Y_1_LO = 20483388993988186158898936606214927647973280136417661115952664461906237727271;

    // Groth16 gamma point in G2 (negated)
    uint256 constant GAMMA_NEG_X_0_HI = 25819768382666510167616256409540653063;
    uint256 constant GAMMA_NEG_X_0_LO = 48527520393885856717007227799397266272706466702682272377914087237837598129929;
    uint256 constant GAMMA_NEG_X_1_HI = 1804222842942597457904237772792889442;
    uint256 constant GAMMA_NEG_X_1_LO = 114939989440009309786268308301820247989809195003651991694651857594731020335007;
    uint256 constant GAMMA_NEG_Y_0_HI = 31299515346437798639343321887184852822;
    uint256 constant GAMMA_NEG_Y_0_LO = 76638980459314115201845613755822485664079655729221622366174100211170127267454;
    uint256 constant GAMMA_NEG_Y_1_HI = 7914991584004776430717637211020731038;
    uint256 constant GAMMA_NEG_Y_1_LO = 23952592627650468889727074081277719360986299958639108984298242276231081759676;

    // Groth16 delta point in G2 (negated)
    uint256 constant DELTA_NEG_X_0_HI = 2652462012542417152159428396345960859;
    uint256 constant DELTA_NEG_X_0_LO = 48403098976405399240262298965262091326502041655553210748839163836608746892501;
    uint256 constant DELTA_NEG_X_1_HI = 688873042720246993921638034907723582;
    uint256 constant DELTA_NEG_X_1_LO = 17093233779449445953482435062191921664669664776021688109813783090200304046056;
    uint256 constant DELTA_NEG_Y_0_HI = 2596354344021967015803021736475459351;
    uint256 constant DELTA_NEG_Y_0_LO = 8243809009619316013177796305868504177108455564600717225920950330218103888807;
    uint256 constant DELTA_NEG_Y_1_HI = 13897255532310580611691736827182224864;
    uint256 constant DELTA_NEG_Y_1_LO = 87671772216936735867893659712833629306191460389185615237362636394720991223277;
    // Pedersen G point in G2
    uint256 constant PEDERSEN_G_X_0_HI = 17332500712076610185761089136086007717;
    uint256 constant PEDERSEN_G_X_0_LO = 89265986848403620151205872529078842193938071987642029104852592364806770999477;
    uint256 constant PEDERSEN_G_X_1_HI = 16473763732798420705604375443848016007;
    uint256 constant PEDERSEN_G_X_1_LO = 27683951685865943841913858117235339293575629628868520720120168648776892195572;
    uint256 constant PEDERSEN_G_Y_0_HI = 8229570824519898170545271693071548533;
    uint256 constant PEDERSEN_G_Y_0_LO = 64665741307652722265452186751176227777394972516844296832444613583239192377791;
    uint256 constant PEDERSEN_G_Y_1_HI = 13314571856475789407913116960188345278;
    uint256 constant PEDERSEN_G_Y_1_LO = 88183270470985002167493968948204627685047457410528040562544722224022253460051;

    // Pedersen GSigmaNeg point in G2
    uint256 constant PEDERSEN_GSIGMANEG_X_0_HI = 16800714273172491612043274225121864239;
    uint256 constant PEDERSEN_GSIGMANEG_X_0_LO = 70815417274956200878471184232007728088089638569900508915282330750248869655126;
    uint256 constant PEDERSEN_GSIGMANEG_X_1_HI = 31846099948327041009413139865253515432;
    uint256 constant PEDERSEN_GSIGMANEG_X_1_LO = 77209536532640508135489091645841481417306299969732884402808178809186210430493;
    uint256 constant PEDERSEN_GSIGMANEG_Y_0_HI = 26045483631303407339398365929455624150;
    uint256 constant PEDERSEN_GSIGMANEG_Y_0_LO = 99904642163833982152383487404944682357587455321301443250469782010057076991521;
    uint256 constant PEDERSEN_GSIGMANEG_Y_1_HI = 31388259486520404502939661340392880826;
    uint256 constant PEDERSEN_GSIGMANEG_Y_1_LO = 108917587475004972293620196570454326479544862633966707870269907567424935236867;

    // Constant and public input points
    uint256 constant CONSTANT_X_HI = 30621997010910130557334219438228754661;
    uint256 constant CONSTANT_X_LO = 57976440897699613949271205991825630815948396575508152391361659241435337495483;
    uint256 constant CONSTANT_Y_HI = 4482891076117494587723523427103405681;
    uint256 constant CONSTANT_Y_LO = 10753182860227271487312688308538525542024532052385479569390277847528084078607;
    uint256 constant PUB_0_X_HI = 3308522728097585010666082269127869065;
    uint256 constant PUB_0_X_LO = 7297631375935353851202840503137867414918332405876070591322829332178339691127;
    uint256 constant PUB_0_Y_HI = 25259630609001689985346057547982626685;
    uint256 constant PUB_0_Y_LO = 35723165279269994590427426664051910078698371807072375417355575853463429335046;
    uint256 constant PUB_1_X_HI = 23236779921093861468073624904590353991;
    uint256 constant PUB_1_X_LO = 22586963132753299354407202430615111889813830369818092475570508161131007108539;
    uint256 constant PUB_1_Y_HI = 31286356883184931576235141462106988121;
    uint256 constant PUB_1_Y_LO = 79004700864643468154242599458209103398035472853042223097535316510990651400836;
    uint256 constant PUB_2_X_HI = 8103631908188041829436813319027903161;
    uint256 constant PUB_2_X_LO = 96204722135987826996695462650221676223661831308237713135309458780497397496297;
    uint256 constant PUB_2_Y_HI = 4080379265750464814557938582105565006;
    uint256 constant PUB_2_Y_LO = 111439485661878953633172171278195005985895492447890344194358863547064829126354;

    /// Compute the public input linear combination.
    /// @notice Uses BLS12-381 G1 MSM precompile (EIP-2537) for efficient computation.
    /// @notice Computes the multi-scalar-multiplication of the public input
    /// elements and the verification key including the constant term.
    /// @param input The public inputs. These are elements of the scalar field Fr.
    /// @param publicCommitments public inputs generated from pedersen commitments.
    /// @param commitments The Pedersen commitments from the proof (padded to 128 bytes each).
    /// @return x_hi The high part of the X coordinate of the resulting G1 point.
    /// @return x_lo The low part of the X coordinate.
    /// @return y_hi The high part of the Y coordinate.
    /// @return y_lo The low part of the Y coordinate.
    function publicInputMSM(
        uint256[2] calldata input,
        uint256[1] memory publicCommitments,
        uint256[4] memory commitments
    )
    internal view returns (uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) {
        // BLS12_G1MSM input: k elements of (G1_point[128 bytes] + scalar[32 bytes]) = k * 160 bytes
        // Output: one G1 point (128 bytes)
        bool success = true;
        assembly ("memory-safe") {
            let f := mload(0x40)
            let s
            // Element 0: CONSTANT with scalar 1
            mstore(f, CONSTANT_X_HI)
            mstore(add(f, 0x20), CONSTANT_X_LO)
            mstore(add(f, 0x40), CONSTANT_Y_HI)
            mstore(add(f, 0x60), CONSTANT_Y_LO)
            mstore(add(f, 0x80), 1)
            // Element 1: PUB_0
            mstore(add(f, 0xa0), PUB_0_X_HI)
            mstore(add(f, 0xc0), PUB_0_X_LO)
            mstore(add(f, 0xe0), PUB_0_Y_HI)
            mstore(add(f, 0x100), PUB_0_Y_LO)
            s := calldataload(input)
            mstore(add(f, 0x120), s)
            success := and(success, lt(s, R))
            // Element 2: PUB_1
            mstore(add(f, 0x140), PUB_1_X_HI)
            mstore(add(f, 0x160), PUB_1_X_LO)
            mstore(add(f, 0x180), PUB_1_Y_HI)
            mstore(add(f, 0x1a0), PUB_1_Y_LO)
            s := calldataload(add(input, 0x20))
            mstore(add(f, 0x1c0), s)
            success := and(success, lt(s, R))
            // Element 3: PUB_2
            mstore(add(f, 0x1e0), PUB_2_X_HI)
            mstore(add(f, 0x200), PUB_2_X_LO)
            mstore(add(f, 0x220), PUB_2_Y_HI)
            mstore(add(f, 0x240), PUB_2_Y_LO)
            s := mload(publicCommitments)
            mstore(add(f, 0x260), s)
            success := and(success, lt(s, R))
            // Add commitment G1 points with scalar 1
            // Commitments are stored in memory as padded 128-byte G1 points (4 uint256 each)
            mstore(add(f, 0x280), mload(add(commitments, 0x0)))
            mstore(add(f, 0x2a0), mload(add(commitments, 0x20)))
            mstore(add(f, 0x2c0), mload(add(commitments, 0x40)))
            mstore(add(f, 0x2e0), mload(add(commitments, 0x60)))
            mstore(add(f, 0x300), 1)

            let out := add(f, 0x320)
            mstore(out, 0)
            mstore(add(out, 0x20), 0)
            mstore(add(out, 0x40), 0)
            mstore(add(out, 0x60), 0)
            let msmOk := staticcall(gas(), PRECOMPILE_BLS12_G1MSM, f, 0x320, out, 0x80)
            success := and(success, and(msmOk, eq(returndatasize(), 0x80)))

            x_hi := mload(out)
            x_lo := mload(add(out, 0x20))
            y_hi := mload(add(out, 0x40))
            y_lo := mload(add(out, 0x60))
        }
        if (!success) {
            // Either Public input not in field, or verification key invalid.
            // We assume the contract is correctly generated, so the verification key is valid.
            revert PublicInputNotInField();
        }
    }

    /// Verify an uncompressed Groth16 proof.
    /// @notice Reverts with InvalidProof if the proof is invalid or
    /// with PublicInputNotInField the public input is not reduced.
    /// @notice There is no return value. If the function does not revert, the
    /// proof was successfully verified.
    /// @param proof the serialized proof, containing Ar (96 bytes G1), Bs (192 bytes G2),
    /// Krs (96 bytes G1) = 384 bytes total.
    /// Followed by commitments (1 × 96 bytes G1) and commitmentPok (96 bytes G1).
    /// @param input the public input field elements in the scalar field Fr.
    /// Elements must be reduced.
    function verifyProof(
        bytes calldata proof,
        uint256[2] calldata input
    ) public view {
        require(proof.length == 576, "invalid proof length");
        // Load commitment points and compute public commitment hashes
        uint256[1] memory publicCommitments;
        uint256[4] memory commitments;

        // Load commitment points from proof (padded to 128 bytes each in memory)
        assembly ("memory-safe") {
            // Commitment 0: load raw 96-byte G1 from calldata, pad to 128 bytes
            mstore(add(commitments, 0x0), 0)
            calldatacopy(add(commitments, 0x10), add(proof.offset, 0x180), 0x30)
            mstore(add(commitments, 0x40), 0)
            calldatacopy(add(commitments, 0x50), add(proof.offset, 0x1b0), 0x30)
        }

        // Compute public commitment hashes
        uint256[] memory publicAndCommitmentCommitted;

        // Hash: keccak256(commitment_raw_bytes || publicAndCommitmentCommitted) % R
        // The commitment raw bytes are 96 bytes from calldata
        {
            bytes memory hashInput = abi.encodePacked(
                proof[384:480],
                publicAndCommitmentCommitted
            );
            publicCommitments[0] = uint256(sha256(hashInput)) % R;
        }

        // Verify Pedersen commitments
        bool success;
        assembly ("memory-safe") {
            let f := mload(0x40)

            // Pair 0: e(commitment, GSigmaNeg)
            // Load commitment G1 point (already padded in commitments memory)
            mcopy(f, commitments, 0x80)
            // GSigmaNeg G2 point
            mstore(add(f, 0x80), PEDERSEN_GSIGMANEG_X_0_HI)
            mstore(add(f, 0xa0), PEDERSEN_GSIGMANEG_X_0_LO)
            mstore(add(f, 0xc0), PEDERSEN_GSIGMANEG_X_1_HI)
            mstore(add(f, 0xe0), PEDERSEN_GSIGMANEG_X_1_LO)
            mstore(add(f, 0x100), PEDERSEN_GSIGMANEG_Y_0_HI)
            mstore(add(f, 0x120), PEDERSEN_GSIGMANEG_Y_0_LO)
            mstore(add(f, 0x140), PEDERSEN_GSIGMANEG_Y_1_HI)
            mstore(add(f, 0x160), PEDERSEN_GSIGMANEG_Y_1_LO)

            // Pair 1: e(Pok, G)
            // Load PoK from proof calldata (96 bytes at offset after commitments)
            mstore(add(f, 0x180), 0)
            calldatacopy(add(f, 0x190), add(proof.offset, 0x1e0), 0x30)
            mstore(add(f, 0x1c0), 0)
            calldatacopy(add(f, 0x1d0), add(proof.offset, 0x210), 0x30)
            // G point
            mstore(add(f, 0x200), PEDERSEN_G_X_0_HI)
            mstore(add(f, 0x220), PEDERSEN_G_X_0_LO)
            mstore(add(f, 0x240), PEDERSEN_G_X_1_HI)
            mstore(add(f, 0x260), PEDERSEN_G_X_1_LO)
            mstore(add(f, 0x280), PEDERSEN_G_Y_0_HI)
            mstore(add(f, 0x2a0), PEDERSEN_G_Y_0_LO)
            mstore(add(f, 0x2c0), PEDERSEN_G_Y_1_HI)
            mstore(add(f, 0x2e0), PEDERSEN_G_Y_1_LO)

            // BLS12_PAIR: 2 pairs × 384 bytes = 768 bytes
            let out := add(f, 0x300)
            mstore(out, 0)
            success := staticcall(gas(), PRECOMPILE_BLS12_PAIR, f, 0x300, out, 0x20)
            success := and(success, and(eq(returndatasize(), 0x20), eq(mload(out), 1)))
        }
        if (!success) {
            revert CommitmentInvalid();
        }

        (uint256 Lx_hi, uint256 Lx_lo, uint256 Ly_hi, uint256 Ly_lo) = publicInputMSM(
            input,
            publicCommitments,
            commitments
        );

        // Verify the Groth16 pairing equation:
        // e(A, B) · e(C, -δ) · e(α, -β) · e(L_pub, -γ) = 1
        //
        // Pairing input: 4 pairs × (G1[128] + G2[256]) = 4 × 384 = 1536 bytes
        assembly ("memory-safe") {
            let f := mload(0x40)

            // Pair 0: e(A, B)
            // A (G1): 96 bytes at proof offset 0x00
            mstore(f, 0)
            calldatacopy(add(f, 0x10), proof.offset, 0x30)
            mstore(add(f, 0x40), 0)
            calldatacopy(add(f, 0x50), add(proof.offset, 0x30), 0x30)
            // B (G2): 192 bytes at proof offset 0x60
            // gnark-crypto serializes G2 as (A1, A0, A1, A0) but EIP-2537 expects (A0, A1, A0, A1)
            // X.A0 (at proof offset 0x90, 2nd component in gnark-crypto serialization)
            mstore(add(f, 0x80), 0)
            calldatacopy(add(f, 0x90), add(proof.offset, 0x90), 0x30)
            // X.A1 (at proof offset 0x60, 1st component in gnark-crypto serialization)
            mstore(add(f, 0xc0), 0)
            calldatacopy(add(f, 0xd0), add(proof.offset, 0x60), 0x30)
            // Y.A0 (at proof offset 0xf0, 4th component in gnark-crypto serialization)
            mstore(add(f, 0x100), 0)
            calldatacopy(add(f, 0x110), add(proof.offset, 0xf0), 0x30)
            // Y.A1 (at proof offset 0xc0, 3rd component in gnark-crypto serialization)
            mstore(add(f, 0x140), 0)
            calldatacopy(add(f, 0x150), add(proof.offset, 0xc0), 0x30)

            // Pair 1: e(C, -δ)
            // C (G1): 96 bytes at proof offset 0x120
            mstore(add(f, 0x180), 0)
            calldatacopy(add(f, 0x190), add(proof.offset, 0x120), 0x30)
            mstore(add(f, 0x1c0), 0)
            calldatacopy(add(f, 0x1d0), add(proof.offset, 0x150), 0x30)
            // -δ (constant G2)
            mstore(add(f, 0x200), DELTA_NEG_X_0_HI)
            mstore(add(f, 0x220), DELTA_NEG_X_0_LO)
            mstore(add(f, 0x240), DELTA_NEG_X_1_HI)
            mstore(add(f, 0x260), DELTA_NEG_X_1_LO)
            mstore(add(f, 0x280), DELTA_NEG_Y_0_HI)
            mstore(add(f, 0x2a0), DELTA_NEG_Y_0_LO)
            mstore(add(f, 0x2c0), DELTA_NEG_Y_1_HI)
            mstore(add(f, 0x2e0), DELTA_NEG_Y_1_LO)

            // Pair 2: e(α, -β)
            mstore(add(f, 0x300), ALPHA_X_HI)
            mstore(add(f, 0x320), ALPHA_X_LO)
            mstore(add(f, 0x340), ALPHA_Y_HI)
            mstore(add(f, 0x360), ALPHA_Y_LO)
            mstore(add(f, 0x380), BETA_NEG_X_0_HI)
            mstore(add(f, 0x3a0), BETA_NEG_X_0_LO)
            mstore(add(f, 0x3c0), BETA_NEG_X_1_HI)
            mstore(add(f, 0x3e0), BETA_NEG_X_1_LO)
            mstore(add(f, 0x400), BETA_NEG_Y_0_HI)
            mstore(add(f, 0x420), BETA_NEG_Y_0_LO)
            mstore(add(f, 0x440), BETA_NEG_Y_1_HI)
            mstore(add(f, 0x460), BETA_NEG_Y_1_LO)

            // Pair 3: e(L_pub, -γ)
            mstore(add(f, 0x480), Lx_hi)
            mstore(add(f, 0x4a0), Lx_lo)
            mstore(add(f, 0x4c0), Ly_hi)
            mstore(add(f, 0x4e0), Ly_lo)
            mstore(add(f, 0x500), GAMMA_NEG_X_0_HI)
            mstore(add(f, 0x520), GAMMA_NEG_X_0_LO)
            mstore(add(f, 0x540), GAMMA_NEG_X_1_HI)
            mstore(add(f, 0x560), GAMMA_NEG_X_1_LO)
            mstore(add(f, 0x580), GAMMA_NEG_Y_0_HI)
            mstore(add(f, 0x5a0), GAMMA_NEG_Y_0_LO)
            mstore(add(f, 0x5c0), GAMMA_NEG_Y_1_HI)
            mstore(add(f, 0x5e0), GAMMA_NEG_Y_1_LO)

            // BLS12_PAIR: 4 pairs × 384 bytes = 1536 bytes
            let out := add(f, 0x600)
            mstore(out, 0)
            success := staticcall(gas(), PRECOMPILE_BLS12_PAIR, f, 0x600, out, 0x20)
            success := and(success, and(eq(returndatasize(), 0x20), eq(mload(out), 1)))
        }
        if (!success) {
            // Either proof or verification key invalid.
            // We assume the contract is correctly generated, so the verification key is valid.
            revert ProofInvalid();
        }
    }
}
