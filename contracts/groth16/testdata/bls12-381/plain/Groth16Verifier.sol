
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

    // Addresses of precompiles
    uint256 constant PRECOMPILE_MODEXP = 0x05;
    uint256 constant PRECOMPILE_BLS12_G1MSM = 0x0c;
    uint256 constant PRECOMPILE_BLS12_PAIR = 0x0f;

    // BLS12-381 scalar field Fr order R.
    uint256 constant R = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;

    // Groth16 alpha point in G1
    uint256 constant ALPHA_X_HI = 3684861650482897363316968953296639571;
    uint256 constant ALPHA_X_LO = 32651853924000130237613292122592707505423243525857342992618794555186718808113;
    uint256 constant ALPHA_Y_HI = 26310625860066814282424927268537727976;
    uint256 constant ALPHA_Y_LO = 35903447213707786583385300725216661288503806665261297205373267961935981784341;

    // Groth16 beta point in G2 (negated)
    uint256 constant BETA_NEG_X_0_HI = 29072092926350653154226040524128649960;
    uint256 constant BETA_NEG_X_0_LO = 79622854709502715053532936347563172500559331536304059926150650661489035374373;
    uint256 constant BETA_NEG_X_1_HI = 5242101593534538252559063739511040990;
    uint256 constant BETA_NEG_X_1_LO = 96511071843427956684340228563791050520353494272064783342588791904317187259117;
    uint256 constant BETA_NEG_Y_0_HI = 13686567583796893569467365588516953604;
    uint256 constant BETA_NEG_Y_0_LO = 47127752904306066186688139618609123976582094453294121367373295478198231646467;
    uint256 constant BETA_NEG_Y_1_HI = 34065080302254267060488667082504604049;
    uint256 constant BETA_NEG_Y_1_LO = 50599707775600016610265987695198869457559471205330714985424234570570874486677;

    // Groth16 gamma point in G2 (negated)
    uint256 constant GAMMA_NEG_X_0_HI = 31397761549711267486250361070958934272;
    uint256 constant GAMMA_NEG_X_0_LO = 50799494580608298564555366786703242425316934102661385253718301366598160616316;
    uint256 constant GAMMA_NEG_X_1_HI = 6227659058615339407223018399882318468;
    uint256 constant GAMMA_NEG_X_1_LO = 3728160261470014916045636051952027547216788142148729563946255152143096402644;
    uint256 constant GAMMA_NEG_Y_0_HI = 33639222831489156986990711265067834856;
    uint256 constant GAMMA_NEG_Y_0_LO = 76550644485225955127911787692318358114579716090303266196608182748434861902361;
    uint256 constant GAMMA_NEG_Y_1_HI = 26407271863051622266873762869733713228;
    uint256 constant GAMMA_NEG_Y_1_LO = 78530237033779349509610674203054713069889381422021004465066500961776606299310;

    // Groth16 delta point in G2 (negated)
    uint256 constant DELTA_NEG_X_0_HI = 17713720538401190820935975390808057543;
    uint256 constant DELTA_NEG_X_0_LO = 108429274336215948762718256938124371073026024494515581502757831593765547468752;
    uint256 constant DELTA_NEG_X_1_HI = 26391258819558854555177357733053406115;
    uint256 constant DELTA_NEG_X_1_LO = 81156004204846862712950883455149259411067932643395729557691714488346683906701;
    uint256 constant DELTA_NEG_Y_0_HI = 32673514297418661052803874302931779741;
    uint256 constant DELTA_NEG_Y_0_LO = 78092755120647533627090617301312549427776651801274774760295411105336644369780;
    uint256 constant DELTA_NEG_Y_1_HI = 26694324066550219904755671339403333717;
    uint256 constant DELTA_NEG_Y_1_LO = 55019073587933456452257492851961640345462290539959312620263842025617805025006;

    // Constant and public input points
    uint256 constant CONSTANT_X_HI = 24574823948592478682782176327658025517;
    uint256 constant CONSTANT_X_LO = 60882096546903369747836359077836886981617916794120750878910350958225441168328;
    uint256 constant CONSTANT_Y_HI = 33325216509756552730329572581732397759;
    uint256 constant CONSTANT_Y_LO = 4936056276737056189207087337470885319494192046432767044923873854465609205791;
    uint256 constant PUB_0_X_HI = 26012980398505906662108531930649112808;
    uint256 constant PUB_0_X_LO = 21986986265759690551527752743186014385351911842244524609735927643829046723147;
    uint256 constant PUB_0_Y_HI = 13843551780403202943865032642152684059;
    uint256 constant PUB_0_Y_LO = 103522364769827928453999785734528434887689782807176495189324601884834832420451;
    uint256 constant PUB_1_X_HI = 6107901521930570314537167348446019302;
    uint256 constant PUB_1_X_LO = 85642228568136430055312267345045017822616584522865058228530619263917725089636;
    uint256 constant PUB_1_Y_HI = 19332839606321563808940475333939282021;
    uint256 constant PUB_1_Y_LO = 69373653623804948245554416383642911658061220241821535111989240575646122466380;

    /// Compute the public input linear combination.
    /// @notice Uses BLS12-381 G1 MSM precompile (EIP-2537) for efficient computation.
    /// @notice Computes the multi-scalar-multiplication of the public input
    /// elements and the verification key including the constant term.
    /// @param input The public inputs. These are elements of the scalar field Fr.
    /// @return x_hi The high part of the X coordinate of the resulting G1 point.
    /// @return x_lo The low part of the X coordinate.
    /// @return y_hi The high part of the Y coordinate.
    /// @return y_lo The low part of the Y coordinate.
    function publicInputMSM(uint256[2] calldata input)
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

            let out := add(f, 0x1e0)
            mstore(out, 0)
            mstore(add(out, 0x20), 0)
            mstore(add(out, 0x40), 0)
            mstore(add(out, 0x60), 0)
            let msmOk := staticcall(gas(), PRECOMPILE_BLS12_G1MSM, f, 0x1e0, out, 0x80)
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
    /// @param input the public input field elements in the scalar field Fr.
    /// Elements must be reduced.
    function verifyProof(
        bytes calldata proof,
        uint256[2] calldata input
    ) public view {
        require(proof.length == 384, "invalid proof length");
        (uint256 Lx_hi, uint256 Lx_lo, uint256 Ly_hi, uint256 Ly_lo) = publicInputMSM(input);

        // Verify the Groth16 pairing equation:
        // e(A, B) · e(C, -δ) · e(α, -β) · e(L_pub, -γ) = 1
        //
        // Pairing input: 4 pairs × (G1[128] + G2[256]) = 4 × 384 = 1536 bytes
        bool success;
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
