// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.28;

import {IPlonkVerifier} from "./IxPlonkVerifier.sol";

/// On-chain verifier adapter for Aiur L3 (`--aiur-stages`) terminal PLONK proofs.
///
/// Both L3 (`CompressGL`) and L4 (`CompressGLFixed`) prove a two-layer
/// `CompressWrap` statement over the root `ix_aggr` claim row:
///   1. `rootClaimsBytes` (160B) = `u64le(1) || u64le(18) || rootStatementPrefix[0..10] || packU32Le(expectedClaimDigest)[0..8]`
///   2. `sRoot = BLAKE3("ix/compress-wrap/v1\0" || rootVkBlake3 || BLAKE3(rootClaimsBytes))`
///   3. `wrapClaimsBytes` (160B) = `u64le(1) || u64le(18) || wrapClaimPrefix[0..2] || 0[0..8] || packU32Le(sRoot)[0..8]`
///   4. `S = BLAKE3("ix/compress-wrap/v1\0" || wrapKeyBlake3 || BLAKE3(wrapClaimsBytes))`
///   5. `publicInputs = [u128le(S[0..16]), u128le(S[16..32])]`
///
/// All verifying keys, prefixes, and the terminal PLONK verifier code hash are
/// immutable constructor pins; caller-supplied public limbs are never accepted.
contract IxL3PlonkVerifier {
    struct Config {
        IPlonkVerifier verifier;
        bytes32 verifierCodeHash;
        bytes32 rootVkBlake3;
        uint64[10] rootStatementPrefix;
        bytes32 wrapKeyBlake3;
        uint64[2] wrapClaimPrefix;
        bytes32 wrapLayoutBlake3;
    }

    // Malformed pairing inputs can consume all gas forwarded to a precompile.
    uint256 public constant VERIFICATION_GAS = 1_000_000;
    uint64 public constant GOLDILOCKS_MODULUS = 0xffffffff00000001;

    // BLAKE3 standard IV.
    uint32 private constant IV0 = 0x6A09E667;
    uint32 private constant IV1 = 0xBB67AE85;
    uint32 private constant IV2 = 0x3C6EF372;
    uint32 private constant IV3 = 0xA54FF53A;
    uint32 private constant IV4 = 0x510E527F;
    uint32 private constant IV5 = 0x9B05688C;
    uint32 private constant IV6 = 0x1F83D9AB;
    uint32 private constant IV7 = 0x5BE0CD19;

    // BLAKE3 single-chunk domain flags.
    uint32 private constant FLAG_CHUNK_START = 1;
    uint32 private constant FLAG_CHUNK_END_ROOT = 10; // CHUNK_END (2) | ROOT (8)

    // "ix/compress-wrap/v1\0" (20 bytes) as 5 little-endian uint32 words.
    uint32 private constant DOMAIN_W0 = 0x632f7869; // "ix/c"
    uint32 private constant DOMAIN_W1 = 0x72706d6f; // "ompr"
    uint32 private constant DOMAIN_W2 = 0x2d737365; // "ess-"
    uint32 private constant DOMAIN_W3 = 0x70617277; // "wrap"
    uint32 private constant DOMAIN_W4 = 0x0031762f; // "/v1\0"

    IPlonkVerifier public immutable verifier;
    bytes32 public immutable verifierCodeHash;
    bytes32 public immutable rootVkBlake3;
    bytes32 public immutable wrapKeyBlake3;
    bytes32 public immutable wrapLayoutBlake3;
    uint64 public immutable wrapClaimPrefix0;
    uint64 public immutable wrapClaimPrefix1;

    uint64 private immutable _rootPrefix0;
    uint64 private immutable _rootPrefix1;
    uint64 private immutable _rootPrefix2;
    uint64 private immutable _rootPrefix3;
    uint64 private immutable _rootPrefix4;
    uint64 private immutable _rootPrefix5;
    uint64 private immutable _rootPrefix6;
    uint64 private immutable _rootPrefix7;
    uint64 private immutable _rootPrefix8;
    uint64 private immutable _rootPrefix9;

    // Precomputed BLAKE3 block-0 chaining values (fixed by immutable prefixes).
    bytes32 private immutable _rootClaimsCv1;
    bytes32 private immutable _wrapClaimsCv1;

    constructor(Config memory cfg) {
        require(address(cfg.verifier).code.length != 0, "missing verifier code");
        require(address(cfg.verifier).codehash == cfg.verifierCodeHash, "verifier code differs");
        require(cfg.rootVkBlake3 != bytes32(0), "zero root vk digest");
        require(cfg.wrapKeyBlake3 != bytes32(0), "zero wrap key digest");
        require(cfg.wrapLayoutBlake3 != bytes32(0), "zero wrap layout digest");
        for (uint256 i; i < 10; ++i) {
            require(cfg.rootStatementPrefix[i] < GOLDILOCKS_MODULUS, "noncanonical root prefix");
        }
        require(cfg.wrapClaimPrefix[0] < GOLDILOCKS_MODULUS, "noncanonical wrap prefix");
        require(cfg.wrapClaimPrefix[1] < GOLDILOCKS_MODULUS, "noncanonical wrap prefix");

        verifier = cfg.verifier;
        verifierCodeHash = cfg.verifierCodeHash;
        rootVkBlake3 = cfg.rootVkBlake3;
        wrapKeyBlake3 = cfg.wrapKeyBlake3;
        wrapLayoutBlake3 = cfg.wrapLayoutBlake3;
        wrapClaimPrefix0 = cfg.wrapClaimPrefix[0];
        wrapClaimPrefix1 = cfg.wrapClaimPrefix[1];

        _rootPrefix0 = cfg.rootStatementPrefix[0];
        _rootPrefix1 = cfg.rootStatementPrefix[1];
        _rootPrefix2 = cfg.rootStatementPrefix[2];
        _rootPrefix3 = cfg.rootStatementPrefix[3];
        _rootPrefix4 = cfg.rootStatementPrefix[4];
        _rootPrefix5 = cfg.rootStatementPrefix[5];
        _rootPrefix6 = cfg.rootStatementPrefix[6];
        _rootPrefix7 = cfg.rootStatementPrefix[7];
        _rootPrefix8 = cfg.rootStatementPrefix[8];
        _rootPrefix9 = cfg.rootStatementPrefix[9];

        // Precompute Block 0 of root_claims_bytes: [u64le(1), u64le(18), rootPrefix[0..6]].
        uint32[16] memory mRoot;
        mRoot[0] = 1;
        mRoot[2] = 18;
        mRoot[4] = uint32(cfg.rootStatementPrefix[0]);
        mRoot[5] = uint32(cfg.rootStatementPrefix[0] >> 32);
        mRoot[6] = uint32(cfg.rootStatementPrefix[1]);
        mRoot[7] = uint32(cfg.rootStatementPrefix[1] >> 32);
        mRoot[8] = uint32(cfg.rootStatementPrefix[2]);
        mRoot[9] = uint32(cfg.rootStatementPrefix[2] >> 32);
        mRoot[10] = uint32(cfg.rootStatementPrefix[3]);
        mRoot[11] = uint32(cfg.rootStatementPrefix[3] >> 32);
        mRoot[12] = uint32(cfg.rootStatementPrefix[4]);
        mRoot[13] = uint32(cfg.rootStatementPrefix[4] >> 32);
        mRoot[14] = uint32(cfg.rootStatementPrefix[5]);
        mRoot[15] = uint32(cfg.rootStatementPrefix[5] >> 32);
        _rootClaimsCv1 = _packWordsLe(_blake3Compress(_iv(), mRoot, 64, FLAG_CHUNK_START));

        // Precompute Block 0 of wrap_claims_bytes: [u64le(1), u64le(18), wrapPrefix[0..2], 0[0..4]].
        uint32[16] memory mWrap;
        mWrap[0] = 1;
        mWrap[2] = 18;
        mWrap[4] = uint32(cfg.wrapClaimPrefix[0]);
        mWrap[5] = uint32(cfg.wrapClaimPrefix[0] >> 32);
        mWrap[6] = uint32(cfg.wrapClaimPrefix[1]);
        mWrap[7] = uint32(cfg.wrapClaimPrefix[1] >> 32);
        _wrapClaimsCv1 = _packWordsLe(_blake3Compress(_iv(), mWrap, 64, FLAG_CHUNK_START));
    }

    function rootStatementPrefix() external view returns (uint64[10] memory prefix) {
        prefix[0] = _rootPrefix0;
        prefix[1] = _rootPrefix1;
        prefix[2] = _rootPrefix2;
        prefix[3] = _rootPrefix3;
        prefix[4] = _rootPrefix4;
        prefix[5] = _rootPrefix5;
        prefix[6] = _rootPrefix6;
        prefix[7] = _rootPrefix7;
        prefix[8] = _rootPrefix8;
        prefix[9] = _rootPrefix9;
    }

    /// Derive the 32-byte L3 terminal statement digest `S` from `expectedClaimDigest`.
    function deriveTerminalStatement(bytes32 expectedClaimDigest) public view returns (bytes32) {
        return _packWordsLe(_deriveTerminalWords(expectedClaimDigest));
    }

    /// Derive the two little-endian 128-bit terminal PLONK public inputs
    /// `(stmtLow, stmtHigh)` from `expectedClaimDigest`.
    function derivePublicInputs(bytes32 expectedClaimDigest)
        public
        view
        returns (uint256 stmtLow, uint256 stmtHigh)
    {
        uint32[8] memory s = _deriveTerminalWords(expectedClaimDigest);
        unchecked {
            stmtLow = uint256(s[0]) | (uint256(s[1]) << 32) | (uint256(s[2]) << 64) | (uint256(s[3]) << 96);
            stmtHigh = uint256(s[4]) | (uint256(s[5]) << 32) | (uint256(s[6]) << 64) | (uint256(s[7]) << 96);
        }
    }

    /// Verify a terminal L3 PLONK proof against `expectedClaimDigest` and this
    /// contract's immutable pinned keys.
    ///
    /// The caller obtains `expectedClaimDigest = BLAKE3(claimBytes)` independently
    /// of the proof.
    function verify(bytes calldata proof, bytes32 expectedClaimDigest) external view returns (bool) {
        if (address(verifier).codehash != verifierCodeHash) return false;
        (uint256 stmtLow, uint256 stmtHigh) = derivePublicInputs(expectedClaimDigest);
        uint256[] memory publicInputs = new uint256[](2);
        publicInputs[0] = stmtLow;
        publicInputs[1] = stmtHigh;
        // EIP-150 forwards at most 63/64 of remaining gas; require enough caller gas
        // for the full VERIFICATION_GAS stipend so gas starvation reverts instead of
        // returning false on a valid proof via catch.
        require(gasleft() >= (VERIFICATION_GAS * 64) / 63 + 10_000, "insufficient gas");
        try verifier.Verify{gas: VERIFICATION_GAS}(proof, publicInputs) returns (bool valid) {
            return valid;
        } catch {
            return false;
        }
    }

    function _deriveTerminalWords(bytes32 expectedClaimDigest) private view returns (uint32[8] memory) {
        // Layer 1a: BLAKE3(root_claims_bytes) where root_claims_bytes is 160 bytes:
        // [u64le(1), u64le(18), rootPrefix[0..10], packU32Le(expectedClaimDigest)[0..8]].
        uint32[8] memory claimWords = _unpackWordsLe(expectedClaimDigest);
        uint32[8] memory rootClaimsDigest = _hashRootClaims160(claimWords);

        // Layer 1b: S_root = BLAKE3("ix/compress-wrap/v1\0" || rootVkBlake3 || rootClaimsDigest).
        uint32[8] memory rootKeyWords = _unpackWordsLe(rootVkBlake3);
        uint32[8] memory sRoot = _hashStatementPreimage84(rootKeyWords, rootClaimsDigest);

        // Layer 2a: BLAKE3(wrap_claims_bytes) where wrap_claims_bytes is 160 bytes:
        // [u64le(1), u64le(18), wrapClaimPrefix0, wrapClaimPrefix1, 0[0..8], packU32Le(sRoot)[0..8]].
        uint32[8] memory wrapClaimsDigest = _hashWrapClaims160(sRoot);

        // Layer 2b: S = BLAKE3("ix/compress-wrap/v1\0" || wrapKeyBlake3 || wrapClaimsDigest).
        uint32[8] memory wrapKeyWords = _unpackWordsLe(wrapKeyBlake3);
        return _hashStatementPreimage84(wrapKeyWords, wrapClaimsDigest);
    }

    function _hashRootClaims160(uint32[8] memory claimWords) private view returns (uint32[8] memory) {
        uint32[8] memory cv = _unpackWordsLe(_rootClaimsCv1);
        uint32[16] memory m;

        // Block 1 (bytes 64..128): [_rootPrefix6.._rootPrefix9, claimWords[0..4] zero-extended to u64].
        m[0] = uint32(_rootPrefix6);
        m[1] = uint32(_rootPrefix6 >> 32);
        m[2] = uint32(_rootPrefix7);
        m[3] = uint32(_rootPrefix7 >> 32);
        m[4] = uint32(_rootPrefix8);
        m[5] = uint32(_rootPrefix8 >> 32);
        m[6] = uint32(_rootPrefix9);
        m[7] = uint32(_rootPrefix9 >> 32);
        m[8] = claimWords[0];
        m[9] = 0;
        m[10] = claimWords[1];
        m[11] = 0;
        m[12] = claimWords[2];
        m[13] = 0;
        m[14] = claimWords[3];
        m[15] = 0;
        cv = _blake3Compress(cv, m, 64, 0);

        // Block 2 (bytes 128..160, len 32): [claimWords[4..8] zero-extended to u64, 0..0].
        m[0] = claimWords[4];
        m[1] = 0;
        m[2] = claimWords[5];
        m[3] = 0;
        m[4] = claimWords[6];
        m[5] = 0;
        m[6] = claimWords[7];
        m[7] = 0;
        m[8] = 0;
        m[9] = 0;
        m[10] = 0;
        m[11] = 0;
        m[12] = 0;
        m[13] = 0;
        m[14] = 0;
        m[15] = 0;
        return _blake3Compress(cv, m, 32, FLAG_CHUNK_END_ROOT);
    }

    function _hashWrapClaims160(uint32[8] memory sRootWords) private view returns (uint32[8] memory) {
        uint32[8] memory cv = _unpackWordsLe(_wrapClaimsCv1);
        uint32[16] memory m;

        // Block 1 (bytes 64..128): [0, 0, 0, 0, sRootWords[0..4] zero-extended to u64].
        m[8] = sRootWords[0];
        m[10] = sRootWords[1];
        m[12] = sRootWords[2];
        m[14] = sRootWords[3];
        cv = _blake3Compress(cv, m, 64, 0);

        // Block 2 (bytes 128..160, len 32): [sRootWords[4..8] zero-extended to u64, 0..0].
        m[0] = sRootWords[4];
        m[2] = sRootWords[5];
        m[4] = sRootWords[6];
        m[6] = sRootWords[7];
        m[8] = 0;
        m[10] = 0;
        m[12] = 0;
        m[14] = 0;
        return _blake3Compress(cv, m, 32, FLAG_CHUNK_END_ROOT);
    }

    function _hashStatementPreimage84(uint32[8] memory keyWords, uint32[8] memory claimsWords)
        private
        pure
        returns (uint32[8] memory)
    {
        uint32[8] memory cv = _iv();
        uint32[16] memory m;

        // Block 0 (bytes 0..64): domain (5 words) || keyWords (8 words) || claimsWords[0..3] (3 words).
        m[0] = DOMAIN_W0;
        m[1] = DOMAIN_W1;
        m[2] = DOMAIN_W2;
        m[3] = DOMAIN_W3;
        m[4] = DOMAIN_W4;
        m[5] = keyWords[0];
        m[6] = keyWords[1];
        m[7] = keyWords[2];
        m[8] = keyWords[3];
        m[9] = keyWords[4];
        m[10] = keyWords[5];
        m[11] = keyWords[6];
        m[12] = keyWords[7];
        m[13] = claimsWords[0];
        m[14] = claimsWords[1];
        m[15] = claimsWords[2];
        cv = _blake3Compress(cv, m, 64, FLAG_CHUNK_START);

        // Block 1 (bytes 64..84, len 20): claimsWords[3..8] (5 words) || 0 (11 words).
        m[0] = claimsWords[3];
        m[1] = claimsWords[4];
        m[2] = claimsWords[5];
        m[3] = claimsWords[6];
        m[4] = claimsWords[7];
        m[5] = 0;
        m[6] = 0;
        m[7] = 0;
        m[8] = 0;
        m[9] = 0;
        m[10] = 0;
        m[11] = 0;
        m[12] = 0;
        m[13] = 0;
        m[14] = 0;
        m[15] = 0;
        return _blake3Compress(cv, m, 20, FLAG_CHUNK_END_ROOT);
    }

    function _iv() private pure returns (uint32[8] memory iv) {
        iv[0] = IV0;
        iv[1] = IV1;
        iv[2] = IV2;
        iv[3] = IV3;
        iv[4] = IV4;
        iv[5] = IV5;
        iv[6] = IV6;
        iv[7] = IV7;
    }

    function _blake3Compress(
        uint32[8] memory cv,
        uint32[16] memory mIn,
        uint32 blockLen,
        uint32 flags
    ) private pure returns (uint32[8] memory out) {
        uint32[16] memory v;
        uint32[16] memory m;
        unchecked {
            for (uint256 i; i < 8; ++i) {
                v[i] = cv[i];
            }
            v[8] = IV0;
            v[9] = IV1;
            v[10] = IV2;
            v[11] = IV3;
            v[12] = 0; // chunk counter low
            v[13] = 0; // chunk counter high
            v[14] = blockLen;
            v[15] = flags;

            for (uint256 i; i < 16; ++i) {
                m[i] = mIn[i];
            }

            for (uint256 r; r < 7; ++r) {
                _g(v, 0, 4, 8, 12, m[0], m[1]);
                _g(v, 1, 5, 9, 13, m[2], m[3]);
                _g(v, 2, 6, 10, 14, m[4], m[5]);
                _g(v, 3, 7, 11, 15, m[6], m[7]);

                _g(v, 0, 5, 10, 15, m[8], m[9]);
                _g(v, 1, 6, 11, 12, m[10], m[11]);
                _g(v, 2, 7, 8, 13, m[12], m[13]);
                _g(v, 3, 4, 9, 14, m[14], m[15]);

                if (r < 6) {
                    _permuteMsg(m);
                }
            }

            for (uint256 i; i < 8; ++i) {
                out[i] = v[i] ^ v[i + 8];
            }
        }
    }

    function _g(
        uint32[16] memory v,
        uint256 a,
        uint256 b,
        uint256 c,
        uint256 d,
        uint32 mx,
        uint32 my
    ) private pure {
        unchecked {
            uint32 va = v[a] + v[b] + mx;
            uint32 vd = _rotr32(v[d] ^ va, 16);
            uint32 vc = v[c] + vd;
            uint32 vb = _rotr32(v[b] ^ vc, 12);
            va = va + vb + my;
            vd = _rotr32(vd ^ va, 8);
            vc = vc + vd;
            vb = _rotr32(vb ^ vc, 7);
            v[a] = va;
            v[b] = vb;
            v[c] = vc;
            v[d] = vd;
        }
    }

    function _rotr32(uint32 x, uint32 n) private pure returns (uint32) {
        unchecked {
            return (x >> n) | (x << (32 - n));
        }
    }

    function _permuteMsg(uint32[16] memory m) private pure {
        uint32 m0 = m[2];
        uint32 m1 = m[6];
        uint32 m2 = m[3];
        uint32 m3 = m[10];
        uint32 m4 = m[7];
        uint32 m5 = m[0];
        uint32 m6 = m[4];
        uint32 m7 = m[13];
        uint32 m8 = m[1];
        uint32 m9 = m[11];
        uint32 m10 = m[12];
        uint32 m11 = m[5];
        uint32 m12 = m[9];
        uint32 m13 = m[14];
        uint32 m14 = m[15];
        uint32 m15 = m[8];
        m[0] = m0;
        m[1] = m1;
        m[2] = m2;
        m[3] = m3;
        m[4] = m4;
        m[5] = m5;
        m[6] = m6;
        m[7] = m7;
        m[8] = m8;
        m[9] = m9;
        m[10] = m10;
        m[11] = m11;
        m[12] = m12;
        m[13] = m13;
        m[14] = m14;
        m[15] = m15;
    }

    function _unpackWordsLe(bytes32 d) private pure returns (uint32[8] memory words) {
        uint256 x = uint256(d);
        unchecked {
            for (uint256 i; i < 8; ++i) {
                uint256 shift = 224 - (i * 32);
                uint32 be = uint32(x >> shift);
                words[i] = ((be & 0x000000ff) << 24) | ((be & 0x0000ff00) << 8)
                    | ((be & 0x00ff0000) >> 8) | ((be & 0xff000000) >> 24);
            }
        }
    }

    function _packWordsLe(uint32[8] memory words) private pure returns (bytes32) {
        uint256 x;
        unchecked {
            for (uint256 i; i < 8; ++i) {
                uint32 w = words[i];
                uint32 be = ((w & 0x000000ff) << 24) | ((w & 0x0000ff00) << 8)
                    | ((w & 0x00ff0000) >> 8) | ((w & 0xff000000) >> 24);
                x |= uint256(be) << (224 - (i * 32));
            }
        }
        return bytes32(x);
    }
}
