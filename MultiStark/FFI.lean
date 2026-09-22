module
public import Ix.Aiur.Protocol

/-! Native execution and proving for the generic Multi-STARK verifier. -/

public section
namespace Aiur
namespace Bytecode.Toplevel

/-- MultiStark-native execution of `verify_multi_stark_proof`: the IO
    advice buffer (channel 0 = proof, 1 = vk, 2 = claims, key `[0]`
    each) is built natively in Rust from the raw byte blobs — no
    per-byte boxing into Lean `G`s, no buffer marshalling across FFI.
    `proofAdviceBytes` is the verified native proof transport returned by
    `AiurSystem.proofToAdviceBytes`.
    `useBytecode` selects the generic Aiur bytecode interpreter over
    the codegen'd verifier (`crates/ixvm-codegen/src/aiur_multi_stark.rs`);
    as with `executeIxVM`, the codegen'd path is only valid when
    `toplevel` is the production `MultiStark.multiStark` bytecode —
    other toplevels (e.g. `multiStarkTests`) must pass
    `useBytecode := true`. Returns the output and per-circuit query
    counts; the final buffer is not returned (the verifier only reads
    its advice). -/
@[extern "rs_aiur_multi_stark_execute"]
opaque executeMultiStark (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (pubInput : @& Array G)
  (proofAdviceBytes vkBytes claimBytes : @& ByteArray) (useBytecode : Bool := false) :
    Except String (Array G × Array QueryCount)


end Bytecode.Toplevel
namespace AiurSystem

/-- Prove the MultiStark recursive verifier over proof-advice/vk/claims
byte blobs. `proofAdviceBytes` must come from
`AiurSystem.proofToAdviceBytes`, which verifies and serializes the native
proof transport. The IO advice buffer is built natively in Rust (see
    `Bytecode.Toplevel.executeMultiStark`); the execute step inside
    the prove routes through the codegen'd verifier
    (`crates/ixvm-codegen/src/aiur_multi_stark.rs`) unless
    `useBytecode` is set. Only valid when `system` was built from the
    production `MultiStark.multiStark` bytecode. Returns the claim
    (`#[functionChannel, funIdx] ++ pubInput ++ output`) and the
    `Proof`; the final buffer is not returned. -/
@[extern "rs_aiur_multi_stark_prove"]
opaque proveMultiStark (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (pubInput : @& Array G)
  (proofAdviceBytes vkBytes claimBytes : @& ByteArray) (useBytecode : Bool := false) :
    Except String (Array G × Proof)


end AiurSystem
end Aiur
end
