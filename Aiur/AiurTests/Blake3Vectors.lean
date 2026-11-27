import Aiur.Library.Blake3.Correctness

/-! # Known-answer vectors for the Lean BLAKE3 model

`Aiur.Library.Blake3.digest` is the specification that the Lean models of the
`Blake3` library are proved against (`Aiur/Aiur/Library/Blake3/Correctness.lean`;
no theorem relates the Aiur source to those models in general; for IxVM's program,
`IxVM.Refinement.Ingress.hash_digest_spec` (`IxVMRefinement/Ingress/Blake3.lean`) proves that
every source derivation of `Blake3::hash` on fewer than `2^64` bytes returns
`Blake3.Pure.digest`; no such theorem exists for the MultiStark
programs or the keyed `StarkHash` and `KzgBlake3` copies). These
are the official BLAKE3 test vectors (`test_vectors/test_vectors.json` in
BLAKE3-team/BLAKE3 at 1.5.4): the input of length `n` is the bytes `i % 251`
for `i < n`, and the expected value is the first 32 bytes of the `hash`
output. They cover the empty input, one byte, one block, both sides of the
1024-byte chunk boundary, and trees of two, three, four and nine chunks. -/

namespace AiurBlake3Vectors
open Aiur.Library.Blake3

private def pattern (n : Nat) : List UInt8 :=
  (List.range n).map fun i => (i % 251).toUInt8

private def hexByte (b : UInt8) : String :=
  let digits := Nat.toDigits 16 b.toNat
  String.ofList (if digits.length < 2 then '0' :: digits else digits)

private def hex (d : Digest) : String :=
  String.join (d.toList.map hexByte)

#guard hex (digest (pattern 0)) ==
  "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
#guard hex (digest (pattern 1)) ==
  "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213"
#guard hex (digest (pattern 64)) ==
  "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98"
#guard hex (digest (pattern 1023)) ==
  "10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11"
#guard hex (digest (pattern 1024)) ==
  "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7"
#guard hex (digest (pattern 1025)) ==
  "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444"
#guard hex (digest (pattern 2048)) ==
  "e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a"
#guard hex (digest (pattern 2049)) ==
  "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030"
#guard hex (digest (pattern 3072)) ==
  "b98cb0ff3623be03326b373de6b9095218513e64f1ee2edd2525c7ad1e5cffd2"
#guard hex (digest (pattern 3073)) ==
  "7124b49501012f81cc7f11ca069ec9226cecb8a2c850cfe644e327d22d3e1cd3"
#guard hex (digest (pattern 8193)) ==
  "bab6c09cb8ce8cf459261398d2e7aef35700bf488116ceb94a36d0f5f1b7bc3b"

/-! ## Keyed, `derive_key`, and multi-chunk domain-separated vectors -/

private def chunkLoopWith (flags : UInt32) (counter : UInt64) (cv : Blake3.Pure.CV)
    (start : Bool) (input : List UInt8) : Blake3.Pure.Output :=
  if _h : input.length ≤ 64 then
    ⟨cv, Blake3.Pure.blockWords input, input.length.toUInt32, counter,
      flags ||| ((if start then 1 else 0) ||| 2)⟩
  else
    let next := Blake3.Pure.compress cv (Blake3.Pure.blockWords (input.take 64))
      counter 64 (flags ||| if start then 1 else 0)
    chunkLoopWith flags counter next false (input.drop 64)
termination_by input.length
decreasing_by simp only [List.length_drop]; omega

private def subtreeWith (key : Blake3.Pure.CV) (flags : UInt32) (counter : Nat)
    (input : List UInt8) : Blake3.Pure.Output :=
  if _h : input.length ≤ 1024 then chunkLoopWith flags counter.toUInt64 key true input
  else
    let split := Blake3.Pure.leftLen input.length
    let left := subtreeWith key flags counter (input.take split)
    let right := subtreeWith key flags (counter + split / 1024) (input.drop split)
    ⟨key, left.chainingValue ++ right.chainingValue, 64, 0, flags ||| 4⟩
termination_by input.length
decreasing_by
  · have := Blake3.Pure.leftLen_lt (size := input.length) (by omega)
    simp only [List.length_take]; omega
  · have := Blake3.Pure.leftLen_positive input.length
    simp only [List.length_drop]; omega

private def digestCVWith (key : Blake3.Pure.CV) (flags : UInt32) (input : List UInt8) :
    Blake3.Pure.CV :=
  let out := subtreeWith key flags 0 input
  Blake3.Pure.compress out.cv out.block 0 out.blockLen (out.flags ||| 8)

private def digestWith (key : Blake3.Pure.CV) (flags : UInt32) (input : List UInt8) :
    Blake3.Pure.Digest :=
  (subtreeWith key flags 0 input).rootHash

private def keyCVOfBytes (bytes : List UInt8) : Blake3.Pure.CV :=
  let arr := bytes.toArray
  Vector.ofFn fun w : Fin 8 =>
    Blake3.Pure.bytesWord (Vector.ofFn fun b : Fin 4 => arr[w.val * 4 + b.val]?.getD 0)

private def digestKeyed (keyBytes input : List UInt8) : Blake3.Pure.Digest :=
  digestWith (keyCVOfBytes keyBytes) 16 input

private def deriveKeyContextCV (ctxBytes : List UInt8) : Blake3.Pure.CV :=
  digestCVWith Blake3.Pure.iv 32 ctxBytes

private def digestDeriveKeyBytes (ctxBytes input : List UInt8) : Blake3.Pure.Digest :=
  digestWith (deriveKeyContextCV ctxBytes) 64 input

private def digestDeriveKey (ctx : String) (input : List UInt8) : Blake3.Pure.Digest :=
  digestDeriveKeyBytes ctx.toUTF8.data.toList input

-- Keyed mode (`KEYED_HASH = 16`) and raw-context `derive_key` reference vectors
private def sampleKeyBytes : List UInt8 :=
  [  3, 123,  16, 175,   8, 196, 101, 134,
   144, 184, 221,  34,  25, 106, 122, 200,
   213,  14, 159, 189,  82, 166,  91, 107,
    33,  78,  26, 226,  89,  65, 188,  92]

#guard hex (digestKeyed sampleKeyBytes [0]) ==
  "91bbdceace8bcd8adc672341c760d21291c983fe4fd0e59d021d0c201176b5e8"

#guard hex (digestDeriveKeyBytes ((List.range 16).map Nat.toUInt8) [0]) ==
  "2239162ba4d341835a37375c445a3f8803eb34758ff69ee0b2aaead3941561b7"

-- All 10 protocol `v6` and `v6-zk` `derive_key` context CVs
#guard deriveKeyContextCV "multi-stark/v6/merkle/leaf".toUTF8.data.toList ==
  #v[0x77042819, 0x5A1DD04F, 0x2F8D0BB8, 0x39D27832,
     0x552A30F6, 0x546C9899, 0x8510A8EF, 0x83ECCD66]
#guard deriveKeyContextCV "multi-stark/v6/merkle/compress".toUTF8.data.toList ==
  #v[0xCC4D7633, 0xF8492FEC, 0x5704B1FD, 0x2D69A6B5,
     0xA871EBB5, 0x6439610D, 0x89E86BE6, 0x02E22A34]
#guard deriveKeyContextCV "multi-stark/v6/transcript/single".toUTF8.data.toList ==
  #v[0x943C1E0F, 0x12B98B0B, 0x1FDA3556, 0x96ECBE49,
     0xF5D6684E, 0xBABD2C79, 0x7E6FD057, 0x4BF1113F]
#guard deriveKeyContextCV "multi-stark/v6/transcript/batch".toUTF8.data.toList ==
  #v[0x56945548, 0x0BAEB2C2, 0xB0BC28DD, 0x9EBE2699,
     0xD7B24F82, 0x35470F4D, 0x065F18D3, 0xF3B2994F]
#guard deriveKeyContextCV "multi-stark/v6/vk".toUTF8.data.toList ==
  #v[0xD7089665, 0x2D51B3C7, 0x1E371C33, 0x324E12A1,
     0xB355FBFF, 0x402B8A4A, 0xD8256C89, 0xB1F439C2]
#guard deriveKeyContextCV "multi-stark/v6-zk/merkle/leaf".toUTF8.data.toList ==
  #v[0x8A663924, 0x051A410E, 0xB5929C7A, 0x52E6E08C,
     0x51D3B0FA, 0x1D1687C6, 0x472E9E06, 0x5A324ECA]
#guard deriveKeyContextCV "multi-stark/v6-zk/merkle/compress".toUTF8.data.toList ==
  #v[0x6E9B081E, 0xBAEEB5DA, 0x18652A0D, 0xA2D1B4E1,
     0x9E40FB01, 0xE905254D, 0x451628D5, 0x3D606842]
#guard deriveKeyContextCV "multi-stark/v6-zk/transcript/single".toUTF8.data.toList ==
  #v[0x89D8BDA2, 0xBDAE2046, 0x9274DB73, 0x13010FD9,
     0xC59663AB, 0x1A374FE0, 0x9FA807DF, 0xA485833F]
#guard deriveKeyContextCV "multi-stark/v6-zk/transcript/batch".toUTF8.data.toList ==
  #v[0x761A4520, 0x275E7AD5, 0xAF9417AE, 0x5177E5AE,
     0x0E64CF93, 0x68F8718A, 0x15874B68, 0x9F503445]
#guard deriveKeyContextCV "multi-stark/v6-zk/vk".toUTF8.data.toList ==
  #v[0x486C73BD, 0x64F0F532, 0xF4D92A23, 0xAE0C2406,
     0x097D11FF, 0x4783BEC5, 0x55B051EF, 0x118424A1]

-- Multi-chunk `multi-stark/v6` `derive_key` vectors (1 block, 8 blocks, 1 chunk, 2 chunks, 5 chunks)
private def domainPattern (n : Nat) : List UInt8 :=
  (List.range n).map fun i => ((i * 37 + 13) % 256).toUInt8

#guard hex (digestDeriveKey "multi-stark/v6/merkle/leaf" (domainPattern 64)) ==
  "4059736d0564475319baa815a76396039b1922ce8b8c51985ec1489f48e4581a"
#guard hex (digestDeriveKey "multi-stark/v6/merkle/leaf" (domainPattern 512)) ==
  "58ec79936d612be378b23c2cfbb876f93179b825100d3ba77c2a8fd189deae51"
#guard hex (digestDeriveKey "multi-stark/v6/merkle/leaf" (domainPattern 1024)) ==
  "0f237b3cbe5c88760fcf0305435c2b6d762142697aa21133b6508af2bd228e9c"
#guard hex (digestDeriveKey "multi-stark/v6/merkle/leaf" (domainPattern 1025)) ==
  "1efbf193b24ebcabf1c230b0f7f2c30265d0a82272db4a19341767e688849358"
#guard hex (digestDeriveKey "multi-stark/v6/merkle/leaf" (domainPattern 4264)) ==
  "bb19b2a12d999d55cc3bb2caf75c085e201c6b387519dfa2cb25eec6b9b54136"
#guard hex (digestDeriveKey "multi-stark/v6/merkle/compress" ((List.range 64).map Nat.toUInt8)) ==
  "8b14c7db6f612da11fa63c6fbec9783e35f74ab3dedf6f382fff8ace42e1b379"

-- Multi-level `derive_key` KATs across all 10 `v6` and `v6-zk` contexts
-- (0B, 64B, 1024B, 1025B, 2049B, 4097B, 8193B on `pattern n`, matching `blake3::derive_key`)
private def multiLevelDomainVectors : Array (String × Nat × String) := #[
  ("multi-stark/v6/merkle/leaf", 0, "a6205af23604bdace5d8217b52809fab1922c6f1033c72ce8d5b80055a0cdf6a"),
  ("multi-stark/v6/merkle/leaf", 64, "84fb68595017ce36f8115560264ca543da724257398e7b5980432f26ac8b1dd4"),
  ("multi-stark/v6/merkle/leaf", 1024, "54d3cf7f1ab87ae044c967bd6be149eaa7095a38694b2645cb92f0ff392cca3e"),
  ("multi-stark/v6/merkle/leaf", 1025, "e4ae7be6e15c5cf2bc97126c1b0440ac584c77981528337a8064365ae915e419"),
  ("multi-stark/v6/merkle/leaf", 2049, "1d9888bc844f399130325de4a2c30142d5ee86596fb5718e5ea8bc2c3e00933d"),
  ("multi-stark/v6/merkle/leaf", 4097, "ffd20dd7c4a23bb980a2d9c3f5698ed17820bbc634c4335b6e7cc9f568dc3e7d"),
  ("multi-stark/v6/merkle/leaf", 8193, "6be8ca1b9ad822f514fa35748fb8dcc19e6f468ec85271c5b3823389c0e67a46"),
  ("multi-stark/v6/merkle/compress", 0, "f3dbd1c88fcc4e67e3aa4f5b8dbdf0febc7b06be403748689d4aaa64310133db"),
  ("multi-stark/v6/merkle/compress", 64, "8b14c7db6f612da11fa63c6fbec9783e35f74ab3dedf6f382fff8ace42e1b379"),
  ("multi-stark/v6/merkle/compress", 1024, "85340510c80725b2cf4db65cf57dd4641453e207c43c91d83fadb5e89b3e5a6f"),
  ("multi-stark/v6/merkle/compress", 1025, "110aa265d508a4ac2458e18d524e7ebc906a145fcc6de568d3d4c206c2d159fe"),
  ("multi-stark/v6/merkle/compress", 2049, "b6cca4de20a8b516994feea65a2efc85aabe499ec95cb2edd4f4fa2686c0f026"),
  ("multi-stark/v6/merkle/compress", 4097, "d5f1d8cf1ef4a9f5e1a6620cc928918d9600510a614b237874900376d082e9f0"),
  ("multi-stark/v6/merkle/compress", 8193, "2ec9735242a25e07a2107cb3bd00bd9ecbe753a403e42153e704977b6dad3901"),
  ("multi-stark/v6/transcript/single", 0, "7cc59d6ab80ef3056cb1cc7da8dbcdf8a4026e0b3531aee245341d6d3a72d9fc"),
  ("multi-stark/v6/transcript/single", 64, "564bfbbd3a13dffeae73bb990fc9be38f41bcde9c9ee34610f80a0eb0275b74f"),
  ("multi-stark/v6/transcript/single", 1024, "3a7b3864ac80349422b57fda6fd93b2efd8cffc0cd1038075fea30f6032bb8c7"),
  ("multi-stark/v6/transcript/single", 1025, "fefa64fee1d7c8547c1dcdf198f31327d2821eaf59b97d005572c875a413d5dc"),
  ("multi-stark/v6/transcript/single", 2049, "229fac00b21e9a8c9cd53028cde501c3998ccaa72526b9aa339083fb04cbdbd6"),
  ("multi-stark/v6/transcript/single", 4097, "87058e365cc75eaca53fb0ff4fb4c25d48f65049257cae5d807b22decb17ffa6"),
  ("multi-stark/v6/transcript/single", 8193, "71f8b57065a7eb3506926ceda42542116cda7acd9bdaf5976be021848756b1e6"),
  ("multi-stark/v6/transcript/batch", 0, "2ead4673a0bf6d0aeb83c5f96456bf706afca9c64f3753c2ea42c32f1eb2a437"),
  ("multi-stark/v6/transcript/batch", 64, "9ab321067511d9761b1c1728a7c0a7e65711ad39a8d8944fd940ad10af69a068"),
  ("multi-stark/v6/transcript/batch", 1024, "354b9eaf62dee90d996b674a794bd176d184a6c9f3b1ff6dbee05571207b7920"),
  ("multi-stark/v6/transcript/batch", 1025, "c4d296b7c62f540291093be21d238a19fc94205f4573ee1d97644237f28758c4"),
  ("multi-stark/v6/transcript/batch", 2049, "70a661402c14063ade49916ad2eb6c5b59f44ad461ece07935d57c81d4759916"),
  ("multi-stark/v6/transcript/batch", 4097, "783dd4f2b8561085c114d353191e2abe8749989a916524b7a7ebd80a334cead6"),
  ("multi-stark/v6/transcript/batch", 8193, "f2a343d4b6b553cb33d3f9f74ab1e647fd7691401be910680a553f1bdb10b165"),
  ("multi-stark/v6/vk", 0, "1ab08f8c7b0bd06336afe5c9300f5812fce9c0e8ea6fe7f8d04ebf37f5110f96"),
  ("multi-stark/v6/vk", 64, "05607faedc09fcf4457ebd86c28fc7c2da344c6a6c73327a264192f9ed121b97"),
  ("multi-stark/v6/vk", 1024, "336695dde1cf70cb2b370cb05830560b5bdeb5269ea17a4f130cfed55390298d"),
  ("multi-stark/v6/vk", 1025, "8bedc19f8a7772e52f2ce3becac656e352d8a32e265ea643fdb2bb56ae957e51"),
  ("multi-stark/v6/vk", 2049, "5711f20789ca11e0a9bd01bd10da9b8e76a28b4a3356eca2fc3e9fe03f88b1bc"),
  ("multi-stark/v6/vk", 4097, "b55ace42e477ee08f2a82dbe9f41440a924eb71a03816fa54c2ef69524569f16"),
  ("multi-stark/v6/vk", 8193, "fc5fb0c4adba81037775f5ec8d1a892c7c3c0a6b28089860bd61c7718468acb0"),
  ("multi-stark/v6-zk/merkle/leaf", 0, "022645c31d68cf5cc5d49dfa8bf46060cfaff4d620bf40c2d3d8dce69b651421"),
  ("multi-stark/v6-zk/merkle/leaf", 64, "4c94869d991764f736f9a071e2f28294ea3302fbea22626c9eedd35b54b2152a"),
  ("multi-stark/v6-zk/merkle/leaf", 1024, "992112216bc63fc5e8001b9629956de88b86559edc63718de1356a1b1b3b0d74"),
  ("multi-stark/v6-zk/merkle/leaf", 1025, "d79d112ff18c035c1a7634b691fa67f16a8b15b1249fac0ced58936f799cf77c"),
  ("multi-stark/v6-zk/merkle/leaf", 2049, "aac0a41c15f64b7ebb707ff5f3040ac98cbe93ca200368db551e4e9c00545a35"),
  ("multi-stark/v6-zk/merkle/leaf", 4097, "f07beba94fac50b1786047286e314f9004144ac689d559cbff8ba063f70b4da0"),
  ("multi-stark/v6-zk/merkle/leaf", 8193, "e93507eb46a3448aba804ce5f1d2fecf7ed6cc1880f420e20bdb6bcf5b1cf256"),
  ("multi-stark/v6-zk/merkle/compress", 0, "533170b759042b54aae33bedeb89b37ae5f09e65af502269fd8c7636d1d5197a"),
  ("multi-stark/v6-zk/merkle/compress", 64, "a96715eb2d8a0e5c7291bb6b1ab0732f57e960ec084fa706f0a8bc7a89f30786"),
  ("multi-stark/v6-zk/merkle/compress", 1024, "f4d637709e85b394e0859ee75975a610b50a0f6088e06f8c09abc962fb8af240"),
  ("multi-stark/v6-zk/merkle/compress", 1025, "63799057ea9b315f407b86a06762c47b061437bd8aa6a198e75f1c87ba6a7284"),
  ("multi-stark/v6-zk/merkle/compress", 2049, "6d2d110b9b998925f1627896b9a372b5f785d009c50574d5ff754e87331eb21f"),
  ("multi-stark/v6-zk/merkle/compress", 4097, "1c64104f3f0be649e58120bb5a39e06358e145444a16104fb7807a655fda83e7"),
  ("multi-stark/v6-zk/merkle/compress", 8193, "40b00f2cf7449e52e9ceacc09e39868951e9c89b36948fd1e86082babb522cc8"),
  ("multi-stark/v6-zk/transcript/single", 0, "869c780196c455c210fb8ec562d26ef029f1c8f6c8559002918e4648bb2833d5"),
  ("multi-stark/v6-zk/transcript/single", 64, "0e24845fd2d4adcb66968668818e8a2f7334bcf4742027dda64edbc5320ed4b2"),
  ("multi-stark/v6-zk/transcript/single", 1024, "47ef043dcba00b79e8edb4202d51ff8778ff2fbc88a095f62fcda54c7b6d8ea7"),
  ("multi-stark/v6-zk/transcript/single", 1025, "baec3db3647179628e87a768ee09dd4eda2737350e47083f502b4e9eee770c0b"),
  ("multi-stark/v6-zk/transcript/single", 2049, "96839147592baffa1c2d07a9f6ae10435c9934aa1ac664b5c82cccb16beb7418"),
  ("multi-stark/v6-zk/transcript/single", 4097, "6217bb97ea04dff48d437371a173c23e655d7b05e604c0103a528178dee60d28"),
  ("multi-stark/v6-zk/transcript/single", 8193, "cb2c27afd865a526bede516cdc968c09ff318697a25cc8e5a6537707663bfce2"),
  ("multi-stark/v6-zk/transcript/batch", 0, "a07b3253afe23c893d8f23265a51bc626b2d32cebb646aa7e70aa0fb0b19ce97"),
  ("multi-stark/v6-zk/transcript/batch", 64, "df56dca8b83164b920f28f4032a167fe6264e1f8afb9ce40b571a2f5dc7ef775"),
  ("multi-stark/v6-zk/transcript/batch", 1024, "0444d6799db425248970e412094ff9c93ef9fe9ba37d47f0830ecc53af0f8fc9"),
  ("multi-stark/v6-zk/transcript/batch", 1025, "00c5c9436ff350f6c6c7f990380b260e027a2d8ecbffd79c772d3669cf4bb478"),
  ("multi-stark/v6-zk/transcript/batch", 2049, "2e5ad9205a05799c1be87d25bb6f54bf2402ea8a558546aac003f9f60da3920c"),
  ("multi-stark/v6-zk/transcript/batch", 4097, "0428a55a420d4fbf74de53bb08c44972cecee40a0e3bd00e185d46b4bc3c3d33"),
  ("multi-stark/v6-zk/transcript/batch", 8193, "a790becd177a9e7814bca8307898922dd97f19e4b6823c841104767b5480ae1b"),
  ("multi-stark/v6-zk/vk", 0, "6f1402c2a53077ff44d7c4cc8926a7f7b0974b75170d2e2f8b0a7d1158211095"),
  ("multi-stark/v6-zk/vk", 64, "edd83a2877624a855e203886b9c8fdc8a217fc12d1e7912bf33a8e2317cc3944"),
  ("multi-stark/v6-zk/vk", 1024, "02f4c01bea021aaf8fda9ee9eea91d3592b8910ab6f723dcdc29f93624236e10"),
  ("multi-stark/v6-zk/vk", 1025, "e1903e07aa79331ef3018a5e9584c8a810c12c3934b60cd13d93940581e7ecea"),
  ("multi-stark/v6-zk/vk", 2049, "4fc672a56434a2ccbc0a00f1fdb7909690fa0c0c2e4b7e56f796c0b25067197b"),
  ("multi-stark/v6-zk/vk", 4097, "0e8be6694b3c5e8c7de82de4ada8fb04e7cf76f531218d5f64eaa02dba52b13f"),
  ("multi-stark/v6-zk/vk", 8193, "bb6fd10eee6bdadcdef65935a993dc3de0451b2485f31691e1cda5340faef171")]

#guard multiLevelDomainVectors.size == 70
#guard multiLevelDomainVectors.all fun (ctx, n, expected) =>
  hex (digestDeriveKey ctx (pattern n)) == expected

end AiurBlake3Vectors
