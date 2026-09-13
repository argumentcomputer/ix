/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

/-! Frozen certified adapter identities. The archive includes the original
patches, source identities, reports and differential corpora. Maintained code
uses Ix.Theory and Ix.Kernel; five audits now traverse full checked declarations.
The historical VM pilot, packet encoder, VM test and native profiling counters
are preserved in the archive for a later change. Host tests omit the
pilot-specific assertions; maintained hashes record all local adaptations. -/

namespace Tests.Certified.ImportManifest

def archive : String := "Tests/Fixtures/Certified/c7-handoff.tar.gz"
def archiveSha256 : String := "94d7b43e2942f9a9f5c3407964905beddb834b8223ce9eb52d8df494fb17faf0"
def ixBaseRevision : String := "3e7586a7adb0c6f3cd3ff5854da832701288ec90"

structure SourceFile where
  source : String
  target : Option String
  sourceSha256 : String
  importedSha256 : String
  deriving Repr

def selected : Array SourceFile := #[
  ⟨"Ix/Certified/Audit.lean", some "Ix/Certified/Audit.lean", "06635e487e0db2bbe57f110245c0dc6e2a9c633ebfe074797567e114da8aec52", "793ea6e189ab20f68120c58d4d5483c08124715c67ffa511424c1522e249080f"⟩,
  ⟨"Ix/Certified/Bytes.lean", some "Ix/Certified/Bytes.lean", "5b01039400a830a3f80420cb011cb76c6a52511b901905f4bf7f811e19986328", "278a9cd43907eeb885e1db5c672b227d59a15713f73317941df09a3d5ca61046"⟩,
  ⟨"Ix/Certified/ClaimAccept.lean", some "Ix/Certified/ClaimAccept.lean", "0c179bd4ea2c1a9d8a3b239ffe2feb60b88038f8f9f09c5d9fd8e1e83011f981", "198d8b9b436b937c311bf7ae7e47d4523bdc80022447e42dcc03a131fb01ef38"⟩,
  ⟨"Ix/Certified/ClaimAudit.lean", some "Ix/Certified/ClaimAudit.lean", "8916803f12bb53e22fa1c94318a6b2a736ec9634ffae811f710b579d3d278bf4", "363f6524397b56c2225d2bdc5cadee29522959d043cfa8a5ace854078a5c30bb"⟩,
  ⟨"Ix/Certified/ClaimCheck.lean", some "Ix/Certified/ClaimCheck.lean", "e4d598badcb189897a339e187b9529658e2ef75445645e1463704cc6b349a196", "8f8f6c94581ed08c8b8b00d3157bd351e7aed29cd8aa53e491cb53dc48e8845f"⟩,
  ⟨"Ix/Certified/ClaimCommand.lean", some "Ix/Certified/ClaimCommand.lean", "8f360b0d0a586ab15e3b8bb3a375f5dc56ad6157344295a67673d876bf8650eb", "e053cb7bab6e1ca19e36de92bcb44c60be9764fc30ab160b92224f4703a4fb4d"⟩,
  ⟨"Ix/Certified/ClaimInput.lean", some "Ix/Certified/ClaimInput.lean", "d2d0df3ef446690600e843c84683a8f2056e1d8a843a523fc57b550763963f32", "861b0cfd3a1dac9c683dbd1b71088065a00d9a47be9ddbdce304722271027451"⟩,
  ⟨"Ix/Certified/ClaimMain.lean", some "Ix/Certified/ClaimMain.lean", "ed1f1b0edaec4e0928d90a814f35673a8989e55037c9cc023a6e0e287c7574e7", "ed1f1b0edaec4e0928d90a814f35673a8989e55037c9cc023a6e0e287c7574e7"⟩,
  ⟨"Ix/Certified/ClaimMeaning.lean", some "Ix/Certified/ClaimMeaning.lean", "78edb69d209768d8010b28b16d334fd2fa8bc6225490f9b2bbe5fd66cc906f36", "5f2550f0235fe84927d654a360a4298f426e7ca2e7911245c84f91dbd11eef6f"⟩,
  ⟨"Ix/Certified/ClaimSuggest.lean", some "Ix/Certified/ClaimSuggest.lean", "5f83e6b65542661c4efacd6389c5c6ca0a0eeaffb2d0d24cb58168be514a10f6", "285ed4b14540aa47afa67e28f20bc44e7fdce93fd94d0742971711f15df8336b"⟩,
  ⟨"Ix/Certified/Command.lean", some "Ix/Certified/Command.lean", "f9f8a32be2761dc97bf7215585cde40b0e310153482707a570f7c1a106252abe", "c6803f699ed2edd6508e2db73b55f4abb163f6425bcf6b755da11b885991ad17"⟩,
  ⟨"Ix/Certified/Corpus.lean", some "Ix/Certified/Corpus.lean", "fc1d66c81430461bed9e0045e6a26a1e01c85de90854eccea2343f24fe5dde97", "fc1d66c81430461bed9e0045e6a26a1e01c85de90854eccea2343f24fe5dde97"⟩,
  ⟨"Ix/Certified/Envelope.lean", some "Ix/Certified/Envelope.lean", "da0269803ff6f48c6d0347627d57a7f7699c0ea06e54f959406e3d8570a326f1", "da0269803ff6f48c6d0347627d57a7f7699c0ea06e54f959406e3d8570a326f1"⟩,
  ⟨"Ix/Certified/Fixtures.lean", some "Ix/Certified/Fixtures.lean", "fe7a503a0e436a2ecf924b48d9b66ed3f6ef901c7bcbe6098853c62c7748675a", "f85f883f498cdee55ab674876dd1fb19bae5dbe8aa729118cffd29ab626c8b25"⟩,
  ⟨"Ix/Certified/Ingress.lean", some "Ix/Certified/Ingress.lean", "1fe00c0a512ae94fddd2847196f1bafa415ff2c452412f0e69e9e060883dd0cf", "afd9e82827fed62d453c3979fbfdb1238f83573f19af3b6728574f97ff1a86a4"⟩,
  ⟨"Ix/Certified/Ixon.lean", some "Ix/Certified/Ixon.lean", "9b7f0d64f08c03ed3a215ff5b23e136bd85c71f953e9198fb940b597d7b54410", "5e37eaa6b5cb872edad7954cde413706f30996950c71d21417174f8166377bcb"⟩,
  ⟨"Ix/Certified/Main.lean", some "Ix/Certified/Main.lean", "c571357f5e1120efbe23c7db4906fc3eeaebffccf2956e1899212494800d38a5", "c571357f5e1120efbe23c7db4906fc3eeaebffccf2956e1899212494800d38a5"⟩,
  ⟨"Ix/Certified/ModelHints.lean", some "Ix/Certified/ModelHints.lean", "74fd6763d56ac5c8aa9af4507172879739c2dc681969a3f342aadbc30ab27837", "de098f48fc03893643c8de08c3bf2bed315f91767c71e9e229816784abb8f124"⟩,
  ⟨"Ix/Certified/ModeledAudit.lean", some "Ix/Certified/ModeledAudit.lean", "55101ebfee84fd89e4c99f08d88aac7edb7000302ef6d022a8c639e331fb3ec2", "c37969f6a69e11d62547bc91b685695cd08f002c115db70a05069f34fe111de1"⟩,
  ⟨"Ix/Certified/Native.lean", none, "7b617483cbeef932b9caaf6ca3e118be93e5621aaf1ca6bb8132821b336b1c82", ""⟩,
  ⟨"Ix/Certified/Packet.lean", none, "a694ff77c95d6fe3bd31b99e28597769604b901926d4e0a3dfea7802fb57711d", ""⟩,
  ⟨"Ix/Certified/Reveal.lean", some "Ix/Certified/Reveal.lean", "2d31e94a72208eddbd52e51ff819131430e374403e8411a9fd90b909f965af2b", "2d31e94a72208eddbd52e51ff819131430e374403e8411a9fd90b909f965af2b"⟩,
  ⟨"Ix/Certified/SourceAudit.lean", some "Ix/Certified/SourceAudit.lean", "fb916b0e7eede60d3d225d7fd8045acf175dc327e83c8705379fd01a52c7866f", "c945ca007d28ad54bcceb25c5d3dafd38029ea2280b7f22a7e85d57f637ecbb6"⟩,
  ⟨"Ix/Certified/SourceExpr.lean", some "Ix/Certified/SourceExpr.lean", "f4de024bc68cb991bbad57bbe0d1c147cfe32329fb9a34dc91a4dbde1177f805", "03417c4f256de2158e71407560d60abeaf77bbacd00533654c67c9c5b4f63334"⟩,
  ⟨"Ix/Certified/SourceMeaning.lean", some "Ix/Certified/SourceMeaning.lean", "69f916348389e4e7d93b67b3d2c3d8abf8e30b89b417de828620627c6012209a", "f96eedf1b7d46564f6c3abf0bf3450bffb5ffca85a68071f567d75837c84ee14"⟩,
  ⟨"Ix/Certified/SourceStore.lean", some "Ix/Certified/SourceStore.lean", "7b963da22cb0d2199ce4bf02353cfff0a6e8a3d571a82e19b3c9edb99336d545", "390d260608e9f4f638758751306e1cf06d4a129379a4ebcf902f5873969d832d"⟩,
  ⟨"Ix/Certified/Store.lean", some "Ix/Certified/Store.lean", "23cd4434c7e1f1784a438bdeecd66378bda1ad280f28f452cb6d51443dd7e3be", "86394770b2c96176e7478a6cdd64bc0a1057b30968b4301030ffdb59751ad733"⟩,
  ⟨"Ix/Certified/Suggest.lean", some "Ix/Certified/Suggest.lean", "cec35a4826b6b6d55bbcf62563d99d192bcb511a25c9d00be7d4341c64189d53", "214b6a2652c46ee93720a8a6f017268f7f06173cfa2e146ce6c067f08b0fa861"⟩,
  ⟨"Ix/Certified/TcAudit.lean", some "Ix/Certified/TcAudit.lean", "a0c0177157fa1a4a891f80e3aa437901a48c2c3814bc66cb26eeaaf5808f6862", "912cae64335baa42740fffea5e26035f4a90bd107fe2e17c603d3071a623e00a"⟩,
  ⟨"Ix/Certified/Trees.lean", some "Ix/Certified/Trees.lean", "cf96fa2ee3ea6263c62c630c848b8f90449d8380a454ba291ed5e7e67011c3a5", "cf96fa2ee3ea6263c62c630c848b8f90449d8380a454ba291ed5e7e67011c3a5"⟩,
  ⟨"Ix/IxVM/Certified/Accept.lean", none, "8c35df5d77369c3bc77747fa872399da1b9709fdfb53f28623809cea60637e71", ""⟩,
  ⟨"Ix/IxVM/Certified/Checker.lean", none, "7da05836aa7701570a6cc35c0dd856ff0ce1b09cfbce58cbec942e9a066c76a3", ""⟩,
  ⟨"Ix/IxVM/Certified/Expr.lean", none, "63906b989d6ade2f3a8b72c3e84c68e887a857227a9f3bacf6a94a6c873a9a1b", ""⟩,
  ⟨"Ix/IxVM/Certified/Levels.lean", none, "c59aea708f0ef66dc61d32754fa3956e597268514917546cd9ce48a1cce71be4", ""⟩,
  ⟨"Ix/IxVM/Certified/Read.lean", none, "6e25a90521af8c0dc1ba9dfb9c849a2dd4e95854484688461f1962c85f1bc650", ""⟩,
  ⟨"Ix/IxVM/Certified/Types.lean", none, "a5bc3333435eee693e5c2af7b444c4ea5de8ca56f9aed37dde6e80f23690a87a", ""⟩,
  ⟨"Ix/Tc/Certified.lean", some "Ix/Kernel/Certified.lean", "ef7be3a4a372fe1c781c4d3e407fd14c55ba0f9289392ab7e8ab5806972ad90b", "cf7d2b617336af369fa5678bcfede46c6e4a9a06f91d5334c8b7b8a6a3b85f2c"⟩,
  ⟨"Ix/Tc/CertifiedClaims.lean", some "Ix/Kernel/CertifiedClaims.lean", "ef79fbdc511c9ae90b729e639f0d57a54f68e40caab1f66d84ebba35501a30a6", "fa6d66105ade421b155c76165f7ad77c900313120e8436ce563b16e0f2451421"⟩,
  ⟨"Tests/Certified/Claims.lean", some "Tests/Certified/Claims.lean", "1a678f07b5645c1f88ff07028793663c37ab74164759953dab5a2a3e311c6a22", "1b358ef41f6b701ca1dad5f309f65e9931a2fe120aa5e22f4feae7500535db49"⟩,
  ⟨"Tests/Certified/ClaimsMain.lean", some "Tests/Certified/ClaimsMain.lean", "01f900c1a61940910c7131fc42a3757d2f7ea1a508f55668f6d54da8ee6eb136", "01f900c1a61940910c7131fc42a3757d2f7ea1a508f55668f6d54da8ee6eb136"⟩,
  ⟨"Tests/Certified/FeatureCases.lean", some "Tests/Certified/FeatureCases.lean", "d68e7731b4864cdf823bdcf94af492158bf8f9a4da3d5dcfc659cf8582795591", "2478888475a43b4d4e07f4d07910f765788870568b96ec282afba6153e44cdeb"⟩,
  ⟨"Tests/Certified/Features.lean", some "Tests/Certified/Features.lean", "65b70e67a51698b4921c6592419658e8b528ac544cdd1b0fedc84a69effa9470", "65b70e67a51698b4921c6592419658e8b528ac544cdd1b0fedc84a69effa9470"⟩,
  ⟨"Tests/Certified/Fidelity.lean", some "Tests/Certified/Fidelity.lean", "7d8fdea26a63bc94ace55943f6c062340ab3b263867ecd21705c70b288784946", "b64958afa2dfbdb90de98f6a0908a8aa18c78f944bcfd6060db317636c8c4f9a"⟩,
  ⟨"Tests/Certified/FidelityMain.lean", some "Tests/Certified/FidelityMain.lean", "47dbf7899235312d4ea171879940cf6eb98028eccbbdaeaa86b8a41a6449bb17", "47dbf7899235312d4ea171879940cf6eb98028eccbbdaeaa86b8a41a6449bb17"⟩,
  ⟨"Tests/Certified/ModelSerialize.lean", some "Tests/Certified/ModelSerialize.lean", "d470f6a95bc48ccc65f141d90abb99d2211ba82b9fa3b9d13e42f7698c755f2b", "86f064fcdd3940bd1385463a6ad65e2a455e5de8950eb025ffbae0397c8cd3e2"⟩,
  ⟨"Tests/Certified/Modeled.lean", some "Tests/Certified/Modeled.lean", "772dcd81eee47d73bbd40b25d068ce4e2f209df6fe22740db456c0b5e6e6353a", "ef4a5257a39154724a8c0c7d0c105aff571cec119353e14309e236f577cc1eb7"⟩,
  ⟨"Tests/Certified/ModeledAdversarial.lean", some "Tests/Certified/ModeledAdversarial.lean", "6147577fa6afdf0b2f05813462c99c32846443717eaea86cfbf6547d42b82e42", "ec7a790339751ba9c0e4760de959faa8eaa4682c50d3afd06d8cacfe57df2dcf"⟩,
  ⟨"Tests/Certified/ModeledMain.lean", some "Tests/Certified/ModeledMain.lean", "459171f71e7d845d1aadead559b1224a07b4d86e9be7ff97f5182fd1a88b974d", "459171f71e7d845d1aadead559b1224a07b4d86e9be7ff97f5182fd1a88b974d"⟩,
  ⟨"Tests/Certified/Ordinary.lean", some "Tests/Certified/Ordinary.lean", "59cbe0be253cda1854481989f9d02d44624db0fa3493dd7dac9cdf68480e0684", "804eca674eb8e663429a74de6710dc612d110c4dbc892da8fa6e6f08a4ac52ba"⟩,
  ⟨"Tests/Certified/Serialize.lean", some "Tests/Certified/Serialize.lean", "ef9286ca27377f034c97e8549e91484e67612aeb83dc0baf1926dff640d07f74", "593acdcb84d7d350bc258df2ad841233e946bf123583f844b516a45669a71af2"⟩,
  ⟨"Tests/Certified/Source.lean", some "Tests/Certified/Source.lean", "78a98301be394278ad90d55599aa1deba55f9463b735626c4cc1965a01200ce0", "703c39031d8211f9d156039e03ede0a5e81adb2b955932596421b2fa6686a31a"⟩,
  ⟨"Tests/Certified/SourceMain.lean", some "Tests/Certified/SourceMain.lean", "5a07d03d9f3e37b5e6e3fd84af66241c2e530054fa01c8157a8f938172c84d58", "5a07d03d9f3e37b5e6e3fd84af66241c2e530054fa01c8157a8f938172c84d58"⟩,
  ⟨"Tests/Certified/VM.lean", none, "7699c996e3238243314318ef63c7e4436bce81264420d9db231b19535552a828", ""⟩
]

end Tests.Certified.ImportManifest
