/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

/-! # Import provenance for the `Ix.Kernel` model port

Recorded on 2026-09-17 from the `jcb/ix-kernel-consistency` branch of the Ix
repository at the pinned revision below (the old workspace's working copy was
identical to the pin). Each ported file is identified by the SHA-256 of its
source and of its ported form; the only transformations are the namespace
rename `Ix.Theory` to `Ix.Kernel` and the provenance header, as the header of
every ported file states. License and notice files are verbatim copies. The
file inventory, hashes, headers, and licenses are enforced by
`Tests/Ix/Kernel/Provenance.lean` (`lake exe kernel-provenance`).

The branch's own provenance chain is retained in `Ix/Kernel/NOTICE`: the
model was authored in the Lean4Ix working tree, and its `SetTheory` and
`SetModel` directories port con-leche revision
`86cd20a65660d757cedc81561a44579099b565d0` under Apache-2.0. -/

namespace Tests.Ix.Kernel.ImportManifest

def sourceBranch : String := "jcb/ix-kernel-consistency"
def sourceRevision : String := "ad60e5f6dd23655da79cf9898d2b6b3fefbe8658"
def conLecheRevision : String := "86cd20a65660d757cedc81561a44579099b565d0"

/-- The header every ported Lean file starts with. -/
def portHeader (source : String) : String :=
  s!"/-\nPorted from Ix branch {sourceBranch} at {sourceRevision}.\nSource: {source}\n"

structure PortedFile where
  /-- Path in the source revision. -/
  source : String
  /-- Path in this repository. -/
  target : String
  sourceSha256 : String
  targetSha256 : String
  deriving Repr

/-- Modules authored in this repository under `Ix/Kernel`, with no source hash. -/
def authored : Array String := #[
  "Ix/Kernel.lean", "Ix/Kernel/Model.lean", "Ix/Kernel/Env.lean", "Ix/Kernel/Check.lean",
  "Ix/Kernel/Consistency.lean", "Ix/Kernel/Audit/Axioms.lean", "Ix/Kernel/Audit/Imports.lean",
  "Ix/Kernel/Audit/Runtime.lean", "Ix/Kernel/Audit/Roots.lean"
]

/-- Ported Lean modules. -/
def ported : Array PortedFile := #[
  ⟨"Ix/Theory/Certified/Level.lean", "Ix/Kernel/Certified/Level.lean", "d129fb7cbced78b6e03c65ec17d2199c83986266d84b4c08966ef489a69a0332", "b338a6e6c4c64f63aab9d0b180d03976dfc4853b78daf861e0b67fff991cc7f6"⟩,
  ⟨"Ix/Theory/Certified/PropWhen.lean", "Ix/Kernel/Certified/PropWhen.lean", "ba546bec95eee9e01b85f28048290a9aad0d3d9d8d4f3041ca55554cb9975e3c", "970966c84576fa99dfdee890e94024d071b54cbe5debbfcded9059df222cd93c"⟩,
  ⟨"Ix/Theory/Const.lean", "Ix/Kernel/Const.lean", "1086a0bc1f440f13ed7d31f398a8dc0f74517900fb45a4f4379b1459d890f91f", "461a3b48f20c2fa18c6539fe21c8a0aa7609a0c2951a30ae06e77ad9c4310e1c"⟩,
  ⟨"Ix/Theory/Expr.lean", "Ix/Kernel/Expr.lean", "dd0d0e2cbeac112343e08d08fb4f226b8aaa1c3c8e65b73aa69858e4a71ec034", "fea831886ed96b437e61f4f52737af632d89b3b138d76ec44cb849db2417f425"⟩,
  ⟨"Ix/Theory/ExprSubstitution.lean", "Ix/Kernel/ExprSubstitution.lean", "78f0ee4169464c6f7f2e51fcf95eb8ba73349adbd871a10a3e5ec9007f35c779", "c2ea3c2c0369c97e7247c70fbb2ccab110585dfb19e68e559f8e7ad1d82d989e"⟩,
  ⟨"Ix/Theory/Model/Annotated.lean", "Ix/Kernel/Model/Annotated.lean", "ed32d33dc81c5f1e0154689f322423d8660f8472067bd3bf19a3d875d082cdc1", "7f7dc900904cfabc3cba8d0fa23a53004d8d2f4051b03122fd62263e3217008d"⟩,
  ⟨"Ix/Theory/Model/BetaSpine.lean", "Ix/Kernel/Model/BetaSpine.lean", "e6105986031ea47df35adfe77feb2f170303e4035027453cfba57a7d47a35838", "18a61d38aecddafd4f1369a79663fb86beb6d66651f74fd4cb9af6866aba7ab3"⟩,
  ⟨"Ix/Theory/Model/BetaSubstitution.lean", "Ix/Kernel/Model/BetaSubstitution.lean", "9118fca2803baee20bb18d3154936cf16e61525c55cb640c9a5b35bf2c80ed45", "f93fb1493a5d319581f5c0f60a4b0702d8d644a3964aa2f9a0edd187fae06ef3"⟩,
  ⟨"Ix/Theory/Model/Checking.lean", "Ix/Kernel/Model/Checking.lean", "e04fd5d5d2882717055cd309048dc69fabe512c2a73ba1aa331f452a95be9814", "4f1c80f4f966bf014e6c39ccd102dffa2d786b27829fa1b06f96ec84b52fd2dd"⟩,
  ⟨"Ix/Theory/Model/Context.lean", "Ix/Kernel/Model/Context.lean", "8c57825ebdb7e28cc54ce42e8924812e2c9988fe7eb0b0364acb4b3afe689585", "50f5dff863b89926dc6a927b9d502be0e2eab8f5ebedabd704e7625144f28495"⟩,
  ⟨"Ix/Theory/Model/ContextTransport.lean", "Ix/Kernel/Model/ContextTransport.lean", "0b8d81d3948b669fe9d401e61a699df38a9aba01d2140dfaaabaa5ccc911bd1b", "6f7c44393cd55e5b94de4c1d58660bc4c419d717c9d71bdd54903b476f3a6b7b"⟩,
  ⟨"Ix/Theory/Model/Environment.lean", "Ix/Kernel/Model/Environment.lean", "d04caed44db24b1e9d975887667fcfd391b18632ad86594b3b0dcece641db70c", "d23a1a78df815f112f1db2f8ed35518cfc3d72fb8d41e480fb616b8216cf5653"⟩,
  ⟨"Ix/Theory/Model/Extension.lean", "Ix/Kernel/Model/Extension.lean", "5f495b1203494322850b8460f6d2cd947c371251f9aba7a74ea63372aafe232b", "b6fdb13f3b4707007b839f8deaa0937ac99563f1e09af4f4675e4b50c7032546"⟩,
  ⟨"Ix/Theory/Model/Inductive/Codes.lean", "Ix/Kernel/Model/Inductive/Codes.lean", "8ebf69a14c0f0b08d721ddd4d91d47c0fc213d5be8afbf628e0e6d6ea304a23e", "0876848dc86ae3d2ed0ec97fafa4494532f38044859ac2150ae66cb5b01011f6"⟩,
  ⟨"Ix/Theory/Model/Inductive/Container.lean", "Ix/Kernel/Model/Inductive/Container.lean", "d91819e3511afeadc5afbcb15136cf4c4a648c00a0df5871391db77382123a7f", "f3b3a785dbbebcad889b2b0d3e841f7b4a0247fb7014981720d952216b4a4129"⟩,
  ⟨"Ix/Theory/Model/Inductive/Recursor.lean", "Ix/Kernel/Model/Inductive/Recursor.lean", "9e3447aa42c3db2c4492691e4bc7f57073e13c27ff46081f48b073bc918739d9", "2e907d235bb731c494bc1f4c2c70dfb3bec8cc5c8e221924297ab27d6960659e"⟩,
  ⟨"Ix/Theory/Model/Inductive/Telescope.lean", "Ix/Kernel/Model/Inductive/Telescope.lean", "b75ffc42b152c5ed7bf3da8d70ca08317c435450ef7274d9e56e6fa25c6dfa94", "3d78cf24fae37e7a82128836a971e47e1b93dac7e818731e0ec009626c761665"⟩,
  ⟨"Ix/Theory/Model/Instantiation.lean", "Ix/Kernel/Model/Instantiation.lean", "042fcc537d6afa91a462c6dedfadc2c2b40140178a9d97cd50758f94147b6f77", "33fe4c4cdee9a00b5792ab0b169f725e10d4b020552203ccb0dd6ea0395efffe"⟩,
  ⟨"Ix/Theory/Model/Interpret.lean", "Ix/Kernel/Model/Interpret.lean", "f46a22934113337b8f4a05b5410cd3205d8430ec9fad97d4e8281b988aa38fa9", "8c1d5c27008a13f89ebf1ccd137878d6d6f334c1f7f9584ac0e5967e980e8e15"⟩,
  ⟨"Ix/Theory/Model/Judgment.lean", "Ix/Kernel/Model/Judgment.lean", "f04301f42ca7bc22d861d0171ec677c34a08a94e73c8eea9d2b885c9c924e111", "13539a386fb9b84dec8e7aadde6f432e1d2d20915d7850e82b697f95775c43bd"⟩,
  ⟨"Ix/Theory/Model/LevelCongruence.lean", "Ix/Kernel/Model/LevelCongruence.lean", "b2f194118fc99d3fa0054174eb5b73095133955c6c09c32719e4ebef76a3d336", "b7e1af7c66d5ea5ed43a6cbd017f0804d396899b3a3153524f359b1a5e5e8e2d"⟩,
  ⟨"Ix/Theory/Model/PrimitiveValues.lean", "Ix/Kernel/Model/PrimitiveValues.lean", "451101f02ea9158fdb4ea81995bde5fcabb2c7496f00435d86cf84c876a77396", "5b167ada76ba6eebde5a63deb0eb4e83858b74688b55a9e704537a4dcf255697"⟩,
  ⟨"Ix/Theory/Model/ReferenceMap.lean", "Ix/Kernel/Model/ReferenceMap.lean", "74bef71492efbfce059d3eb35ea7d263f85baa24d33b51dcfd53dadd1a5ec95c", "9d8151092c62ccad0bfb5f89aeac9759964d72d1ba28202e45b8279b22db9a4c"⟩,
  ⟨"Ix/Theory/Model/SetModel/Container.lean", "Ix/Kernel/Model/SetModel/Container.lean", "08928de8de78f1fabc535b65e8511b068ad3c8b517055aa363674c2c90cebd4e", "a12e420f84b6efbfa68301fd089c66ba5a699576ff969f212ff9d8d2adc32702"⟩,
  ⟨"Ix/Theory/Model/SetModel/Iter.lean", "Ix/Kernel/Model/SetModel/Iter.lean", "019ef9fa62f5d141ccc8c7e41259ff52dfba56412b3a57917ba60c28a2bfb378", "1fd1bd1ce3fbf52c7af70d725d2303a035dad90c8d37798c0188407b71c75d2a"⟩,
  ⟨"Ix/Theory/Model/SetModel/Ops.lean", "Ix/Kernel/Model/SetModel/Ops.lean", "6ce498a847103c32824e40f22e51db42163da98c09374f6a69e2a85a69f1e732", "9f3004547865e30453a4bf2303e8ac7dd19ad0e55ce3f30212d4fab93479c3b9"⟩,
  ⟨"Ix/Theory/Model/SetModel/RecGraph.lean", "Ix/Kernel/Model/SetModel/RecGraph.lean", "da698d1a7346eaaa2f5b4734de06c955a05791ff52728d554082814328bd5caa", "43a093497c18669ad278e4a96e91f3123fdaaf83d8c8e815a2645f71f6d7ebaa"⟩,
  ⟨"Ix/Theory/Model/SetModel/TaggedSum.lean", "Ix/Kernel/Model/SetModel/TaggedSum.lean", "53b565da9a2ce8848ca2442e52bfa0ff13b3f044017858fe69be42a9b2614aff", "f3291256efdbed5e18a14f9b928194762af542677981b636e401145b5ef7c927"⟩,
  ⟨"Ix/Theory/Model/SetModel/TupleTower.lean", "Ix/Kernel/Model/SetModel/TupleTower.lean", "1089b4ea6d9e7ff3ed9902a3c3d8f6697332b2aac23f94e503584b9cdf972750", "bb562d364a074fac120f5db08ac566efff06e6e95cdb05798806454f0bb9ce80"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Core.lean", "Ix/Kernel/Model/SetTheory/Core.lean", "9e8d3537a66ded9e4d9142765c9ebda3eb4c3a8f780927cea6657e076933657b", "a3df853f71dd17d713ea4d177f3331108404cd19bf681f5cefd87a3d26d146ae"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Choice.lean", "Ix/Kernel/Model/SetTheory/Derive/Choice.lean", "47e64bd1d52287230b993398ba5ee584d7b15e256b86f4fa0eaf1735c4510b93", "5ee9e163ea3262a24fd006cbb1b0c67b10980ce53ed636f8a9d73829e9e9e707"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Empty.lean", "Ix/Kernel/Model/SetTheory/Derive/Empty.lean", "b9a961b71e8a0576ceb00fbdc0288231d360576cd7afa72375606c793da15541", "18598a6e1a9fb28c02cccde80d7eaf58e4a75f5ef26ecce4035e10cd4e6c29e1"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Graphs.lean", "Ix/Kernel/Model/SetTheory/Derive/Graphs.lean", "5bff626e2b77ea3d83302dd8959ef0e0816e9d9da59d52d573134f139e69316c", "ab3d4e4d9cf89054cdb6ae173a444bd862c5a2697fd0eb0fa18eab2f305c4995"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/LfpFam.lean", "Ix/Kernel/Model/SetTheory/Derive/LfpFam.lean", "0657c96c6dffb7a49fec92c97769356595ec8a6f06b5f73594d4732d2fef8b8f", "b4fed947411651c58a8be7a1619908a919b873a5b3e01de5df494f622f6a3c16"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Lfp.lean", "Ix/Kernel/Model/SetTheory/Derive/Lfp.lean", "65e44e5bfe2fa0720b334cd31aff2c2eff511364feadfd5fd60c1ebf150b9a89", "2748c55f9ec18eddee10aa5deebd77194b0660ebf309ebc3a27f91f107ca6ea2"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Omega.lean", "Ix/Kernel/Model/SetTheory/Derive/Omega.lean", "0cf178fada4077bfc8ba7dc257d8ceb77e7db8a452a9fba09eb736ad84f475be", "1c5662e3ac0c1a4a4b693fddc2320ae882695db4802d98afccd5b389ff1383c5"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Pair.lean", "Ix/Kernel/Model/SetTheory/Derive/Pair.lean", "a72c5b13f5657a8299b060bd344068f56c3e2fadfc3619e64b9bc28e98085c91", "7dd45c53e966fd7d7b2c117eb65033fe4082cfeb257f6e1e8ea8a8104de3227e"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Pt.lean", "Ix/Kernel/Model/SetTheory/Derive/Pt.lean", "520286bf987d29f56976d32ed2527ddf494ac80592fba05c1ffc4ad7627d9934", "32ca4a27611dfd2b97d04dea804426da594b073ae83e599d7f6490aea1d70c98"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Quot.lean", "Ix/Kernel/Model/SetTheory/Derive/Quot.lean", "356b3b639fad5c6a9990bf106a38d49b32d0b0ae80537aba2719aaab8f9d9c84", "80f9c695f545bbc0b32a217a9124902172fbe85ea93c1b56f9351ef7e36ff377"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Sep.lean", "Ix/Kernel/Model/SetTheory/Derive/Sep.lean", "38536c268957fe0ad6e0127a1f07677bbfe4a17de82d0a2738b9042db55be2c7", "6eef056423c2a2c0c86f8bd6cd27b75a52754cef785143dc2042251f1a29618a"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Sigma.lean", "Ix/Kernel/Model/SetTheory/Derive/Sigma.lean", "59cfd35485e1b90d199089aea2886fe7ed12bd9f02637d2d7cd5e21536ec6ef5", "e60583d46c64046841ff9296fdd3bcf920ca9ec0390b70e1d0a00f3fd074e065"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Universe.lean", "Ix/Kernel/Model/SetTheory/Derive/Universe.lean", "c3eb55ee316ce142c16fa5c9a3e06ac45721767bad845ce8cd4c485ac7cce494", "31e12562c17d07630f72469e35b5fa8b47463fb8f321c20cbd00b182cb70cd2f"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Univ.lean", "Ix/Kernel/Model/SetTheory/Derive/Univ.lean", "33e83e18da0a782904f42acc563c1c4259b60a1833bf2b22af41a28f1bd797e0", "59140f05a139f36e57fc8770e700ef53557d867771df0392911cad04ef0a8826"⟩,
  ⟨"Ix/Theory/Model/Signature.lean", "Ix/Kernel/Model/Signature.lean", "bb1a22e9c2e82a865b9c0c221f4f53356417a539099c42814f4290cfd71029c6", "ce5c71df5744183ccb6fbb4909031fb87e837ba556d5191a063f5f29011df8a0"⟩,
  ⟨"Ix/Theory/Model/Substitution.lean", "Ix/Kernel/Model/Substitution.lean", "e90eace7615fb232d1f948fd1f25bfccec833277d8df16239dbe7225ecd5adcd", "839e9245864878305efd06d898bd6c722314ceb074008051bd1e1d803062b51d"⟩,
  ⟨"Ix/Theory/Model/Support.lean", "Ix/Kernel/Model/Support.lean", "85a181776d1c09e59f024b45faffdd2ac25129eea88644f499771befc3b215d0", "077e15763b64b8b458a0b14cdfffea59b1732f6c98f2ff74dedf79e2c6b84528"⟩,
  ⟨"Ix/Theory/Model/TelescopeSemantics.lean", "Ix/Kernel/Model/TelescopeSemantics.lean", "d6bd21fe9f80863e7ccf6cbf7bb374228309be2929be9b56130b2601840bc27c", "d87146f45b304aaeaefba2f6ed2593b3279004e3002f02d8a9cb909458406476"⟩,
  ⟨"Ix/Theory/Model/UniverseBounds.lean", "Ix/Kernel/Model/UniverseBounds.lean", "6122c479c70781d03dc890aa01fe62433a87a9e6b8ee18c04593f4b0394f8fcd", "4b702d3b0ca93165cd363ac2f6edb5b6815da9f77b76765eba4d39a3566a5d93"⟩,
  ⟨"Ix/Theory/Model/Value.lean", "Ix/Kernel/Model/Value.lean", "5165837492c4f96220f275ada33f881529c18c476f7485a02140f103967361fb", "d036f404789ed6123eb2b2badc6906b06ce60dfbd468a63f0b92592a6c973a4a"⟩,
  ⟨"Ix/Theory/Model/WellDenoted.lean", "Ix/Kernel/Model/WellDenoted.lean", "22161a9e497bd3c5398c26865ff7d0f2f92ba3d2faf0d7017a4b5440509868ee", "fb1ac8fb5cb73f546733affdffd52ed62f99e0571619fb9a16156c69c7d83f68"⟩,
  ⟨"Ix/Theory/Quot.lean", "Ix/Kernel/Quot.lean", "542671181d3ab2ba9999a8e0ea85778760f2bc145850513cf6fcad14d4ac7dd9", "da6a080e9b93ef3b4acbfdfbb21032237341c556412ddd60d6788ad3f871883f"⟩,
  ⟨"Ix/Theory/Ref.lean", "Ix/Kernel/Ref.lean", "72b21fcb84bf5653761ff1bbc305447c391c6446a0d5ffcab7151e42013b5844", "caf46bf8c993b544c75973b1091af72006573433faa23a38b35e6ed9fd422255"⟩,
  ⟨"Ix/Theory/Rename.lean", "Ix/Kernel/Rename.lean", "1adeda5dd1a733eaeda6e345ef4c5f0fbefaf80e1caaebedb79c1f73c4193c9e", "1c1b26441a0495345c3e0974f241ca38b32dc9b91471e0f1550bbaf307e8b4f6"⟩,
  ⟨"Ix/Theory/Std/Basic.lean", "Ix/Kernel/Std/Basic.lean", "6e82da238805fcdb9225996b96028f816444615a885d22747d1d860953c0c313", "da2cde72dae5dedc5cf3030fd45e4ee626515fda803c1f07076c7d3d6fff063c"⟩,
  ⟨"Ix/Theory/Store.lean", "Ix/Kernel/Store.lean", "2c47bffde6a5357f35ca24bcf194d554afa86ff3b62267c0961d61e65136015a", "23f6c6ffaa0582e37e8d116e9cbdc98d693ceff2baf16c081801dcb845faddd5"⟩,
  ⟨"Ix/Theory/StringLiteral.lean", "Ix/Kernel/StringLiteral.lean", "9b1d58085ef74448a85d0a56cf8e4991b5335cdeb39b7e55160d422f96ae48b2", "6c356365a23ec00701925ca3aa3eb4a8ca295e08f23c0ba36221487d5fa3684a"⟩,
  ⟨"Ix/Theory/VLevel.lean", "Ix/Kernel/VLevel.lean", "8fd068d8f412a42c4f69461ebb7f56a4232fbcbe644dd3e43f4ea5ab554b2a3b", "166e7ff0aed57ce8d108588adea8f4e2073dd5244ea00be960862f925d83ffae"⟩,
  ⟨"Ix/Theory/VLevelLemmas.lean", "Ix/Kernel/VLevelLemmas.lean", "9f17589c3888e03bd1e66d3d3ef04b86ea5761570a928e49bce1b71c5947c6b0", "f4cd1f5f171dcb6c7cbee0c35dacad5c3d81e706eeff7d923871a489dcf1a849"⟩
]

/-- Verbatim license and notice copies. -/
def licenses : Array PortedFile := #[
  ⟨"Ix/Theory/LICENSE", "Ix/Kernel/LICENSE", "cf9ee0e22d7f19885552c933d4097d500c9027fdddfea3bd675e90af212284e9", "cf9ee0e22d7f19885552c933d4097d500c9027fdddfea3bd675e90af212284e9"⟩,
  ⟨"Ix/Theory/LICENSE-APACHE", "Ix/Kernel/LICENSE-APACHE", "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4", "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4"⟩,
  ⟨"Ix/Theory/LICENSE-MIT", "Ix/Kernel/LICENSE-MIT", "fb722e573ab676ffc697f17a01fb13888dad389fbc879314018380a7dbfc70d7", "fb722e573ab676ffc697f17a01fb13888dad389fbc879314018380a7dbfc70d7"⟩,
  ⟨"Ix/Theory/NOTICE", "Ix/Kernel/NOTICE", "046d7aefcc035fac38420bef9c4eded1591efe83b6d8e68739d70f055c8d7497", "046d7aefcc035fac38420bef9c4eded1591efe83b6d8e68739d70f055c8d7497"⟩
]

end Tests.Ix.Kernel.ImportManifest
