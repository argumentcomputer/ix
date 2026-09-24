/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

/-! # Import provenance for the `Ix.Kernel` model port

Recorded on 2026-09-17 from the `jcb/ix-kernel-consistency` branch of the Ix
repository at the pinned revision below (the old workspace's working copy was
identical to the pin). Each ported file is identified by the SHA-256 of its
source and of its ported form; the transformations are the namespace
rename `Ix.Theory` to `Ix.Kernel`, the provenance header, for three files
the import trim that makes the kernel depend on Lean core only, and for twelve
files the `letE` constructor with its cases, for three model files the
`ConstantFact.recursor` constructor, and for the ordinary-inductive route
the K2 adaptation (no input store, the recursor at member 1 of its block,
inference in place of witness validation, published rule facts) and likewise
for the structure and natural-number routes and the `Signature` rule checker,
for the equality, `Iff`, and `Nonempty` bases and the quotient and standard-axiom
routes (no input store, per-primitive facts and readings, the model-only
split of the equality basis, inference in place of witness validation),
and the natural-number family reference on literals, as the header of
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
  "Ix/Kernel/Audit/Runtime.lean", "Ix/Kernel/Audit/Roots.lean", "Ix/Address/Core.lean",
  "Ix/Kernel/Model/LetRules.lean", "Ix/Kernel/Level.lean", "Ix/Kernel/Claims.lean", "Ix/Kernel/Infer.lean",
  "Ix/Kernel/Annotate.lean", "Ix/Kernel/Certified/Checker.lean", "Ix/Kernel/Certified/Ordinary/Read.lean",
  "Ix/Kernel/Inductive/Ordinary.lean", "Ix/Kernel/Certified/Structure/Read.lean",
  "Ix/Kernel/Inductive/Structure.lean", "Ix/Kernel/Inductive/Natural.lean",
  "Ix/Kernel/Model/QuotientValues.lean", "Ix/Kernel/Certified/Quotient/Install.lean",
  "Ix/Kernel/Certified/Standard/Install.lean"
]

/-- Ported Lean modules. -/
def ported : Array PortedFile := #[
  ⟨"Ix/Theory/Certified/Basis/Equality.lean", "Ix/Kernel/Certified/Basis/EqualityChecked.lean", "66c404ed6c66211dfb60690cd072197238ab6305efa3a6dbcef7b5ddca5baf27", "5f49fa99eb80747ff180dd01380d869cd50c82e853aa1a9113ed8b150a538440"⟩,
  ⟨"Ix/Theory/Certified/Basis/Equality.lean", "Ix/Kernel/Certified/Basis/Equality.lean", "66c404ed6c66211dfb60690cd072197238ab6305efa3a6dbcef7b5ddca5baf27", "b8cee7826bb4495b4e7708200d4ab3d08bf164c6ddabaf531f6bbc36e10f5784"⟩,
  ⟨"Ix/Theory/Certified/Basis/Iff.lean", "Ix/Kernel/Certified/Basis/Iff.lean", "e8f04f80953d924a7d1d36084d21fb8d9e03461d72eb23a9f32c220c9f151af7", "85e50f7a2d2487066022cbe313f304a2a118c12c661862eeeb69e27c0967487d"⟩,
  ⟨"Ix/Theory/Certified/Basis/Interface.lean", "Ix/Kernel/Certified/Basis/Interface.lean", "421d43c0a613c49819c3edc962a82da503b9509f0d5f1515b2b479787f1648de", "7856d31e9c69c04a8f03d318f2a17321ae8857edb06581c9a83aa30f5e5720d2"⟩,
  ⟨"Ix/Theory/Certified/Basis/Nonempty.lean", "Ix/Kernel/Certified/Basis/Nonempty.lean", "b717b2ea0c59eb6b359df24c0f45fbeeb2a9cafe0775fe319e8e38b4c2427065", "284ac37e35abca883356730e7bb108e5d8ed9fbe6f184d157d3cb1a0fd81b906"⟩,
  ⟨"Ix/Theory/Certified/LevelEq.lean", "Ix/Kernel/Certified/LevelEq.lean", "f2597b5a6c63ba437c90c77d3ea92d45ce9d340fc9e4fb615a8843fabdb1f7fb", "efbd7eb167a895a810c5c0dad3d02dfb26a821399ec300915718ed70b4d6df9f"⟩,
  ⟨"Ix/Theory/Certified/Level.lean", "Ix/Kernel/Certified/Level.lean", "d129fb7cbced78b6e03c65ec17d2199c83986266d84b4c08966ef489a69a0332", "b338a6e6c4c64f63aab9d0b180d03976dfc4853b78daf861e0b67fff991cc7f6"⟩,
  ⟨"Ix/Theory/Certified/Natural/Checked.lean", "Ix/Kernel/Certified/Natural/Checked.lean", "d1bff0ed4bc1231d76044bac3964947a6dd4d6272256537a1d69ccc9e061a53b", "7351e5c477412a6ba2d0592c56ba4b3f197b8e8e3e0a37e811676a1e2842d68f"⟩,
  ⟨"Ix/Theory/Certified/Natural/Publish.lean", "Ix/Kernel/Certified/Natural/Publish.lean", "6ac732a887610b95b85da5f6dbd516c7c261ecb1a53c8b20c1ccf526a16a54fb", "48e148341394cb225c828846b19f30bc099ba703dad8ac373c67584b2d6c31ee"⟩,
  ⟨"Ix/Theory/Certified/Natural/Value.lean", "Ix/Kernel/Certified/Natural/Value.lean", "767478f45bbf8ab14125a40ec79f8e92bda04bf8dabba367643b44603984623c", "65605d1e58677fcfa8b81b9333126c9ebc1573ad6c2e2599c149c4b09d8ee243"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Checked.lean", "Ix/Kernel/Certified/Ordinary/Checked.lean", "057c155790636810073b2fee33877e581e1feda5192de32b2358b1838e14966d", "3f976d1628a49c9e75525e7db6b4af23e428f3b89bedce972ac149e5521885e9"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Computation.lean", "Ix/Kernel/Certified/Ordinary/Computation.lean", "0ec36fa1fb5bf9d3865f4b389df1eb6e23b79fbe7b8e29a3a91ccd02794dd578", "f91eb0ba4e7434ece504489dd2613dc94d2d8efc90ce8ed823eba1f1dbbcb2ba"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Constructors.lean", "Ix/Kernel/Certified/Ordinary/Constructors.lean", "ce1fcbcd3644cc3485764cb9b3e39f271a146486db395668024f9e5c9f8b3b1a", "f64cda9e731d223284d33b8639721d897a10f9163bb63f3774f2eb8f98414587"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/ConstructorStage.lean", "Ix/Kernel/Certified/Ordinary/ConstructorStage.lean", "8612f402adad29023d40195337679f7cdd17915f500d11461e746f608d46fa37", "1bdd9214b9dc35d2becec4ab4ef8e6b2344d60081260e9f3ae1d53c46139070a"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Container.lean", "Ix/Kernel/Certified/Ordinary/Container.lean", "229fa390d45d0052ef899b5e609b8f86bc81e57213d72b5a02be6f8d223e859c", "05174d0a323ef376ec340856e4c546899bcc8c148dfa734207605beb4b9ec129"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Eliminator.lean", "Ix/Kernel/Certified/Ordinary/Eliminator.lean", "f447bab9bea15ef6d0ee1b68d3483b6d9403b7ddc9058449ce0601396bbd9ec8", "72ddcb287339570bd531034ca33e7156e750f7600418156269c9a5b1265525bb"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Family.lean", "Ix/Kernel/Certified/Ordinary/Family.lean", "8c563254b994b8f6c4b5ff2d4a2387072789634b3121b86a45c10149be9c8923", "14eba9e20c2b09e5d0008c4cd40e994c0b2178dbe62f190a8f239617c7eda57c"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/LargeElim.lean", "Ix/Kernel/Certified/Ordinary/LargeElim.lean", "cea67ca384c6c67bc8f110ca73a981fc2054a4eb8814a06bff194c46e35577cc", "d8bf720342df8d43757390891209c7cb13b13ae867205051ddc515cbf801a21e"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Reading.lean", "Ix/Kernel/Certified/Ordinary/Reading.lean", "ae00e1e0185abc8f2208f3d0665ab1d6119e58589b37ed8059ded5e72869fccc", "9a5b54e58b4b8712f53c749c1159b8a961e8a28542a3ea1e4f70c713f2480a8b"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RecursorReading.lean", "Ix/Kernel/Certified/Ordinary/RecursorReading.lean", "7418c845cbea665fd05504ceec48dd13d252c84a554ea511ac45107823f79b98", "3bff55614bc237a5ead680475e81884aaa2d9b17bda5a4659bbadd07d2ae13c4"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RecursorStage.lean", "Ix/Kernel/Certified/Ordinary/RecursorStage.lean", "e6b240ea2dd0365184be563f6e2894fc2e0bf560ee2fb5abf2bebf52058b736d", "016d87669adc5161c364122f23698a6f6ca73a03de66ba8c04ffe85650026d13"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RecursorSyntax.lean", "Ix/Kernel/Certified/Ordinary/RecursorSyntax.lean", "a15eb2395e6bd2a91dde535e931baaedc2e36a7e96a415905635da942316c18d", "f3502416fab1fc41f64d05d83d2f7e69d7f17bf564750cb3ea30c69347c0e903"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RecursorValue.lean", "Ix/Kernel/Certified/Ordinary/RecursorValue.lean", "f0915684633f08b93588652dc5cc9d44ae0ad79e5de1bbbf2816511559d59a0a", "91004f490f3e1a819b7a9bb4bfa77f8d38c86452e71b0cc1333f6780f0d9ecb8"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RuleChecks.lean", "Ix/Kernel/Certified/Ordinary/RuleChecks.lean", "6e748d47998f1d3314f71c4a320f28a6bb400e8a3068e4d58357f38c16bb51ef", "caa68417d2290e2b3512952eea74a331811ec0776b75133e9d14cc51b9d573a5"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RuleEquations.lean", "Ix/Kernel/Certified/Ordinary/RuleEquations.lean", "ffa708a84577d0edee7bf90abdbaeab41f025b74fd55b9faa430c0fc6ebf418f", "21d3f67c2fc89cfa0f0b45eb2aeed21bf2f7b8d1c19cb4e969e355f5234f5254"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RuleReading.lean", "Ix/Kernel/Certified/Ordinary/RuleReading.lean", "42ca1e10514a2c1e97f8e645dfc584fc1788e87bfb6fe9fc63cf82e5c6b491c3", "1a45e0af2a8965df8cfa43f5e03c338e17e475e1f194ea8174659d351fa50f93"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Shape.lean", "Ix/Kernel/Certified/Ordinary/Shape.lean", "b90dfc2e5e5366d9bac38b6a3afb80f5a5ebb4939d0f8a56cf967e48e4559f3a", "f9edf69435fbe81a2e3621aa841163ae8de0a87da15140a345dfb0fc09c7c61d"⟩,
  ⟨"Ix/Theory/Certified/PropWhen.lean", "Ix/Kernel/Certified/PropWhen.lean", "ba546bec95eee9e01b85f28048290a9aad0d3d9d8d4f3041ca55554cb9975e3c", "970966c84576fa99dfdee890e94024d071b54cbe5debbfcded9059df222cd93c"⟩,
  ⟨"Ix/Theory/Certified/Quotient/Reading.lean", "Ix/Kernel/Certified/Quotient/Reading.lean", "879cd33813a146d4f42a27954a49b3a14c0b577f74e667225eb3c3b6949f3f8d", "8d5a2f538fc27634854388eb493d3ef18afeb77d52bd89097ea6873f35cde80f"⟩,
  ⟨"Ix/Theory/Certified/Quotient/Syntax.lean", "Ix/Kernel/Certified/Quotient/Syntax.lean", "1a7b4f53dc2c2ec0a7ab1798c10491943c851a8496aaa2be64fea60af9080ff8", "828d4c71afb5b7c6b67bf6a504befc3aad2888f440f7a8089aaa13c236fc3a33"⟩,
  ⟨"Ix/Theory/Certified/Signature.lean", "Ix/Kernel/Certified/Signature.lean", "e06ebc68dbd7b7997ed9c85ea6cc8bfe541c7830cc1af06c12a4062fbc4c8f00", "ee56501137d0b13d16653bf2c8e80ea6954ebfe469ed14021b1e53a696b8f9f6"⟩,
  ⟨"Ix/Theory/Certified/Standard/Checked.lean", "Ix/Kernel/Certified/Standard/Checked.lean", "3090dea2c13b7a4cfe48fc298121f8671a776166f2ce27b7736cba38e8a87c85", "c24432acad2d6f56502e5085a1e25ef5350d3d461685a82185aa9c2e110e2dea"⟩,
  ⟨"Ix/Theory/Certified/Standard/Realization.lean", "Ix/Kernel/Certified/Standard/Realization.lean", "f0b7a970b3a4a9d8f1eafcd807bf91707139024a089b88f227c6fb8930cba4fa", "d4bb4f8be74595049ba6ba62e9a4df77ae7d5fa5b37525648e08b4f5eb873833"⟩,
  ⟨"Ix/Theory/Certified/Structure/Checked.lean", "Ix/Kernel/Certified/Structure/Checked.lean", "bd8336b3506f61303e5f2068ad300bfbcff9fbbca3f4ea40fdd3a08e1caabf13", "2719934b182b9a8a5da48fe86f4e43e9f41a1d4f0869a6e8001b51ad0beb257c"⟩,
  ⟨"Ix/Theory/Certified/Structure/Computation.lean", "Ix/Kernel/Certified/Structure/Computation.lean", "e9319a046b644a5412b4c0b88433af3522d5d7038ac24807477dd0045badcc92", "2b0e43d7a8bf68d3a47b21c28d7f6d6fa6453c1b7b4a712a87b1303b4c40eece"⟩,
  ⟨"Ix/Theory/Certified/Structure/Publish.lean", "Ix/Kernel/Certified/Structure/Publish.lean", "562aa6be637c211cbc44a79ea7051f5322e7a378cb54150a02fafff606b47d1c", "33bc8dde71b41b27f631b849460c641028fad399097f00a069f7a705ca3566e6"⟩,
  ⟨"Ix/Theory/Certified/Structure/Reading.lean", "Ix/Kernel/Certified/Structure/Reading.lean", "ea25446679471ed786d5487f1375ee2ccf07e7602b10787b4ff51b7fb7dd2f38", "b9a9f0945d015959d4e269c9103e6c6f909061e45038c955a6f2340f97c67b3b"⟩,
  ⟨"Ix/Theory/Certified/Structure/Syntax.lean", "Ix/Kernel/Certified/Structure/Syntax.lean", "e114fddb504393ee7975ce521a1e0218ece270c9cbece13850a334252f1ad3b9", "8678933b082d9e3839aa45542a182503c56d57e003a20b9d8dd1557df3e5c351"⟩,
  ⟨"Ix/Theory/Certified/Structure/Value.lean", "Ix/Kernel/Certified/Structure/Value.lean", "e89f5f99c5b1154812062665fba0704902400d8209a6300cad6c72533e163f53", "d702cfe3e097e268719c235debb0303b112b1f30646f0c5af50d52dbf6c295e9"⟩,
  ⟨"Ix/Theory/Certified/Telescope.lean", "Ix/Kernel/Certified/Telescope.lean", "03e54b24dc101b2ecd1800ac780fe544dbf20f04db8984854e5015480f7575c7", "aa7382e8f2e2eac7a6dbcfc85a43fd6075113607358d08fbc2522a2f02399b35"⟩,
  ⟨"Ix/Theory/Const.lean", "Ix/Kernel/Const.lean", "1086a0bc1f440f13ed7d31f398a8dc0f74517900fb45a4f4379b1459d890f91f", "461a3b48f20c2fa18c6539fe21c8a0aa7609a0c2951a30ae06e77ad9c4310e1c"⟩,
  ⟨"Ix/Theory/Expr.lean", "Ix/Kernel/Expr.lean", "dd0d0e2cbeac112343e08d08fb4f226b8aaa1c3c8e65b73aa69858e4a71ec034", "fb0b557a963aa3f1e642b6b27149616c5abe412b08b7b96f1eaffd533ea0d435"⟩,
  ⟨"Ix/Theory/ExprSubstitution.lean", "Ix/Kernel/ExprSubstitution.lean", "78f0ee4169464c6f7f2e51fcf95eb8ba73349adbd871a10a3e5ec9007f35c779", "02c15d4bd2186be30f36a41fbb596849785869c1f531bc74317beed6eb132722"⟩,
  ⟨"Ix/Theory/Inductive/Levels.lean", "Ix/Kernel/Inductive/Levels.lean", "84724e7502dc16a5d32000b32b46bc518c851ab0ce2e4600d56878def665a339", "ee06f871612287b2027bff4450434d5a394143d5a832754425dc804581410280"⟩,
  ⟨"Ix/Theory/Model/Annotated.lean", "Ix/Kernel/Model/Annotated.lean", "ed32d33dc81c5f1e0154689f322423d8660f8472067bd3bf19a3d875d082cdc1", "57eca844e700c8e4fcc7a3e98d2ec26990825bee2eece3e193e938a38fc7396c"⟩,
  ⟨"Ix/Theory/Model/BetaSpine.lean", "Ix/Kernel/Model/BetaSpine.lean", "e6105986031ea47df35adfe77feb2f170303e4035027453cfba57a7d47a35838", "18a61d38aecddafd4f1369a79663fb86beb6d66651f74fd4cb9af6866aba7ab3"⟩,
  ⟨"Ix/Theory/Model/BetaSubstitution.lean", "Ix/Kernel/Model/BetaSubstitution.lean", "9118fca2803baee20bb18d3154936cf16e61525c55cb640c9a5b35bf2c80ed45", "ec38ca4b4063c0bf35c3565a194972caf28d074bc806a8e249618df1659bbe03"⟩,
  ⟨"Ix/Theory/Model/Checking.lean", "Ix/Kernel/Model/Checking.lean", "e04fd5d5d2882717055cd309048dc69fabe512c2a73ba1aa331f452a95be9814", "4f1c80f4f966bf014e6c39ccd102dffa2d786b27829fa1b06f96ec84b52fd2dd"⟩,
  ⟨"Ix/Theory/Model/Context.lean", "Ix/Kernel/Model/Context.lean", "8c57825ebdb7e28cc54ce42e8924812e2c9988fe7eb0b0364acb4b3afe689585", "50f5dff863b89926dc6a927b9d502be0e2eab8f5ebedabd704e7625144f28495"⟩,
  ⟨"Ix/Theory/Model/ContextTransport.lean", "Ix/Kernel/Model/ContextTransport.lean", "0b8d81d3948b669fe9d401e61a699df38a9aba01d2140dfaaabaa5ccc911bd1b", "6f7c44393cd55e5b94de4c1d58660bc4c419d717c9d71bdd54903b476f3a6b7b"⟩,
  ⟨"Ix/Theory/Model/Environment.lean", "Ix/Kernel/Model/Environment.lean", "d04caed44db24b1e9d975887667fcfd391b18632ad86594b3b0dcece641db70c", "8f43a1335b529494e710efae685d38ab1dc2c86b5af1653156654baf1f054103"⟩,
  ⟨"Ix/Theory/Model/Extension.lean", "Ix/Kernel/Model/Extension.lean", "5f495b1203494322850b8460f6d2cd947c371251f9aba7a74ea63372aafe232b", "ed3b1cb3f11348f633fab0efe7823a5b70e7f8352fed080abb3d7098175b913c"⟩,
  ⟨"Ix/Theory/Model/Inductive/Codes.lean", "Ix/Kernel/Model/Inductive/Codes.lean", "8ebf69a14c0f0b08d721ddd4d91d47c0fc213d5be8afbf628e0e6d6ea304a23e", "0876848dc86ae3d2ed0ec97fafa4494532f38044859ac2150ae66cb5b01011f6"⟩,
  ⟨"Ix/Theory/Model/Inductive/Container.lean", "Ix/Kernel/Model/Inductive/Container.lean", "d91819e3511afeadc5afbcb15136cf4c4a648c00a0df5871391db77382123a7f", "f3b3a785dbbebcad889b2b0d3e841f7b4a0247fb7014981720d952216b4a4129"⟩,
  ⟨"Ix/Theory/Model/Inductive/Recursor.lean", "Ix/Kernel/Model/Inductive/Recursor.lean", "9e3447aa42c3db2c4492691e4bc7f57073e13c27ff46081f48b073bc918739d9", "2e907d235bb731c494bc1f4c2c70dfb3bec8cc5c8e221924297ab27d6960659e"⟩,
  ⟨"Ix/Theory/Model/Inductive/Telescope.lean", "Ix/Kernel/Model/Inductive/Telescope.lean", "b75ffc42b152c5ed7bf3da8d70ca08317c435450ef7274d9e56e6fa25c6dfa94", "3d78cf24fae37e7a82128836a971e47e1b93dac7e818731e0ec009626c761665"⟩,
  ⟨"Ix/Theory/Model/Instantiation.lean", "Ix/Kernel/Model/Instantiation.lean", "042fcc537d6afa91a462c6dedfadc2c2b40140178a9d97cd50758f94147b6f77", "bd310c3957254db3f264dcc8305624962a4c96c8b6b0f03a2abf753e4de94a7f"⟩,
  ⟨"Ix/Theory/Model/Interpret.lean", "Ix/Kernel/Model/Interpret.lean", "f46a22934113337b8f4a05b5410cd3205d8430ec9fad97d4e8281b988aa38fa9", "a001b6965fb05827b6cf80b50fd804a3af87957f3cb72492889fb19baef4e8d5"⟩,
  ⟨"Ix/Theory/Model/Judgment.lean", "Ix/Kernel/Model/Judgment.lean", "f04301f42ca7bc22d861d0171ec677c34a08a94e73c8eea9d2b885c9c924e111", "1b7504ac05f16cd41c8fb0c145c7d13f0fd1e88c2e3686c3b58313d818313efa"⟩,
  ⟨"Ix/Theory/Model/LevelCongruence.lean", "Ix/Kernel/Model/LevelCongruence.lean", "b2f194118fc99d3fa0054174eb5b73095133955c6c09c32719e4ebef76a3d336", "d02d2e8d8978d5c7ad30edebd13e9d4bfb050a286980971021413859db21e474"⟩,
  ⟨"Ix/Theory/Model/PrimitiveValues.lean", "Ix/Kernel/Model/PrimitiveValues.lean", "451101f02ea9158fdb4ea81995bde5fcabb2c7496f00435d86cf84c876a77396", "5b167ada76ba6eebde5a63deb0eb4e83858b74688b55a9e704537a4dcf255697"⟩,
  ⟨"Ix/Theory/Model/ReferenceMap.lean", "Ix/Kernel/Model/ReferenceMap.lean", "74bef71492efbfce059d3eb35ea7d263f85baa24d33b51dcfd53dadd1a5ec95c", "dbef023f0d087436c251e9a7e8d4dee4220014fd971684edaf6d45ba06e601d2"⟩,
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
  ⟨"Ix/Theory/Model/Substitution.lean", "Ix/Kernel/Model/Substitution.lean", "e90eace7615fb232d1f948fd1f25bfccec833277d8df16239dbe7225ecd5adcd", "e099a74df59e17e099dc91baaac1d6ffcf81c89516fe92c746b890626050f3c4"⟩,
  ⟨"Ix/Theory/Model/Support.lean", "Ix/Kernel/Model/Support.lean", "85a181776d1c09e59f024b45faffdd2ac25129eea88644f499771befc3b215d0", "a749c9d978e7fabe2413c55968fcdea51c974fdf5800fd8b741a4a2a7622eedb"⟩,
  ⟨"Ix/Theory/Model/TelescopeSemantics.lean", "Ix/Kernel/Model/TelescopeSemantics.lean", "d6bd21fe9f80863e7ccf6cbf7bb374228309be2929be9b56130b2601840bc27c", "d87146f45b304aaeaefba2f6ed2593b3279004e3002f02d8a9cb909458406476"⟩,
  ⟨"Ix/Theory/Model/UniverseBounds.lean", "Ix/Kernel/Model/UniverseBounds.lean", "6122c479c70781d03dc890aa01fe62433a87a9e6b8ee18c04593f4b0394f8fcd", "4b702d3b0ca93165cd363ac2f6edb5b6815da9f77b76765eba4d39a3566a5d93"⟩,
  ⟨"Ix/Theory/Model/Value.lean", "Ix/Kernel/Model/Value.lean", "5165837492c4f96220f275ada33f881529c18c476f7485a02140f103967361fb", "d036f404789ed6123eb2b2badc6906b06ce60dfbd468a63f0b92592a6c973a4a"⟩,
  ⟨"Ix/Theory/Model/WellDenoted.lean", "Ix/Kernel/Model/WellDenoted.lean", "22161a9e497bd3c5398c26865ff7d0f2f92ba3d2faf0d7017a4b5440509868ee", "382b6cb6843246a9989abd50f653518284eef1d85f790ae71a6cdc401238f9e8"⟩,
  ⟨"Ix/Theory/Quot.lean", "Ix/Kernel/Quot.lean", "542671181d3ab2ba9999a8e0ea85778760f2bc145850513cf6fcad14d4ac7dd9", "da6a080e9b93ef3b4acbfdfbb21032237341c556412ddd60d6788ad3f871883f"⟩,
  ⟨"Ix/Theory/Ref.lean", "Ix/Kernel/Ref.lean", "72b21fcb84bf5653761ff1bbc305447c391c6446a0d5ffcab7151e42013b5844", "caf46bf8c993b544c75973b1091af72006573433faa23a38b35e6ed9fd422255"⟩,
  ⟨"Ix/Theory/Rename.lean", "Ix/Kernel/Rename.lean", "1adeda5dd1a733eaeda6e345ef4c5f0fbefaf80e1caaebedb79c1f73c4193c9e", "3b0c8ab150f98e855310a696712dd92f16790cbf82b826f11ee2f69a220a4e6c"⟩,
  ⟨"Ix/Theory/Std/Basic.lean", "Ix/Kernel/Std/Basic.lean", "6e82da238805fcdb9225996b96028f816444615a885d22747d1d860953c0c313", "d9fe83f1ec7d8e30d55befb54b79030f336d46a5b86be39d3a5c6038b05c5db1"⟩,
  ⟨"Ix/Theory/Store.lean", "Ix/Kernel/Store.lean", "2c47bffde6a5357f35ca24bcf194d554afa86ff3b62267c0961d61e65136015a", "23f6c6ffaa0582e37e8d116e9cbdc98d693ceff2baf16c081801dcb845faddd5"⟩,
  ⟨"Ix/Theory/StringLiteral.lean", "Ix/Kernel/StringLiteral.lean", "9b1d58085ef74448a85d0a56cf8e4991b5335cdeb39b7e55160d422f96ae48b2", "87ebb506d20f3193dbd005ea5b4822450e17acecd1434db3ff8dd227a6763006"⟩,
  ⟨"Ix/Theory/VLevel.lean", "Ix/Kernel/VLevel.lean", "8fd068d8f412a42c4f69461ebb7f56a4232fbcbe644dd3e43f4ea5ab554b2a3b", "0483937c0bf0154af1fdb54421be0ffdedbf005ecf3820cb743b973742aaed9a"⟩,
  ⟨"Ix/Theory/VLevelLemmas.lean", "Ix/Kernel/VLevelLemmas.lean", "9f17589c3888e03bd1e66d3d3ef04b86ea5761570a928e49bce1b71c5947c6b0", "a131cafa208faf7dbce493bbdbd08dfa93041d5b425e92598e4d724b50dd05e7"⟩
]

/-- Verbatim license and notice copies. -/
def licenses : Array PortedFile := #[
  ⟨"Ix/Theory/LICENSE", "Ix/Kernel/LICENSE", "cf9ee0e22d7f19885552c933d4097d500c9027fdddfea3bd675e90af212284e9", "cf9ee0e22d7f19885552c933d4097d500c9027fdddfea3bd675e90af212284e9"⟩,
  ⟨"Ix/Theory/LICENSE-APACHE", "Ix/Kernel/LICENSE-APACHE", "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4", "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4"⟩,
  ⟨"Ix/Theory/LICENSE-MIT", "Ix/Kernel/LICENSE-MIT", "fb722e573ab676ffc697f17a01fb13888dad389fbc879314018380a7dbfc70d7", "fb722e573ab676ffc697f17a01fb13888dad389fbc879314018380a7dbfc70d7"⟩,
  ⟨"Ix/Theory/NOTICE", "Ix/Kernel/NOTICE", "046d7aefcc035fac38420bef9c4eded1591efe83b6d8e68739d70f055c8d7497", "046d7aefcc035fac38420bef9c4eded1591efe83b6d8e68739d70f055c8d7497"⟩
]

end Tests.Ix.Kernel.ImportManifest
