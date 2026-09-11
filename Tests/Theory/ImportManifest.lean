/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

/-! Import provenance, recorded from the Lean4Ix working tree on 2026-09-11.
The working tree contained the new, uncommitted consistency model; the base
revision alone does not identify these inputs. Source hashes identify each file.
The selected file inventory is enforced by `Tests/Theory/Provenance.lean`.
The generated `Ix/Theory.lean` umbrella records its sole upstream import. -/

namespace Tests.Theory.ImportManifest

def lean4IxBaseRevision : String := "ab42e79e2a4e2615a3ca6ef983d510f374057a38"
def conLecheRevision : String := "86cd20a65660d757cedc81561a44579099b565d0"

structure SourceFile where
  source : String
  target : String
  sourceSha256 : String
  deriving Repr

def selected : Array SourceFile := #[
  ⟨"Lean4Ix/Certificate/Build.lean", "Ix/Theory/Certificate/Build.lean", "833e462fae9934f3d7809fc78b7c791d7ede3ab4398732079f26ea73f53abc4c"⟩,
  ⟨"Lean4Ix/Certificate/Claims.lean", "Ix/Theory/Certificate/Claims.lean", "c3532bd7b49d0657f52913f4da285580aa2de467ecd27b41f5263a165ae34d0f"⟩,
  ⟨"Lean4Ix/Certificate/Modeled.lean", "Ix/Theory/Certificate/Modeled.lean", "28d4f7cd3bdb5945d31b8f6f10c686d6c22889e96511c765b7a28c59b17ac47a"⟩,
  ⟨"Lean4Ix/Certificate/Ordinary.lean", "Ix/Theory/Certificate/Ordinary.lean", "7c85145faf3bef4f934087fe9694171dd457c2e84190000f8c5c355af9d357c3"⟩,
  ⟨"Lean4Ix/Certificate/OrdinarySource.lean", "Ix/Theory/Certificate/OrdinarySource.lean", "291704dd2ff2d53d70ac73876ff1505eb99c96e4a029f46e9428dc64eadd24f4"⟩,
  ⟨"Lean4Ix/Certificate/Quotient.lean", "Ix/Theory/Certificate/Quotient.lean", "8c5a44003cc09313a600d3e53ebf0de1bfbee5d64c6c24fa6753fc87659aad83"⟩,
  ⟨"Lean4Ix/Certificate/Standard.lean", "Ix/Theory/Certificate/Standard.lean", "54605d2a22c2671429fe65e9cd210677deee90dc38f629991f1f0f1dc157bea8"⟩,
  ⟨"Lean4Ix/Certificate/Structure.lean", "Ix/Theory/Certificate/Structure.lean", "a0e5c274ed5c5ced8854841144086396d11c105b080bdb2c46b8ccf44d34a1d2"⟩,
  ⟨"Lean4Ix/Certificate/Suggest.lean", "Ix/Theory/Certificate/Suggest.lean", "d7863536599fa0554d4ce34427b496b306301982cdef8a9bda2395380fd1ee2a"⟩,
  ⟨"Lean4Ix/Certified.lean", "Ix/Theory/Certified.lean", "db42519eb53c5c24965b27879cb1ad81eca1010513fc67cf486f324c942fce98"⟩,
  ⟨"Lean4Ix/Certified/Accept.lean", "Ix/Theory/Certified/Accept.lean", "ce3975aa6a82f020ad6c92a5644945d3bb68ea323f97ef7eace8ba9d5d5aa80e"⟩,
  ⟨"Lean4Ix/Certified/Admission.lean", "Ix/Theory/Certified/Admission.lean", "ea6a1b8d3126190332557d424957551af7d780abe98aa0af5433a928d97ba991"⟩,
  ⟨"Lean4Ix/Certified/Basis/Equality.lean", "Ix/Theory/Certified/Basis/Equality.lean", "fa4886a2d0d764ba85c0711a258d0d94888a30cf39db2842290d220b1d7213c0"⟩,
  ⟨"Lean4Ix/Certified/Basis/Iff.lean", "Ix/Theory/Certified/Basis/Iff.lean", "368fa1c9c359a29a5877af993f16698025d84aed967ce4720122280532644fc8"⟩,
  ⟨"Lean4Ix/Certified/Basis/Interface.lean", "Ix/Theory/Certified/Basis/Interface.lean", "6bcd43996a8101c48f3f11a17f1950b3db74ca1a7cb970de324cd0fe78f8d4ce"⟩,
  ⟨"Lean4Ix/Certified/Basis/Nonempty.lean", "Ix/Theory/Certified/Basis/Nonempty.lean", "5f62092f92138ee8433f9f56977aec6c03827819342bb7417080cdc2c19b35d4"⟩,
  ⟨"Lean4Ix/Certified/Checker.lean", "Ix/Theory/Certified/Checker.lean", "677f0f68b1422d9ccc467234acaa12737fd97f9ecdc43755b46e12f36be9858a"⟩,
  ⟨"Lean4Ix/Certified/ClaimComposition.lean", "Ix/Theory/Certified/ClaimComposition.lean", "d99702d5199447cb696e365ccbb246b3bf9663b432ead0563b6572101f19f731"⟩,
  ⟨"Lean4Ix/Certified/Claims.lean", "Ix/Theory/Certified/Claims.lean", "fe28187c7eeabd148c8b737532f0559f0424397b8ba70cf2b990edd7d9623738"⟩,
  ⟨"Lean4Ix/Certified/Frontier.lean", "Ix/Theory/Certified/Frontier.lean", "a0dfec4872d5e7ef728494a0a71bef107cfb243a42107fe92185e3fb0d371fb0"⟩,
  ⟨"Lean4Ix/Certified/Level.lean", "Ix/Theory/Certified/Level.lean", "37c6fa05fddfc0a01a70288cf49d870a77625119be6c73bd0061fe76c0d27420"⟩,
  ⟨"Lean4Ix/Certified/LevelEq.lean", "Ix/Theory/Certified/LevelEq.lean", "a6402afba171af4b4df58ea4de64b3e1517fae90bd8ce145bb96775bb4862923"⟩,
  ⟨"Lean4Ix/Certified/LogicalPolicy.lean", "Ix/Theory/Certified/LogicalPolicy.lean", "763a20bd20133c2cf235c27cec875f2c67bb0ec0c5a7c25c5df82562531a496a"⟩,
  ⟨"Lean4Ix/Certified/Modeled/Admission.lean", "Ix/Theory/Certified/Modeled/Admission.lean", "68c0ef0b5e19984d08e8d34c296548eceeb4f5c4f4d86d5df3174be9ae0d939c"⟩,
  ⟨"Lean4Ix/Certified/Modeled/Equation.lean", "Ix/Theory/Certified/Modeled/Equation.lean", "bb49b60d019b57819c030e0ea41f853727f4d0aecb0174e31c236639747dde4d"⟩,
  ⟨"Lean4Ix/Certified/Modeled/Source.lean", "Ix/Theory/Certified/Modeled/Source.lean", "ac4a72a22fc77f5a512511a19c0b0c01925cf2eca5b1c1de4f00c111b048c88d"⟩,
  ⟨"Lean4Ix/Certified/Modeled/Transport.lean", "Ix/Theory/Certified/Modeled/Transport.lean", "d0d020ca9fd123fb036cd35d662b237778f9e1c24119250185cb2946bd3d99ab"⟩,
  ⟨"Lean4Ix/Certified/Natural/Admission.lean", "Ix/Theory/Certified/Natural/Admission.lean", "8d7ce4e7f0da80d5ffe45b45aeba72320ec7da35bbad3eb3fdc321512ff74a1a"⟩,
  ⟨"Lean4Ix/Certified/Natural/Checked.lean", "Ix/Theory/Certified/Natural/Checked.lean", "2dd7ad9e96c65a5d74a84f8c6c6cec3ba2693ab6f77aefcd7a29089529d6172b"⟩,
  ⟨"Lean4Ix/Certified/Natural/Publish.lean", "Ix/Theory/Certified/Natural/Publish.lean", "fac41bc4b4a409d0266d64b4375a638ed1ec281c28ec20c993d7166072d15ca1"⟩,
  ⟨"Lean4Ix/Certified/Natural/Value.lean", "Ix/Theory/Certified/Natural/Value.lean", "db39def05ce46d1da7b78209acfba10596e67642a2942ad438b38a049ab5d51b"⟩,
  ⟨"Lean4Ix/Certified/Operations.lean", "Ix/Theory/Certified/Operations.lean", "9c7bb4b947421dfbaa12b7dc7ddbac0021847a0f2b2c092decfb3dd2e582fc34"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/Admission.lean", "Ix/Theory/Certified/Ordinary/Admission.lean", "b19b0077e451aae6cc608d9007def64bd66523e89e2a5f558d0cf7abf77926ad"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/Checked.lean", "Ix/Theory/Certified/Ordinary/Checked.lean", "04ffd22d2d6b5c0070f8e8bb6b8504b408046ae39ffd07625f2708f7994bed8e"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/Computation.lean", "Ix/Theory/Certified/Ordinary/Computation.lean", "27dc5c8f9d2a7990e64c13c2fab256da3dd99d5fa5ba8eeea9134f3d39f44792"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/ConstructorStage.lean", "Ix/Theory/Certified/Ordinary/ConstructorStage.lean", "ebd00026aff885831dc52fa28f33be3a562d19980bbbb50ec0111b9ebbbb60b2"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/Constructors.lean", "Ix/Theory/Certified/Ordinary/Constructors.lean", "e57eac74ac4190013c6fc603b14fbf747985266a1369bf1b7d8cdf3785da718c"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/Container.lean", "Ix/Theory/Certified/Ordinary/Container.lean", "a5f560feda487c89356faa1e775a4133f2dfc9bfaa8002472a217a227ddac582"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/Eliminator.lean", "Ix/Theory/Certified/Ordinary/Eliminator.lean", "8e2162333ed48c3fbeeef2ce15ccc2406628dfa71f927550204eb1c295a2dde2"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/Family.lean", "Ix/Theory/Certified/Ordinary/Family.lean", "b668e27738cbe8336059f8cd0313feb8709ab112ee64126d53e28998aac77568"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/LargeElim.lean", "Ix/Theory/Certified/Ordinary/LargeElim.lean", "af7d28444877b6a7524aaaf277944c6fc9b75bdadfa4baf481bdc3edf4ee337f"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/Reading.lean", "Ix/Theory/Certified/Ordinary/Reading.lean", "8da97d7af13f89fc5a1983c45f1988bb5c8dea391481825b5040a102599b7cbb"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/RecursorReading.lean", "Ix/Theory/Certified/Ordinary/RecursorReading.lean", "0013a5e2233423cc0bfc5e6db6259a86d45649098912594cf5e9bb844d6f1043"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/RecursorStage.lean", "Ix/Theory/Certified/Ordinary/RecursorStage.lean", "9e6cbbfee2e9748be9042845d5d7f702b60aaa0516483892d16d974d8315ea26"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/RecursorSyntax.lean", "Ix/Theory/Certified/Ordinary/RecursorSyntax.lean", "df1bef5d63e0e84506bc7f3c9be345d080ace1e226b3573073b005a493b9c4fb"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/RecursorValue.lean", "Ix/Theory/Certified/Ordinary/RecursorValue.lean", "ab4328139fc3b76b25b71a42e01ddb089ae17e04d811dbc63aead88450370f30"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/RuleChecks.lean", "Ix/Theory/Certified/Ordinary/RuleChecks.lean", "ef1fe53fa44205b23ef384cb6b72e0129d3341e07834339184d694a8951225bb"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/RuleEquations.lean", "Ix/Theory/Certified/Ordinary/RuleEquations.lean", "40b04a47431f9c12aaf8450c408cddc849aa6da53c77b11c33612fbcfb9b7236"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/RuleReading.lean", "Ix/Theory/Certified/Ordinary/RuleReading.lean", "263f59728e844b9d905c7e28ba20eefc7f3c708b2237157814248490e40d19bd"⟩,
  ⟨"Lean4Ix/Certified/Ordinary/Shape.lean", "Ix/Theory/Certified/Ordinary/Shape.lean", "e071e91be7609ed73c995623153a28d96cae1c1e057e3b0464373d85f9084c7e"⟩,
  ⟨"Lean4Ix/Certified/Policy.lean", "Ix/Theory/Certified/Policy.lean", "67f69859dfed1dd21bdb6b253a578b1473d34fca6d408d13bbcd0176644373d9"⟩,
  ⟨"Lean4Ix/Certified/Prelude.lean", "Ix/Theory/Certified/Prelude.lean", "1cdc62000e9c5532b989c905d7bf1b37c3c1578cd15c19a6cccfae7a1581892c"⟩,
  ⟨"Lean4Ix/Certified/PropWhen.lean", "Ix/Theory/Certified/PropWhen.lean", "c4d80fc1af048f6bf97841d4b63f8528cf7891a71f6e05744fd33edabc757343"⟩,
  ⟨"Lean4Ix/Certified/Quotient/Admission.lean", "Ix/Theory/Certified/Quotient/Admission.lean", "4efb5df9a2703a1aaed2f286e47fc0445ea05c0a4891499e9b58e3ddaac7a347"⟩,
  ⟨"Lean4Ix/Certified/Quotient/Checked.lean", "Ix/Theory/Certified/Quotient/Checked.lean", "d093c1dd39f35be954c8ddbc0267f00cbf6119262a512efb5c9ad96250e208ba"⟩,
  ⟨"Lean4Ix/Certified/Quotient/Publish.lean", "Ix/Theory/Certified/Quotient/Publish.lean", "e637fa623b20d14592b09fbf8101bd08a741d525dab462404a057fbcafc004bd"⟩,
  ⟨"Lean4Ix/Certified/Quotient/Reading.lean", "Ix/Theory/Certified/Quotient/Reading.lean", "b20e0748f126fa0281d4c552e242f22d9ba3c2ce2d578de0604794504b199f60"⟩,
  ⟨"Lean4Ix/Certified/Quotient/Syntax.lean", "Ix/Theory/Certified/Quotient/Syntax.lean", "25ec7aebc6499c1a2778355bef69c0dc262b66a00fe12124c78c38dd7a867adb"⟩,
  ⟨"Lean4Ix/Certified/Quotient/Value.lean", "Ix/Theory/Certified/Quotient/Value.lean", "08575dd364648ad62fadba8b2d67e514b03e775354c17b029dea6a6b4c7c0985"⟩,
  ⟨"Lean4Ix/Certified/Signature.lean", "Ix/Theory/Certified/Signature.lean", "7be85d7fa465ce50f0dfc8ab65e364c5562e81763914fa779857a636d97a64b7"⟩,
  ⟨"Lean4Ix/Certified/Source.lean", "Ix/Theory/Certified/Source.lean", "f1bbfea2e6e31b9969c3acc70da1182b015c2a11700f92ce8d6304c74128b3ec"⟩,
  ⟨"Lean4Ix/Certified/Standard/Admission.lean", "Ix/Theory/Certified/Standard/Admission.lean", "cfd3c5d8662b25116d3c58cf3fa7429368b36071f0ebc032df154e154fa05ff4"⟩,
  ⟨"Lean4Ix/Certified/Standard/Checked.lean", "Ix/Theory/Certified/Standard/Checked.lean", "cb58c99a87d53fa919f1a742fef8727df0690d77b2713b42d1c815e880666cfd"⟩,
  ⟨"Lean4Ix/Certified/Standard/Realization.lean", "Ix/Theory/Certified/Standard/Realization.lean", "2a90165564c1f56591d6b68501dbfa846673f4fe59cf47aeaa16d0fb79e6c172"⟩,
  ⟨"Lean4Ix/Certified/Store.lean", "Ix/Theory/Certified/Store.lean", "84ab117484c092edd994dff513cea86042f23bb5d076c61bcb640fda3d146842"⟩,
  ⟨"Lean4Ix/Certified/Structure/Admission.lean", "Ix/Theory/Certified/Structure/Admission.lean", "b38964cc9ff83d383c8a4d110cb3e11d9d0ea66c0b3498e9e7481a31cd560483"⟩,
  ⟨"Lean4Ix/Certified/Structure/Checked.lean", "Ix/Theory/Certified/Structure/Checked.lean", "1d92b154e7a69cf25bbfbf138aca9f0a77172e55be1e2f5392cc0a2d84f27f33"⟩,
  ⟨"Lean4Ix/Certified/Structure/Computation.lean", "Ix/Theory/Certified/Structure/Computation.lean", "c537302f6d91deb46c5b9eb29641124fc30fb0acc84d231d51d6ae7c3be4c65f"⟩,
  ⟨"Lean4Ix/Certified/Structure/Publish.lean", "Ix/Theory/Certified/Structure/Publish.lean", "48015840ff11abaea77db702acca3ec29e479395f4509a5fc409cba7cb2f923d"⟩,
  ⟨"Lean4Ix/Certified/Structure/Reading.lean", "Ix/Theory/Certified/Structure/Reading.lean", "36074e7c2f8a23d4ea5cece00a703773cdc9bc8907304072038b78845b359ddd"⟩,
  ⟨"Lean4Ix/Certified/Structure/Syntax.lean", "Ix/Theory/Certified/Structure/Syntax.lean", "ffdbc5cced526a36b7f5139af30cdb2fb3be03222194b56b0f68edb5e72775d4"⟩,
  ⟨"Lean4Ix/Certified/Structure/Value.lean", "Ix/Theory/Certified/Structure/Value.lean", "6e96be97f9894a209efdc79d2ff96c21f4202ad11afb7afa639f9d5bc5c553ee"⟩,
  ⟨"Lean4Ix/Certified/Telescope.lean", "Ix/Theory/Certified/Telescope.lean", "40fecfc7cf9d1abafb855079b8c8d55cff471e6ffb9b7ddd919ea90951b78987"⟩,
  ⟨"Lean4Ix/Theory/Const.lean", "Ix/Theory/Const.lean", "bfb95d9f4af666804e79e34933e2fd094c0a783bce5b5d3da7b8b6061f4d0f0a"⟩,
  ⟨"Lean4Ix/Theory/Expr.lean", "Ix/Theory/Expr.lean", "c848e36c9654d211718ef4fedba3c338ac0428e4e54024c770022263aecf437b"⟩,
  ⟨"Lean4Ix/Theory/Inductive/Levels.lean", "Ix/Theory/Inductive/Levels.lean", "59c8752ec02adbe0860adf60eadedd480152d5bf352058f647512158f0a9a6cb"⟩,
  ⟨"Lean4Ix/Model/Annotated.lean", "Ix/Theory/Model/Annotated.lean", "55f71adb9e40f4a85aae2fbb4349498f4f2007d568a6bc84fffbdec437741a04"⟩,
  ⟨"Lean4Ix/Model/Context.lean", "Ix/Theory/Model/Context.lean", "b0ce5e4808fc1a4a4d4ca8bf5faf850420675eb9065d3912ce9156de4ba93c37"⟩,
  ⟨"Lean4Ix/Model/Environment.lean", "Ix/Theory/Model/Environment.lean", "bd646827350485bde61df1825f47a4ff20861ebf6f45853ddb2f3cf611858e38"⟩,
  ⟨"Lean4Ix/Model/Extension.lean", "Ix/Theory/Model/Extension.lean", "c1f649360ad30417e9ddb84d6dea939e77c0aebc80279fa5b56d806feb22f109"⟩,
  ⟨"Lean4Ix/Model/Inductive/Codes.lean", "Ix/Theory/Model/Inductive/Codes.lean", "9855264e0038c77b57491c3818c192bbd0bd4fba210e33bf5a2d9dfded591939"⟩,
  ⟨"Lean4Ix/Model/Inductive/Container.lean", "Ix/Theory/Model/Inductive/Container.lean", "e14328e0152de4f8017a28b0500e96615bc432f98b1475babb229b34967394ba"⟩,
  ⟨"Lean4Ix/Model/Inductive/Recursor.lean", "Ix/Theory/Model/Inductive/Recursor.lean", "3028689c3bb11d90e38170e680560c8a9d123bce42d46b00f1bfd4e78d4c9026"⟩,
  ⟨"Lean4Ix/Model/Inductive/Telescope.lean", "Ix/Theory/Model/Inductive/Telescope.lean", "8867df5a379798d10615f7c7b068f4982c3e846b1511cdb18bfc600ec66c7c18"⟩,
  ⟨"Lean4Ix/Model/Instantiation.lean", "Ix/Theory/Model/Instantiation.lean", "994e4027343d62e996fb814fc32d12c86571d4557fe7a157349a6eaf5b2e81f6"⟩,
  ⟨"Lean4Ix/Model/Interpret.lean", "Ix/Theory/Model/Interpret.lean", "a505d97b1c6658d72391f0187462c443396cdce88fe6256f070842d71ea3fdf9"⟩,
  ⟨"Lean4Ix/Model/Judgment.lean", "Ix/Theory/Model/Judgment.lean", "a98aff0288e2db11369e658f7e083309ff4e6794bc66e0b3cab7465aac0a7591"⟩,
  ⟨"Lean4Ix/Model/PrimitiveValues.lean", "Ix/Theory/Model/PrimitiveValues.lean", "84d16a4015cc253f731494e4c5213170d8b4174b6e33871becc598f9c1a46d55"⟩,
  ⟨"Lean4Ix/Model/ReferenceMap.lean", "Ix/Theory/Model/ReferenceMap.lean", "a9d50c7c0f6ae0f4258ecfaa828a127361c277a242ae8111b9d149c137acb29e"⟩,
  ⟨"Lean4Ix/Model/SetModel/Container.lean", "Ix/Theory/Model/SetModel/Container.lean", "bfc5c926aee16b6456151f48832bd8c41bbb9582f541ccc864eec753277c3a25"⟩,
  ⟨"Lean4Ix/Model/SetModel/Iter.lean", "Ix/Theory/Model/SetModel/Iter.lean", "6962b64d8ccd7b34df2dce7c7e0dff6bf4872b6d11de2ab608807b4787e230a0"⟩,
  ⟨"Lean4Ix/Model/SetModel/Ops.lean", "Ix/Theory/Model/SetModel/Ops.lean", "17a7e331d36a0fb0a5153bad2e115f3795cdb2db24f20e1a96a3102e845b1955"⟩,
  ⟨"Lean4Ix/Model/SetModel/RecGraph.lean", "Ix/Theory/Model/SetModel/RecGraph.lean", "e6ca5ce2ab2681efbc6d3f549d596e6c7522860d1656db7bbe3528a874b8593c"⟩,
  ⟨"Lean4Ix/Model/SetModel/TaggedSum.lean", "Ix/Theory/Model/SetModel/TaggedSum.lean", "3f8f97c2b4d752a97bada45b5e7bc6dd3cb20a054f703a72c5e06af1646286dc"⟩,
  ⟨"Lean4Ix/Model/SetModel/TupleTower.lean", "Ix/Theory/Model/SetModel/TupleTower.lean", "0665b318c36faad149ccc4ef213fe81be47d36d7283c372ff70f26d80c0fd8a9"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Core.lean", "Ix/Theory/Model/SetTheory/Core.lean", "1ad5614af10cf9d8eb3e390ee279d1161a0704d3af1ba36d50012e8683aa06d5"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/Choice.lean", "Ix/Theory/Model/SetTheory/Derive/Choice.lean", "a451c14971f8be37fcc35534a45b6b8f569a87abb87920aa3efb02c352d4ffa5"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/Empty.lean", "Ix/Theory/Model/SetTheory/Derive/Empty.lean", "72408fc268cf2d0bd6a39d27873a69576a67f8b75a1539dc26fd6147c11bcbb2"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/Graphs.lean", "Ix/Theory/Model/SetTheory/Derive/Graphs.lean", "fcea63a8b11704d8f25b8dcf92fa05c494097a7195673859fe45288503deae00"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/Lfp.lean", "Ix/Theory/Model/SetTheory/Derive/Lfp.lean", "9a4f8d03a9b8dca4b112e89862540aa9cf4d53efe7580f7dc6d61690783101b2"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/LfpFam.lean", "Ix/Theory/Model/SetTheory/Derive/LfpFam.lean", "862fce7477e11f1a18c5e07336ba5331b5325e7f9efc6926a87eac836f6715e7"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/Omega.lean", "Ix/Theory/Model/SetTheory/Derive/Omega.lean", "aa76b574e7a6fe136cca8f9ba3d87cbd6a9577cec39cbdb91a193c265185d39d"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/Pair.lean", "Ix/Theory/Model/SetTheory/Derive/Pair.lean", "99ecac13fda8ad3f3e87e0a2d4bf2f5dd72e8e859dfb98d0da17ca0b14c77134"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/Pt.lean", "Ix/Theory/Model/SetTheory/Derive/Pt.lean", "3a2213814398c232d3a1f46365f22fc71d028f0e40f9c55fd1e135d07b304260"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/Quot.lean", "Ix/Theory/Model/SetTheory/Derive/Quot.lean", "de5148118f48b3042609d813fdfe930924330af6ca0a5cd1b831560a035a51bc"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/Sep.lean", "Ix/Theory/Model/SetTheory/Derive/Sep.lean", "24624815b917df8747786c56e2e47be740fc1e1be9f685f5fd053ac1001dbdc7"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/Sigma.lean", "Ix/Theory/Model/SetTheory/Derive/Sigma.lean", "ca545076118e71a0235b6f3f6ada2e6c4c96830ca606e31dade4f3a2e060e681"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/Univ.lean", "Ix/Theory/Model/SetTheory/Derive/Univ.lean", "3d59dcca1339d8e1e28bee7efe8792f44c0917fb1d1c749c61ed5a5976fcdeae"⟩,
  ⟨"Lean4Ix/Model/SetTheory/Derive/Universe.lean", "Ix/Theory/Model/SetTheory/Derive/Universe.lean", "f2c24862145d6624dcd9dacfcd68b845b6c68522d0fc81c1eac06839b455b61e"⟩,
  ⟨"Lean4Ix/Model/Signature.lean", "Ix/Theory/Model/Signature.lean", "5c6d3f9467466e3d677865a1536309bc05b96aafadf4312f7dc1679710929837"⟩,
  ⟨"Lean4Ix/Model/Support.lean", "Ix/Theory/Model/Support.lean", "020dc36c6376e3f7f725db8d4fd6a559f4e1ad303cdfb41c5e738f00c6ac05de"⟩,
  ⟨"Lean4Ix/Model/TelescopeSemantics.lean", "Ix/Theory/Model/TelescopeSemantics.lean", "a717a653a8d8d88d69a52acba0a8fe81b0c5635194c408bfdb503382ec9d0d66"⟩,
  ⟨"Lean4Ix/Model/Value.lean", "Ix/Theory/Model/Value.lean", "b2cf0796c8bcf6e138136c3f9f017d3df551b2a243d2e860fa943bb8d1411524"⟩,
  ⟨"Lean4Ix/Model/WellDenoted.lean", "Ix/Theory/Model/WellDenoted.lean", "8fc3eeb787fcc0182da41c880cf416c214d7930a433d0f35f77f393a2e9526e8"⟩,
  ⟨"Lean4Ix/Theory/Quot.lean", "Ix/Theory/Quot.lean", "321d4c7739af0b052da2a5c59ba875fe1ec35ec334a382d6107e02aeac238b49"⟩,
  ⟨"Lean4Ix/Theory/Ref.lean", "Ix/Theory/Ref.lean", "885181febe5ce0e1f9c6baac03e4604efb4acea27e0e8b61fde9900c14112f00"⟩,
  ⟨"Lean4Ix/Theory/Rename.lean", "Ix/Theory/Rename.lean", "3ce70afd260f3d9f68b830e11c5d1937f0d9ccf3b3f8a4e70ffc139a84fb8322"⟩,
  ⟨"Lean4Ix/Std/Basic.lean", "Ix/Theory/Std/Basic.lean", "450413877e701f1d906d13cf3074149127bb1637a9e5a4bd723d20769662fe89"⟩,
  ⟨"Lean4Ix/Theory/Store.lean", "Ix/Theory/Store.lean", "316c34c9f083a5d751f0fe9a478c50d6f3fc511a7aa8529042776a5b774fd763"⟩,
  ⟨"Lean4Ix/Theory/VLevel.lean", "Ix/Theory/VLevel.lean", "fc91db763262069edc1181dcb0ff12ac78d1efdd370a8acb2b297d3fcec963ee"⟩,
  ⟨"Lean4Ix/Certified.lean", "Ix/Theory.lean", "db42519eb53c5c24965b27879cb1ad81eca1010513fc67cf486f324c942fce98"⟩]

structure ConLecheFile where
  source : String
  target : String
  sourceSha256 : String
  lean4IxSha256 : String
  targetSha256 : String
  deriving Repr

def conLeche : Array ConLecheFile := #[
  ⟨"ConLeche/SetTheory/Core.lean", "Ix/Theory/Model/SetTheory/Core.lean", "52f54c7f8664a0d00ba04083d428ff81c2b89e7e68fbd6e24ffb349ef441f19a", "1ad5614af10cf9d8eb3e390ee279d1161a0704d3af1ba36d50012e8683aa06d5", "9e8d3537a66ded9e4d9142765c9ebda3eb4c3a8f780927cea6657e076933657b"⟩,
  ⟨"ConLeche/SetTheory/Derive/Empty.lean", "Ix/Theory/Model/SetTheory/Derive/Empty.lean", "259b3b365926256fbe8281a7066be601e419c3e492452b62086e0fd44e1a3f16", "72408fc268cf2d0bd6a39d27873a69576a67f8b75a1539dc26fd6147c11bcbb2", "b9a961b71e8a0576ceb00fbdc0288231d360576cd7afa72375606c793da15541"⟩,
  ⟨"ConLeche/SetTheory/Derive/Sep.lean", "Ix/Theory/Model/SetTheory/Derive/Sep.lean", "a6a452a34028ff2e194987de8fc5bc8f847ff8950f962b5d33c6c6ee5045a52e", "24624815b917df8747786c56e2e47be740fc1e1be9f685f5fd053ac1001dbdc7", "38536c268957fe0ad6e0127a1f07677bbfe4a17de82d0a2738b9042db55be2c7"⟩,
  ⟨"ConLeche/SetTheory/Derive/Pair.lean", "Ix/Theory/Model/SetTheory/Derive/Pair.lean", "851f954187fcc05ba2f43a6b81112df27c91e34f7de54352eaf461380fee1bd7", "99ecac13fda8ad3f3e87e0a2d4bf2f5dd72e8e859dfb98d0da17ca0b14c77134", "a72c5b13f5657a8299b060bd344068f56c3e2fadfc3619e64b9bc28e98085c91"⟩,
  ⟨"ConLeche/SetTheory/Derive/Universe.lean", "Ix/Theory/Model/SetTheory/Derive/Universe.lean", "57a24b4144088ac14dabdb9b6f88c49cf251a0659f8d4c073aad6682baeb099d", "f2c24862145d6624dcd9dacfcd68b845b6c68522d0fc81c1eac06839b455b61e", "c3eb55ee316ce142c16fa5c9a3e06ac45721767bad845ce8cd4c485ac7cce494"⟩,
  ⟨"ConLeche/SetTheory/Derive/Pt.lean", "Ix/Theory/Model/SetTheory/Derive/Pt.lean", "93f9ed86375f7af7a004f3ef2612ce8c9d8c6626ce73dbf6c3d6702f95f67eae", "3a2213814398c232d3a1f46365f22fc71d028f0e40f9c55fd1e135d07b304260", "520286bf987d29f56976d32ed2527ddf494ac80592fba05c1ffc4ad7627d9934"⟩,
  ⟨"ConLeche/SetTheory/Derive/Graphs.lean", "Ix/Theory/Model/SetTheory/Derive/Graphs.lean", "f61433765add5a733b38e95e38e217273f526a5e710b7109f24eb0f83f70faaf", "fcea63a8b11704d8f25b8dcf92fa05c494097a7195673859fe45288503deae00", "5bff626e2b77ea3d83302dd8959ef0e0816e9d9da59d52d573134f139e69316c"⟩,
  ⟨"ConLeche/SetTheory/Derive/Omega.lean", "Ix/Theory/Model/SetTheory/Derive/Omega.lean", "c0b20ecd0cc88a74ff6091e5a88506269b587bbc6f1919f72cc63083d2f7e55a", "aa76b574e7a6fe136cca8f9ba3d87cbd6a9577cec39cbdb91a193c265185d39d", "0cf178fada4077bfc8ba7dc257d8ceb77e7db8a452a9fba09eb736ad84f475be"⟩,
  ⟨"ConLeche/SetTheory/Derive/Univ.lean", "Ix/Theory/Model/SetTheory/Derive/Univ.lean", "e1084f7c82d9c0d144281491ceb05b015001d1215947d0d687e4dc07497ff911", "3d59dcca1339d8e1e28bee7efe8792f44c0917fb1d1c749c61ed5a5976fcdeae", "33e83e18da0a782904f42acc563c1c4259b60a1833bf2b22af41a28f1bd797e0"⟩,
  ⟨"ConLeche/SetModel/Ops.lean", "Ix/Theory/Model/SetModel/Ops.lean", "b19d965f92d1e281afd40a7ee4b2edd1a324b9bdf6d8f26425944dbafe987a11", "17a7e331d36a0fb0a5153bad2e115f3795cdb2db24f20e1a96a3102e845b1955", "6ce498a847103c32824e40f22e51db42163da98c09374f6a69e2a85a69f1e732"⟩,
  ⟨"ConLeche/SetTheory/Derive/Sigma.lean", "Ix/Theory/Model/SetTheory/Derive/Sigma.lean", "1a844ecb6709ae0ccefd43a4eb8d6da92b3753033e882ce74cfbd27c6890545f", "ca545076118e71a0235b6f3f6ada2e6c4c96830ca606e31dade4f3a2e060e681", "59cfd35485e1b90d199089aea2886fe7ed12bd9f02637d2d7cd5e21536ec6ef5"⟩,
  ⟨"ConLeche/SetTheory/Derive/Lfp.lean", "Ix/Theory/Model/SetTheory/Derive/Lfp.lean", "d6c1a824ee0b358f4007c2d297c4e29011c95914c2241d402f5bf27da333614f", "9a4f8d03a9b8dca4b112e89862540aa9cf4d53efe7580f7dc6d61690783101b2", "65e44e5bfe2fa0720b334cd31aff2c2eff511364feadfd5fd60c1ebf150b9a89"⟩,
  ⟨"ConLeche/SetTheory/Derive/LfpFam.lean", "Ix/Theory/Model/SetTheory/Derive/LfpFam.lean", "18fa2c12b37d9786b9a1961ed526e7d411869d93cfa241ebbdf2910d4418ac97", "862fce7477e11f1a18c5e07336ba5331b5325e7f9efc6926a87eac836f6715e7", "0657c96c6dffb7a49fec92c97769356595ec8a6f06b5f73594d4732d2fef8b8f"⟩,
  ⟨"ConLeche/SetTheory/Derive/Choice.lean", "Ix/Theory/Model/SetTheory/Derive/Choice.lean", "a8404566f4d831874e044dcfba6865b750fda3c9427e13c3d2b68d7ac45d5b48", "a451c14971f8be37fcc35534a45b6b8f569a87abb87920aa3efb02c352d4ffa5", "47e64bd1d52287230b993398ba5ee584d7b15e256b86f4fa0eaf1735c4510b93"⟩,
  ⟨"ConLeche/SetModel/TupleTower.lean", "Ix/Theory/Model/SetModel/TupleTower.lean", "143b965d29faae965c16288021ba1cf401c3f10e76550386ddb81d9ca1f5cbee", "0665b318c36faad149ccc4ef213fe81be47d36d7283c372ff70f26d80c0fd8a9", "1089b4ea6d9e7ff3ed9902a3c3d8f6697332b2aac23f94e503584b9cdf972750"⟩,
  ⟨"ConLeche/SetModel/TaggedSum.lean", "Ix/Theory/Model/SetModel/TaggedSum.lean", "eb64def578bf85bc2b197b83648749996ebcd243be573752f617a5f91f3332d8", "3f8f97c2b4d752a97bada45b5e7bc6dd3cb20a054f703a72c5e06af1646286dc", "53b565da9a2ce8848ca2442e52bfa0ff13b3f044017858fe69be42a9b2614aff"⟩,
  ⟨"ConLeche/SetModel/Iter.lean", "Ix/Theory/Model/SetModel/Iter.lean", "0688fa56fad4dcac618589cd9bafc2860c43b95978dc6dcf6c3e292cafc4b149", "6962b64d8ccd7b34df2dce7c7e0dff6bf4872b6d11de2ab608807b4787e230a0", "019ef9fa62f5d141ccc8c7e41259ff52dfba56412b3a57917ba60c28a2bfb378"⟩,
  ⟨"ConLeche/SetModel/RecGraph.lean", "Ix/Theory/Model/SetModel/RecGraph.lean", "66de7b97c640cec3987f89c31ae19c4daa27b6da53ba6943767e0078802f1faf", "e6ca5ce2ab2681efbc6d3f549d596e6c7522860d1656db7bbe3528a874b8593c", "da698d1a7346eaaa2f5b4734de06c955a05791ff52728d554082814328bd5caa"⟩,
  ⟨"ConLeche/SetModel/Container.lean", "Ix/Theory/Model/SetModel/Container.lean", "47b7bbab4764309ad1a11d7e6a3d2061c2968928367e2285e2a7e549bf7e6c0c", "bfc5c926aee16b6456151f48832bd8c41bbb9582f541ccc864eec753277c3a25", "08928de8de78f1fabc535b65e8511b068ad3c8b517055aa363674c2c90cebd4e"⟩,
  ⟨"ConLeche/SetTheory/Derive/Quot.lean", "Ix/Theory/Model/SetTheory/Derive/Quot.lean", "cadc387495c563d796ba4ca45cc0125cbe8ff5168d81bc47b364bd6776c3898b", "de5148118f48b3042609d813fdfe930924330af6ca0a5cd1b831560a035a51bc", "356b3b639fad5c6a9990bf106a38d49b32d0b0ae80537aba2719aaab8f9d9c84"⟩]

end Tests.Theory.ImportManifest
