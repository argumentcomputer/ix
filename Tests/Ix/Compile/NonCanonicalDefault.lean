/-
  The non-canonical record of the compiler: every byte difference between two
  presentations of a twin family (`Tests.Ix.Compile.Twins.allFamilies`), with
  its reviewed cause and its pinned evidence. Types and policy:
  `Tests.Ix.Compile.NonCanonical`.

  This file is data, written by the `twins` suite's re-record mode
  (`IX_TWINS_RECORD=<file> lake exe IxTests --ignored twins`) and then
  reviewed: a new difference arrives as `(.unreviewed "<suggested cause>")`
  and is given its cause by hand, from the dumped terms (`IX_TWINS_DUMP`);
  the gate fails until it is. Entries are ordered by family (in
  `allFamilies`' order), then by presentation pair, then by constant name.
  Change it only in a commit that states why the differences moved.
-/
import Tests.Ix.Compile.NonCanonical

namespace Tests.Ix.Compile.NonCanonicalDefault

open Tests.Ix.Compile.NonCanonical

/-- Entries 0 to 199. -/
def part0 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev "clique member" .pendingTransport (.root false true false)
    "6a95c0e321c602cf788b502681a2d273157a5a0653c26af77691ea83721dcb5d" "c8550d91c030b61f2772d502e35b62c37b006d9fa2b6e080bdfe80ad44f0ea5c" "value.λ.body" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev._f "structural functional" .pendingTransport (.root false true false)
    "32ac0d0b7ab46893597f46158112832e456669f74427196c7392b187d6da2f1c" "bb08c2c77fa597768efd23f70721372b6a62c794e689d33030e180afec296cc3" "value.λ.body.λ.body.@3.λ.body.λ.body" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev._sunfold "user constant" .inherited (.inherited [`od])
    "50bf80ce5ec29abe144366e7fc94cae42c60fc4c660b1c3875012c6ba7e2de09" "8d7903ac63b702ac9927c35f0b7834b0eba1ea564f8a860eaeb1759ca449dd2d" "",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev4 "user constant" .inherited (.inherited [`ev])
    "b945850c13f8e15f4cfbf8b69962546a45ef1408548f478b3f62a327d4b5005d" "61176222ba2bb2c44e2c01cdc7d74dfabe86842cf164708538bcf8a77f7ca088" "",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `od "clique member" .pendingTransport (.root false true false)
    "d0fbb9dc3009c45b10d6614048dd0c8f7fa62bed1b833946403b7730466d8bfc" "d9174bb759379e687c6af1f2f334f056d0307a6f6d25e7b314875540b35af96a" "value.λ.body" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `od._f "structural functional" .pendingTransport (.root false true false)
    "43281966e05730c23b3a58e91c7d538d88266e8eb7f3b7c4fe9ee28bb30f003e" "65e783795028f8e0de56fed91c7f0e72c756296832635fd169f985d3b9193187" "value.λ.body.λ.body.@3.λ.body.λ.body" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `od._sunfold "user constant" .inherited (.inherited [`ev])
    "9315038a844c113e85a7946065c46b6f2607eed124e9e88d752150f766ccb75e" "f86c3755548414c515942455c73d44cff29d8132308f4b27fb3eb7f53ba4dd2d" "",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev "clique member" .pendingTransport (.root false true false)
    "6a95c0e321c602cf788b502681a2d273157a5a0653c26af77691ea83721dcb5d" "c8550d91c030b61f2772d502e35b62c37b006d9fa2b6e080bdfe80ad44f0ea5c" "value.λ.body" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev._f "structural functional" .pendingTransport (.root false true false)
    "32ac0d0b7ab46893597f46158112832e456669f74427196c7392b187d6da2f1c" "bb08c2c77fa597768efd23f70721372b6a62c794e689d33030e180afec296cc3" "value.λ.body.λ.body.@3.λ.body.λ.body" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev._sunfold "user constant" .inherited (.inherited [`od])
    "50bf80ce5ec29abe144366e7fc94cae42c60fc4c660b1c3875012c6ba7e2de09" "8d7903ac63b702ac9927c35f0b7834b0eba1ea564f8a860eaeb1759ca449dd2d" "",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev4 "user constant" .inherited (.inherited [`ev])
    "b945850c13f8e15f4cfbf8b69962546a45ef1408548f478b3f62a327d4b5005d" "61176222ba2bb2c44e2c01cdc7d74dfabe86842cf164708538bcf8a77f7ca088" "",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `od "clique member" .pendingTransport (.root false true false)
    "d0fbb9dc3009c45b10d6614048dd0c8f7fa62bed1b833946403b7730466d8bfc" "d9174bb759379e687c6af1f2f334f056d0307a6f6d25e7b314875540b35af96a" "value.λ.body" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `od._f "structural functional" .pendingTransport (.root false true false)
    "43281966e05730c23b3a58e91c7d538d88266e8eb7f3b7c4fe9ee28bb30f003e" "65e783795028f8e0de56fed91c7f0e72c756296832635fd169f985d3b9193187" "value.λ.body.λ.body.@3.λ.body.λ.body" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `od._sunfold "user constant" .inherited (.inherited [`ev])
    "9315038a844c113e85a7946065c46b6f2607eed124e9e88d752150f766ccb75e" "f86c3755548414c515942455c73d44cff29d8132308f4b27fb3eb7f53ba4dd2d" "",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m0 "clique member" .pendingTransport (.root false true false)
    "03122a79297aa4094f1c6e51bcf9608a7aaca756e8375472ea2be1ae426c9e58" "7648a473b4a506ce6c12dea7e565108a75b886ddc2555c59185bb584f1e96af7" "value.λ.body.proj0" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m0._f "structural functional" .pendingTransport (.root false true false)
    "fedaafc7f9367356e16f3202220f6bd36dfebc7c0fd73d316b979b0de7f938c4" "2ca8a8b47168b5ab5934c3da7114471d5bfb37bfadd265f5cf61d457209a9a1b" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m0._sunfold "user constant" .inherited (.inherited [`m1])
    "a5ee14fd7150d178b2ee2cbfeb6ad4c7e02347e9f0d88e4a5a9f9275a77918c1" "ebb965050e6e77227ea8255964a2bf4e86f964499b143ed839afe5c153718ace" "",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m1 "clique member" .pendingTransport (.root false true false)
    "767f4225ec1f4ac399f138df7adbce32a7aa5d11c750b3e30d8011b07761c756" "ee47bbcec22de52e177783fd93a2bc91960b8b9352178c29ce5ddffd039e8a8c" "value.λ.body" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m1._f "structural functional" .pendingTransport (.root false true false)
    "b473b69e52a37dafd09fb533128843a07dbcc58d58777409ffab856ef6d29407" "d2e57d36c50cd5775f4c95be7157e608df904c29760f0632f8715f3d8d31477a" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m1._sunfold "user constant" .inherited (.inherited [`m2])
    "05f990b4deabf4cd06b15b91dd8ded3cb149e645ca0cd164109736ba511f3c09" "ccfd7b978c8732ff65d05b7278e15c23d6df69be023fe3f7dfaacb59c2a91fbe" "",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m2 "clique member" .pendingTransport (.root false true false)
    "14d5577906f40f9b12639e2d5bbde2f977f42adf269a72dd8eacd1d3a9abf002" "c4c36f2b9fe75fcd51f1a11b0610a30666fe1b4fec0d1349ef05d57bb009921d" "value.λ.body" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m2._f "structural functional" .pendingTransport (.root false true false)
    "9bcdd88d009edbd1f0d37bf051063ad4c1f0530790133cb6a8fadabc96584fcb" "6d92f0bfe7815b036aa2e8aa94555be69ceca2b9ea03b336e21155446a12035a" "value.λ.body.λ.body.@3.λ.body.λ.body.@4.proj0" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m2._sunfold "user constant" .inherited (.inherited [`m0])
    "a431a53139e1e5459d676fa6912c189fafecdbd8ec6bc0d6647cc342fb5a45ad" "225e87d17b4f82795b381cdf4914aff5a47a6643aadc6c29111029389cb29557" "",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m0 "clique member" .pendingTransport (.root false true false)
    "03122a79297aa4094f1c6e51bcf9608a7aaca756e8375472ea2be1ae426c9e58" "9202cdb86d48b9c93c1ba3c318455ef847898b72785c55a82a0ace73e31e156e" "value.λ.body" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m0._f "structural functional" .pendingTransport (.root false true false)
    "fedaafc7f9367356e16f3202220f6bd36dfebc7c0fd73d316b979b0de7f938c4" "d06c6d35cc3c901f92352c900abf036ce204f29228dec3299fc7791f4efb0a9a" "value.λ.body.λ.body.@3.λ.body.λ.body.@4.proj0" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m0._sunfold "user constant" .inherited (.inherited [`m1])
    "a5ee14fd7150d178b2ee2cbfeb6ad4c7e02347e9f0d88e4a5a9f9275a77918c1" "816cae03790bcf05055200ca9ab956e8562975ad79a9fecfb535a343f8475be2" "",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m1 "clique member" .pendingTransport (.root false true false)
    "767f4225ec1f4ac399f138df7adbce32a7aa5d11c750b3e30d8011b07761c756" "e13bd9b19b38e598d925fd1750c3a93551a4b9d685d6145284c00628a9dd4921" "value.λ.body.proj0" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m1._f "structural functional" .pendingTransport (.root false true false)
    "b473b69e52a37dafd09fb533128843a07dbcc58d58777409ffab856ef6d29407" "9b5514479236441cb7b31271e82f528edd1374ef82f3bb7966587f98c1faa76d" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m1._sunfold "user constant" .inherited (.inherited [`m2])
    "05f990b4deabf4cd06b15b91dd8ded3cb149e645ca0cd164109736ba511f3c09" "ad27c742e38e5d14f0f32ac3f749bc123c90e0c69d7f8e3ef1e6051ad062d212" "",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m2 "clique member" .pendingTransport (.root false true false)
    "14d5577906f40f9b12639e2d5bbde2f977f42adf269a72dd8eacd1d3a9abf002" "b0b46bf9703cebbe8cdf02c8a1830218e2640d02e6e7a65ace6924b1e5cf71f8" "value.λ.body" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m2._f "structural functional" .pendingTransport (.root false true false)
    "9bcdd88d009edbd1f0d37bf051063ad4c1f0530790133cb6a8fadabc96584fcb" "95694ad293b38d37c4a3ce5685b2515611e91594ee8be66d080c374c078df146" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m2._sunfold "user constant" .inherited (.inherited [`m0])
    "a431a53139e1e5459d676fa6912c189fafecdbd8ec6bc0d6647cc342fb5a45ad" "21d4163d0aa268861745cfdc3b865fe1058e47174afe808a127d337d028aaba3" "",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo "clique member" .pendingTransport (.root false true false)
    "afebd23516717e00faaaabc32e9a7e9e51f92c801e988ce60e5b59a9494a0667" "1d57c9d6a15dc716724c6bdd34f7b5d30a0210f3878a35c0a6d40f22eb4edd60" "value.λ.body" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo._f "structural functional" .pendingTransport (.root false true false)
    "52a987639794c1db5e7385fbb563c6a75f665679ea982622300e77922ad501d5" "ae363b9cda9638fa9686d4b381dc9a676f2d52a4ffff51c061021c19a890fb99" "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@5" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo._sunfold "user constant" .inherited (.inherited [`cTr, `cFo])
    "84d6687318a0390626aae0b6332afcffc528cb72c628f23a80a65adf63779da0" "c67aaa84685619f700339b0eb7b8440355902662f7211f8567addecc66fac353" "",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr "clique member" .pendingTransport (.root false true true)
    "f99fd1eb14be1a67d25284e9055e3b6d2cfcb8084cca9f58f34a3e9aebb8e2ce" "b5c9af1ed68ea0ba15f553099630d3ed33fdfa47d175eeb1100a3d0edea90c91" "value.λ.body.@4.λ.body.λ.body.@2.fn" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr._f "structural functional" .pendingTransport (.root false true false)
    "14aaa1ec78220ab13ef4eb9134c9260fb940dbabd9fb801f7e39ccd21b6d6be9" "f315630469a6313017fabc85531d5a356ab7e5f810c7b3592d4e66b390a31398" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr._sunfold "user constant" .inherited (.inherited [`lFo, `cFo])
    "13329e3da51b3b9c43173b812e7d67c9f5df9597d01c65d0b2e09e0db4d9ea91" "d6c5817185198cea2e0ed69af806ae9da7afe6a90de53fe02e56057e1d2d42af" "",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo "clique member" .pendingTransport (.root false true false)
    "6a522057e328e93aa4b88592b9a4ee2cbadd188330db0f88cccb650a15f70383" "35a0dbbee311d292a99d1eecf8b45f46599e724c3d079112025c46a82c50a37f" "value.λ.body" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo._f "structural functional" .pendingTransport (.root false true false)
    "d90b3fb84212449b28689dda72a5b33a2441536c0026aef7d0d52ea4a43f3720" "f5485ab3ad53ac26004d88c0f094a13a6e9b46c004027eb6199621f909fee63c" "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@4.@4" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo._sunfold "user constant" .inherited (.inherited [`lFo, `cTr])
    "1513bbdcb5cdd2a55a51482b4af3302cfd1aade1297189a3f3716e8ded3d5922" "12863ec37d5bde0e3dfe7720c820ac0b7e17ff50b969cf927b77e3a3ec9daa14" "",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa "clique member" .pendingTransport (.root false true true)
    "4759d7fe47f0d21c2b99cf95bfc7d5cb7b9ca281166e4f3f92d37c8c308a06b2" "641529fc41f1f6b72045cde3fb9c20357b95df6d1e659d54b53617f145b99f36" "value.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual "clique encoding" .pendingTransport (.root false true true)
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447" "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "`PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual._proof_1 "encoding obligation" .pendingTransport (.root true true true)
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6" "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68" "type.∀.body.∀.body.@4.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual._proof_2 "encoding obligation" .pendingTransport (.root true true true)
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307" "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408" "type.∀.body.∀.body.@4.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual.eq_def "encoding equation" .orderStmt (.root true true false)
    "2b874d7adcde67692447fa1de16691fb35bd9efae63943a64358f346f5832fee" "cc2a2148e21ce32e46eff6a75dfd00a1b67f9a0dadbf91639b57c0d4948cf459" "type.∀.body.@2.@4.λ.body.@1" "statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa.eq_def "equation lemma" .lazy (.root false true true)
    "3f7017a98ae057bd3f51728c1078b8151be63f88e3e40dead4719de56ac6e964" "311ecc3184b86b232a250a4ca678b70b6e40b57a267e1cdc54ea5c32a98fb21f" "value.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wb "clique member" .pendingTransport (.root false true true)
    "c485a2c9367144d0f6cef0490348f437998387316f56f259b2524484428b862e" "fae38748a4ee68cdd161650cc02b0ab89db1a0b4bc97c2f9f6a4f25fbbed84de" "value.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wb.eq_def "equation lemma" .lazy (.root false true true)
    "e59e349deb22c46e57c0e71786433574411b8dd1522d2e8e69249cc61321ac8c" "327144d5b893ee7f5d24097c8fa728d6c7eb81225d9bf0c8fd1f3f3503bbf103" "value.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa "clique member" .pendingTransport (.root false true true)
    "4759d7fe47f0d21c2b99cf95bfc7d5cb7b9ca281166e4f3f92d37c8c308a06b2" "641529fc41f1f6b72045cde3fb9c20357b95df6d1e659d54b53617f145b99f36" "value.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual "clique encoding" .pendingTransport (.root false true true)
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447" "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "`PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual._proof_1 "encoding obligation" .pendingTransport (.root true true true)
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6" "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68" "type.∀.body.∀.body.@4.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual._proof_2 "encoding obligation" .pendingTransport (.root true true true)
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307" "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408" "type.∀.body.∀.body.@4.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual.eq_def "encoding equation" .orderStmt (.root true true false)
    "2b874d7adcde67692447fa1de16691fb35bd9efae63943a64358f346f5832fee" "cc2a2148e21ce32e46eff6a75dfd00a1b67f9a0dadbf91639b57c0d4948cf459" "type.∀.body.@2.@4.λ.body.@1" "statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa.eq_def "equation lemma" .lazy (.root false true true)
    "3f7017a98ae057bd3f51728c1078b8151be63f88e3e40dead4719de56ac6e964" "311ecc3184b86b232a250a4ca678b70b6e40b57a267e1cdc54ea5c32a98fb21f" "value.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wb "clique member" .pendingTransport (.root false true true)
    "c485a2c9367144d0f6cef0490348f437998387316f56f259b2524484428b862e" "fae38748a4ee68cdd161650cc02b0ab89db1a0b4bc97c2f9f6a4f25fbbed84de" "value.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wb.eq_def "equation lemma" .lazy (.root false true true)
    "e59e349deb22c46e57c0e71786433574411b8dd1522d2e8e69249cc61321ac8c" "327144d5b893ee7f5d24097c8fa728d6c7eb81225d9bf0c8fd1f3f3503bbf103" "value.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga "clique member" .pendingTransport (.root false true true)
    "f565ce3d9ce8ac675ba4e535eddbb0fa48b4e91e7b507e1385056a070b2f971e" "8a34e4cd993fb7d9b189ce7b0b75f2670b21b46a029b433f76a82ed106a27bb8" "value.λ.body.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual "clique encoding" .pendingTransport (.root false true true)
    "0e27ba25c79dc7793a8ba162691f785ee152ec1f68d31f4f597d4b09db0a5ef5" "9cc2b3854a5c3cc7cdb261fadd317f19800a7d2a2f1eb5c1bed9d698f9f2cc70" "value.@4.λ.body.λ.body.@4.λ.body.λ.body.@4.λ.body.λ.body.λ.body.@3.λ.body" "`PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual._proof_2 "encoding obligation" .pendingTransport (.root true true true)
    "6d43105b925565d18ef4797b4cd28ef0ecf7d80f7d1c95ca138f121a5f4cf40d" "bceac634d415df450def06d4a22b21a761b5ed1656541840965438fa4762b8a9" "type.∀.body.∀.body.∀.body.@0.@2.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual._proof_3 "encoding obligation" .pendingTransport (.root true true true)
    "1a6d56af84d790f0f5f694bd7eb082c0a1beafe6aacd11323972d60dd5fb64b8" "b3b9365f8cbdd96920326a32b76e706633c74d36ce659bd9ac7e8371a71c5b3e" "type.∀.body.∀.body.∀.body.@0.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual._proof_4 "encoding obligation" .pendingTransport (.root true true true)
    "ce71876d8dc1a733cf4a015111ba6be5780a8e830183d26f90e2182f961f21cc" "2bd27fb76859701c03ad9a256da78686e99bf9bdf55c62591ec604b81592ac37" "type.∀.body.∀.body.∀.body.@0.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual.eq_def "encoding equation" .orderStmt (.root true true false)
    "205423647ec0cfd85f0923b6927f8ea21ec2aeb2caecd718dd3ee0ef039b3991" "d0f98e93be3e30d814cb45b26997053706c312d701e191eedcdfa0a5b6cf2ff5" "type.∀.body.@2.@4.λ.body.@4.λ.body.λ.body.@3.λ.body" "statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga.eq_def "equation lemma" .lazy (.root false true true)
    "f8c18f7082d58145f2a39a644c001fb69d3a99ad05e83f00add2273c7fe17e59" "f710ebdcf62e60f8399a516774451ac201a75910363716906bc87bfd428e2bd7" "value.λ.body.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gb "clique member" .pendingTransport (.root false true true)
    "f7787b8d0cd56368b87bb53196fe36fc0b9c2839a10ff3b0fd5e8092369be486" "c5e76ac756f4686274196cd37fcc1b8cceeb217a4adf50296aabb36d04303c48" "value.λ.body.λ.body.@0.@2.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gb.eq_def "equation lemma" .lazy (.root false true true)
    "80a975c58a9c3458b4cc9fd6107a93d37c686fab90119ba3332ae55995c99cc6" "eda78c77eafd830877efe20d1b014da7d7f284b706a579c2de8f5b6c15126dc7" "value.λ.body.λ.body.@1.@0.@2.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gc "clique member" .pendingTransport (.root false true true)
    "b6c20f5e441e355d2c4c0af88c436faa414c952532edf32cec404f23e1442de1" "2e11e2833c410ba92b2b10f39e2a9aeac6101a2c43c10d352ab60925fea5fe9e" "value.λ.body.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gc.eq_def "equation lemma" .lazy (.root false true true)
    "3bba15edc4fcd75ef0851890fa2fb1fdab78f716f53725e64a2feb572e97cb77" "9246d7d2b9b39b3a602201240eb94a7f71f84d46ff77138221fd398073a3405b" "value.λ.body.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga "clique member" .pendingTransport (.root false true true)
    "f565ce3d9ce8ac675ba4e535eddbb0fa48b4e91e7b507e1385056a070b2f971e" "2c41be0e21fc26c4193b3acf79ff54ebe9db6c51435930697eb2dc2662ede79f" "value.λ.body.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual "clique encoding" .pendingTransport (.root false true true)
    "0e27ba25c79dc7793a8ba162691f785ee152ec1f68d31f4f597d4b09db0a5ef5" "43efb240d50538091e93d4cdf2ffa2140037e6df0cda820c120ab0c46dc3b447" "value.@4.λ.body.λ.body.@4.λ.body.λ.body.@4.λ.body.λ.body.λ.body.@1.@1" "`PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual._proof_2 "encoding obligation" .pendingTransport (.root true true true)
    "6d43105b925565d18ef4797b4cd28ef0ecf7d80f7d1c95ca138f121a5f4cf40d" "776dbac01f0a7c74dd91c8d188c9e34fe6a7cf75c293f611385a8223789eaca2" "type.∀.body.∀.body.∀.body.@0.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual._proof_3 "encoding obligation" .pendingTransport (.root true true true)
    "1a6d56af84d790f0f5f694bd7eb082c0a1beafe6aacd11323972d60dd5fb64b8" "fe16646b2b3f46f4d57a175b5b47d4d644c49dc4d12145774993cb86d21f145d" "type.∀.body.∀.body.∀.body.@0.@2.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual._proof_4 "encoding obligation" .pendingTransport (.root true true true)
    "ce71876d8dc1a733cf4a015111ba6be5780a8e830183d26f90e2182f961f21cc" "757d86daa0a585e4986d23619f3b86f704e970c806116b70cd7932d948b6940b" "type.∀.body.∀.body.∀.body.@0.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual.eq_def "encoding equation" .orderStmt (.root true true false)
    "205423647ec0cfd85f0923b6927f8ea21ec2aeb2caecd718dd3ee0ef039b3991" "554d9601db74da49f2f7e6e581f9e461b0cfacf16cb79a7fbb58cf49060aebc3" "type.∀.body.@2.@4.λ.body.@4.λ.body.λ.body.@1.@1" "statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga.eq_def "equation lemma" .lazy (.root false true true)
    "f8c18f7082d58145f2a39a644c001fb69d3a99ad05e83f00add2273c7fe17e59" "4801b23753ad6cf3a56f04dee9d12fe507df470f09436510af9c550f57aa10a8" "value.λ.body.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gb "clique member" .pendingTransport (.root false true true)
    "f7787b8d0cd56368b87bb53196fe36fc0b9c2839a10ff3b0fd5e8092369be486" "05ba5aaf6cc1a11fe2b70b8a352d383eac701c8c8664fd79f55dcc56fed95b28" "value.λ.body.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gb.eq_def "equation lemma" .lazy (.root false true true)
    "80a975c58a9c3458b4cc9fd6107a93d37c686fab90119ba3332ae55995c99cc6" "b33c695be2db8daff75040287be55e02c3af085aad7a3c578c0a91af7ee46f79" "value.λ.body.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gc "clique member" .pendingTransport (.root false true true)
    "b6c20f5e441e355d2c4c0af88c436faa414c952532edf32cec404f23e1442de1" "1645a1d44ec15056218e26836cee53bb5734275d598fede262d1bfa0a0aa6124" "value.λ.body.λ.body.@0.@2.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gc.eq_def "equation lemma" .lazy (.root false true true)
    "3bba15edc4fcd75ef0851890fa2fb1fdab78f716f53725e64a2feb572e97cb77" "2019c99986595cfc25a562b82c729700a516e8df62dcb1cf92bee249feddf9cc" "value.λ.body.λ.body.@1.@0.@2.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga "clique member" .guessLex (.root false true true)
    "242e5c784fb1c56336cfb8bd9be95aae375a3e029bb6787da7e3802667cd64df" "a54529c0d974aef16d4b2a61a038a49491a2f2640bb4451ae4d13b0d18d273d5" "value.λ.body.λ.body.@0.fn" "`PSum` injection, over the GUESSLEX-differing `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga._mutual "clique encoding" .guessLex (.root false true true)
    "9505e594f820630cddb3e20b6708419abb613c308ad91953d41372120ec19313" "f1b52679b1aa1207b01b494315252882f78493caaab7a40793cd0837c62a17aa" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@4.λ.body.λ.body.λ.body.@3.λ.body.@1" "GuessLex measure: (ga.x, gb.y) under P0, (gb.x, ga.y) under P1 (non-uniform combinations enumerated in function order, first that works); the canonical functional differs",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga._mutual.eq_def "encoding equation" .orderStmt (.root true true false)
    "04e8346072b66c68dde386ff5a5a1ce9144a185d226fc9099d8865ad22cc3c9f" "1dffc78b59df95be2ef948f52dd2c2138e3c7c9fe8f05aa4c808f72a2d0c359f" "type.∀.body.@2.@4.λ.body.@4.λ.body.λ.body.@3.λ.body.@1" "statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga.eq_def "equation lemma" .lazy (.root false true true)
    "725de1dc9e6a16cbe621aefb2d4196d823e049f91cb1bb290f8d48051de49a7e" "338a400d2f57837f41c97d82d4cab4732b0b4490a5304a9d3143bd5be77cf6e5" "value.λ.body.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `gb "clique member" .guessLex (.root false true true)
    "978a66e918dbcc26dee988dbbd25fd28f5f613c3482a5c14e1e32951b0bbccd9" "b0865eadcc8365b3b3d27419f53a0779d72ca275dd90978551c382b52fcf3f49" "value.λ.body.λ.body.@0.fn" "`PSum` injection, over the GUESSLEX-differing `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `gb.eq_def "equation lemma" .lazy (.root false true true)
    "8c620db260db49063de075bc9839f00b2d732c0468bb8b87f896facb9385a128" "40f2789bf7efed9f6c15d43fedf77c2d9d497674c59a312cecac7bd3f8082943" "value.λ.body.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta "clique member" .pendingTransport (.root false true true)
    "4759d7fe47f0d21c2b99cf95bfc7d5cb7b9ca281166e4f3f92d37c8c308a06b2" "641529fc41f1f6b72045cde3fb9c20357b95df6d1e659d54b53617f145b99f36" "value.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual "clique encoding" .pendingTransport (.root false true true)
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447" "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "`PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual._proof_1 "encoding obligation" .pendingTransport (.root true true true)
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6" "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68" "type.∀.body.∀.body.@4.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual._proof_2 "encoding obligation" .pendingTransport (.root true true true)
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307" "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408" "type.∀.body.∀.body.@4.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual.eq_def "encoding equation" .orderStmt (.root true true false)
    "2b874d7adcde67692447fa1de16691fb35bd9efae63943a64358f346f5832fee" "cc2a2148e21ce32e46eff6a75dfd00a1b67f9a0dadbf91639b57c0d4948cf459" "type.∀.body.@2.@4.λ.body.@1" "statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta.eq_def "equation lemma" .lazy (.root false true true)
    "3f7017a98ae057bd3f51728c1078b8151be63f88e3e40dead4719de56ac6e964" "311ecc3184b86b232a250a4ca678b70b6e40b57a267e1cdc54ea5c32a98fb21f" "value.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `tb "clique member" .pendingTransport (.root false true true)
    "c485a2c9367144d0f6cef0490348f437998387316f56f259b2524484428b862e" "fae38748a4ee68cdd161650cc02b0ab89db1a0b4bc97c2f9f6a4f25fbbed84de" "value.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `tb.eq_def "equation lemma" .lazy (.root false true true)
    "e59e349deb22c46e57c0e71786433574411b8dd1522d2e8e69249cc61321ac8c" "327144d5b893ee7f5d24097c8fa728d6c7eb81225d9bf0c8fd1f3f3503bbf103" "value.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba "clique member" .pendingTransport (.root false true true)
    "4759d7fe47f0d21c2b99cf95bfc7d5cb7b9ca281166e4f3f92d37c8c308a06b2" "641529fc41f1f6b72045cde3fb9c20357b95df6d1e659d54b53617f145b99f36" "value.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual "clique encoding" .pendingTransport (.root false true true)
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447" "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "`PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual._proof_1 "encoding obligation" .pendingTransport (.root true true true)
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6" "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68" "type.∀.body.∀.body.@4.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual._proof_2 "encoding obligation" .pendingTransport (.root true true true)
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307" "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408" "type.∀.body.∀.body.@4.fn" "decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual.eq_def "encoding equation" .orderStmt (.root true true false)
    "2b874d7adcde67692447fa1de16691fb35bd9efae63943a64358f346f5832fee" "cc2a2148e21ce32e46eff6a75dfd00a1b67f9a0dadbf91639b57c0d4948cf459" "type.∀.body.@2.@4.λ.body.@1" "statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba.eq_def "equation lemma" .lazy (.root false true true)
    "3f7017a98ae057bd3f51728c1078b8151be63f88e3e40dead4719de56ac6e964" "311ecc3184b86b232a250a4ca678b70b6e40b57a267e1cdc54ea5c32a98fb21f" "value.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `bb "clique member" .pendingTransport (.root false true true)
    "c485a2c9367144d0f6cef0490348f437998387316f56f259b2524484428b862e" "fae38748a4ee68cdd161650cc02b0ab89db1a0b4bc97c2f9f6a4f25fbbed84de" "value.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `bb.eq_def "equation lemma" .lazy (.root false true true)
    "e59e349deb22c46e57c0e71786433574411b8dd1522d2e8e69249cc61321ac8c" "327144d5b893ee7f5d24097c8fa728d6c7eb81225d9bf0c8fd1f3f3503bbf103" "value.λ.body.@1.@0.fn" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pa "clique member" .pendingTransport (.root false true false)
    "dade135fc1eaa15b37cbf0b182a8b0c752f54bf12eb02840b88f106f4e7fe67a" "9911ee6af0f00d2ed01c598fd0263f8aa08491b8d21f22986127f92488458dd3" "value.proj0" "`PProdN.proj` at the factor position",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pa.mutual "clique encoding" .pendingTransport (.root false true true)
    "aae0295814cc6f61f77a936266e0a0bdedf33c89f9e37ea54b90ed658af55105" "35e34d7f00e53729f8c161ece500c8b896c38e2fbfadd9a2269617327da253c0" "value.@2.λ.body.@2.λ.body.@1" "`PProd` factor order of the packed functional and instance",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pa.mutual._proof_1 "encoding obligation" .pendingTransport (.root true true false)
    "0ddea573a18b7aac2d20a006f8cda1fcef605fc2f31cd9e8782c5e4d1816b923" "17dad592622f8c1da82e3fab3f43a962e034ddd7f804ff221d35fbd6846c8469" "type.@4.λ.body.@2.λ.body.@1" "monotonicity proof: `PProd.monotone_mk` tree in factor order; `monotone_fst`/`monotone_snd` projection paths per call (A)+(G); statement over the packed type (S)",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pb "clique member" .pendingTransport (.root false true false)
    "fc4304ee5143837aac1bbe637884c0babff4d7acc1eaf5bd92d3f92185d32bda" "e9177ca30906fde9a52fd1ea6038f4fcde04f2ad313c17bcf0a38e9b89d10567" "value" "`PProdN.proj` at the factor position",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pc "clique member" .pendingTransport (.root false true false)
    "0c0ebc4460fee8cd928f746e7f2582faa54239b60a439fdff41096a5285ed27a" "968c560933816d33fa072b641daa169659e5a3e15f37fea0459f3427a827ca80" "value" "`PProdN.proj` at the factor position",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pa "clique member" .pendingTransport (.root false true false)
    "dade135fc1eaa15b37cbf0b182a8b0c752f54bf12eb02840b88f106f4e7fe67a" "e6b782605202d40bd549614ec9dde18bc3924ace440f0ae00ba59fa6854f68b8" "value" "`PProdN.proj` at the factor position",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pa.mutual "clique encoding" .pendingTransport (.root false true true)
    "aae0295814cc6f61f77a936266e0a0bdedf33c89f9e37ea54b90ed658af55105" "026e16e83c5526336e4c936926791e6e0d9159f175139d64eb2654deffe595ae" "value.@2.λ.body.@2.λ.body.@3.@1.@1" "`PProd` factor order of the packed functional and instance",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pa.mutual._proof_1 "encoding obligation" .pendingTransport (.root true true false)
    "0ddea573a18b7aac2d20a006f8cda1fcef605fc2f31cd9e8782c5e4d1816b923" "8043e9fdebd60d01ee161bee0427b12e1ed4b505ac63c2534a24c2ea6c2bea04" "type.@4.λ.body.@2.λ.body.@3.@1.@1" "monotonicity proof: `PProd.monotone_mk` tree in factor order; `monotone_fst`/`monotone_snd` projection paths per call (A)+(G); statement over the packed type (S)",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pb "clique member" .pendingTransport (.root false true false)
    "fc4304ee5143837aac1bbe637884c0babff4d7acc1eaf5bd92d3f92185d32bda" "4fbec683f761044ed4c47df9efa8b70e609f9da8ae9ea45976bc75181dfa8735" "value.proj0" "`PProdN.proj` at the factor position",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pc "clique member" .pendingTransport (.root false true false)
    "0c0ebc4460fee8cd928f746e7f2582faa54239b60a439fdff41096a5285ed27a" "78ddb333047b376621b3023a40c92677d0a73f7fb9525e3cf8b5ae94cfba9955" "value" "`PProdN.proj` at the factor position",
  e `Tests.Ix.Compile.Twins.Cliques.TS "P0" "P1" `evT "clique member" .pendingTransport (.root false true true)
    "bb7f9eb5c1eee2076d608222ae2e59b3bec450945e57240aec1971bc7f4b8402" "e968d779096bf66ed8060322ad076feb752b84c1de9c494355ebbe36d7e3e4b8" "value.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.TS "P0" "P1" `evT._mutual "clique encoding" .pendingTransport (.root true true true)
    "78a3577514987bc92d9a2729706e613221b268472784a8d1d7e53287ba4814fa" "38b13258377b659e92f44c3b92385ec4029f9fa33836e6f6fb498d9441e0818e" "type.∀.body.@4.λ.body.@1.@0.fn" "theorem clique by well-founded recursion (not structural: odT (n+1) calls evT (n+1)); GuessLex `(n, funIdx)` literals travel with each function; `PSum` order; inline decreasing proofs equal up to the packing",
  e `Tests.Ix.Compile.Twins.Cliques.TS "P0" "P1" `odT "clique member" .pendingTransport (.root false true true)
    "6795d98ab1593083c24882a9ef2d0fd34e1ca351fa107ea677c78781d5c25666" "79c0ad141956a442d22eba6ea4f4f0045595168ae83fd0cad44774a3599088b9" "value.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.TW "P0" "P1" `wa "clique member" .pendingTransport (.root false true true)
    "5ddf195d3f8e7cbe8820d6db12a14b2472f47e6aa4952f1975ca3f02aa0ec075" "44e227a443b047e91bbd536284c16c6bc79fa1f3c2ebb8101a96bcae0b0a8025" "value.λ.body.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.TW "P0" "P1" `wa._mutual "clique encoding" .pendingTransport (.root true true true)
    "f4215cec1c7e681c3804e51a25357202c2d500c4acc04ffa3f8ddc9c58a9c012" "09a6c8908407175fda86ab1e581780f564eb41fc1fd79ae3ea11581474cfe582" "type.∀.dom.@0.@1.λ.body.@2.@1" "theorem clique by well-founded recursion; `PSum` order of the `PSigma` domains (hypothesis carried)",
  e `Tests.Ix.Compile.Twins.Cliques.TW "P0" "P1" `wb "clique member" .pendingTransport (.root false true true)
    "5883e50b907830935e717e5aa88faf8733fa45e2442687db5aa916e51bad0cb7" "993b8c17a4ddf9cec241eef2cfb7fa4913d8bba3683caac3388dc9b7b5a88f50" "value.λ.body.λ.body.@0.fn" "`PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `evM "clique member" .pendingTransport (.root false true false)
    "04be654a74f5e7b2d215ed31d6df2c3a94135831839e8d5db0cb3ebfd22259bd" "e600d0c3c44de06ef8144fdad20f5b81fb1633e60fe6ea29f1d73947ad82315c" "value.λ.body.λ.body.let.ty.∀.body.∀.dom.fn" "`let funType_i` bound in clique order (`withFunTypes`); zeta-equivalent",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `evM.match_2 "transformed matcher" .pendingTransport (.root true true false)
    "c6811a1fabf7498b43ed04a9215d9bade1a8635f1bf3eff5477ee8e7e905a17e" "bb86122e6c18f5806837f497e2236d93bda8a9d2742582dbac273dbdba1e2fe9" "type.∀.dom.∀.body.∀.dom.fn" "IndPred `below` matcher: `funType_i` binders in clique order; regenerated by transport (R)+(A)",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `odM "clique member" .pendingTransport (.root false true false)
    "12b8e7bd40d3b653755c49eb607e9d2219b0151389ea4cb6aeded800b844d9ff" "176f8daeff65c30c7c52f6ff6bc97e5ec990f66a128011aa08dcb1f11cc6bbef" "value.λ.body.λ.body.let.ty.∀.body.∀.dom.fn" "`let funType_i` bound in clique order (`withFunTypes`); zeta-equivalent",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `odM.match_2 "transformed matcher" .pendingTransport (.root true true false)
    "ad2109b70d8bcfdd495136d20ec3129341fc3e8f7cb40ec3c12f0d9c994101f5" "36eb9a22918e8eb22c991c6c46f9b457b79b2b605a04da5d497cac78941b5b4b" "type.∀.dom.∀.body.∀.dom.fn" "IndPred `below` matcher: `funType_i` binders in clique order; regenerated by transport (R)+(A)",
  e `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sa "clique member" .pendingTransport (.root false true false)
    "e9d460ba7b4cd906fd0f660108b189fbfe154953883e20319d7dd6452d4ddaab" "3c2d53a05c70b77a5269ac8412b0095ed0dcca53d9ccebb753fbc6368e74d723" "value.λ.body" "projection into the packed `brecOn` result at the clique position",
  e `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sa._f "structural functional" .pendingTransport (.root true true false)
    "fd47ab03aaa9797d850828664dca8a12002076c9a72c4ac8bac3309ffdaab7fd" "dddcbfd408991573a7c2afd6458b448e746deaada99201f81ea52af60cdaf431" "type.∀.body.∀.dom.@0.λ.body.@0.@1.@0.@4" "type of `_f` mentions the packed `below` motive (theorem statements in clique order); path into it",
  e `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sb "clique member" .pendingTransport (.root false true false)
    "22717b47155044f9187d41730a2f8c2a576647cb2d98eb1ad6d8d7cb08ece66c" "c4151352703a615979f59fe2a8d00d70f6afc7d99b28b8845845f23e1da01764" "value.λ.body" "projection into the packed `brecOn` result at the clique position",
  e `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sb._f "structural functional" .pendingTransport (.root true true false)
    "2d3cb49f17edbe9962dffe39839decfcef1b848e952b2b0f0eb5a6bcfb0a46e9" "bb0d910606ace0c4f4f2ff9c4fe40706a578a62ae074e0184d55ed0b3758cf43" "type.∀.body.∀.dom.@0.λ.body.@0.@1.@0.@4" "type of `_f` mentions the packed `below` motive (theorem statements in clique order); path into it",
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fa "clique member" .pendingTransport (.root false true false)
    "527d25952a6ba44c02993e69db17900753c35a642dfbca24394a9d6397c12f23" "0a8782a03088cd47ee3cdfc257b03f5e386e8548f945f5427065b0540c437611" "value.λ.body.λ.body.λ.body" "fixed-parameter telescope in the first function order (O13b), plus the projection into the packed `brecOn` result",
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fa._f "structural functional" .pendingTransport (.root true true false)
    "f1623552388b51d41e965671cfc420cc8024ebffd72bf81675062fee794f180b" "df188f2d008db128174d3049a067aea93c06d7dbcf69ef358032120e773aa144" "type.∀.dom" "fixed-parameter telescope in the first function order (O13b), plus the path into the packed `below` motive",
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fa._sunfold "user constant" .inherited (.inherited [`fb])
    "524593d208bc2e19ec9b7718cde53e602dda7ef836f446de9199a2a7906ec7e1" "139fdb2c10ccbe60a2a493900668e67f0788c53f9a57960a20982e1d348b0587" "",
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fb "clique member" .pendingTransport (.root false true false)
    "78f12253d960f64c81c3e72c93ce696a8bb79a6c0b2deb13853e1a161faefabb" "b675671ee9607fb8c67697885976f9b1b0ed1ca10352c2163f153c204ea22122" "value.λ.body.λ.body.λ.body" "fixed-parameter telescope in the first function order (O13b), plus the projection into the packed `brecOn` result",
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fb._f "structural functional" .pendingTransport (.root true true false)
    "4755dc9f98893af601cf942a679f3239403d4ae45ab03eafd0be03414a48816b" "9c564d42d27f9d5a1b58a4befaa82a883e5c438577317f2931ecf4e43078305c" "type.∀.dom" "fixed-parameter telescope in the first function order (O13b), plus the path into the packed `below` motive",
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fb._sunfold "user constant" .inherited (.inherited [`fa])
    "5964fafa5cc2ed01ffbd65046721bbd87504094c6adf3baf1c9622221c98f6fe" "7c5ce3d71009032d8d428b9402e0fdf231689095fd78f0e053dc33bef2a285a2" "",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha "clique member" .pendingTransport (.root false true false)
    "96439b5e84d57a74ff0dcacd08017d631b47efee00bacc29669b08843b53440e" "97dfbfe76350192cf901c5d92e8c6ea1cb22b69d49e90a4cdd7aae657bab95a8" "value.λ.body.λ.body.λ.body.@0" "fixed-parameter telescope in the first function order (O13b), plus the `PSum` injection",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual "clique encoding" .pendingTransport (.root true true false)
    "e5b17bdb3751da6746ae4ef84d225c3586b1d87a412334584fed79217c9c33ba" "5a1b5db06609153eba1fec84761e1e7f3a2c91adc473ac9b6322cea011795fd4" "type.∀.dom" "fixed-parameter telescope in the first function order (O13b), plus the `PSum` summand order",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual._proof_1 "encoding obligation" .pendingTransport (.root true true true)
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6" "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68" "type.∀.body.∀.body.@4.fn" "decreasing obligation re-stated over the packing (S); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual._proof_2 "encoding obligation" .pendingTransport (.root true true true)
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307" "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408" "type.∀.body.∀.body.@4.fn" "decreasing obligation re-stated over the packing (S); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual.eq_def "encoding equation" .orderStmt (.root true true false)
    "304abeedf1bd87f73382bcfc024dedb0aac1a01ea5f7ccb92efa730fb2732633" "89a8772f25d96b69de96009004693da023d46169108c225c9aab72ecc40a9aa7" "type.∀.dom" "statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha.eq_def "equation lemma" .lazy (.root false true false)
    "57a59c6c6683b306cca70ca5a92e04b85385414bff173296c04667216610c387" "7024839b94a5786e1512be86fd721d95f38cbda1035ea692508c8b4206f3c6bf" "value.λ.body.λ.body.λ.body.@1.@0" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `hb "clique member" .pendingTransport (.root false true false)
    "b71ab54eb93bd5f8e5cac47b1a83061f3fb5e05e1855139378d94d4a29516b4f" "a58ab00877da16960b0d732d2fe021fa9f40fbf5e58b3c84e8bbd53e98fbb9bb" "value.λ.body.λ.body.λ.body.@0" "fixed-parameter telescope in the first function order (O13b), plus the `PSum` injection",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `hb.eq_def "equation lemma" .lazy (.root false true false)
    "ba50c991443c66700984e2ebd7e783f68e71b5a574b26685aff7feb82265f671" "d3e27bed829407376d4cb0c7da14671d63e7994196c558c340f953fa0f4aec1b" "value.λ.body.λ.body.λ.body.@1.@0" "lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta "clique member" .pendingTransport (.root false true true)
    "deec05de7b347d76dbf742d9a27ff97653086ffdbf18a8b5de4c7a3580d26992" "88be839c49a3224cd64a80ef9852bd686dc4a12851e7a7b0d51832972c1fcb8e" "value.λ.body.@0.fn" "member injection at its clique position",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual "clique encoding" .pendingTransport (.root false true true)
    "77072c5e6560d1be6a9bc9685b5e7c79aa56f2065994f84d86c4c2d6b749b28a" "3b0e15526feeeacadb93a1a5eef651ad56ddc066b50212431324a6a92bdb4779" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "PSum order of the domain, motive, case trees and measure tree; the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_1 "encoding obligation" .pendingTransport (.root true true true)
    "2f26cbff694f6a8bb72246aaa44ff036340467b83cba9f59b64b4e12127053e2" "7d5de2d4739bfa89706b90112b4e6679596ba69c90bd83b447f17585844dec15" "type.∀.body.∀.body.@5.fn" "obligation re-stated over the packing; the goal-specific decreasing_by gives the same proof in both orders (no TACTIC-ASYM)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_2 "encoding obligation" .pendingTransport (.root true true true)
    "266d5a80810da61f2cdb9a05392dd32e8f1f8e19b8a523dcd9980bf9d4f8b7d1" "10331ba20de201615de5919ad83281e9c5fdd020902cf78beff8fdbd62719e6e" "type.∀.body.∀.body.@4.fn" "obligation re-stated over the packing (no TACTIC-ASYM)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_3 "encoding obligation" .pendingTransport (.root true true true)
    "9a89308b9978c15485d5e24b90d25e240a0b20aa76ca8f8cad49fdaf7d7298a8" "9037a9baf5fd0aa1923085d1063c69088bf90196b57d59073019802980a446ba" "type.∀.body.∀.body.@4.fn" "obligation re-stated over the packing (no TACTIC-ASYM)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_4 "encoding obligation" .pendingTransport (.root true true true)
    "ebafd6516a002329594de44610e5b29caa9a7b1ec0e96c307e0cc61eaf227425" "adf61a53598121f7b789c3363512982f6c8f0be8ea7eb2714358053fe36e7a7b" "type.∀.body.∀.body.@4.fn" "obligation re-stated over the packing (no TACTIC-ASYM)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual.eq_def "encoding equation" .orderStmt (.root true true false)
    "1fe0c2bdbc40ee7e7b51cc3ecc79ab82366db41efd0e90e30c51105e045001c3" "106e35daeb35e4579cc1bfa0610afaf7705543552ea524d2e4d8c483a1fdb629" "type.∀.body.@2.@4.λ.body.@1" "statement over the packed _mutual",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta.eq_def "equation lemma" .lazy (.root false true true)
    "cf825df0fcdc215d96592a72d56d9a67d42e587d49464fee89ff21aca5cc0271" "1b2f24b1a260bd9002ac4e0541802782dd493f452e46cabb20fa6dd5bca61acf" "value.λ.body.@1.@0.fn" "proof unfolds the encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `tb "user constant" .inherited (.inherited [`ta._mutual])
    "060e9defd68316c2b6f13f719ad81b2e08737319aaa3f6745331aaed4d080f78" "5b8df7a16a1ca945d6443430cad1d45195909c1cbdb777ee86a9990143597d1a" "",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `tb.eq_def "user constant" .inherited (.inherited [`ta._mutual.eq_def, `tb, `ta])
    "087b311976df8ed12f1184ecba573e5665c896d2dd105c72ccf174b047c297a7" "aa747436471a140a76269da1c4ec0f7f2442ee9dd52c899a3b8dc852cf9d0dfa" "",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `tc "clique member" .pendingTransport (.root false true true)
    "41bcc27da9f28ffd1eaca4151a3064ca03fce76cfe4e5d7286446563d1038a12" "f519ad6711975650e15ca602b08522ed1a9207d7d59977fe3462f06214227260" "value.λ.body.@0.fn" "member injection at its clique position",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `tc.eq_def "equation lemma" .lazy (.root false true true)
    "2cba5fe7547104f0b93943b1c609b25d54c43287149b3e9987d643ab8a2d23d8" "cf4fc56bc13c1093ff201d3d1de52a259243c01ede0dceaef0b563abea4bccd5" "value.λ.body.@1.@0.fn" "proof unfolds the encoding",
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `na "clique member" .pendingTransport (.root false true false)
    "6acfa58679ee85cdf1aaccdf61558625f8a41cd5f83c6ff584bf28e956a95b31" "95c284613996b282c88299bcd6c4028256be8388656282563cdef3a0ceb2ce27" "value.λ.body" "identical statements (na of P0 is nb of P1 byte for byte); the recovered specifications tie in one class, ordered by Pass 1's seed order (Q6, A5f); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `na._f "structural functional" .pendingTransport (.root false true false)
    "ad617d6050b9c71451d88c8b0afbbc8593d98af5452ed0dcdef9492090d5e67a" "992a551847a56ae1a88b48b4c37ef9b0ab8311e5dc7836421375b8471321bea4" "value.λ.body.λ.body.@3.λ.body.λ.body.let.val" "path into the packed below motive; identical statements; ordered by the recovered specification (Q6, A5f); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `nb "clique member" .pendingTransport (.root false true false)
    "95c284613996b282c88299bcd6c4028256be8388656282563cdef3a0ceb2ce27" "6acfa58679ee85cdf1aaccdf61558625f8a41cd5f83c6ff584bf28e956a95b31" "value.λ.body" "identical statements; the recovered specifications tie in one class, ordered by Pass 1's seed order (Q6, A5f); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `nb._f "structural functional" .pendingTransport (.root false true false)
    "992a551847a56ae1a88b48b4c37ef9b0ab8311e5dc7836421375b8471321bea4" "ad617d6050b9c71451d88c8b0afbbc8593d98af5452ed0dcdef9492090d5e67a" "value.λ.body.λ.body.@3.λ.body.λ.body.let.val" "path into the packed below motive; identical statements; ordered by the recovered specification (Q6, A5f); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `ra "clique member" .pendingTransport (.root false true false)
    "a1f04a02148000c792d8ae0aef37fd6a62cbe17ae0a191882ee888940c9c357d" "45cd8d22b3641f5c5f2a66236c0dc3602aa02f13b3558bcb38dc41d4e0d9c456" "value.λ.body" "packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `ra._f "structural functional" .pendingTransport (.root false true false)
    "adb0877becc21251dba32d6f1ccbe6735a0bba7f7b0a6550890f5bf4d9a80d44" "bfc0b1efabc2c32500e3e3fbec6f4d7f7b87e8f00b09522dd2aebc99ffcadeb7" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `ra._sunfold "user constant" .inherited (.inherited [`rb])
    "0e10259004a1e15be0a34942ae27ac32cb04ab641159239103e307e0eb4c4d33" "ea65b60d25f1477b9518d896fe934ddd7d0d68a58d6e009a48243a6c56439e2f" "",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `rb "clique member" .pendingTransport (.root false true false)
    "ac60049a1892d2d7929e6245b9d38cc4e61693debee7b0a9886e2e9acecdf237" "81ecddd3fbcf0168139a2e1e1f1a0384d90d3f3c8a8b1d826c654ee64e3b06c1" "value.λ.body" "packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `rb._f "structural functional" .pendingTransport (.root false true false)
    "ce212569e61531f373a9766d9040cab31cf4bedcbd528748232748bc7c78c2d7" "4c5dce85fe8586bb8a1ea4fa76cf70bcfec977748c8418dfd47f8c794b2afa8a" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `rb._sunfold "user constant" .inherited (.inherited [`rb, `ra])
    "4125c6cad27672ccece179097e483aaca0c95328a1e4069f5b2787ab9bf076e9" "34088b183e9c4bfd3ad3253b77197c359e44034d3fd56866cfe4bfbe63b70bc7" "",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `ra "clique member" .pendingTransport (.root false true false)
    "a1f04a02148000c792d8ae0aef37fd6a62cbe17ae0a191882ee888940c9c357d" "45cd8d22b3641f5c5f2a66236c0dc3602aa02f13b3558bcb38dc41d4e0d9c456" "value.λ.body" "packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `ra._f "structural functional" .pendingTransport (.root false true false)
    "adb0877becc21251dba32d6f1ccbe6735a0bba7f7b0a6550890f5bf4d9a80d44" "bfc0b1efabc2c32500e3e3fbec6f4d7f7b87e8f00b09522dd2aebc99ffcadeb7" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `ra._sunfold "user constant" .inherited (.inherited [`rb])
    "0e10259004a1e15be0a34942ae27ac32cb04ab641159239103e307e0eb4c4d33" "ea65b60d25f1477b9518d896fe934ddd7d0d68a58d6e009a48243a6c56439e2f" "",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `rb "clique member" .pendingTransport (.root false true false)
    "ac60049a1892d2d7929e6245b9d38cc4e61693debee7b0a9886e2e9acecdf237" "81ecddd3fbcf0168139a2e1e1f1a0384d90d3f3c8a8b1d826c654ee64e3b06c1" "value.λ.body" "packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `rb._f "structural functional" .pendingTransport (.root false true false)
    "ce212569e61531f373a9766d9040cab31cf4bedcbd528748232748bc7c78c2d7" "4c5dce85fe8586bb8a1ea4fa76cf70bcfec977748c8418dfd47f8c794b2afa8a" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `rb._sunfold "user constant" .inherited (.inherited [`rb, `ra])
    "4125c6cad27672ccece179097e483aaca0c95328a1e4069f5b2787ab9bf076e9" "34088b183e9c4bfd3ad3253b77197c359e44034d3fd56866cfe4bfbe63b70bc7" "",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `na "clique member" .pendingTransport (.root false true false)
    "ca628c3971f7484713705196f4a2b00005332b12c9e679f3207e9d0954697091" "c7ec1143f700e0bc71939855daac9330d717659f878141282de61288aaff0352" "value.λ.body" "packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `na._sunfold "user constant" .inherited (.inherited [`nl])
    "2b10963d7700959aad09815f4259bb47ca5868c967691808899d841bd1fe7077" "c354948fc1480c4a6a6ff334d4422dc40fc85679a4d92dfd24640451569ae59d" "",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `nb "clique member" .pendingTransport (.root false true false)
    "addfd774526a0e194c7cd5df50968dd0256ac3af941229c85c6166c304ede1e5" "2c981aaf53cd21287f755cb46d9924d997bf752c49744615e6dd93502e166389" "value.λ.body" "packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `nb._sunfold "user constant" .inherited (.inherited [`nl])
    "a1d2d1ac5294333f302ae9ca47f47a31eddb43894ffcca2a1e4355c826c91e19" "147b50011dd987e7fed44728db3d8917e71df83690dbdff7eeecb0e3f780499a" "",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `nl "clique member" .pendingTransport (.root false true true)
    "3849636eeadba2246db3e4e2ce8d9254d524f2ed5eac67d697670f199a7c328c" "28dc5b9646e1b87e571b2ed282965b1a7d0d001ba044fe1914b1bd5e9d6cd403" "value.λ.body.@3.λ.body.λ.body.@2.fn" "packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `nl._f "structural functional" .pendingTransport (.root false true false)
    "ed06ae82fa8626f18f62f1bcbbe20cdb0433be69c6df7d582d9805fa5615d49b" "082e23013ad28dd96fbbcdc68320a2d28df5b1ea2385c510f208023421cecfd8" "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@4.@4" "packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `nl._sunfold "user constant" .inherited (.inherited [`nl, `na, `nb])
    "93e8a5f08c16b4b81782fb01bb0f23d0b14861cae1011ae762a728d630da670a" "e75c0032e98a10a4755b5e1b021daf70e40c4fd5e4e21e2c74a75be8bc10491c" "",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `na "clique member" .pendingTransport (.root false true false)
    "ca628c3971f7484713705196f4a2b00005332b12c9e679f3207e9d0954697091" "c7ec1143f700e0bc71939855daac9330d717659f878141282de61288aaff0352" "value.λ.body" "packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `na._sunfold "user constant" .inherited (.inherited [`nl])
    "2b10963d7700959aad09815f4259bb47ca5868c967691808899d841bd1fe7077" "c354948fc1480c4a6a6ff334d4422dc40fc85679a4d92dfd24640451569ae59d" "",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `nb "clique member" .pendingTransport (.root false true false)
    "addfd774526a0e194c7cd5df50968dd0256ac3af941229c85c6166c304ede1e5" "2c981aaf53cd21287f755cb46d9924d997bf752c49744615e6dd93502e166389" "value.λ.body" "packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `nb._sunfold "user constant" .inherited (.inherited [`nl])
    "a1d2d1ac5294333f302ae9ca47f47a31eddb43894ffcca2a1e4355c826c91e19" "147b50011dd987e7fed44728db3d8917e71df83690dbdff7eeecb0e3f780499a" "",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `nl "clique member" .pendingTransport (.root false true true)
    "3849636eeadba2246db3e4e2ce8d9254d524f2ed5eac67d697670f199a7c328c" "28dc5b9646e1b87e571b2ed282965b1a7d0d001ba044fe1914b1bd5e9d6cd403" "value.λ.body.@3.λ.body.λ.body.@2.fn" "packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `nl._f "structural functional" .pendingTransport (.root false true false)
    "ed06ae82fa8626f18f62f1bcbbe20cdb0433be69c6df7d582d9805fa5615d49b" "082e23013ad28dd96fbbcdc68320a2d28df5b1ea2385c510f208023421cecfd8" "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@4.@4" "packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `nl._sunfold "user constant" .inherited (.inherited [`nl, `na, `nb])
    "93e8a5f08c16b4b81782fb01bb0f23d0b14861cae1011ae762a728d630da670a" "e75c0032e98a10a4755b5e1b021daf70e40c4fd5e4e21e2c74a75be8bc10491c" "",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `la "clique member" .pendingTransport (.root false true false)
    "794636154366ec6dc813c37fc84560f9dd123a2dc5189ec542d18f462b0af64a" "343f2868bb45d3b0e5e94c8464a9f23feda4dc03bafe73b3faef36814ef4a1bf" "value" "PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `la.mutual "clique encoding" .pendingTransport (.root false true true)
    "844a3be331e7f7c758450925cb2a90675dcf0b0860acdc05e16d81c61e5df7ed" "0df7605cdc6de89fc8c8e5a82f154ca3474e0411a1701835480f6af2bd4a7682" "value.@2.λ.body.@2.λ.body" "PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `la.mutual._proof_1 "encoding obligation" .pendingTransport (.root true true false)
    "23f2fcf243de4f203af437cecae5aa8e456a296211e7f854d84afba79be84183" "c6f2eaa1f32e2bef4c81216442e92f4387ed945253669b02d356188afec72db4" "type.@4.λ.body.@2.λ.body" "PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `lb "user constant" .inherited (.inherited [`la.mutual])
    "365e2b96a786e4251db200a6e5d9085c3eea6086ecd1d6bc80a64804479fc2ca" "f5ce712e07338faf8adde6db117546817ac84b50c53b203c172c68eb7bbc02fb" "",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `lc "clique member" .pendingTransport (.root false true false)
    "c6bf45aa737fa84ea64238f4834cf8da5b7d869963c25796f8e4c0b3d4c58275" "5234d7f723dbab4efa505988576ae3f72c905c69da3ae46b572c03bc22876d6c" "value" "PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `la "clique member" .pendingTransport (.root false true false)
    "794636154366ec6dc813c37fc84560f9dd123a2dc5189ec542d18f462b0af64a" "7a884321a9426c7970621310d2f19b60b63bfe1b8890c24ecc9db23e40050aba" "value.proj0" "PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `la.mutual "clique encoding" .pendingTransport (.root false true true)
    "844a3be331e7f7c758450925cb2a90675dcf0b0860acdc05e16d81c61e5df7ed" "7487e2bca961ef77d3aa8b7eca1691fe462020f9be2b4b99fa6dbab3b52d5e43" "value.@2.λ.body.@2.λ.body.@3" "PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `la.mutual._proof_1 "encoding obligation" .pendingTransport (.root true true false)
    "23f2fcf243de4f203af437cecae5aa8e456a296211e7f854d84afba79be84183" "1142aeb7fe76382e4b955041246185112babeb5fed14dc8cc1a4d65cb0c19b46" "type.@4.λ.body.@2.λ.body.@3" "PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `lb "clique member" .pendingTransport (.root false true false)
    "365e2b96a786e4251db200a6e5d9085c3eea6086ecd1d6bc80a64804479fc2ca" "f6af9ba245fe8ca2d99be2d31078f152f98f50bb75455c30895e1f9eec5c03e8" "value.proj0" "PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `lc "user constant" .inherited (.inherited [`la.mutual])
    "c6bf45aa737fa84ea64238f4834cf8da5b7d869963c25796f8e4c0b3d4c58275" "07aca8decf37c349736afb62b21e3a1a1f41ac53b2b02785dcbe38fd19d86cf0" "",
  e `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `ca "clique member" .pendingTransport (.root false true false)
    "e86bf216cc4b16624aacd3e4ab50da5ff52925a9eb8841fecbd0ce263082834f" "f0a459489ed8443f6cb1313451a2aab90fa87698e259a8b4e373422772a606b3" "value" "PProd factor order of the coinductive fixpoint (ReverseImplicationOrder), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `ca.mutual "clique encoding" .pendingTransport (.root false true true)
    "ebf6e6b156580df2615158241987a80dad9d4c32fe0b016dcd3067ef5289eddf" "26f0280c765173003d6dbf565073450987c730824676f6bd699c78134addd1c6" "value.@2.λ.body.@2.λ.body" "PProd factor order of the coinductive fixpoint (ReverseImplicationOrder), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `ca.mutual._proof_1 "encoding obligation" .pendingTransport (.root true true false)
    "c0238e623b000ba4cab169e97fa2f5bbe19c1b19257da7c955f568859dcd9e39" "d1986090ac5216fe4f2a0d6667c95969888402b565139e4191d8717f5ba63ad9" "type.@4.λ.body.@2.λ.body" "PProd factor order of the coinductive fixpoint (ReverseImplicationOrder), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `cb "clique member" .pendingTransport (.root false true false)
    "80120e58691cbe338529b87f7617bfe7187d814a86e1f4a0d304efa7564aa2d7" "b76d692d77bf7afa6bd6d7c3714a6d56d53126863bbea898272ccdefc17af824" "value" "PProd factor order of the coinductive fixpoint (ReverseImplicationOrder), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ua "clique member" .pendingTransport (.root false true false)
    "c8e4b93e1e28fd1dcf8ef447ff7977c39411c7123d2cfddabbc0da9b7bf601a4" "bbbe1e9e94849a0ac25db829e901e10bf54091ea7d597a4f329bc6ee2abfe771" "value" "PProd factor order of the fixpoint and the members' paths; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ua.mutual "clique encoding" .pendingTransport (.root false true true)
    "98442a03f9dfa6b72b5ac7adb902937dfd834e3071aec027601dc2c8c245a95b" "c98c6d8730e61475657d5c36d5642286dc8898eb0cefb389a14982923822f9cf" "value.@2.λ.body.@2.λ.body.@3.@1.@1" "PProd factor order of the fixpoint and the members' paths; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ua.mutual._proof_1 "encoding obligation" .shape (.root true true false)
    "b7bc40a157711d751e43e91fc474e33b76c2fb4c878863a4ac3722312b1a8b0b" "326b4257346d42a8eefa6b46b73df65f6862789cadf88ea8baa7fb8435a78296" "type.@4.λ.body.@2.λ.body.@3.@1.@1" "the user-written monotonicity proofs (an intro script projecting h : f ⊑ g, and a lemma chain with the instances its own unification found) are outside the grammar: the composition fallback monotone_compose (mono φ) h keeps Lean's proofs (clique-transport (f))",
  e `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ub "clique member" .pendingTransport (.root false true false)
    "95b8e93dbb6bf28a4ac287b7b37ddd209f005d9ce94001abb50af0fec2500de1" "f382cb3d3db3db3d41ff4548771c3e6a09c409d50346a7c712d880b496b55e83" "value" "PProd factor order of the fixpoint and the members' paths; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra "clique member" .recArg (.root false true false)
    "2e382f44b64ef0d59ad37730359abdb14ab33271ebd7b616a348302c555198fc" "36c4cfebb52faba910bfe2269aa5c77b87d855eab9e47eb07f8d4982f50ca86c" "value.λ.body.λ.body.fn" "Lean's allCombinations picked (ra.x, rb.y) under P0 and (rb.x, ra.y) under P1: brecOn over different arguments (clique-transport (f))"
]

/-- Entries 200 to 399. -/
def part1 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra._f "structural functional" .recArg (.root false true false)
    "a4ca7ec36d6d47cba1a964f929947892dcaa354e1cda9c8f43b169ce83a4e220" "bcaa8bdad6fddf93d4d61cb14fed4674b79cc401f7f900fd7a556e715b984a50" "value.λ.body.λ.body.λ.body.@0.λ.body.λ.body.∀.dom.@1" "Lean's allCombinations picked (ra.x, rb.y) under P0 and (rb.x, ra.y) under P1: brecOn over different arguments (clique-transport (f))",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra._sparseCasesOn_1 "clique auxiliary" .recArg .onlyA
    "3a4d0a9cb60745860c348a96bb097d439c3b156a60085eedbf4febb58fc9821d" "-" "" "Lean's sparse casesOn for ra's match on x, which exists only while x is ra's recursive argument; Lean's allCombinations picked (ra.x, rb.y) under P0 and (rb.x, ra.y) under P1: brecOn over different arguments (clique-transport (f))",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra._sunfold "user constant" .inherited (.inherited [`rb])
    "20b17d2ad280c9b4ddd850127fec81a0c06d4c66b3f05897fa0afecc4c221437" "cf89d6a713e90d90f1c073e808471a6e8b060e158976270489471bd25f666d83" "",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `rb "clique member" .recArg (.root false true false)
    "d578cc4aed44eacedaa3d6c3b01a3f91a1df96a6619568c2295f3a538b538400" "69ec6b468f31adb4416a5337d78d0a3683b962fc779aa41b8554f663f8c99af4" "value.λ.body.λ.body.fn" "Lean's allCombinations picked (ra.x, rb.y) under P0 and (rb.x, ra.y) under P1: brecOn over different arguments (clique-transport (f))",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `rb._f "structural functional" .recArg (.root false true false)
    "17354ef0aeee92d76a8d286b6d7872b467fd3f60fe44a0a2fa5b0ec653ff1921" "0b4277b06c6b8bc03ead07e16f0edbc44affdb19387289d0680576f912f10a83" "value.λ.body.λ.body.λ.body.@0.λ.body.λ.body.∀.dom.@1" "Lean's allCombinations picked (ra.x, rb.y) under P0 and (rb.x, ra.y) under P1: brecOn over different arguments (clique-transport (f))",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `rb._sunfold "user constant" .inherited (.inherited [`ra])
    "dd1cadd5effc2fc02b6642e09ed35b19d7ec83d85bd2b0e09a478f3a4abea61b" "3dd5a6e4da52f7619e1b99a75ee18e22599a4748509a9abb410ce9e28531d17a" "",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `ha "clique member" .pendingTransport (.root false true false)
    "81a1116c189347bb57bfeed4fdc7502c5269315582c04aa9815485162ea27be0" "15ec7af204f1cc5615f11aa34dc0d3d54c919fabc00fe81d8781292884bbdca3" "value.λ.body.λ.body.λ.body.λ.body.@1" "PSum order of the encoding and the fixed telescope; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `ha._mutual "clique encoding" .tacticAsym (.root false true true)
    "a7bf3d2955497f278338733e61cc5d3dc811eb0b4f52a132982b9ee267ca1cfa" "533939407aa6db690941e7c604843562fb5b16c7ca42c09118038d78f3bef142" "value.λ.body.λ.body.λ.body.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body.@1" "decreasing_by `assumption` takes the most recent `1 < k` in the packed function's context, whose fixed parameters follow the first function: _proof_k k h₂ under P0, k h₁ under P1 (Lean.Elab.Tactic.assumption, FixedParams.lean); the rest of the encoding transports exactly",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `ha._mutual.eq_def "encoding equation" .orderStmt (.root true true false)
    "713e343c7260eec8f36e0df24ebae7be003ad5f43c0913868cc6f35bccc135aa" "c5647bc6499224213d33344f77cdf7498457ba83c22144acbc3b14dc3c4268a4" "type.∀.body.∀.body.∀.body.∀.body.@2.@4.λ.body.@3.λ.body.@1",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `ha.eq_def "equation lemma" .lazy (.root false true false)
    "c8a926c0b15ac771de190bb1bb38887a9b14e03df3a51e239cb1954d3bf52183" "479546722f8190cc7f83279478c11b5521d4d706f1d04b861b57e927cba53a2b" "value.λ.body.λ.body.λ.body.λ.body.@1.@1",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `hb "clique member" .pendingTransport (.root false true false)
    "afc03d9f741d843fe9590666f7f260990cc457cc68a552ed117eff1ae1561f7c" "5b029055e35a1a6ca14149c622e343b185991dfd6fae99026eb71cae6e73e90e" "value.λ.body.λ.body.λ.body.λ.body.@1" "PSum order of the encoding and the fixed telescope; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `hb.eq_def "equation lemma" .lazy (.root false true false)
    "895d6edfc2e83439b104aeb6f8a2e044351f4dd4a6dc95f9867ed343ae8edc7d" "5190c7ce167080fce7857892a64aceaa792805a9c69f5615a0f01730fd508310" "value.λ.body.λ.body.λ.body.λ.body.@1.@1",
  e `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `ra "clique member" .pendingTransport (.root false true false)
    "f515069851bec772c86c3429da59017111da4e12fec7a2c50f55a4dc3ba2e7dd" "c57bf565c6293ef91fd9162550ed5e87273fc22950125916325790cf69473b83" "value.λ.body" "identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `ra._f "structural functional" .pendingTransport (.root false true false)
    "6b6a82b3efe33c928262df29a6e1e52725b2dd8a78d90979b1b57fd8353cbbc7" "68deb3de80fe3694fc0389a033a873e633618467eaa924299bec4b449353613d" "value.λ.body.λ.body.@3.λ.body.λ.body.let.val" "identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `rb "clique member" .pendingTransport (.root false true false)
    "7085cfdfb166749435e0c1d59f22e1796877dcb83ecfa64a8b3d05bf7362406d" "55e412c17212dd415e079e198e94f2d0e5ee81ae9a232371140af0052f959767" "value.λ.body" "identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `rb._f "structural functional" .pendingTransport (.root false true false)
    "98108fcdcffe277bf9fdce4b8af643b1b785867304c24a149d4b775f5160a4ab" "cb12be024d8ab4425c89facd16419aa4416f8a35a02dc910c309e29fb3d6a16a" "value.λ.body.λ.body.@4.λ.body.λ.body.let.val" "identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TQ "P0" "P1" `qa "clique member" .pendingTransport (.root false true true)
    "b54f2593059f634aacbc338c3a6a9f1d174e9c878602a973ccb39b94a1da691b" "808cbd7f9bf7daab6785c7cf800175ac51255af01e73840ef56b4f111b1da16d" "value.λ.body.@0.fn" "identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TQ "P0" "P1" `qa._mutual "clique encoding" .pendingTransport (.root false true true)
    "e221ec86aeb3fe776065dda776611fdc22c24a263d0fcf3e070a8d5bd1b4c39c" "71fe3265b59618938cb2faf2c8de64ba2c21e021af3bc308451210711fa2af30" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TQ "P0" "P1" `qb "clique member" .pendingTransport (.root false true true)
    "5ff24256028f491cffba1917f580101010c8cd13ec8c2b5eb46b8a31c85be8a6" "77b89a107f331e04c153051103491879bb066e16f5a60ed7614aaad2dd3a8e3c" "value.λ.body.@0.fn" "identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wx "clique member" .pendingTransport (.root false true true)
    "d4453beb9378ad0545d57b3921bd3679fc92382e9a8278fef1183e3c8247c289" "1ae9cccb49d7220eb4d0e94e465b26444c563356f14ce8d6ba9ee97ca9248b90" "value.λ.body.@0.fn" "PSum order of the encoding; the user values of type PSum Nat Nat stay (the position restriction); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wx._mutual "clique encoding" .pendingTransport (.root false true true)
    "29ade7866807a108f74e5e7af9dd2d16e97e0bc0ec70d8c0348e2f72461a77e2" "ea34c5fded17085a9976c048f5b01246fb7ace26452defea241709934aee40d1" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body" "PSum order of the encoding; the user values of type PSum Nat Nat stay (the position restriction); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wx._mutual.eq_def "encoding equation" .orderStmt (.root true true false)
    "a3574f238552c2f40c8328764184166dd04daa2832607300df5528398e21d223" "d80a2ec1dea3ed3a5569755bacc357727c3092c1b2f37454047f9f1ab969f2c7" "type.∀.body.@2.@4.λ.body.@3.λ.body",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wx.eq_def "equation lemma" .lazy (.root false true true)
    "578298758d13c63deba908d0afe1e68292db2343eb7f5587f4b2e701cb291b2a" "1369d30019bbd8c870ac4a620feece8eaaf1963ade3dc8a01d756f4370422d97" "value.λ.body.@1.@0.fn",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wy "clique member" .pendingTransport (.root false true true)
    "92a70374d60266f75c22cc5167b08c23ecd199f5e0fc61dbc36ee39e069dfee2" "c65c287d359b894044850482f45c4d64856e31f7561d672d368ff84b6d7120a3" "value.λ.body.@0.fn" "PSum order of the encoding; the user values of type PSum Nat Nat stay (the position restriction); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wy.eq_def "equation lemma" .lazy (.root false true true)
    "5a031c526f0532f55fb04fe46bac9ce987909707d19a3f7842cb223a007318d8" "f9a53f194d6e42939af76f7dd338862ff4c9081d9b15b7ed9a7137a63edf3e2e" "value.λ.body.@1.@0.fn",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "cd37d419d255515656933e6d23afe32bffc3622104ad299967bf429b71328188" "94a62e97c96672f915d263f7c4acf33cbf96f553aea6f06157fb39ad491176fb" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "9f571cee8cd34435aae331146255374c3c30bd41d22263eb4d83e9487a9971d1" "16ea542df804267faa23bb4107683ca08e202828b49b22ddd8bb93b34e3e57ca" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.a.elim "user constant" .inherited (.inherited [`A.ctorIdx, `A.ctorElim])
    "0d513ba8e78a3c89b4da0b1d6840743a5d50e11c0ff69067aaed6dd89d7b4d29" "2bf72496f04ccd50da098a9ead68e54d21e011a905ceef3523bd3d933528e76a" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.a.inj "user constant" .inherited (.inherited [`A.a.noConfusion])
    "3617e858203ee3d647eecb17b1de90aa88fc5f3996b1c38454ba6a6df8f273ea" "498e514b3963a4d3015589c2e4de8b6eea75361c5b4b36d14fef2418fd3367c5" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.a.injEq "user constant" .inherited (.inherited [`A.a.inj])
    "b54352c518facc3baa803080b37ddb1c133458530083efe572f5bc8cc6d02d19" "ecb568eb121862e67f29deb80a90fe1a5f6355a30fad0fd3c4a698a9a772c586" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.a.noConfusion "user constant" .inherited (.inherited [`A.noConfusion])
    "1bf6befe874d4bae51d4537e3fb3bebb06c0c800b32e3829d723b7422bfa2be9" "dc0a55a255fb144a662df79a2fe6cb131a4c74a87cc9d120e97811892a669594" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.a.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "6d49117afba347441fd9d5c801883965a81a59d32b23b89e2f613cce8ede1432" "c54a583208689e148335d6d010218544cd030b5ec6a2a5da36e6d82fe8748e07" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6825ad81f198d5b2c2383e8f41765aa9173509839d83eca74daf8ed4250cf7f6" "edb22d889d302d4fc637bd44e88dcadb1f8a38bf305e62670e018b630cfcb4fa" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c87e3173622cbced80a8ba699a7da4f6dedba809cbef16bd6e968dc15278c30c" "377aeaba992e9d9c13d4aa246284169c574fb6350f892c0c02d0e5a69b133506" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "61409cf8593535276483244e4931eddbcfe3c128ec76ebb73f98e09c5235aa04" "162916defdace1c6bef8b2e24099f7dcd356717119fd8de74c9f49e3d71199f9" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "231dc18951ea73da5c170f4d74f2cc36c744823c7a2e5bc63d2833f57237bc90" "607b55c6ab4127543778e692744db18f9f4d0403b2f323cdde273214930d053e" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.ctorElim "user constant" .inherited (.inherited [`A.ctorIdx])
    "3ade96a931f0f9df33f1f515c479ce60d8ca24690d4cfadd44c7fd5b70a778e4" "7ac021f3ad8fa90434e367a2b458c4300be8c37f71e723cfc12d57a17cb141b1" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "c2809d9d2e483b695fa6d99877550b4e039ffd57d2213b9238d0c866570908b7" "db09c8fd38d13f2bd835b106874e4b073c257a0af22bd9144629014e482364de" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.nil.elim "user constant" .inherited (.inherited [`A.ctorIdx, `A.ctorElim])
    "1a3d3a60851af2763727a798a7dc00c1615232a6284a4a08c55c21aa47366692" "546a3eceb55e758bd4911558031c5ecfa084ef30defe4b81169a0e4abd221a4a" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.nil.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "1306c44721989e0badcb92934c7b477015f0d751772f8b67a115b6124d735d07" "2501d5ca713a54950234ba373d88943b3d00b70a8d74e8e6afd58143db8b3c64" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.noConfusion "user constant" .inherited (.inherited [`A.noConfusionType])
    "1afc8f389ee7ec94213ce0b743d528f9b7113e62aab67af4108c45bd7369eca6" "2343e59aefc761da079722d3afdbcde6f724bae01aa392b979188a09e1fca7af" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "5f73c471da9b5d8b7975d69a8069bb565619aeb1bf9ef216aaf11335661319c6" "45ca3e2ba0d023ed9d8789b58d8a03e67a5f230f7286cf2f396b7ce92db95f51" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3ccc83899f75d3c94a6f6edac10f5a968ab26ea933205cbc7ac420376c39080d" "c25c953a464d477303c1228a5d162fb91be4191770fda51ed39d0a34c7ca1524" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d80456773bd6b4b102754a79e2c45bd6feaee3685cb0646a3b41716daddd1e02" "81a68179231d6907cae95db052b597990c7a2b1f31f5e1b6a79ff245082fe9d1" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.size "caller of a changed block" .pendingPasses (.root false true false)
    "a079964bc4740aa5f8db3225b1cede4039647cdd6ab1f0a8b3c24454bfa9bf10" "beeb358d6276b70b8fd01028844cb379409bd296ce3b577c2f06497a4a5bb937" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.size._f "caller of a changed block" .pendingPasses (.root true true false)
    "52f668901e95777428555c59f3cfd2c3a90221269c7a3ef2c67fd4342a007d5a" "509507128ddf71301e57e0f67312e69e20972f9b96e08097a0ac24041781eef9" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.size._sunfold "user constant" .inherited (.inherited [`A.size.match_1, `B.size, `A.size])
    "73bf83c71709837e792456ee256596e7dc4254ffca8cded759b3072af5512be0" "83024766cfafd9ca0e77350c9287035d19eaa998f34f80f4bf18997ead21c152" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.size._unsafe_rec "user constant" .inherited (.inherited [`A.size.match_1, `B.size, `A.size._unsafe_rec])
    "ad920014303db3248d907b1a8ab3ce2f10cca2dd45f2bc80f257b5edc2c291c0" "c58aa02e75e8ab32e3256fd23464cade5e3561de91f3d2f1f9cbdde969df67ff" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.size.match_1 "caller of a changed block" .pendingPasses .unexplained
    "d8686b9025ae6689dc2bb0a34bc72d46ea1e0ce0f6ce6ce637cc978506ed4559" "2bc551a79701891357e9926ee03a72a7f96414fd1bee42604ac0ac8c617d79b3" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a17da90a847d92e8024d980f152101a3ee8f2096baa675ddc6cb69732b2d1ebc" "f6abd9ed9fa5e1d41083e3fd94b9497f3929b8c3b57bb15bd3ecd84afea5c021" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fd85ad262719d83a12fc1d950e9cbab5a15eddf153ec38dbcd5fc507216927a7" "27ae2ec72b9d470cb04e1fec2db3bf84a0db4376e54bc964cfcb5188b8fba868" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ab8acb574825a6d2c00a02642757cc90d37a478525eab15ffd76f53041572b70" "f51addddeb2bda9e8d058e0b18aea15c86380b78e043b35d6ad475e6954ed292" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "597541cb7d1515de8618e8ab7f7f7e0f4f5693cfb3ea6be3dd1cb1fd8891e662" "6fee31554733eb6825e76545eec5a750f07ca2367e17928095e4e31dd46915f0" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.ctorElim "user constant" .inherited (.inherited [`B.ctorIdx])
    "f3db120744d25a57d5535442d6bb7d0923b45b056da302e19f82067a40f3f702" "bb0d99ae86cca402f8472a2af43f9d28ca73012c424a72dfb12c8475253d05cc" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "2613f00a4d5923be077387ceeb87f0fe68cd361ae987bd818e066f6042264c17" "99c2ddaa2a310a32946ff5e6c7aff43a10d3f34da117567aa635f410b50e8196" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.nil.elim "user constant" .inherited (.inherited [`B.ctorIdx, `B.ctorElim])
    "bbb6ffe937a7d246d1cd455b1e4f49eaae681c4fdeed60078775e57fb5a1dad9" "020fc73b74c112376cdf6a9e6503d7c118a914ab6492526ae3f0c64fab5e8b4d" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.noConfusion "user constant" .inherited (.inherited [`B.noConfusionType])
    "567f68cba689df3ecee088d50c35c5224bc83709602c1ec997dbd49835743974" "2385f1db4bdebbb2adf0ab4ba60a69b81525887ee1d6faff61d8f4aff080632a" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "2028e58d86f9a54b9e53c4f4201b53ccac824e2a3733a06ff4c6a43d5d859b51" "a182e4bd4c6d5d25365ac60ca2d530d30bf455f5438cedfe7effa74ca153922c" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c8322e03d558f85a8edc7fe68524013880ad0bbcb7dc890136d247154b230992" "488ee843bd3a5db6dcaea357ec8fb7edfe5e5b79537f9417cc7b85f7ae348707" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "32038f41f6815ac7654830d5262dd2880649a594097cc8af729505ce45c84ef9" "9ac4ffee9f38aecd8787eaacb1f4c9ad3748ec11379ffd85e516843877f35f52" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.s.elim "user constant" .inherited (.inherited [`B.ctorIdx, `B.ctorElim])
    "16107ddc18248b7ccccad13cc7b76b39febcc21962b84984ab8dd2070a21bbe0" "0156e4461afe70d1ca687424214af7f9d316610272830975133e5e4070e2ffbf" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.s.inj "user constant" .inherited (.inherited [`B.s.noConfusion])
    "3fb46b0bb6ee82b33e855925ffa40315b616788be62d07411c4ffc45f51565a8" "be92ed1113e3653e828477b28cedc14b6e09c331e2e32160d78bf22e2d4deebe" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.s.injEq "user constant" .inherited (.inherited [`B.s.inj])
    "1917356cd419691dc94a7a54c0ec9781350524e1244c139252f96b6e9d8c7a20" "79002c702ace448c4f930447a41a621a70ed82e33eead9d69d0b392eb5c5c223" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.s.noConfusion "user constant" .inherited (.inherited [`B.noConfusion])
    "b0a8929138060d1c635634bdcfa7cedd7c2cfba0cc376de8c5de511d3cf8cc5b" "15b70b6899ce544ea80ccab1fb0bbbc6852edfd669f5e5286b2c8588f942b507" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.size "caller of a changed block" .pendingPasses (.root false true false)
    "7ab66120eb546a328d7a77dc24057c2590921b439880bd534377f46929624447" "21870540e2cba122e4e1540db3e57cf9293fabef721d4662e1e4e9558d42a89c" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.size._f "caller of a changed block" .pendingPasses (.root true true false)
    "c0ed98ee378360d330b40f22a2fd2b9a06153d051825644cec6ae0333f7250b2" "3f3d5ff8ec4dd9a4d6e391b114e9b2f9992caaf8ca3394ac410ed7f8148b54a0" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.size._sunfold "user constant" .inherited (.inherited [`B.size, `B.size.match_1])
    "ca27ead5b84f96c21500cca4e0522c912e2547f9f9045e34b242979270809eed" "620c0bf7c379abd350db9fc3e12c058a6fd462e00b1d09f5c31da8a54ca83a77" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.size._unsafe_rec "user constant" .inherited (.inherited [`B.size._unsafe_rec, `B.size.match_1])
    "9812e80ea5a87bfe8c706f22bcbb0088aec3f8dfdb907bbdef65aaa4271756e2" "a3d948ce8b6896f74743038b277f89ba08275dd89d7ad4d7791d4cc166b38113" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.size.match_1 "caller of a changed block" .pendingPasses .unexplained
    "8456b93a61151feea7878938feb7e719ffbef279f28f05c3e798f036ff56fa5c" "674ddde219dd2651a2205b62d3a70ecf57c352e9f674e164d3ef2c3ef449cb3a" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `size2 "user constant" .inherited (.inherited [`A.size])
    "81c2c0294c78f9ec0a8639ef01410a81fe0b57486d2db8631d4d22742cb1c8d6" "8e5d0af872e0e6f168f2942ba3a56a5047adc99bfa37fc95d60885f024a3208d" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7f763b22ab7d2313414b0863abcfd8be6d6248a894cafa3985de4aa1ee87dc76" "ebc3c6e344916a094060c73b9dbffccf4be05a447422a622d604072e21f82db9" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0d06ac6e1421355535a9373b31b4c6c694d6a90e27e88ebbc5df987ac06e167e" "de13524f04eb0a83af891ea98d10e5e75f7ecb56d8980251a58f64be8b610094" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7ae45a0991d805839663d60aaa3c1a21e95d2d82884cb29bd25e4dfbce5a0609" "36db7a4a9d8402bfa9bac3644c5222f85f12c1538671e96918d01c0d5752e4a2" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "162f42113d4810a627b1428cba24770478ac759a69c93f1f6308c7046e52e791" "1cb86054c4b59b486a1ac476d135afe8752728f43713d1061c908f1b6ecd6731" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.ctorElim "user constant" .inherited (.inherited [`Even.ctorIdx])
    "61c84c444af18e5b10eeddacf9038769c5df20c3635297aca0368a85c81c7767" "08e99a0444f4df4c1a491b461873b4763a4ce5753fe30844cc7410eab61e8e4c" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "6b41af9ed4cdeac27411e001be93c064d7d94b68cfc2387eb27edb1d12860645" "e0b9a325ad87d97e290ed0ca7616f68b606d4a5ffb9f158cf801d388f6b4a673" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.noConfusion "user constant" .inherited (.inherited [`Even.noConfusionType])
    "a41136ce4221a23887503cb3acf7cae609d1c6fe6412c8abbcb3e31625244007" "608d719f5edd195e52a868b55989683301c242f5016920e025f4f3c83ef5a0ee" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "6be1c9c3d68f215e125ea41348db280f98b2cd824ae42e32242e7f342daf801e" "21c1b84fdac19e3ac3aadcc268e5197709461f2bbdc4f44758b0f62c9299e60b" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6bb942cd82f258244933f967c95096c6f2224be3e42000044f6c48bea7494a5c" "828c49458b8195d317602ed1e50d073f750366fdd0fb2d8805ea2fb12c57e372" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ceae26812d0993921e96c02861e907a6ebb35bf8ba2a569b93520c1b49a243b3" "dcea23ce9f3d4d3171865b8ddece321fa8b7016725e8821b11f5b4d6c464508a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.s.elim "user constant" .inherited (.inherited [`Even.ctorIdx, `Even.ctorElim])
    "86cf501cb076978ac197991c6f88a35a4f28e2915bae7605f9558b48e862d3a8" "33b10e945a4da1545df9353e14d5e4d0ab23189249df6d145cd325f50578bb9d" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.s.inj "user constant" .inherited (.inherited [`Even.s.noConfusion])
    "d231031d72e12e13cced04bd0d5ae6dd40f8e20cf7a8e4f66f9347ec7456f275" "a3c29fd41fa1a8698e36a94103cfb82de3162d64fde332e285bd301fac3fb106" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.s.injEq "user constant" .inherited (.inherited [`Even.s.inj])
    "abc7a7047558ca0a326f461e5c59eb59f9ce9da9dd55d85d3464ff5080827099" "2448b9a4d5a2ea41fcc5cf920d460df30bac780a97a074e11f50053a8c108e9a" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.s.noConfusion "user constant" .inherited (.inherited [`Even.noConfusion])
    "fd6b519f6d0ccdc418e738e94af933bd2dd285678224df4cd75071aa61b11a8d" "6bb89cd4e3e99d1b2948cb54bac210c7a235215391ba000879ade2fb1726a256" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.toNat "caller of a changed block" .pendingPasses (.root false true false)
    "14c008d747384a6b658c0c1e481a978ba8dc0aeaf43f66382603291dea591706" "263876896bd23b55c0483cf8c5bad31ba877fe03432f899e835a4f871d9eb58c" "value.λ.body.@0.λ.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.toNat._f "caller of a changed block" .pendingPasses (.root true true false)
    "655194ed3bcd02171f46ea536300e78cf92b053d527c2070743416ed1e2bdb69" "81f93e12c74024993ba78be8217091073a60d0f1a69c5cc4851b6c325169ffc0" "type.∀.body.∀.dom.@0.λ.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.toNat._sunfold "user constant" .inherited (.inherited [`Even.toNat.match_1, `Odd.toNat])
    "b026e2ce6b56bc8ab4aae8d71c3bc37463b24263df2cd485d4ad169348c28e4b" "10827ad349ba4894d553a615d54c039b5c96813a8045fea3e7952fff1316cc9c" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.toNat._unsafe_rec "user constant" .inherited (.inherited [`Even.toNat.match_1, `Odd.toNat._unsafe_rec])
    "7732c7afdf7ff4d158242dfc661b38c50a2b3a150927f31efed49b06f995cd0b" "3921437e2f19e4522e87e25925f7e9087f57d99dc388116928cf6ecbe0f34e05" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.toNat.match_1 "caller of a changed block" .pendingPasses .unexplained
    "285973d99afb436f6b20ea696fd6f05570ffb65c40c59dcdc87905652bcaf672" "dcb2370fa5a38d78508941209befb90e8fccd42fe5ac70de08fda9aa4476af0e" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.z.elim "user constant" .inherited (.inherited [`Even.ctorIdx, `Even.ctorElim])
    "d6178667d513bccbf91b324abaff28fdcb96b9665457dec69490e6ddff79d7a8" "c7614d70bbb3db3f37d31c830ca95b706b6dfb38d760568fbd88af6e4f8aad8e" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6c1946534e24d67671f05c36dae164a239acbf49a727475b6836e00b11869cdb" "635e2c9b6b9b2b3919e4d03d5465a968917f2a818cc061f5cf71634ddd86eb17" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "df0c39076c064a2919c5dfb2f1b73c9e9c20d6425039e0f17133c7356490d71b" "f709e453f6ff968b5a08f4cced87c6563ccbb2399ce07726fd6ab0c7cd616eb8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fee09fb5867ff9dbae55ae9aedbf8c3119464b44caae329e490a0286172b57d7" "7d6f949ba4fb394bafe9abbff8d1b55a99903326c2ff5c06f0442d5b71878985" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "166df2c4e8e3fe7a8b6ed7d65b3c5f2c17fc342de8c3d22bb46f54f70e4689ce" "27d3ce37d2427158d4c7b9d458ae803c555d55f579f44848054bbea895e194de" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.noConfusion "user constant" .inherited (.inherited [`Odd.noConfusionType])
    "e264ef0bc51c3b7da9167b2eeda2477c80e46758b77f81660149ff75407cf56c" "e235cb81be4c39d557ad864eaafb78d89e496347fbfe285b371215ae8feaebff" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "df6e6c95a0c0bed5ecef8c56873ee533e15a9f09dc47f7b287c0579f60d87cea" "4edbdf765ad1e027cbca9608ea3b95664c446be15823d9dea46ee0aa8c19b229" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c9cce8cecf22064511a309ecf5cd00f6c87b031ed8e058eb09fd699217fa8c71" "16322604a39ee2bc2c59b6433315f3b40ddb32f55011712161bc88252942c5bf" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1527c316d83a38d43628ce583eb0dba56fdbb7a296b8a0e2e0f64f0e845a3ac4" "c3c6e9068e2b7d3a4ecb6fdc5243e5a0c8288a344a7bb8240e67e9bd8e382cb8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.s.inj "user constant" .inherited (.inherited [`Odd.s.noConfusion])
    "ce92aadef7eedb994d10c8131fd1eb26f9e3f2d30122f5fc0a2710169ee35112" "500fe00a16ace79e19648db1a4309450112ebd9e6c5387fc74861304a9e3e37f" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.s.injEq "user constant" .inherited (.inherited [`Odd.s.inj])
    "38cd356185eb273408ba6421026a9034f94242e455ff6617591a48db3b7a46b8" "1136df113c8e2ab5827369eb1bcd4c2f630558e8d816a7897f1ef89f0916153e" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.s.noConfusion "user constant" .inherited (.inherited [`Odd.noConfusion])
    "3ccc52cb2955604e7ef13afd8d7db2b5e1981f8eddd7012250695d5f78d404ff" "487e5a43f7761729420e07afafe7e20d62fcbdec11effe4ba8868e55c1a2d5f8" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.toNat "caller of a changed block" .pendingPasses (.root false true false)
    "6083ccc0c89479a3a3a552495d925a46473543f579d241c324e4c78d73d2c2ec" "a0ab6e9d00d5e4af919ea0cafcdc513f013098e20f2208a34865008dee08ae31" "value.λ.body.@0.λ.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.toNat._f "caller of a changed block" .pendingPasses (.root true true false)
    "5e277db726358ebccf819553d2429d548b12355953ce0305205e4e5b1be2e126" "6aea37f61b507f4b4e0c2d2089118db8c57bd596fbdd275ad33c7e97972d38ec" "type.∀.body.∀.dom.@0.λ.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.toNat._sunfold "user constant" .inherited (.inherited [`Even.toNat, `Odd.toNat.match_1])
    "ead543ab4f3b5d2598c3223025de93eb010d3f3a53e27af0bf8b41553146a457" "0c9d62e55188afb11a76355edc14dc470e765da2abe99b3d7406c934e391adcc" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.toNat._unsafe_rec "user constant" .inherited (.inherited [`Even.toNat._unsafe_rec, `Odd.toNat.match_1])
    "5a64c69661458a2e7bdcd85a626c0639828dc08b00915c0aa9e7bdc7750828de" "7754ef449f8aa89aff9baf7f25418a22eeaed3d6a4f50a84cceca6f37bea755e" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.toNat.match_1 "caller of a changed block" .pendingPasses .unexplained
    "830a13bfe81958d85007d87a73d4d9fcf860d9120355b09a145f8abacc248c79" "2a19d83dd3bd7d71f7849700303bb6cd165dbf4cf10f0530cd1d80d05f7f530b" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `two "user constant" .inherited (.inherited [`Even.toNat])
    "0a6285ba7aa56c3f51debe49de7f1b93876c1852da1f6706657608c7bf839ce2" "7bffa0f3540416a1eb8523301ddf4d711098b592b5a7ef5c006855dfcca1b6d1" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "19e46c2c75aba8115ea388c0f2c1cbc22f450d7fcd18cf31fd375cde30828552" "64f73e5929554af59b40bbf9d8e2abd18f1ba99399b0b911fdec6fa274c739b3" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "cb38961a123f89cadfc53462a78ff4dbfea68b5aabccb0706ec0e7a5853ad4b7" "674c201c98986446aaa3c41c2ecd087ac343df36ddd465a35ab6039a841955a5" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.a.elim "user constant" .inherited (.inherited [`A.ctorElim, `A.ctorIdx])
    "2fe5c94bdb5c99cea736c5e6fc8a1e8d18c5442936199baf3a3855885a4da6e3" "ac1079750e498f2d1d2476c9ac8de4c595817cad40e431c9d186c2b7c7619b77" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.a.inj "user constant" .inherited (.inherited [`A.a.noConfusion])
    "dac85c3a439cc5c559800b5997a596faa98e077f7b469b03782533a845da572b" "7ae17ca0afa411ad2d83273992a1d0d5bb46fce0167ee640832f953d98ece197" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.a.injEq "user constant" .inherited (.inherited [`A.a.inj])
    "a6d4e7c5074c1d2b7e1263bce37b903ddd9ca894af60dc0fcd746ff6327e1ae7" "2fc72e3c4e25c32cd79dc7dc6ebae87399619f4a121c681b88bd2b2b096a4552" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.a.noConfusion "user constant" .inherited (.inherited [`A.noConfusion])
    "25f2aa0fec2a85138cae95219d238d035da11afe50fb56d4242fe9ec483f8988" "239550c092be430ec9a70ba710e67a3d22e3e3dd42cd8c67cc273b585e2df747" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.a.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "028b918c12d718298eb45d488de35571619507e7cd476a66da582e007caf017d" "de6bb0378364a26b8b1daecc0f1058e134c3c962c34b9a5c5d7dc5cc6ce7b96c" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5415f5f54a992d17fec6b65e0382c4577c3c7dfeb1d4f1e16b36448e23f299cb" "17f5ea7d767f19b280e22f1194210bc852a2d9697596daa4818a050fb08d2272" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1ebbb6b48539de5701c56e706a923d1db699775392773af34933912d17dc61da" "1d83bc6710567484d746c04b269c933d0fc03437e0b2348e9fd65b1b77b965e9" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ae750f0205d850cbda2dc93d13b6a498c0750ccf4b91d2bb68ddc3c414937faf" "4d96be5956fca8ab6be3115d25c1fe60a2a278d7386d5854a0554ea08f562f9d" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "bdd6c50576fd96d51f72aed7ffa79736ef61ca32aa8158e3a6b51d92c1750f53" "4b75385c7045e7852c776f7feb439b030baa2eeed7fcb618c66bb16e3bd36ccd" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.ctorElim "user constant" .inherited (.inherited [`A.ctorIdx])
    "d25e34074b183a135a4f2df96f878d71ca5c64ad893d3eb9a83dff43f8f5741b" "6b3a5d7c5b824480572bcc336db942a68f9f517a69544e4ca93ef1327def398d" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "03ad90414d41ef7e006e41bbb315847d9029ed973148409cd0e7276951ff5d99" "3c8863264d334b5481afd1832013e3d1b245de3a06ddd8e99515b7a904e32dfa" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.len "caller of a changed block" .pendingPasses (.root false true false)
    "a547241d523add64489dbe6d9bcffdaa0e11cee9fd2d77c1f8340fb5c5899246" "c5ff4cc37f93189b090350c0dc81abab77e562793f72da3ff480e1d94b1cf3e1" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.len._f "caller of a changed block" .pendingPasses (.root true true false)
    "4cf893733c374cb1e3d3193e6849687b35b597e8339b7a494c69912565a5b934" "f0138f4fad74d0c00abda006f79c12f2b300f4ae2a88998db1d94c1a438d32a9" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.len._sunfold "user constant" .inherited (.inherited [`A.len, `A.len.match_1])
    "4d723026dd9e109918901fa7dad29203102a220255ced0743a93ddfe9d957c37" "b1bfa3bdb69dae69ff83575d7b5b64f224460cfb2c72bd682c8e57945649c0a8" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.len._unsafe_rec "user constant" .inherited (.inherited [`A.len._unsafe_rec, `A.len.match_1])
    "5dd47dd55a222477bd8d4d3358736c6bda8a716a3d224ef892ae1b0282088d95" "d6936ea943eae5d11f58fe257663c3ad868d5a97c9090b69d102e60d758cd7ea" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.len.match_1 "caller of a changed block" .pendingPasses .unexplained
    "6761fbb4e5f559551e69c80cb5de2b5ed45fc64bc94d91db9c6927e45d073ee6" "bc8ef32918106301c93ecae547b8fe9d825729d6255433c045c94f943ffaa1de" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.nil.elim "user constant" .inherited (.inherited [`A.ctorElim, `A.ctorIdx])
    "b22a414f8dac147c49e118a27e58b13f01801314cb7e2c286effb532f4fc78e2" "aca4af067c9f1762dc15a022d191be56db6710b53cb857c5ce86e611f3e6f1e1" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.nil.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "9a2ccaeac841163498ff30c729158232c2fde2948c593b0434359c016a391fcf" "b89da649732f4728e1ea3ee6ebe0408417aa2bf5808f6d38fba2bec7be15feb0" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.noConfusion "user constant" .inherited (.inherited [`A.noConfusionType])
    "28816d4a33674a5f2a109945f07cd0f2e8787609d9a602b59cc54ef05980ab68" "0b09729545c26e6d0034691a485d449e5d099ac38b733699f3cfd0a024f331fb" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "072df558b5d01b3fe91d84db848aa8512ff4bb7b2b18c8007e29c8081115b532" "ff4bc28df40d5e1109835b0fc35aad6cd4502e9708624f69ad6a9cbb704f592c" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "507879810bce736d4eaf20aa5fe5e0ff6a59641422f54f61cb7c7dee3614eb55" "bc4d5e04e34bebe33ec6ad6138a67ad9f50db6f517d43e758c0ee5217b23f322" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2ac559561fdbc297ca67c47f791c18079f104f9c745c0ab4b340dfe4fdd42b76" "7fb0e68c45047dbe22e7ab84978f97973a15c93b9c602ba55093eb18cde6f369" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.sum "caller of a changed block" .pendingPasses (.root false true false)
    "c7129e39f7bfd2043f3378c09e6f9d5edf719f73180cd4ae03f319cc262f60fd" "9dd56734ca2e0977bddda88d55136b11d232e28ab594a63e8b75491def5667d8" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.sum._f "caller of a changed block" .pendingPasses (.root true true false)
    "de86570efb9b22e8cf776caf80d968a5ad6fab401dadf8c32bd55dcc70c4fffa" "5f7ed53b105bf8959039d02249754b8eeda8ec6593955acdd05a2e2e1365cbfa" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.sum._sunfold "user constant" .inherited (.inherited [`A.sum, `B.val, `A.len.match_1])
    "94b9d8b062531a4a3943a576e713f7a9dd7512501e1c51f224b970bf400aa145" "878340a13a22b4f4f2dc151ddc6d6fdf189330a1ac195e9de70395cab07c1a2c" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.sum._unsafe_rec "user constant" .inherited (.inherited [`A.sum._unsafe_rec, `B.val, `A.len.match_1])
    "95f0d8ea5f21f9863ddbd9991ba2f9e76256905ddbb9d6c098f99b993e24b8a5" "743a0ae731b49a4fe01ad80c6a36776e830245f10c4faf5e5694d6dd4bc745c0" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.below "block auxiliary" .image .onlyB
    "-" "11a02ff01639cb2e18097f2819d5aeffa7863652a43edd53dbcb6a8a0ccc5424" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.brecOn "block auxiliary" .image .onlyB
    "-" "4352a61a2f59ac64ef865cd4c6fab60c7787fd23be1381a339f82f9ca28b162e" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.brecOn.eq "block auxiliary" .image .onlyB
    "-" "2ff628a276a05b418b962c3b16ad80d0d5893649c9d6e754a0c1a9cfd18de6a6" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.brecOn.go "block auxiliary" .image .onlyB
    "-" "a16b21c967e7357925412409876fd0316caeb5ccf96819e5726384bb6193cf4f" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.noConfusion "noConfusion" .pendingNoConfusion (.root false true false)
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "abd3af6627f5d3c14eab547715953d68eb79793adee7b6b73ad6b4b0c82581f3" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "a13871a9d6c0f80bec0828b0d0bb5b706bcaf3036c0fd63791655cb1bf8a9100" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "62097ef059b0e99d2abee440f8691386cb2afd54beb68a2cf3a336a726852a0b" "f9cc97e627e1497c57d63be38890d913085305c7273ede067538078438900f73" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dfa05d5f71d78161d48645eae61fe74366ed0196a36d361827c4b360c8af6812" "8db08eb4c7eb99558e309570ed6f1ebab46facccc9c9f247986ee5314891839a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.val "user constant" .inherited (.inherited [`B.val.match_1])
    "5a9809d68bd40dd0f451d95118426d4f8e8637ce156ef0cab2cc9c386662a8f5" "2423083e95f8e05fbb67b6de53be2fea58831e0cc5278de4a2e81a5942a1ac6e" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.val.match_1 "caller of a changed block" .pendingPasses .unexplained
    "b1ea810b383f4dbd7b749e796f7db68cbc10a01f96acf7709d4af3949d8bb9a0" "4129c74ecefde87ab2bff3f2904acdc49e8aec8740d1549bceb1afb47c4f0444" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `len2 "user constant" .inherited (.inherited [`A.len])
    "c7de97e5d77bc5368dd7623036851ed5296ee3ad2b92c5b103e44f3ac577d806" "7cb019b07b25aebfe3a6872e06283a9faaa383bb3073a38ca3158b9c6d0c0874" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `len_succ "user constant" .inherited (.inherited [`A.len])
    "989a21960afdfd4c3e43ac3e8a38c11d77ce64f365deeeb593253f1358a8a82c" "5549d75a0f0166556653cf7b4429db5dcb960fa242e6da9031dfc1b0a085903d" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `sum1 "user constant" .inherited (.inherited [`A.sum])
    "cb50a2624f5ad023677ab12de80a33455ead17b955e22e4d1d61e8efc413b113" "2cea65837549eac6ac340e5a197a95bf9d9981bf6aae83b5715e03947af1335c" "",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "b7026d7e4027e86fbe090ab636abd8a416c3c971b1d812279d35834decbb2206" "d21ddd05d636f844de163fe5ff3c0ae7a9fe49623a4d8044f70891ca4bf74613" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A._sizeOf_3 "sizeOf family" .o11aPending .onlyB
    "-" "36110cd2e8e6fb2938574fc6b5491a1af20c3602a899dc7fb60e1972784a9fd7" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A._sizeOf_3_eq "sizeOf family" .o11aPending .onlyB
    "-" "42d337e078053600f22d2f6fea2ae0adfade6b64bacf1bda325652ce68e95de8" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "c9d5273c0cd7358fdd658363e800e780d218f2dbb4a459e54809caa2b5771f70" "5e96e26f1dd45f4cfbe51966f0f78fbb3d1d4c2648face40b909799e21b2495b" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.below "block auxiliary" .image .onlyB
    "-" "91a28ffcb5f56be00705de97a94f11381b1b728b8a48bf9a3db14947c8852e4a" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.below_1 "block auxiliary" .image .onlyB
    "-" "4c1ce33b261f2cae0d311e964844e499bc279b18639374368fb2ac14f3794be9" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.brecOn "block auxiliary" .image .onlyB
    "-" "101a1262072c241fafe779f7d9c9b95943360e1719cb505727376b242ed63f15" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.brecOn.eq "block auxiliary" .image .onlyB
    "-" "cff3047e533c51d61936b58dd97ecac65c1577e3a4af3d0d4b3c07fd6dde717a" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.brecOn.go "block auxiliary" .image .onlyB
    "-" "31c4e62e6a96fb006d184073c227f84d56b7c3e8be12c9f3d7add6fde2f2c440" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.brecOn_1 "block auxiliary" .image .onlyB
    "-" "784ce6e8ca906b0a43be68efe5515db6bc763f9a5e7ca5efdfc877fab39bbb4f" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.brecOn_1.eq "block auxiliary" .image .onlyB
    "-" "38199ce4669f45f08fd939f42b385bb6a6bed7b033f2adc2580b32dfab4b780a" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.brecOn_1.go "block auxiliary" .image .onlyB
    "-" "428529884300be0c4637b83aabc365aad465da6b7e9229f32630d7323bc95690" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.mk.inj "user constant" .inherited (.inherited [`A.mk.noConfusion])
    "a56748a2d93254e4060a9e9cb23d30d6622e6139eda5d5e17b09d21d00d2fbcc" "f00c5f2afcddae630d6cc06ba722be8f9800500e9e952a62faef16e223d256f6" "",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.mk.injEq "user constant" .inherited (.inherited [`A.mk.inj])
    "89791cf3e44a17692aff1bddd0e108f5b0332e2271a65c71da6594eb1cd20c34" "b304eb0bbd5e2d008befa102c50107d6782af49fc5d2d8d30f198c628dd0b44f" "",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.mk.noConfusion "user constant" .inherited (.inherited [`A.noConfusion])
    "8ffccbc5764cc9e8a2c4f8332fe3f4c5777b81a73fad30f4dce98b541d9979dd" "7e98cf4a6fbb82c2b04156a78f93917206131d182a6d3cf99f49c2d8e35b3f37" "",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.mk.sizeOf_spec "sizeOf family" .o11aPending (.root false true false)
    "62da2845006a89ddbf242ec098db179137bec49fd23f804e990969d2cc35c5d3" "c47e4738b2c89a7c1a32c0466f3694cfa40cda5127f84d5b82ea64e19fd5eb5f" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.noConfusion "user constant" .inherited (.inherited [`A.noConfusionType])
    "e33da13f8a61384e608ac707e002e06475c9f46458d8d67683c6ac6e3ca350ee" "fa43fa46b46abd4706092b08394c6d01333002b89b0087776986ddbf4bf0cd62" "",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "030ae1156180b1ac49ed4f5eec6a82408207719c56bb8724462953ced6d7dea4" "9a49dfadf6985009d708e56ae4505210b53d0abfda8152b37dedbc7a5751f3ec" "",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "001293f7f7890c8941d95ddff31e3d9e6a4bba42204d00a8a9da983677fec23d" "c6f4c9ef77bf9bb5326f5f668dae16b86df01b495c9565c39c55678c2966f57d" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1ed4553a14482ddca6bdd6edad60854958ec2a5487f219b7ea2746affb1e8b0d" "f5d32e768429ef56dcfd352f7c03888b2524947c48be691507328bf134e6bd55" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.rec_1 "block auxiliary" .image .onlyB
    "-" "c7f59215d14ef2b35ca5bbfd749f16dee94336156e2fcdfcca2525ddcca640c4" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.below "block auxiliary" .image .onlyB
    "-" "b0782747033c62bdd93ce0f6e1e54493b17cb7634107527fe80f240ae973e2fd" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.brecOn "block auxiliary" .image .onlyB
    "-" "922bbf33b177831e0ecbe06d0fccbd2b40428e64db7e38b38a64fa633bb10e59" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.brecOn.eq "block auxiliary" .image .onlyB
    "-" "877826a718d6a20dd2f42c33cc100acfd2c9e36232b8656f864a043c75463cff" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.brecOn.go "block auxiliary" .image .onlyB
    "-" "f280f4cd05ec7ca01893c2aceecfe2a89b1f0a1cf31c8c06e73102cfa9d1bc1d" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.noConfusion "noConfusion" .pendingNoConfusion (.root false true false)
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "abd3af6627f5d3c14eab547715953d68eb79793adee7b6b73ad6b4b0c82581f3" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "a13871a9d6c0f80bec0828b0d0bb5b706bcaf3036c0fd63791655cb1bf8a9100" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "62097ef059b0e99d2abee440f8691386cb2afd54beb68a2cf3a336a726852a0b" "38a0af07b0206343309225612792bd3d2c1d87b1b9b1e9c54c9dc98ee08115e1" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dfa05d5f71d78161d48645eae61fe74366ed0196a36d361827c4b360c8af6812" "239c0dde0c354de1bb9ac55d18211c95299ec5562eb98e636350c6c2a02a7730" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "4df3202436ffbd70a6b1d5c75d7ea85dd0830c7e39e20e3970fa53d5f37b787a" "2edc2528b2d1aec786557670b61916a21b523c878bc0f2e649077a328ba408c2" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A._sizeOf_2 "sizeOf family" .o11aPending (.root false true false)
    "8ac1ffd7a325a4cc834a0db80f114b18eb64eecfa0788eddcbb23ccb1dc11022" "e7c27ad11ce227f653dda73bb886144a2d8beac974319476527e359dbb05a31b" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "ad41f074d6cd167050a2d658c140c0ea24d874307d19f62c1c590d197a92afc9" "dc65430879c204fbe617511a158c5ff37fd7eb70f78cc29900b1d955cefc0387" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "f4a50e7d05b1d1b709bfc1e926d7b50e4b42c04fc7669c57cd54cfaa213bea2b" "58a9ca0b5cd41e686933127bd126384c606220d082932b13b65550eb767a7caa" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "402279f60af6fbc277207c1bc351bfb8c45f2f02854eaa4ceaf1a7827a94f585" "517d9531b7448e83ba4bbc9b1159d25983de40f0df4192263e478abe482fadcb" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5f4992ab19e74ee1fe40f781f0bb307b2ba142ff9a1b31414c3153bbfbaa0e52" "ea85ec5534971bff0abfb24bc49c96ffdd021c8c216516830ba62edac165fba8" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "79659ca1c5d6856dd5b89842d6d9b208f6d92a011569f33e8e683765a4005063" "01b9f907f76d7cf82d2069e8e03975cbd5c64da50812f2b360fba81d285959a7" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root false true false)
    "f0b07f995a472afc5818d30b96df272fc18416b32b4c6e83e8653f7cff35f512" "5aa7c9732b647101475a4d8d28707dd17887caaef0ba782384dc99da8f0c3081" "value.λ.body.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.ctorElim "user constant" .inherited (.inherited [`A.casesOn, `A.ctorIdx])
    "1d691a3fea45edf55554e36348228c671f49d32e75af8641d14bd67f9c3b5f0f" "357230a1e8f3d48b010b7d428f5be42da95a3890acb12925d59a7991e7c0f3d2" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.ctorIdx "user constant" .inherited (.inherited [`A.casesOn])
    "7419dddaa67dea7842d13e024e33b377869ba44600c6962f62deac1cf5722509" "9f1ff4c283565ea540040da42c9689e3dedc031a4c16e3df52467accbc797391" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.noConfusion "user constant" .inherited (.inherited [`A.casesOn, `A.noConfusionType])
    "651f6e39a1359126951895de03225018ab50fd85caabcfd26a22f383395ac5c7" "b971b438ea7ce9586def6da7b5959434c0ad0f12b0c826c581217a33c6d5b24c" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.noConfusionType "user constant" .inherited (.inherited [`A.casesOn])
    "296af3989fb1a9bbf97a59d656f36fd9ce3a761d4b39b0cf86b6e9352e68fa18" "dda562bfd50d237c8d20edb760a8b61c409cef8f320dd0d4765e8600c6aac963" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "21bd436add8d2a123217186c00606ebe19f6c150d57a38100a7bb7638e3b45aa" "ab2189a5a647556d0c675f52347b2dc822c367749cedb98aaad50e95b147cf50" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b0179d12aacab6290d221a78f05017fb716f2cc2a1aaa71bf091f0d8da6777a8" "791c072d8465e745cd3cec463fa89f4577e4b0f4e7f9c6e6f8617bca364a1333" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.s.elim "user constant" .inherited (.inherited [`A.ctorElim, `A.ctorIdx])
    "b842f09986bd8205863da45ec3abb5cd9940718cf3ea08b5f752b0fc0e1724ad" "2206dac49b3a511f8e3312163f65e6e0f78d47a7b8566470c12df72d7c2a0e6c" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.s.inj "user constant" .inherited (.inherited [`A.s.noConfusion])
    "17a89cb6f7c0554559dffb423aa094e09e2a1941b9cc68fd75461cbec785c59e" "2f88e5f13ec4b702e37219732568e11ba994e2a7b6691b5c0830b82375db98df" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.s.injEq "user constant" .inherited (.inherited [`A.s.inj])
    "a051501e65fcf2cde163af7b6bab4c5673da095f10c10244b19042ae0aa8c4d7" "bef07c557385cd63aa1a8decea6e722dd7d19c3a0ac4b5738badfeb73ab13368" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.s.noConfusion "user constant" .inherited (.inherited [`A.noConfusion])
    "2d521d1fa99a3b74bfaecf8101f69172b2a4d26d0873cbe692f223e2a451d2a5" "cc02b3e015b9c04bd6b446bb22840111ab16ef21222a8e3e63636d98196eefdc" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.s.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst, `C._sizeOf_inst])
    "a3b1225ae3473d9d3271495559449a3496a3fb272c503853962af6d35a87c83c" "da2178735e270d1e3c5f87be18a2dc09fe6fe52ccd11f621405b920466359563" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.z.elim "user constant" .inherited (.inherited [`A.ctorElim, `A.ctorIdx])
    "d028eabb3376dc94cb3bca9b2e91a8495ecb7e08da0259e10c9382780f5d12c3" "f5f5a0721b98bc3b4640c38c550545052ac3d61f45c8c73afbce7c6b1ad6440e" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `A.z.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "1c5c0e6939b1ff906f3f6e9c08fd919cb710d43979f17f8b718f3d4fa1d0a2ac" "93d2881c45b1b27520c7a4a18647425c18660298402e7c2bf6fd52fd3bc722a6" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_2])
    "91fe08946a3682f5c478201ed18493e1a93b178a956790722e289a48104d1411" "2dbebfb1fac3b5d4b73ab3f78e701cc0ebaab9df52c0dac8768ea14ec05d0420" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6592d6b48818dbd9faa38a6d7a6d6605e1d1b570be9bdcfec1ecaddef860dd5f" "a0e4f22c6582e6e416d45942fc12c02fce1f00e7769072e0e22d797a30cd5857" "type.∀.body.∀.dom.∀.dom"
]

/-- Entries 400 to 599. -/
def part2 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "18f208088e87a88bec0c4126ca8b2dbaa72b79089e906bc4f9a20588e0f6bcf6" "912bd70b8882a0a8edcdedd4bacf227b2ee414c53361472a78a435d23014fc4d" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a3ebe2ea2de1a87beba846a93f66b94045a9669da5a0ca109a809f2f34fbad10" "de4e80676d1747d0fb4885472f5826e9a0cf2d05130427fa0d7d11071de9948c" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b68b3f48312ceb93a4fe4c3418f611e657f9d2da65b200d7e528ce8eb6827444" "0a44589caea0780d7661277e49d3038e452a247d1063563cd894387113afed94" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root false true false)
    "f3fd05ba1dbe2484d997b7227533dd83148dca45fd75b452c6db1146ccf84e69" "b72a03924d3972205ad69e5834cffa1e84f2045463422120a46b4e202a293d30" "value.λ.body.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.ctorElim "user constant" .inherited (.inherited [`C.ctorIdx, `C.casesOn])
    "471b38f71db9f7f88847f579fdf823d1f4c163ba0f0d233f25e28156fed4ba62" "8a963951b6bcbf7f1489d525d82a3e08da9ee06a5f74ebd389ce7736b452422a" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.ctorIdx "user constant" .inherited (.inherited [`C.casesOn])
    "e9be2bc93c9281f14765682407b6449e5fb2536390d8490e308ac8ed69dfcd11" "7b07082724ac4b3bd5d9f8dda5f506dda22b8367053e4e939565f14df1ce811a" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.e.elim "user constant" .inherited (.inherited [`C.ctorElim, `C.ctorIdx])
    "82c9f61017a5d780cbf81f57770c41d45a833794dd60bfac4eb19a4088184c27" "01d01359252339cf4423e279e7a6740e338e1315e2d911f12ed6da351b9c4537" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.e.sizeOf_spec "user constant" .inherited (.inherited [`C._sizeOf_inst])
    "a56bcaba6f9e79817580fd8308d592489008db84da4950b38a90c9a3ca2d4c65" "76305e269fdaf43221a49974ad82e3423339731c27596657304e6b7a72902d0d" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.n.elim "user constant" .inherited (.inherited [`C.ctorElim, `C.ctorIdx])
    "ba35f5b8bbcb261105385fc0c1450a93871dd18db696c5374258849bda16a9db" "cd40b7bee2a62b83e89eaeb3414833b0a9548ae670e917e637616552376971cd" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.n.inj "user constant" .inherited (.inherited [`C.n.noConfusion])
    "5261432f246e7d049271e245bec5bfc11aae72507a6949e4ae1404cd863dcb47" "ed45c66fe6405062444b9eb76573493b514442828d081536b2badb150cbe0190" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.n.injEq "user constant" .inherited (.inherited [`C.n.inj])
    "e1cfcc108ee8d778870e9eea8a2b56733f245d8d87c5d0f7e733da10ccdc6f8e" "2a426282937032c6f38240b180778d734b34d2a89badfb7878326a05b8b402b5" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.n.noConfusion "user constant" .inherited (.inherited [`C.noConfusion])
    "f72ee5ebd980711b29285a228787e0da55ff2f4e027b6f5a2b790d15c3662096" "b19d08efabe493d165f4a3d146ed41c824bc211241412304474b7a54da82f1f2" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.n.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst, `C._sizeOf_inst])
    "53cb04d58b9aaaf53b7b54cc7110020950a5864528d0d9fc48c819c9eafc86d4" "fd62962f3018f1c04fd51008a77f0842d97cbc85a9f942d2fe509a4df24128c3" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.noConfusion "user constant" .inherited (.inherited [`C.noConfusionType, `C.casesOn])
    "46455d14178d43dbb20ac69e2467cc4fe1ce853f6ef57f4db2455e706413adf8" "1cd6267b96a16e9e5ac4f3113e389375c5ae77fbbd44bfe375423ed70f8667cb" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.noConfusionType "user constant" .inherited (.inherited [`C.casesOn])
    "a9b26c84bd9894e5099db4a91e7841a53bdd91d8da391426578c17ca2c656ddd" "aae1fdc729824c6e3a668a4fa473b7e7bea7d0ef5fd03b5002f70aa1de6782ae" "",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c84b13272edeb24925d656bce950f924180d9364ce5eea6b00eb45201526e154" "06ef6b703cd4afcaba7654297a591a5a9cbded813638e5b28bc3a0ca4f63659d" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F1_Collapse2p1 "twin" "orig" `C.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8f13608c4f86cee45f69d66cabc4adaf8fffb40022460077ea455adb01ed7adb" "a260b1d75f97387420ad333375cbbcd5902840ea42d51341d234f5af9fcab179" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "b7026d7e4027e86fbe090ab636abd8a416c3c971b1d812279d35834decbb2206" "d21ddd05d636f844de163fe5ff3c0ae7a9fe49623a4d8044f70891ca4bf74613" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A._sizeOf_3 "sizeOf family" .o11aPending .onlyB
    "-" "36110cd2e8e6fb2938574fc6b5491a1af20c3602a899dc7fb60e1972784a9fd7" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A._sizeOf_3_eq "sizeOf family" .o11aPending .onlyB
    "-" "42d337e078053600f22d2f6fea2ae0adfade6b64bacf1bda325652ce68e95de8" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "c9d5273c0cd7358fdd658363e800e780d218f2dbb4a459e54809caa2b5771f70" "5e96e26f1dd45f4cfbe51966f0f78fbb3d1d4c2648face40b909799e21b2495b" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.below "block auxiliary" .image .onlyB
    "-" "91a28ffcb5f56be00705de97a94f11381b1b728b8a48bf9a3db14947c8852e4a" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.below_1 "block auxiliary" .image .onlyB
    "-" "4c1ce33b261f2cae0d311e964844e499bc279b18639374368fb2ac14f3794be9" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.brecOn "block auxiliary" .image .onlyB
    "-" "101a1262072c241fafe779f7d9c9b95943360e1719cb505727376b242ed63f15" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.brecOn.eq "block auxiliary" .image .onlyB
    "-" "cff3047e533c51d61936b58dd97ecac65c1577e3a4af3d0d4b3c07fd6dde717a" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.brecOn.go "block auxiliary" .image .onlyB
    "-" "31c4e62e6a96fb006d184073c227f84d56b7c3e8be12c9f3d7add6fde2f2c440" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.brecOn_1 "block auxiliary" .image .onlyB
    "-" "784ce6e8ca906b0a43be68efe5515db6bc763f9a5e7ca5efdfc877fab39bbb4f" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.brecOn_1.eq "block auxiliary" .image .onlyB
    "-" "38199ce4669f45f08fd939f42b385bb6a6bed7b033f2adc2580b32dfab4b780a" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.brecOn_1.go "block auxiliary" .image .onlyB
    "-" "428529884300be0c4637b83aabc365aad465da6b7e9229f32630d7323bc95690" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.mk.inj "user constant" .inherited (.inherited [`A.mk.noConfusion])
    "a56748a2d93254e4060a9e9cb23d30d6622e6139eda5d5e17b09d21d00d2fbcc" "f00c5f2afcddae630d6cc06ba722be8f9800500e9e952a62faef16e223d256f6" "",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.mk.injEq "user constant" .inherited (.inherited [`A.mk.inj])
    "89791cf3e44a17692aff1bddd0e108f5b0332e2271a65c71da6594eb1cd20c34" "b304eb0bbd5e2d008befa102c50107d6782af49fc5d2d8d30f198c628dd0b44f" "",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.mk.noConfusion "user constant" .inherited (.inherited [`A.noConfusion])
    "8ffccbc5764cc9e8a2c4f8332fe3f4c5777b81a73fad30f4dce98b541d9979dd" "7e98cf4a6fbb82c2b04156a78f93917206131d182a6d3cf99f49c2d8e35b3f37" "",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.mk.sizeOf_spec "sizeOf family" .o11aPending (.root false true false)
    "62da2845006a89ddbf242ec098db179137bec49fd23f804e990969d2cc35c5d3" "c47e4738b2c89a7c1a32c0466f3694cfa40cda5127f84d5b82ea64e19fd5eb5f" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.noConfusion "user constant" .inherited (.inherited [`A.noConfusionType])
    "e33da13f8a61384e608ac707e002e06475c9f46458d8d67683c6ac6e3ca350ee" "fa43fa46b46abd4706092b08394c6d01333002b89b0087776986ddbf4bf0cd62" "",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "030ae1156180b1ac49ed4f5eec6a82408207719c56bb8724462953ced6d7dea4" "9a49dfadf6985009d708e56ae4505210b53d0abfda8152b37dedbc7a5751f3ec" "",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "001293f7f7890c8941d95ddff31e3d9e6a4bba42204d00a8a9da983677fec23d" "c6f4c9ef77bf9bb5326f5f668dae16b86df01b495c9565c39c55678c2966f57d" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1ed4553a14482ddca6bdd6edad60854958ec2a5487f219b7ea2746affb1e8b0d" "f5d32e768429ef56dcfd352f7c03888b2524947c48be691507328bf134e6bd55" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.rec_1 "block auxiliary" .image .onlyB
    "-" "c7f59215d14ef2b35ca5bbfd749f16dee94336156e2fcdfcca2525ddcca640c4" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.below "block auxiliary" .image .onlyB
    "-" "b0782747033c62bdd93ce0f6e1e54493b17cb7634107527fe80f240ae973e2fd" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.brecOn "block auxiliary" .image .onlyB
    "-" "922bbf33b177831e0ecbe06d0fccbd2b40428e64db7e38b38a64fa633bb10e59" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.brecOn.eq "block auxiliary" .image .onlyB
    "-" "877826a718d6a20dd2f42c33cc100acfd2c9e36232b8656f864a043c75463cff" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.brecOn.go "block auxiliary" .image .onlyB
    "-" "f280f4cd05ec7ca01893c2aceecfe2a89b1f0a1cf31c8c06e73102cfa9d1bc1d" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.noConfusion "noConfusion" .pendingNoConfusion (.root false true false)
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "abd3af6627f5d3c14eab547715953d68eb79793adee7b6b73ad6b4b0c82581f3" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "a13871a9d6c0f80bec0828b0d0bb5b706bcaf3036c0fd63791655cb1bf8a9100" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "62097ef059b0e99d2abee440f8691386cb2afd54beb68a2cf3a336a726852a0b" "38a0af07b0206343309225612792bd3d2c1d87b1b9b1e9c54c9dc98ee08115e1" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dfa05d5f71d78161d48645eae61fe74366ed0196a36d361827c4b360c8af6812" "239c0dde0c354de1bb9ac55d18211c95299ec5562eb98e636350c6c2a02a7730" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "3b894264fb2b61fa899db79e1b64ace46e4c3391452a5711668292b060f6fffa" "985ff08fa8d8e09ddbd17874f2445dd1f3f85871e39cd2cc893d34d035bf3939" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A._sizeOf_2 "sizeOf family" .o11aPending (.root false true false)
    "c0d565ce645018032c7aae2532bd445df402682958293efbd1c1d5ed84832a01" "176446dcc09322674d80c85aaaf0fed03cfe9101bc64a26832c353bc438131be" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A._sizeOf_2_eq "sizeOf family" .o11aPending .onlyA
    "203831d813d2dd11fdb6657a41dbb43dc270341bb11c039dae14f3c436c1dd12" "-" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A._sizeOf_3_eq "sizeOf family" .o11aPending .onlyB
    "-" "8c3d5c60cf7778f688209b71df25948bfcfb2d650b0b54da4675a6e5aa7239a4" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A._sizeOf_4 "sizeOf family" .o11aPending .onlyB
    "-" "cecdff16d6ada8becbc5bbe3f4bc8fad301798755455bcbb2c19635ab096f020" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor; the one-sided member of the numbered family (`_sizeOf_3` in the old branch's record: generated numbered names now pair in name order)",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A._sizeOf_4_eq "sizeOf family" .o11aPending .onlyB
    "-" "21f302727c37ec9d8f63614ec36d9cd84de11655847179f8a32a5d573f4f5eb1" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor; the one-sided member of the numbered family (`_sizeOf_3` in the old branch's record: generated numbered names now pair in name order)",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "468712bc2de1630f0ac171407ec951df386bbd97f23749d2155361d355acf7db" "9ba220135b636cfcd3103987d63805193fe8769e81bca67b5f7c9000f8467824" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "393c19bcfc3d36debd4a341f75d8d9f92e1565f200b7eee52aec412d7576dc80" "87204dd3ef5f87d5aab746826f1541c203b25d6aa307c28e7475486cfed1ea1f" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.below_1 "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d7f5d16bbb3c95c180ccf2e4fc1be40b70d3c86cb5d2017748ff4fc9abb5e306" "c3638aebb88305b4e2b92bd13adbdf2a8cce0444d4762491caca86b9e1f54df1" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.below_2 "block auxiliary" .image .onlyB
    "-" "7d378e78f60865a8c8d138c784c692a57db3eeb5b4bbb357035c5454a8344767" "" "nested auxiliary of the collapsed member (`List B`, merged into `List A` by collapse)",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "708995f2027a2687064e5ce8c97e8746ca517fe0c46363bf775135e674447f37" "87c676aff09edbd436a0b360253062a15c90ed25fc443fbe153992a0718b7bb9" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "326fa2b5b47d23e5d607f0c447c0bdbd4f53ca35962801619dc3e580f991b329" "61dd69e95c2fcb23ddc97f2122c0988d59280a1efd08d97f52565201049989b3" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2fa3dba45c3558e1e33fae597b0aff662547030205229969c417681aee0fa2b9" "a792294b5b4f6eab16438a4c7c9b33b663ee1837d38118ec3bd331fb7b436a83" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.brecOn_1 "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6739616e5d84bf5a9240792f0588464613e15c9a479545a31b4acad21081205a" "23241a7ae7a117e26c5ac8bf5b07dc815792e0cae072476653b793ab69172edc" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.brecOn_1.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0e365d4cda30bffdafe0e6576d147fc6fc288cafa2839e85680713603bafa0f2" "abfd8503e6f42316c34d681a4448ff7d06627191285d4881f476cea00ae1931d" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.brecOn_1.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "bc2cc1290f485c52fa239c5176521e5ca35616fa432ecaf10746e5dada00439b" "c7f7998ec5cd3a4e09e1cf01545908fe85c0c64e8fde7cc33fba1a1b95752f74" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.brecOn_2 "block auxiliary" .image .onlyB
    "-" "4fe4c4c69b6d9322e9d935ee73611d91193604fe308041e874e11417ffbde53e" "" "nested auxiliary of the collapsed member (`List B`, merged into `List A` by collapse)",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.brecOn_2.eq "block auxiliary" .image .onlyB
    "-" "d6443541501e9f3812791e1acf4bfec5ef1c281db165d8e450202bf5e056a6d6" "" "nested auxiliary of the collapsed member (`List B`, merged into `List A` by collapse)",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.brecOn_2.go "block auxiliary" .image .onlyB
    "-" "0e49cae4a621589188cddff655ffba318b2456427d397374218abbf90caeffa1" "" "nested auxiliary of the collapsed member (`List B`, merged into `List A` by collapse)",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root false true false)
    "b5129a4db9760b668b3ce4c54bef6dde6f2ae7289e7da1820aebf54259d5c95c" "aa5294a61e636d9f8b9b40d3221b21df44c1c09133fc6472c800a8fa8e2bea3c" "value.λ.body.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.ctorElim "user constant" .inherited (.inherited [`A.casesOn, `A.ctorIdx])
    "cdf71ad7133b27c4ad42bf2a8913c0c166291e291e0c694cb79f9604b5f527d2" "01891a9000315265b2065b0ea36e9838c08426f294e29187aa36593004646eab" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.ctorIdx "user constant" .inherited (.inherited [`A.casesOn])
    "c00129f0fdcc04b1f23eb5d033abc1588e2b70f6e2569ce9b6bd5df9d12f4b1d" "318d7b7597afe40d4ed767995ba25dee8d6ce55cf124807f6d0f560f206f2194" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.leaf.elim "user constant" .inherited (.inherited [`A.ctorIdx, `A.ctorElim])
    "787244bf421dd3dae973713845b31ca206d9f62ac53ca92dc428effee645a1b9" "1070795a89583cb555c0e304196e0279d82306135d0caef34f3568264b6cf5b1" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.leaf.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "fecb57ac5ee4d217b6b500abc2c76553bc568e58d520aaa1c107c8e31a889527" "413914a3589a3d83e9f71338491d6cb7128a287aa9eae89f88be11be284537da" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.noConfusion "user constant" .inherited (.inherited [`A.casesOn, `A.noConfusionType])
    "9467af5e6275aca62adbb52893986ae8fee0133cdd61c1f9ebbd54110ef8963d" "b4080636b1fc2fd1c72cccd535c2d97c56af3355aada93a5f7f67266c6a7c9a8" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.noConfusionType "user constant" .inherited (.inherited [`A.casesOn])
    "1ea2dbced6cccbd13cc2fed49624085a5ec614d60ecddc7d534b34f3ab655fce" "efea47ec89bfe3948eb0b0385e2baf9646f3e972a6cb64f7f1ad58600459e3c5" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.node.elim "user constant" .inherited (.inherited [`A.ctorIdx, `A.ctorElim])
    "40ddd9eef32e24ee4ded078992b1037698c1ac9011878c9b630a0fdfa502fb18" "6bdc183f5e3d097a041b0ee16fb34eac0c1126681bc9bf2647b1837117b10c33" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.node.inj "user constant" .inherited (.inherited [`A.node.noConfusion])
    "2cac384d7ac546c6d236663e5c81f0bfadbd463e1311d26cab8e0ee51b726791" "570ba64ccffa3d5767ccb526a4b75ab9075909142348fec3b0be643c830354f3" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.node.injEq "user constant" .inherited (.inherited [`A.node.inj])
    "0898dda0d47e92d050ab5c93d410eb4561621824d2f9b506322fd7985a67e162" "24f5ded008758deed117c7e263f75f3e4d460a6f1b1d0eed4f1647650aa2ca1c" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.node.noConfusion "user constant" .inherited (.inherited [`A.noConfusion])
    "3b97266ece91e440ed13a1a4fa7c781d59f3ad93b4ce70eee7d4583871348852" "e2008047c54d1107ebfa632aeeeb3ec975b0762f4e00214de244b1e4a9ddf6b6" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.node.sizeOf_spec "sizeOf family" .o11aPending (.root false true false)
    "766d18254b7fe03d966e71b5821070ee77821ca810d179f405ded4c101530f17" "1022b6f55c92e7b990d8fb796cc745723f1d8ea8fa22678833b4495ad353cb0a" "value.λ.body.@2.fn",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "71e319881bd6ac8553779c53aadd388f7929e338ae20c90950fdc5d38c78142a" "aaa265cf1b22cc4d7214bf68b6d27d665939e2395b5da72eb72322031cb42e23" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c997c3f635a8f7df1d6b74a1328fbe386ebe7e057aaf84e2a0a0aecadafc13d6" "e58018a42149877be16f046475b20dd0e6ef7b7f71028a1ec12f2ed676c65166" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.rec_1 "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "257eb892f1c8b97c2e18a13a2f390629e3a9594fe2cddb6c0042e3004e633d56" "7047c78981dad793438fc076e08bd6a65b22dee19ce8aab1a76a1e4850451079" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.size "caller of a changed block" .pendingCollapse (.root false true false)
    "df9a1e202e7159fc0eb3faa141298171578ba209326c1308a7f646675ef22124" "6108a315aa49de15fe96309e59bc50fa2c3d22d23d7e4bfeae07ee1879d6d421" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.size._f "caller of a changed block" .pendingCollapse (.root true true false)
    "e1b2e6e6493ede7a08c11159867ee70d0a62b9d86d4e838117f0981f10d797f8" "0c23b240307f068960cb125261c810260a921f19cebb2d6524c1141d5a765b7c" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.size._sunfold "user constant" .inherited (.inherited [`A.size.match_1, `sizeL])
    "0db65e72c9423c5689a068bd3e74933157a6922151de8211058c3b392902a5e5" "0bebf38118fe7d609235a75ca5063b338f94c51a518cad4eee1da38efe5a4b28" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.size._unsafe_rec "user constant" .inherited (.inherited [`A.size.match_1, `sizeL._unsafe_rec])
    "307bde7844f927e0e89b1a3cd617c093b241b6d80620dd56ee1826fd37d28325" "cca965d805edbe965f54b5759b744659cb7f7f6582e9e60633ef344f4f363145" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.size.match_1 "user constant" .inherited (.inherited [`A.casesOn])
    "2422320aa671b881b3e541524aae2380ca5f0382b97419a16afc01bca9f55f35" "1bcf5426b965b2d082588d8c5da557eeccc61e46b1cdabebc26d598629c72638" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `r "caller of a changed block" .collapseArms (.root true false false)
    "86299fa8f0c366ae2631be68e91d8b14c1b3e342e11670eaeba6dcc994681448" "49822e4d6c75b01ed81bb67d043894a47b725204791f3043b955ecf4b19d45bb" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `sizeL "caller of a changed block" .pendingCollapse (.root false true false)
    "7b6608b149fec240854e97969576ad96be59e29b5818cdeda80d3bd4c7e0f092" "6d17c51811a9b5d475dae7aee8e86a7753c634d73d631808a6c029aa8e13992f" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `sizeL._f "caller of a changed block" .pendingCollapse (.root true true false)
    "037b5de95dd4ac848ea561b8f9a4214f47c596a843db366f7dae3d009456d2ba" "30183927ded7446d9381eac438342ace030a0f6666a4992a646a9369e2558b5a" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `sizeL._sunfold "user constant" .inherited (.inherited [`sizeL, `A.size])
    "328e1c6620768a98be905083dfab01a606c5147e5cc0f98123862e76ed34c385" "f33e7560cce38b1a06f0aa5fc33bb71e5d0eec413cf00caf989db61840b219ea" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `sizeL._unsafe_rec "user constant" .inherited (.inherited [`A.size._unsafe_rec, `sizeL._unsafe_rec])
    "6b1465d98c72bd70854434743bd7eb0804cd87e3b353d3e5b7f7101e45ae2c8b" "8badaf5a31e92ba97ff6f55a6f299a4ff92590edbc5025ef4453014645e8ff20" "",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `t "caller of a changed block" .pendingCollapse (.root false true false)
    "66f0298784b387cef1912fed3629e137fe56806fb4abf9a6f660518c7632407c" "f6fcd4a1a64564815f219c9a8c370c2acf3a799341be5638f0d9f0ac5fcf7fd9" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.PropCollapse "twin" "orig" `P.below "caller of a changed block" .indPredBelow (.root true false false)
    "6f1fe7f3c3dd2d2f35d7dfbe43f9ccbf0555b1a249a68b87a602b59443a38b91" "0c325996612ad7d8f4bf11558c17d896ebff1a3ac3dc94c7bed2b27c2a1357bb" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.PropCollapse "twin" "orig" `P.below.casesOn "caller of a changed block" .indPredBelow (.root true true false)
    "c3c96567ad6ac1122ac549909bf588eea5853da47c6c3fa42d7851d6ff95a26a" "e42360053f09b8aae33d36a2d277a02fad1287290fc7b9130488433e482abe1d" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropCollapse "twin" "orig" `P.below.rec "caller of a changed block" .indPredBelow (.root true true false)
    "e786c4d7b1e58e50e27a3029cc385ad678b18a3e6e449d0f5b83ac7172b11498" "52a40624bd45239f91b826780deeb53ea5df25cdaedbad812897328ba280ffdd" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropCollapse "twin" "orig" `P.below.step "caller of a changed block" .indPredBelow (.root true false false)
    "c7d2ff48d3c2a61b7874e7adb856a76e797630169e66d522132779611a8fba94" "623938b3c45e295931a70e88d9edafcf719bb210e1ec831fbdb3e9d31960a9b0" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.PropCollapse "twin" "orig" `P.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "325030773752e6221e81047702555e42b20ae97d90394812357fa6de8451b25a" "8df4c3df360355864f579006ad91d54dfda599b85d435d9efbb2df7397d343fd" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.PropCollapse "twin" "orig" `P.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "17278107c75276fd55ec867d7ce1dbb30e5ab6b0e4a8554c5cdfa173d9a2e3c2" "41f8d83349a7e1a2cab13e105c6481c4f37d316917b0160b938b93c6911e92ca" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropCollapse "twin" "orig" `P.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "053e75bc2248b024827e23daa4544e8d41ba628579c8c7f18df3455da42755d6" "d0541858189f80e9b4a1af5109fa71436230daf4dbc7b198a630db37d7934277" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropCollapse "twin" "orig" `P.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "155344c30c98a2f2d5af2888ddcfcd58ad5bf73f83b46a7f020f896d32c3bda6" "559e27d699ea73daa701db2d4420ee71ce322d21905a917c2810303c558c1c0d" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropCollapse "twin" "orig" `p_cases "user constant over the block" .pendingCollapse (.root false true false)
    "6a99811d2992052ed277106b72cc898e60dcd6a850b6bdcbd9bd9c8945cac093" "9c4d1367e40ad5a1bac4b8dfe5790e00a0f9de37a8fc3676c912ef37a71f096a" "value.λ.body.fn" "`cases` on a collapsed Prop pair (O8)",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `P1.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2efa4bbd958d459004f3a93a7400ab7ba98da1688554df3e17a1fcbd2439a636" "757541206477da5f1aed7a4f6069168ddc96ad6897815cb4215d140048bd3c09" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `P1.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d2d89c26f75ac727358474a7f94e4f3243cda39617619200efcd322e701c98d3" "a0d6a9f7105a2e25f72767aa82e60b9102aa3a36dc698a74ffa13f4644e264d2" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `P1.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b39239fea24258438423f0a464b8cb32cacc283668fb10d77328c32e0ecd90f3" "43a1bbd268cfc7e918ba0b1029244ef4b94277d7ad55c112ec6c72d09231cc54" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `P2.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "26e056cdb9eb90cb0103dfebbba0506eae6ab1fa8b4e892ba0c478e29fc7d3eb" "fe0ef7c47acd826641679345d88ce32d6135caf09230ac971cd6c06ce0952de1" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `P2.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "02631bff3dbd7aec90361b15db1201ea59596ce01c9fdf0e8249a4f142b0c0ec" "f43bfe52374537caa6bab6039bb47e348205dd64f3ab201706bf0c920c4c6c5a" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `P2.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "df87562805b13b3da098f668c41c2e2a1fa7a34c8c6955da0a176da010716375" "7b17790983f970ed990d6887a9a66dcfdd2d2d1f3269f5d84e966d6f9afd84c8" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `Q1.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2efa4bbd958d459004f3a93a7400ab7ba98da1688554df3e17a1fcbd2439a636" "757541206477da5f1aed7a4f6069168ddc96ad6897815cb4215d140048bd3c09" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `Q1.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d2d89c26f75ac727358474a7f94e4f3243cda39617619200efcd322e701c98d3" "8c91a944c6505733a4f525d2b3dd0dae7c5adad9af49ced202f90c5b8ba73866" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `Q1.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b39239fea24258438423f0a464b8cb32cacc283668fb10d77328c32e0ecd90f3" "33f4863c8256713a69dfa6a0a8444028a3702f46e37f9eee0cd6dd8398b1a1e4" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `Q2.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2efa4bbd958d459004f3a93a7400ab7ba98da1688554df3e17a1fcbd2439a636" "757541206477da5f1aed7a4f6069168ddc96ad6897815cb4215d140048bd3c09" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `Q2.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d2d89c26f75ac727358474a7f94e4f3243cda39617619200efcd322e701c98d3" "233d6fa3e66563b7daa38b5edd161c4e07004ea7a57c053da9fa854ecf0ff06a" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `Q2.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b39239fea24258438423f0a464b8cb32cacc283668fb10d77328c32e0ecd90f3" "719e3d4a07995c1f38dca4e53b2759c8dd40a1215602e62195950c377f1d86a4" "kind",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `p1 "caller of a changed block" .pendingPasses (.root false true false)
    "fe79fec6d1b0c2a7a6511dd85a3ae5407ce9f77705e235b76cbdab970db69667" "f05a5067cb7234e0422da400d9bd4fa2a9a6d12ac0f21212a60de263cabdf944" "value.λ.body.fn" "user of a split Prop member recursor (WB PropSplit: universe count; images, A3)",
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `q1 "caller of a changed block" .pendingPasses (.root false true false)
    "fe79fec6d1b0c2a7a6511dd85a3ae5407ce9f77705e235b76cbdab970db69667" "f05a5067cb7234e0422da400d9bd4fa2a9a6d12ac0f21212a60de263cabdf944" "value.λ.body.fn" "user of a split Prop member recursor (WB PropSplit: universe count; images, A3)",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "f3f9cc6a6602b8596c5bfbbc20987f4be2892697fb83368bcf1e2283b3f68a7b" "3065cd9acad534a6fd9f24cd399806c9e03b8a4aaa49b7ea7e324e3bf081fd59" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "0bb01d3cc9090441a4b6e2ebc8038a1ff31e3e06e850342abf7a5be8e27837a3" "26b433d08ab2345ae0ee9f95833f95fb9da3bc1a4f968bacb74551ae3d5945b5" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.a.elim "user constant" .inherited (.inherited [`A.ctorIdx, `A.ctorElim])
    "16107ddc18248b7ccccad13cc7b76b39febcc21962b84984ab8dd2070a21bbe0" "c75198d862f70349fc93d3883e2301c8028705585c85274afd7814cfb80cee33" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.a.inj "user constant" .inherited (.inherited [`A.a.noConfusion])
    "3fb46b0bb6ee82b33e855925ffa40315b616788be62d07411c4ffc45f51565a8" "d2c7d5c9d625bbd92169ae55fb85ce0d8afceb21236488e38ea22089bbd07848" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.a.injEq "user constant" .inherited (.inherited [`A.a.inj])
    "1917356cd419691dc94a7a54c0ec9781350524e1244c139252f96b6e9d8c7a20" "4e2910d8eab1e269cc0435b2b18d74948a4385560094cd24445193c75eea540a" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.a.noConfusion "user constant" .inherited (.inherited [`A.noConfusion])
    "b0a8929138060d1c635634bdcfa7cedd7c2cfba0cc376de8c5de511d3cf8cc5b" "f1a2109cfe6e51882ded42fe36533c37904790acd0372b1547d3eb4b26cff2c7" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.a.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "853a2628d1ceb69d1a65b68133be82b294e6575e9d0458cddaf8f2b5f57dc8fb" "4b36d340ce269a600d50891be6ae5a7280e18e5fa6bce619838bae3bf41a5f3e" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a17da90a847d92e8024d980f152101a3ee8f2096baa675ddc6cb69732b2d1ebc" "c285ec21b9ac97c61d17ed6637138e172c9392126700a2e246f27d4ce8808778" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fd85ad262719d83a12fc1d950e9cbab5a15eddf153ec38dbcd5fc507216927a7" "7de70c7cd8763f5d9c2fe8d82c4607a9394134be12e8c6a238fd838823b0b44a" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ab8acb574825a6d2c00a02642757cc90d37a478525eab15ffd76f53041572b70" "0a2b7d64c4838b3c2d288531867c0bb35e8696aeca3342796a78b20be4a1d178" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "597541cb7d1515de8618e8ab7f7f7e0f4f5693cfb3ea6be3dd1cb1fd8891e662" "064bc2e72f73d385c43914ee836d339161cd28662c58d3d5547ce8b5b0a7874b" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root false true false)
    "937374ed09b8b62f36ef75f06f1ee46dd487c7a9f3e74db919bde48bb76b2cc6" "c2d4661d41cb812f18de5092c847722e9806f220618586cc56e8cdfbb3437852" "value.λ.body.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.ctorElim "user constant" .inherited (.inherited [`A.ctorIdx, `A.casesOn])
    "f3db120744d25a57d5535442d6bb7d0923b45b056da302e19f82067a40f3f702" "42f88d1bd9a21685eb392c9496827ef142d22da18bb3b36fc96ead1d39603e72" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.ctorIdx "user constant" .inherited (.inherited [`A.casesOn])
    "2613f00a4d5923be077387ceeb87f0fe68cd361ae987bd818e066f6042264c17" "196fb28b5c37f4f0a9e1ae439f40f0042e492900446bc51a7ad3c7f343fc4173" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.f "caller of a changed block" .collapseArms (.root false true false)
    "eb51753163b5c03ca62651f58f5819aee628d81d70bb82576db800be3617ac21" "a858010777fc36ad93c67367919660ea534599d50e50a171afc95e3b1b179dfd" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.f._f "user constant over the block" .collapseArms (.root true true false)
    "e800823c91a33fa63d7fde3629e0a00848f7316f8d091c7541922145298bb764" "2cf15299c74f86ce42cd3b7ebb4c9d4ac0acf49ced21f56cb934c95bbb028781" "type.∀.body.∀.dom" "collapsed pair with different arms (WB-B4; refused after A0)",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.f._sunfold "user constant" .inherited (.inherited [`A.f.match_1, `B.g])
    "20c99d4437f9bab6f7f011cdc25dd9ee8fa9bb6e423ca29ac2b0c0ccae5b2d0b" "c0062b9a589bea8acbb9944c905c73a213b4ff44ce01e583fd3b33e208ae17da" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.f._unsafe_rec "user constant" .inherited (.inherited [`A.f.match_1, `B.g._unsafe_rec])
    "dd790a317dba717283244433d2b7a8f74ba197521d9641364b6ee89458b7865a" "6a5da6c91de2cd0004f6d4c5d24e9989114c77f50ea7bba489b9d15fe8e7dec7" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.f.match_1 "user constant" .inherited (.inherited [`A.casesOn])
    "8456b93a61151feea7878938feb7e719ffbef279f28f05c3e798f036ff56fa5c" "1e8fb2d16072f99c92b9f9ef07e3d8795d61adf1ed4060b2c058a9cd11fca046" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.nil.elim "user constant" .inherited (.inherited [`A.ctorIdx, `A.ctorElim])
    "bbb6ffe937a7d246d1cd455b1e4f49eaae681c4fdeed60078775e57fb5a1dad9" "885aeba0ee1276695f887830b870ba5f30bc5939f7d81c67e04143ce9985139c" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.nil.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "a572550a6184263f6d3999ca82aa84c41b6e33ef8fa4c1ab4a4b72e95496e4be" "54b4288db5d14dfa34199cb58d10ca65aa4ba1ce70d219649534ee53b4644389" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.noConfusion "user constant" .inherited (.inherited [`A.casesOn, `A.noConfusionType])
    "567f68cba689df3ecee088d50c35c5224bc83709602c1ec997dbd49835743974" "ad1f01e0b43bcddb903a7578e07b8dc94139187e04452c5398f67da4f4423972" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.noConfusionType "user constant" .inherited (.inherited [`A.casesOn])
    "2028e58d86f9a54b9e53c4f4201b53ccac824e2a3733a06ff4c6a43d5d859b51" "5d8cc79549e7987db34159f9e5b36c853b531ad363fa70440bef847652f624e5" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c8322e03d558f85a8edc7fe68524013880ad0bbcb7dc890136d247154b230992" "df681a33a70885d2467f0443ffbb11c3f604824a24a4701b09dd0219d2cffb23" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "32038f41f6815ac7654830d5262dd2880649a594097cc8af729505ce45c84ef9" "365b5efab9c077da18be5bde39551085bacabd0e875002da8e1ce84bda4be760" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `B.g "caller of a changed block" .collapseArms (.root false true false)
    "134a7a9f34fc485fac30cec655ec00100c540956a105cdcd37d7e86c98ffe269" "267441cde0a9b0ffa99c9726d6c3e25469b5b5b6cad01642e8db84ad47c4d57f" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `B.g._f "user constant over the block" .collapseArms (.root true true false)
    "613f59a1c61670d3010245031560fec838787e2cd97f1de4c5c4481c24310a3a" "92f1d8eb80de18ca8d9ed32d830eb3f7890650b6de1ab4df330cde6bdb38fe9f" "type.∀.body.∀.dom" "collapsed pair with different arms (WB-B4; refused after A0)",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `B.g._sunfold "caller of a changed block" .collapseArms (.root false true false)
    "5e43692a9ebf82c357e0fcf3aae38885984ad14a9e9470afebc0f241434c57bc" "17ed2f502d828a17d0f3863f76275cfca47dd21f28c624a60ac20c06a784bdd1" "value.λ.body.fn",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `B.g._unsafe_rec "caller of a changed block" .collapseArms (.root false true false)
    "338e77b8d5f131f717be03eb216b313a1c044f79969ee176704c5333dc825c9e" "b625939fef24e186c022838e7bf58b1f9b3a742406fa89eae3141e1f1d493f52" "value.λ.body.fn",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `B.g.match_1 "matcher over the block" .collapseArms .onlyB
    "-" "c30016faa606a224ce3dd9f0b96efd961e8832739fb43a1f4716835fa9fa5e9a" "" "the source `B.g` matches on `B` with its own matcher; the twin's `B.g` matches on `A`, where Lean reuses `A.f.match_1`, so the source's second matcher has no counterpart",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `f "caller of a changed block" .collapseArms (.root false true false)
    "3c9135f1e3f63dfd29969a8d01c25a8645a4a945598f61c6a26732dd711d6ab6" "e455151a6dd2d0e6724ad865f06a168931ca4ab29b90f2fcec5f304dc799d772" "value",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `f_ab "caller of a changed block" .collapseArms .onlyB
    "-" "447a96833b2155f7986c9f91f22eb655dbf158a1624d7f67f4ed8934ef6e56eb" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `fg_ab "user constant" .inherited (.inherited [`A.f])
    "41ff23acda237cb9bb054d197a1b5637f5383f5b00f0c81efc3b8147143e8c26" "492c491c844bebb7aeea604686c91540ab5ada6ad62e68fa95ccb7968295fd79" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.below "block auxiliary" .image .onlyB
    "-" "051b42b16de7e029fe0684f491b4009ad51b7596598b604cd5bdc8b832fe5a88" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.brecOn "block auxiliary" .image .onlyB
    "-" "4cea72f8b09109ca9c71cf7aff25fcf4355929b5457c8db9bb27140f8fc5f315" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.brecOn.eq "block auxiliary" .image .onlyB
    "-" "8de6f57cd6df7e5b7325eebcc5eb42d339c21243d60d44404d391aedf6eaf542" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.brecOn.go "block auxiliary" .image .onlyB
    "-" "0091e04ae3b9fa1fa756f58ab14b83fd18ec411e48ae84fc081a0469eb47e450" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.noConfusion "user constant" .inherited (.inherited [`A.noConfusionType])
    "4e162da1310edec1751cbd070181e6c04921240edd8d0b573d48f9d6415bcc07" "ea29d26a799c122c0386979262d2fc3a47d5694aa79f397a5235da7c152382a8" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "dc1e4d43c25244583ec3fe667f43d9a43eb6ffe610c00f04a13f1a3523509204" "551655be3a8d16d466f67bd4dbdbd543ac83a3d19cf6e76feeded6ab72d67bd6" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "86c5ed797f418d21ef9b78fd12e34719586d0e01ebad49793d44f877315341e2" "5896555a46e22d9da91b7d62f8fb25708ff85deafa83bb23c982a54d434664d3" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "252a9162bf5e363a78e7c602f5957da274d5edfa17341a8ae511fdd0d197af02" "4de5f01d3d9211c82d0399787d02b1eea38bf65221287bc4a103b1c143758337" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a17da90a847d92e8024d980f152101a3ee8f2096baa675ddc6cb69732b2d1ebc" "d93312206e88c9cb32bb93f0f5004734c26b4308abd12af80a808eb262da79c1" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fd85ad262719d83a12fc1d950e9cbab5a15eddf153ec38dbcd5fc507216927a7" "ade00cb41552d5ffa1658f8d9222a791547e130277b03e0b0c79e8b300964a4d" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ab8acb574825a6d2c00a02642757cc90d37a478525eab15ffd76f53041572b70" "2fd077d4c8fa911e9f10a49d6106065b49ed513cab36c6d3341cecbc5f08b0d6" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "597541cb7d1515de8618e8ab7f7f7e0f4f5693cfb3ea6be3dd1cb1fd8891e662" "005318ef032022d814ea8e52ee7ceb47745f560fa28e11902cd5a06e97737f05" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.ctorElim "user constant" .inherited (.inherited [`B.ctorIdx])
    "f3db120744d25a57d5535442d6bb7d0923b45b056da302e19f82067a40f3f702" "bb0d99ae86cca402f8472a2af43f9d28ca73012c424a72dfb12c8475253d05cc" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "2613f00a4d5923be077387ceeb87f0fe68cd361ae987bd818e066f6042264c17" "99c2ddaa2a310a32946ff5e6c7aff43a10d3f34da117567aa635f410b50e8196" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.leaf.elim "user constant" .inherited (.inherited [`B.ctorElim, `B.ctorIdx])
    "bbb6ffe937a7d246d1cd455b1e4f49eaae681c4fdeed60078775e57fb5a1dad9" "020fc73b74c112376cdf6a9e6503d7c118a914ab6492526ae3f0c64fab5e8b4d" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.noConfusion "user constant" .inherited (.inherited [`B.noConfusionType])
    "567f68cba689df3ecee088d50c35c5224bc83709602c1ec997dbd49835743974" "2385f1db4bdebbb2adf0ab4ba60a69b81525887ee1d6faff61d8f4aff080632a" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "2028e58d86f9a54b9e53c4f4201b53ccac824e2a3733a06ff4c6a43d5d859b51" "a182e4bd4c6d5d25365ac60ca2d530d30bf455f5438cedfe7effa74ca153922c" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.node.elim "user constant" .inherited (.inherited [`B.ctorElim, `B.ctorIdx])
    "16107ddc18248b7ccccad13cc7b76b39febcc21962b84984ab8dd2070a21bbe0" "0156e4461afe70d1ca687424214af7f9d316610272830975133e5e4070e2ffbf" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.node.inj "user constant" .inherited (.inherited [`B.node.noConfusion])
    "3fb46b0bb6ee82b33e855925ffa40315b616788be62d07411c4ffc45f51565a8" "be92ed1113e3653e828477b28cedc14b6e09c331e2e32160d78bf22e2d4deebe" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.node.injEq "user constant" .inherited (.inherited [`B.node.inj])
    "1917356cd419691dc94a7a54c0ec9781350524e1244c139252f96b6e9d8c7a20" "79002c702ace448c4f930447a41a621a70ed82e33eead9d69d0b392eb5c5c223" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.node.noConfusion "user constant" .inherited (.inherited [`B.noConfusion])
    "b0a8929138060d1c635634bdcfa7cedd7c2cfba0cc376de8c5de511d3cf8cc5b" "15b70b6899ce544ea80ccab1fb0bbbc6852edfd669f5e5286b2c8588f942b507" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c8322e03d558f85a8edc7fe68524013880ad0bbcb7dc890136d247154b230992" "b6f32918f179e32bd0049cb1297eb6572a5871926a40ed3d0a51a555429fad50" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "32038f41f6815ac7654830d5262dd2880649a594097cc8af729505ce45c84ef9" "3dcc60338f89f14c89d8f004a220779404782d40e4fbc28b10c6913cb80c0d14" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.below "block auxiliary" .image .onlyB
    "-" "6bc3d8626d4806b7f937f6e5858b2da252e041b128e6856a63b46558c39a541b" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.brecOn "block auxiliary" .image .onlyB
    "-" "ad84d40488f2d759ed30eb86b5f73b8ab247db1f4e3cdc25783ccfa03e75b756" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.brecOn.eq "block auxiliary" .image .onlyB
    "-" "7c4451a9a68d52e49e13b866b6b3ab5241124c97357c8233a9969fc606d46af5" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.brecOn.go "block auxiliary" .image .onlyB
    "-" "7db1fcf5ba13b618e73951b0c3f48c7ae27929cee300c048eef0009fff117f6a" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.noConfusion "noConfusion" .pendingNoConfusion (.root false true false)
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "abd3af6627f5d3c14eab547715953d68eb79793adee7b6b73ad6b4b0c82581f3" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "a13871a9d6c0f80bec0828b0d0bb5b706bcaf3036c0fd63791655cb1bf8a9100" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "62097ef059b0e99d2abee440f8691386cb2afd54beb68a2cf3a336a726852a0b" "345109cd4d01ceb6b1a4dcf9a5391ca7731db4d5ff6ce8fd6c3b95e2dfe4bef8" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dfa05d5f71d78161d48645eae61fe74366ed0196a36d361827c4b360c8af6812" "8a0748b03412e448bbb9be38db1aa217701a0021929244c5e7b913f83b023ce8" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c7a4089052cec064308225fceba4180140048be56d863790f6fb03b72baf27d8" "8cdd32df61483dec2d1388a7d4529abebebfcca802cac297a3fd90e49c9bbb0f" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6914455895402708d495f8cf2e06c5da1c380f128ccb89899ead54e46cfa34f0" "2d5d4f118114c31b18f9b315f88c8f16ef751edd68363bef75815aa19b8ede82" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "67cc4696c99ea8cb3ef08a4675791fc57a3248b8bcd5fce527b5fb907562aa0d" "7d0f581123383072c6a9f09ed864869c8fc810cb674aade415b9f5f3a1868b82" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "305f40ded1e4543cfd568ecfac5f47e048a74dc59b339bc071b1eee254fd9ac4" "e20962f831bf2871ddd77e9a151e27de1f70b28704d27f9daf0170de760c3800" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.ctorElim "user constant" .inherited (.inherited [`B.ctorIdx])
    "173a8836f585720c136243d9cc38f667cd21aaac3ab6527d326822ddef81e70b" "7b3e4f0c83960cc287bc0455e91bb6b0c38be800338a8c518fb2e4ac17ab69de" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "72298e9a550067849ced8cf1b2dcc21eef4bde7d05e32164a056200ef254a528" "718d8c03d80a917d73ada514c8f031288c29bb15aa82cd503b09adebd037a3d8" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.leaf.elim "user constant" .inherited (.inherited [`B.ctorElim, `B.ctorIdx])
    "da4072afc5475a368ba3e798ed8752666b40520bc366dd861a12422a6cb6ad3e" "3bd7d54874a686680b52403c4062bb44ac9d297a7e29a52cf93e59d172a6009b" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.noConfusion "user constant" .inherited (.inherited [`B.noConfusionType])
    "89c223c805f36e247f585f079e3598d323c37e33f455077b365c0658163baf0f" "ff86f6d033da8a0b103478feb94d37a9305b9b6d0dcc918795878728f2866db5" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "462938b1f98040306621f15aa7b4626eedbb5118dbcc24028ce5d9f07cd8d282" "13dac7fe8fda5593c6e70e70b5105d707e93d1d2c1b6c8a0a077b93500065073" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.node.elim "user constant" .inherited (.inherited [`B.ctorElim, `B.ctorIdx])
    "b1160b115c64c292c49ff2b4ca4e9b8c1cc826c981c0b0e7560104992d6df9f0" "dc366f5ccb1de4cdc9dd8ab95a35ffedd37421b09e0922eacc5a7b22a18c7e9f" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.node.inj "user constant" .inherited (.inherited [`B.node.noConfusion])
    "06d0d69db10e7e72ec16e3a0613792ff746ef08e10047e1cda39669a222e2811" "3a24cc1dc1bbffe6bda74940a5dcf5054024c71d7ac8aacf5d29a41ce79c62c1" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.node.injEq "user constant" .inherited (.inherited [`B.node.inj])
    "4e01205b35c4b3632e3f407d9614cf0ecad94d43ed80c9b0b3b57bca00c3e43c" "bdcb93c936f9791563217a4f26992587824f8b397df99ba12c9602e0cce2f384" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.node.noConfusion "user constant" .inherited (.inherited [`B.noConfusion])
    "30e42f3893f2746955c2e1e27546c99093d8465a50ff91a4b38ce6cf92424d1f" "7847114d8c073cdd40ef53c1305aaa634687bc8467057fcf479f2de93fadd6ed" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c09085185737921cb32d9f4ae87bf398174cf7c6ff37b1f84018fa1232b60565" "982b163bacf09f5d93e21edf31f66e438929df26c44e7fd4d774a104633bc674" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1ef1eab0f0ea73af40b15337444a8317d7359eeab39e3123d36624c6a3612825" "6416e95e5dbc8465b4094be3510d9b9b262131e0e367fa41a838ce7b001546e4" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.size "caller of a changed block" .pendingPasses (.root false true false)
    "6080eafe62eb306a3fd21ce255d6bb2e851ebd04f14bf55105e5ffb01f208bb8" "e69b7e104f2ca740081015d4153b96b731d7059949ddef261a2e01d862ce420c" "value.λ.body.λ.body" "brecOn call site of a member with another index count (WB SurgIdx; images, A3)",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.size._f "caller of a changed block" .pendingPasses (.root true true false)
    "31412935835a3fb0d46666e16bdb86dea8b23a49d0850f235f0ac7282d87c385" "ed4f5dcbcfe0e8776436bde7406b69476bd856fac783cd8dc5fe1a973946599e" "type.∀.body.∀.body.∀.dom" "brecOn call site of a member with another index count (WB SurgIdx; images, A3)",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.size._sunfold "user constant" .inherited (.inherited [`B.size, `B.size.match_1])
    "4939f2f2890510c9c6c6b3c2e71ec76cccd617d865eec7695fa65cb5cdd17455" "1546ec53fdec2d51b3feee0de8eadcc56b47ae82def22d2213147b8e52a06d29" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.size._unsafe_rec "user constant" .inherited (.inherited [`B.size.match_1, `B.size._unsafe_rec])
    "750177b50dc3fcae2ea0f211ed0fcb6da4d59defa9330d280bf67d1ed642e5ee" "5be97be8143f88d4c3f98afe8d7456654d48e9ab72dc3240803bc11e64ec6419" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.size.match_1 "caller of a changed block" .pendingPasses .unexplained
    "06677337979a84c8e121ff9d473ff304f2567ef857553172f669598662f94f0b" "7a1ccc33b482cd83a58746c7b940f8ab96f70d707e6487c5cf5b4c77fc0d3a35" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `bsize "user constant" .inherited (.inherited [`B.size])
    "79607be1835bfd6e897fb762fcb38297ab2e0e1897c873fe478ece6235635206" "8b817d626858eaa579ca9ee1bab5d1a62b92d0d4961773b946d1fec5a15c660f" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "19e46c2c75aba8115ea388c0f2c1cbc22f450d7fcd18cf31fd375cde30828552" "64f73e5929554af59b40bbf9d8e2abd18f1ba99399b0b911fdec6fa274c739b3" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor"
]

/-- Entries 600 to 799. -/
def part3 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "cb38961a123f89cadfc53462a78ff4dbfea68b5aabccb0706ec0e7a5853ad4b7" "674c201c98986446aaa3c41c2ecd087ac343df36ddd465a35ab6039a841955a5" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.a.elim "user constant" .inherited (.inherited [`A.ctorElim, `A.ctorIdx])
    "2fe5c94bdb5c99cea736c5e6fc8a1e8d18c5442936199baf3a3855885a4da6e3" "ac1079750e498f2d1d2476c9ac8de4c595817cad40e431c9d186c2b7c7619b77" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.a.inj "user constant" .inherited (.inherited [`A.a.noConfusion])
    "dac85c3a439cc5c559800b5997a596faa98e077f7b469b03782533a845da572b" "7ae17ca0afa411ad2d83273992a1d0d5bb46fce0167ee640832f953d98ece197" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.a.injEq "user constant" .inherited (.inherited [`A.a.inj])
    "a6d4e7c5074c1d2b7e1263bce37b903ddd9ca894af60dc0fcd746ff6327e1ae7" "2fc72e3c4e25c32cd79dc7dc6ebae87399619f4a121c681b88bd2b2b096a4552" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.a.noConfusion "user constant" .inherited (.inherited [`A.noConfusion])
    "25f2aa0fec2a85138cae95219d238d035da11afe50fb56d4242fe9ec483f8988" "239550c092be430ec9a70ba710e67a3d22e3e3dd42cd8c67cc273b585e2df747" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.a.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "028b918c12d718298eb45d488de35571619507e7cd476a66da582e007caf017d" "de6bb0378364a26b8b1daecc0f1058e134c3c962c34b9a5c5d7dc5cc6ce7b96c" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5415f5f54a992d17fec6b65e0382c4577c3c7dfeb1d4f1e16b36448e23f299cb" "17f5ea7d767f19b280e22f1194210bc852a2d9697596daa4818a050fb08d2272" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1ebbb6b48539de5701c56e706a923d1db699775392773af34933912d17dc61da" "1d83bc6710567484d746c04b269c933d0fc03437e0b2348e9fd65b1b77b965e9" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ae750f0205d850cbda2dc93d13b6a498c0750ccf4b91d2bb68ddc3c414937faf" "4d96be5956fca8ab6be3115d25c1fe60a2a278d7386d5854a0554ea08f562f9d" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "bdd6c50576fd96d51f72aed7ffa79736ef61ca32aa8158e3a6b51d92c1750f53" "4b75385c7045e7852c776f7feb439b030baa2eeed7fcb618c66bb16e3bd36ccd" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.ctorElim "user constant" .inherited (.inherited [`A.ctorIdx])
    "d25e34074b183a135a4f2df96f878d71ca5c64ad893d3eb9a83dff43f8f5741b" "6b3a5d7c5b824480572bcc336db942a68f9f517a69544e4ca93ef1327def398d" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "03ad90414d41ef7e006e41bbb315847d9029ed973148409cd0e7276951ff5d99" "3c8863264d334b5481afd1832013e3d1b245de3a06ddd8e99515b7a904e32dfa" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.len "caller of a changed block" .pendingPasses (.root false true false)
    "a547241d523add64489dbe6d9bcffdaa0e11cee9fd2d77c1f8340fb5c5899246" "c5ff4cc37f93189b090350c0dc81abab77e562793f72da3ff480e1d94b1cf3e1" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (WB SurgSplit)",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.len._f "caller of a changed block" .pendingPasses (.root true true false)
    "4cf893733c374cb1e3d3193e6849687b35b597e8339b7a494c69912565a5b934" "f0138f4fad74d0c00abda006f79c12f2b300f4ae2a88998db1d94c1a438d32a9" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (WB SurgSplit)",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.len._sunfold "user constant" .inherited (.inherited [`A.len, `A.len.match_1])
    "4d723026dd9e109918901fa7dad29203102a220255ced0743a93ddfe9d957c37" "b1bfa3bdb69dae69ff83575d7b5b64f224460cfb2c72bd682c8e57945649c0a8" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.len._unsafe_rec "user constant" .inherited (.inherited [`A.len._unsafe_rec, `A.len.match_1])
    "5dd47dd55a222477bd8d4d3358736c6bda8a716a3d224ef892ae1b0282088d95" "d6936ea943eae5d11f58fe257663c3ad868d5a97c9090b69d102e60d758cd7ea" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.len.match_1 "caller of a changed block" .pendingPasses .unexplained
    "6761fbb4e5f559551e69c80cb5de2b5ed45fc64bc94d91db9c6927e45d073ee6" "bc8ef32918106301c93ecae547b8fe9d825729d6255433c045c94f943ffaa1de" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.nil.elim "user constant" .inherited (.inherited [`A.ctorElim, `A.ctorIdx])
    "b22a414f8dac147c49e118a27e58b13f01801314cb7e2c286effb532f4fc78e2" "aca4af067c9f1762dc15a022d191be56db6710b53cb857c5ce86e611f3e6f1e1" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.nil.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "9a2ccaeac841163498ff30c729158232c2fde2948c593b0434359c016a391fcf" "b89da649732f4728e1ea3ee6ebe0408417aa2bf5808f6d38fba2bec7be15feb0" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.noConfusion "user constant" .inherited (.inherited [`A.noConfusionType])
    "28816d4a33674a5f2a109945f07cd0f2e8787609d9a602b59cc54ef05980ab68" "0b09729545c26e6d0034691a485d449e5d099ac38b733699f3cfd0a024f331fb" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "072df558b5d01b3fe91d84db848aa8512ff4bb7b2b18c8007e29c8081115b532" "ff4bc28df40d5e1109835b0fc35aad6cd4502e9708624f69ad6a9cbb704f592c" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "507879810bce736d4eaf20aa5fe5e0ff6a59641422f54f61cb7c7dee3614eb55" "bc4d5e04e34bebe33ec6ad6138a67ad9f50db6f517d43e758c0ee5217b23f322" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2ac559561fdbc297ca67c47f791c18079f104f9c745c0ab4b340dfe4fdd42b76" "7fb0e68c45047dbe22e7ab84978f97973a15c93b9c602ba55093eb18cde6f369" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.below "block auxiliary" .image .onlyB
    "-" "11a02ff01639cb2e18097f2819d5aeffa7863652a43edd53dbcb6a8a0ccc5424" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.brecOn "block auxiliary" .image .onlyB
    "-" "4352a61a2f59ac64ef865cd4c6fab60c7787fd23be1381a339f82f9ca28b162e" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.brecOn.eq "block auxiliary" .image .onlyB
    "-" "2ff628a276a05b418b962c3b16ad80d0d5893649c9d6e754a0c1a9cfd18de6a6" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.brecOn.go "block auxiliary" .image .onlyB
    "-" "a16b21c967e7357925412409876fd0316caeb5ccf96819e5726384bb6193cf4f" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.noConfusion "noConfusion" .pendingNoConfusion (.root false true false)
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "abd3af6627f5d3c14eab547715953d68eb79793adee7b6b73ad6b4b0c82581f3" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "a13871a9d6c0f80bec0828b0d0bb5b706bcaf3036c0fd63791655cb1bf8a9100" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "62097ef059b0e99d2abee440f8691386cb2afd54beb68a2cf3a336a726852a0b" "f9cc97e627e1497c57d63be38890d913085305c7273ede067538078438900f73" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dfa05d5f71d78161d48645eae61fe74366ed0196a36d361827c4b360c8af6812" "8db08eb4c7eb99558e309570ed6f1ebab46facccc9c9f247986ee5314891839a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `len2 "user constant" .inherited (.inherited [`A.len])
    "c7de97e5d77bc5368dd7623036851ed5296ee3ad2b92c5b103e44f3ac577d806" "7cb019b07b25aebfe3a6872e06283a9faaa383bb3073a38ca3158b9c6d0c0874" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7f763b22ab7d2313414b0863abcfd8be6d6248a894cafa3985de4aa1ee87dc76" "ebc3c6e344916a094060c73b9dbffccf4be05a447422a622d604072e21f82db9" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0d06ac6e1421355535a9373b31b4c6c694d6a90e27e88ebbc5df987ac06e167e" "de13524f04eb0a83af891ea98d10e5e75f7ecb56d8980251a58f64be8b610094" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7ae45a0991d805839663d60aaa3c1a21e95d2d82884cb29bd25e4dfbce5a0609" "36db7a4a9d8402bfa9bac3644c5222f85f12c1538671e96918d01c0d5752e4a2" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "162f42113d4810a627b1428cba24770478ac759a69c93f1f6308c7046e52e791" "1cb86054c4b59b486a1ac476d135afe8752728f43713d1061c908f1b6ecd6731" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.ctorElim "user constant" .inherited (.inherited [`Even.ctorIdx])
    "61c84c444af18e5b10eeddacf9038769c5df20c3635297aca0368a85c81c7767" "08e99a0444f4df4c1a491b461873b4763a4ce5753fe30844cc7410eab61e8e4c" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "6b41af9ed4cdeac27411e001be93c064d7d94b68cfc2387eb27edb1d12860645" "e0b9a325ad87d97e290ed0ca7616f68b606d4a5ffb9f158cf801d388f6b4a673" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.isZero "user constant" .inherited (.inherited [`Even.toNat.match_1])
    "6bac7cf1cc445d6c858f970ae9032cf04ee51d101445a7712d50485a3a99b927" "8014c700093c1502d2417451c408bd31b7d2b1397b57eece90b41eef215a67fb" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.noConfusion "user constant" .inherited (.inherited [`Even.noConfusionType])
    "a41136ce4221a23887503cb3acf7cae609d1c6fe6412c8abbcb3e31625244007" "608d719f5edd195e52a868b55989683301c242f5016920e025f4f3c83ef5a0ee" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "6be1c9c3d68f215e125ea41348db280f98b2cd824ae42e32242e7f342daf801e" "21c1b84fdac19e3ac3aadcc268e5197709461f2bbdc4f44758b0f62c9299e60b" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6bb942cd82f258244933f967c95096c6f2224be3e42000044f6c48bea7494a5c" "828c49458b8195d317602ed1e50d073f750366fdd0fb2d8805ea2fb12c57e372" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ceae26812d0993921e96c02861e907a6ebb35bf8ba2a569b93520c1b49a243b3" "dcea23ce9f3d4d3171865b8ddece321fa8b7016725e8821b11f5b4d6c464508a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.s.elim "user constant" .inherited (.inherited [`Even.ctorElim, `Even.ctorIdx])
    "86cf501cb076978ac197991c6f88a35a4f28e2915bae7605f9558b48e862d3a8" "33b10e945a4da1545df9353e14d5e4d0ab23189249df6d145cd325f50578bb9d" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.s.inj "user constant" .inherited (.inherited [`Even.s.noConfusion])
    "d231031d72e12e13cced04bd0d5ae6dd40f8e20cf7a8e4f66f9347ec7456f275" "a3c29fd41fa1a8698e36a94103cfb82de3162d64fde332e285bd301fac3fb106" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.s.injEq "user constant" .inherited (.inherited [`Even.s.inj])
    "abc7a7047558ca0a326f461e5c59eb59f9ce9da9dd55d85d3464ff5080827099" "2448b9a4d5a2ea41fcc5cf920d460df30bac780a97a074e11f50053a8c108e9a" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.s.noConfusion "user constant" .inherited (.inherited [`Even.noConfusion])
    "fd6b519f6d0ccdc418e738e94af933bd2dd285678224df4cd75071aa61b11a8d" "6bb89cd4e3e99d1b2948cb54bac210c7a235215391ba000879ade2fb1726a256" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.toNat "caller of a changed block" .pendingPasses (.root false true false)
    "14c008d747384a6b658c0c1e481a978ba8dc0aeaf43f66382603291dea591706" "263876896bd23b55c0483cf8c5bad31ba877fe03432f899e835a4f871d9eb58c" "value.λ.body.@0.λ.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.toNat._f "caller of a changed block" .pendingPasses (.root true true false)
    "655194ed3bcd02171f46ea536300e78cf92b053d527c2070743416ed1e2bdb69" "81f93e12c74024993ba78be8217091073a60d0f1a69c5cc4851b6c325169ffc0" "type.∀.body.∀.dom.@0.λ.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.toNat._sunfold "user constant" .inherited (.inherited [`Even.toNat.match_1, `Odd.toNat])
    "b026e2ce6b56bc8ab4aae8d71c3bc37463b24263df2cd485d4ad169348c28e4b" "10827ad349ba4894d553a615d54c039b5c96813a8045fea3e7952fff1316cc9c" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.toNat._unsafe_rec "user constant" .inherited (.inherited [`Odd.toNat._unsafe_rec, `Even.toNat.match_1])
    "7732c7afdf7ff4d158242dfc661b38c50a2b3a150927f31efed49b06f995cd0b" "3921437e2f19e4522e87e25925f7e9087f57d99dc388116928cf6ecbe0f34e05" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.toNat.match_1 "caller of a changed block" .pendingPasses .unexplained
    "285973d99afb436f6b20ea696fd6f05570ffb65c40c59dcdc87905652bcaf672" "dcb2370fa5a38d78508941209befb90e8fccd42fe5ac70de08fda9aa4476af0e" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.viaRec "caller of a changed block" .bare (.root false true false)
    "5b91b50d4c4fe9b970fc85af1f8a09eb7b0012c72d86d62f07185f6b9f63bd99" "00cc400d69c397b1984d30f194f57844d20749e702925c9363727765bd20d09f" "value.@0.λ.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.zero.elim "user constant" .inherited (.inherited [`Even.ctorElim, `Even.ctorIdx])
    "d6178667d513bccbf91b324abaff28fdcb96b9665457dec69490e6ddff79d7a8" "c7614d70bbb3db3f37d31c830ca95b706b6dfb38d760568fbd88af6e4f8aad8e" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6c1946534e24d67671f05c36dae164a239acbf49a727475b6836e00b11869cdb" "635e2c9b6b9b2b3919e4d03d5465a968917f2a818cc061f5cf71634ddd86eb17" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "df0c39076c064a2919c5dfb2f1b73c9e9c20d6425039e0f17133c7356490d71b" "f709e453f6ff968b5a08f4cced87c6563ccbb2399ce07726fd6ab0c7cd616eb8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fee09fb5867ff9dbae55ae9aedbf8c3119464b44caae329e490a0286172b57d7" "7d6f949ba4fb394bafe9abbff8d1b55a99903326c2ff5c06f0442d5b71878985" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "166df2c4e8e3fe7a8b6ed7d65b3c5f2c17fc342de8c3d22bb46f54f70e4689ce" "27d3ce37d2427158d4c7b9d458ae803c555d55f579f44848054bbea895e194de" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.noConfusion "user constant" .inherited (.inherited [`Odd.noConfusionType])
    "e264ef0bc51c3b7da9167b2eeda2477c80e46758b77f81660149ff75407cf56c" "e235cb81be4c39d557ad864eaafb78d89e496347fbfe285b371215ae8feaebff" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "df6e6c95a0c0bed5ecef8c56873ee533e15a9f09dc47f7b287c0579f60d87cea" "4edbdf765ad1e027cbca9608ea3b95664c446be15823d9dea46ee0aa8c19b229" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c9cce8cecf22064511a309ecf5cd00f6c87b031ed8e058eb09fd699217fa8c71" "16322604a39ee2bc2c59b6433315f3b40ddb32f55011712161bc88252942c5bf" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1527c316d83a38d43628ce583eb0dba56fdbb7a296b8a0e2e0f64f0e845a3ac4" "c3c6e9068e2b7d3a4ecb6fdc5243e5a0c8288a344a7bb8240e67e9bd8e382cb8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.s.inj "user constant" .inherited (.inherited [`Odd.s.noConfusion])
    "ce92aadef7eedb994d10c8131fd1eb26f9e3f2d30122f5fc0a2710169ee35112" "500fe00a16ace79e19648db1a4309450112ebd9e6c5387fc74861304a9e3e37f" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.s.injEq "user constant" .inherited (.inherited [`Odd.s.inj])
    "38cd356185eb273408ba6421026a9034f94242e455ff6617591a48db3b7a46b8" "1136df113c8e2ab5827369eb1bcd4c2f630558e8d816a7897f1ef89f0916153e" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.s.noConfusion "user constant" .inherited (.inherited [`Odd.noConfusion])
    "3ccc52cb2955604e7ef13afd8d7db2b5e1981f8eddd7012250695d5f78d404ff" "487e5a43f7761729420e07afafe7e20d62fcbdec11effe4ba8868e55c1a2d5f8" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.toNat "caller of a changed block" .pendingPasses (.root false true false)
    "6083ccc0c89479a3a3a552495d925a46473543f579d241c324e4c78d73d2c2ec" "a0ab6e9d00d5e4af919ea0cafcdc513f013098e20f2208a34865008dee08ae31" "value.λ.body.@0.λ.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.toNat._f "caller of a changed block" .pendingPasses (.root true true false)
    "5e277db726358ebccf819553d2429d548b12355953ce0305205e4e5b1be2e126" "6aea37f61b507f4b4e0c2d2089118db8c57bd596fbdd275ad33c7e97972d38ec" "type.∀.body.∀.dom.@0.λ.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.toNat._sunfold "user constant" .inherited (.inherited [`Odd.toNat.match_1, `Even.toNat])
    "ead543ab4f3b5d2598c3223025de93eb010d3f3a53e27af0bf8b41553146a457" "0c9d62e55188afb11a76355edc14dc470e765da2abe99b3d7406c934e391adcc" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.toNat._unsafe_rec "user constant" .inherited (.inherited [`Odd.toNat.match_1, `Even.toNat._unsafe_rec])
    "5a64c69661458a2e7bdcd85a626c0639828dc08b00915c0aa9e7bdc7750828de" "7754ef449f8aa89aff9baf7f25418a22eeaed3d6a4f50a84cceca6f37bea755e" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.toNat.match_1 "caller of a changed block" .pendingPasses .unexplained
    "830a13bfe81958d85007d87a73d4d9fcf860d9120355b09a145f8abacc248c79" "2a19d83dd3bd7d71f7849700303bb6cd165dbf4cf10f0530cd1d80d05f7f530b" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "19e46c2c75aba8115ea388c0f2c1cbc22f450d7fcd18cf31fd375cde30828552" "64f73e5929554af59b40bbf9d8e2abd18f1ba99399b0b911fdec6fa274c739b3" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "cb38961a123f89cadfc53462a78ff4dbfea68b5aabccb0706ec0e7a5853ad4b7" "674c201c98986446aaa3c41c2ecd087ac343df36ddd465a35ab6039a841955a5" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.a.elim "user constant" .inherited (.inherited [`A.ctorIdx, `A.ctorElim])
    "2fe5c94bdb5c99cea736c5e6fc8a1e8d18c5442936199baf3a3855885a4da6e3" "ac1079750e498f2d1d2476c9ac8de4c595817cad40e431c9d186c2b7c7619b77" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.a.inj "user constant" .inherited (.inherited [`A.a.noConfusion])
    "dac85c3a439cc5c559800b5997a596faa98e077f7b469b03782533a845da572b" "7ae17ca0afa411ad2d83273992a1d0d5bb46fce0167ee640832f953d98ece197" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.a.injEq "user constant" .inherited (.inherited [`A.a.inj])
    "a6d4e7c5074c1d2b7e1263bce37b903ddd9ca894af60dc0fcd746ff6327e1ae7" "2fc72e3c4e25c32cd79dc7dc6ebae87399619f4a121c681b88bd2b2b096a4552" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.a.noConfusion "user constant" .inherited (.inherited [`A.noConfusion])
    "25f2aa0fec2a85138cae95219d238d035da11afe50fb56d4242fe9ec483f8988" "239550c092be430ec9a70ba710e67a3d22e3e3dd42cd8c67cc273b585e2df747" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.a.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "028b918c12d718298eb45d488de35571619507e7cd476a66da582e007caf017d" "de6bb0378364a26b8b1daecc0f1058e134c3c962c34b9a5c5d7dc5cc6ce7b96c" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5415f5f54a992d17fec6b65e0382c4577c3c7dfeb1d4f1e16b36448e23f299cb" "17f5ea7d767f19b280e22f1194210bc852a2d9697596daa4818a050fb08d2272" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1ebbb6b48539de5701c56e706a923d1db699775392773af34933912d17dc61da" "1d83bc6710567484d746c04b269c933d0fc03437e0b2348e9fd65b1b77b965e9" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ae750f0205d850cbda2dc93d13b6a498c0750ccf4b91d2bb68ddc3c414937faf" "4d96be5956fca8ab6be3115d25c1fe60a2a278d7386d5854a0554ea08f562f9d" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "bdd6c50576fd96d51f72aed7ffa79736ef61ca32aa8158e3a6b51d92c1750f53" "4b75385c7045e7852c776f7feb439b030baa2eeed7fcb618c66bb16e3bd36ccd" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.cnt "caller of a changed block" .pendingPasses (.root false true false)
    "9d8bdb0bfbdc878f109d4e9acc712eb7e09b04a0fffcde3fd31b9495e9117212" "5eb3dd4a134d704ad48fadf6e4f93574c49876d795f2cf704eecf89bb3d8abac" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.cnt._f "caller of a changed block" .pendingPasses (.root true true false)
    "737d9847f6255247ce5ac946c55c9a631b41f125be5e7933ab807eaeb40c54d4" "b69085bd4005624d8284ec8e3deeca9bd92db7c660f6382d0e3ed87f278116c7" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.cnt._sunfold "user constant" .inherited (.inherited [`A.len.match_1, `A.cnt, `B.cnt])
    "c7b4b2af419c9bc6cf2285fd0b048dfaf8e422835c91f0e96ac44b85891a449a" "e23cb1e690359d19b4674c72bb2c3f63f7cc61111aa121f9e33953d537774a19" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.cnt._unsafe_rec "user constant" .inherited (.inherited [`A.len.match_1, `A.cnt._unsafe_rec, `B.cnt])
    "57412b7f88c74026359db297b51e704457bb46dc360f1e89361ee94ea681ca5f" "79a72efbb6ef3a3263fce08e14ee37993a39e99238160026176b073b3c37c222" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.ctorElim "user constant" .inherited (.inherited [`A.ctorIdx])
    "d25e34074b183a135a4f2df96f878d71ca5c64ad893d3eb9a83dff43f8f5741b" "6b3a5d7c5b824480572bcc336db942a68f9f517a69544e4ca93ef1327def398d" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "03ad90414d41ef7e006e41bbb315847d9029ed973148409cd0e7276951ff5d99" "3c8863264d334b5481afd1832013e3d1b245de3a06ddd8e99515b7a904e32dfa" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.isNil "user constant" .inherited (.inherited [`A.len.match_1])
    "21a27b0eff8b2e21569a67a09e52566e0a94d719e2ba19a77d525ef0cbb1a27c" "8c35397795cd830de78d0908f05c3211b249a0ed0ec49b9bc79c1b6c6891eca6" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.len "caller of a changed block" .pendingPasses (.root false true false)
    "a547241d523add64489dbe6d9bcffdaa0e11cee9fd2d77c1f8340fb5c5899246" "c5ff4cc37f93189b090350c0dc81abab77e562793f72da3ff480e1d94b1cf3e1" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.len._f "caller of a changed block" .pendingPasses (.root true true false)
    "4cf893733c374cb1e3d3193e6849687b35b597e8339b7a494c69912565a5b934" "f0138f4fad74d0c00abda006f79c12f2b300f4ae2a88998db1d94c1a438d32a9" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.len._sunfold "user constant" .inherited (.inherited [`A.len.match_1, `A.len])
    "4d723026dd9e109918901fa7dad29203102a220255ced0743a93ddfe9d957c37" "b1bfa3bdb69dae69ff83575d7b5b64f224460cfb2c72bd682c8e57945649c0a8" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.len._unsafe_rec "user constant" .inherited (.inherited [`A.len._unsafe_rec, `A.len.match_1])
    "5dd47dd55a222477bd8d4d3358736c6bda8a716a3d224ef892ae1b0282088d95" "d6936ea943eae5d11f58fe257663c3ad868d5a97c9090b69d102e60d758cd7ea" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.len.match_1 "caller of a changed block" .pendingPasses .unexplained
    "6761fbb4e5f559551e69c80cb5de2b5ed45fc64bc94d91db9c6927e45d073ee6" "bc8ef32918106301c93ecae547b8fe9d825729d6255433c045c94f943ffaa1de" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.nil.elim "user constant" .inherited (.inherited [`A.ctorIdx, `A.ctorElim])
    "b22a414f8dac147c49e118a27e58b13f01801314cb7e2c286effb532f4fc78e2" "aca4af067c9f1762dc15a022d191be56db6710b53cb857c5ce86e611f3e6f1e1" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.nil.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "9a2ccaeac841163498ff30c729158232c2fde2948c593b0434359c016a391fcf" "b89da649732f4728e1ea3ee6ebe0408417aa2bf5808f6d38fba2bec7be15feb0" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.noConfusion "user constant" .inherited (.inherited [`A.noConfusionType])
    "28816d4a33674a5f2a109945f07cd0f2e8787609d9a602b59cc54ef05980ab68" "0b09729545c26e6d0034691a485d449e5d099ac38b733699f3cfd0a024f331fb" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "072df558b5d01b3fe91d84db848aa8512ff4bb7b2b18c8007e29c8081115b532" "ff4bc28df40d5e1109835b0fc35aad6cd4502e9708624f69ad6a9cbb704f592c" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "507879810bce736d4eaf20aa5fe5e0ff6a59641422f54f61cb7c7dee3614eb55" "bc4d5e04e34bebe33ec6ad6138a67ad9f50db6f517d43e758c0ee5217b23f322" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2ac559561fdbc297ca67c47f791c18079f104f9c745c0ab4b340dfe4fdd42b76" "7fb0e68c45047dbe22e7ab84978f97973a15c93b9c602ba55093eb18cde6f369" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.viaRec "caller of a changed block" .pendingPasses (.root false true false)
    "b3070b38cc2e3180e858b80263b21baf221e1a1cfbb4a835309c88695deb77f3" "2a6838771a850fb1540444d60b99f9a115d1e7d3d2bfa8c852b229f004ab3544" "value" "raw `rec` user over a split block: relocated calls (O2)",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.below "block auxiliary" .image .onlyB
    "-" "11a02ff01639cb2e18097f2819d5aeffa7863652a43edd53dbcb6a8a0ccc5424" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.brecOn "block auxiliary" .image .onlyB
    "-" "4352a61a2f59ac64ef865cd4c6fab60c7787fd23be1381a339f82f9ca28b162e" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.brecOn.eq "block auxiliary" .image .onlyB
    "-" "2ff628a276a05b418b962c3b16ad80d0d5893649c9d6e754a0c1a9cfd18de6a6" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.brecOn.go "block auxiliary" .image .onlyB
    "-" "a16b21c967e7357925412409876fd0316caeb5ccf96819e5726384bb6193cf4f" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.cnt "user constant" .inherited (.inherited [`B.cnt.match_1])
    "2a65d23888976f9a8efdfa3293dfb0b5fb39a84238e9f5fd71f417841e6fb9e0" "e2aee5be6d4e757657fc2b5d8c1763aca229c85136ed26b7536f5a2612723468" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.cnt.match_1 "caller of a changed block" .pendingPasses .unexplained
    "b1ea810b383f4dbd7b749e796f7db68cbc10a01f96acf7709d4af3949d8bb9a0" "4129c74ecefde87ab2bff3f2904acdc49e8aec8740d1549bceb1afb47c4f0444" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.noConfusion "noConfusion" .pendingNoConfusion (.root false true false)
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "abd3af6627f5d3c14eab547715953d68eb79793adee7b6b73ad6b4b0c82581f3" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "a13871a9d6c0f80bec0828b0d0bb5b706bcaf3036c0fd63791655cb1bf8a9100" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "62097ef059b0e99d2abee440f8691386cb2afd54beb68a2cf3a336a726852a0b" "f9cc97e627e1497c57d63be38890d913085305c7273ede067538078438900f73" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dfa05d5f71d78161d48645eae61fe74366ed0196a36d361827c4b360c8af6812" "8db08eb4c7eb99558e309570ed6f1ebab46facccc9c9f247986ee5314891839a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a17da90a847d92e8024d980f152101a3ee8f2096baa675ddc6cb69732b2d1ebc" "0c1d91e395ab21583e991f4688ebb77097638a9b2cb5383334feb02094add053" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fd85ad262719d83a12fc1d950e9cbab5a15eddf153ec38dbcd5fc507216927a7" "cd880360e2e518693040188316633b2df76f8d5a0803cf371d9529a46ead7996" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ab8acb574825a6d2c00a02642757cc90d37a478525eab15ffd76f53041572b70" "b2dd5c642f9fc340d51e423d1708e58307a9ad02deb23b34a96d8a4d90eabc73" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "597541cb7d1515de8618e8ab7f7f7e0f4f5693cfb3ea6be3dd1cb1fd8891e662" "1b248444b6a8267e44e643649c03dcc7e3b5c9a1f2f34594cb47582b35626bba" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.cons.elim "user constant" .inherited (.inherited [`A.ctorIdx, `A.ctorElim])
    "16107ddc18248b7ccccad13cc7b76b39febcc21962b84984ab8dd2070a21bbe0" "0156e4461afe70d1ca687424214af7f9d316610272830975133e5e4070e2ffbf" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.cons.inj "user constant" .inherited (.inherited [`A.cons.noConfusion])
    "3fb46b0bb6ee82b33e855925ffa40315b616788be62d07411c4ffc45f51565a8" "be92ed1113e3653e828477b28cedc14b6e09c331e2e32160d78bf22e2d4deebe" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.cons.injEq "user constant" .inherited (.inherited [`A.cons.inj])
    "1917356cd419691dc94a7a54c0ec9781350524e1244c139252f96b6e9d8c7a20" "79002c702ace448c4f930447a41a621a70ed82e33eead9d69d0b392eb5c5c223" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.cons.noConfusion "user constant" .inherited (.inherited [`A.noConfusion])
    "b0a8929138060d1c635634bdcfa7cedd7c2cfba0cc376de8c5de511d3cf8cc5b" "15b70b6899ce544ea80ccab1fb0bbbc6852edfd669f5e5286b2c8588f942b507" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.ctorElim "user constant" .inherited (.inherited [`A.ctorIdx])
    "f3db120744d25a57d5535442d6bb7d0923b45b056da302e19f82067a40f3f702" "bb0d99ae86cca402f8472a2af43f9d28ca73012c424a72dfb12c8475253d05cc" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "2613f00a4d5923be077387ceeb87f0fe68cd361ae987bd818e066f6042264c17" "99c2ddaa2a310a32946ff5e6c7aff43a10d3f34da117567aa635f410b50e8196" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.len "caller of a changed block" .pendingPasses (.root false true false)
    "7ab66120eb546a328d7a77dc24057c2590921b439880bd534377f46929624447" "21870540e2cba122e4e1540db3e57cf9293fabef721d4662e1e4e9558d42a89c" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (no cross field)",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.len._f "caller of a changed block" .pendingPasses (.root true true false)
    "c0ed98ee378360d330b40f22a2fd2b9a06153d051825644cec6ae0333f7250b2" "3f3d5ff8ec4dd9a4d6e391b114e9b2f9992caaf8ca3394ac410ed7f8148b54a0" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (no cross field)",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.len._sunfold "user constant" .inherited (.inherited [`A.len, `A.len.match_1])
    "ca27ead5b84f96c21500cca4e0522c912e2547f9f9045e34b242979270809eed" "620c0bf7c379abd350db9fc3e12c058a6fd462e00b1d09f5c31da8a54ca83a77" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.len._unsafe_rec "user constant" .inherited (.inherited [`A.len._unsafe_rec, `A.len.match_1])
    "9812e80ea5a87bfe8c706f22bcbb0088aec3f8dfdb907bbdef65aaa4271756e2" "a3d948ce8b6896f74743038b277f89ba08275dd89d7ad4d7791d4cc166b38113" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.len.match_1 "caller of a changed block" .pendingPasses .unexplained
    "8456b93a61151feea7878938feb7e719ffbef279f28f05c3e798f036ff56fa5c" "674ddde219dd2651a2205b62d3a70ecf57c352e9f674e164d3ef2c3ef449cb3a" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.nil.elim "user constant" .inherited (.inherited [`A.ctorIdx, `A.ctorElim])
    "bbb6ffe937a7d246d1cd455b1e4f49eaae681c4fdeed60078775e57fb5a1dad9" "020fc73b74c112376cdf6a9e6503d7c118a914ab6492526ae3f0c64fab5e8b4d" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.noConfusion "user constant" .inherited (.inherited [`A.noConfusionType])
    "567f68cba689df3ecee088d50c35c5224bc83709602c1ec997dbd49835743974" "2385f1db4bdebbb2adf0ab4ba60a69b81525887ee1d6faff61d8f4aff080632a" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "2028e58d86f9a54b9e53c4f4201b53ccac824e2a3733a06ff4c6a43d5d859b51" "a182e4bd4c6d5d25365ac60ca2d530d30bf455f5438cedfe7effa74ca153922c" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c8322e03d558f85a8edc7fe68524013880ad0bbcb7dc890136d247154b230992" "3b55a957c18509c4818766ba0c5a867842d197258a19f1aa6b717108f211ca5f" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "32038f41f6815ac7654830d5262dd2880649a594097cc8af729505ce45c84ef9" "b8947903c39da99bd16ac0265e3792d000786d6cab084dda20653e3dd4d1f427" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a7142532ef03ef9c02a010e3143e66386deb168d4bd9592552b6ba36033ac08b" "810583b98590955484b7aba9d2773354676afe236e2819fc1b7f2c4c604cb590" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "82687ce6e10c2fcc84cc42f7690d8fa72b297fcf10c42b356fe5b0902aefa4ec" "064476a572d48e954bf285c33917e10a206dc6e18305ef7b33a8e9edee12d79c" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e16a6ac555728d7cc0a93ad6f747afe0c1b8f5e5087ade1fdc0b08585ee535f2" "5b4770e4a9e993bcce1ea313ce657228b620b29e4ed873ceddd872b8f75c5609" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dca1b4876dfa97c897a0067dee74cbada04bdc1e92b8e984a815999ffa7fbe40" "3f7a048f2486de5c94a198ef454077868fdd220423e6255ced8bcc205579c237" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.ctorElim "user constant" .inherited (.inherited [`B.ctorIdx])
    "e49706a66c20b1ea8f001c4c496d74d3cafd6567677bd447fec0a3a6785dc94c" "4e5c79f9a3fece5958e95281c3f04048e52f0e9a90ef8f6f973407c409f9b987" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "87612022651d416fae1a9887e2d25b9bccc86753207748e8a6baac25593c085a" "310219cffc0ea9ce77292acc80560e8d6b846655577f668687cd61dd7145ee2d" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.leaf.elim "user constant" .inherited (.inherited [`B.ctorElim, `B.ctorIdx])
    "1c4cef29a29248b4050b65c1775cea0387f18c215a116af5325675bcb93c53f5" "c9798f36c19c3575893adfeb66bf636e53d24ce970974ed1ac01f3e30626a073" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.noConfusion "user constant" .inherited (.inherited [`B.noConfusionType])
    "119fc3352c30940c930472b32ac1175b1c5e12b0460974dca0897ce8885eff5c" "92c6213b7fc0728270aa55e1ead3625aa6072c0cb8fbff2732be0b56294df68c" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "28f2476a4b077da9f16152e63a6578c72b4f16917b92a9cf3261122b14ecfbec" "72438e24be71a952f07a99d8470facdc1e686366cb297059c514f844cfa342a9" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8506418545e3a8f96e273e6ec1054ce2a27cb455e5cf544a96d3ba1d8c4c2449" "36954ffccccd1451205a7cf2f8d4a2145398685ff143420f3f529a32ac5b9ac7" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "cc008ce1e8d15a1fc4ebf96569c3367f1236054d8fbc115679f75c1f4f329293" "ccd3ec3dcc20fc1964201f45b7bb48e92ecf3d3fcafbe655715d44a57fa59ea2" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.size "caller of a changed block" .pendingPasses (.root false true false)
    "d1d1b84b12affbd542eb57f26314db23b6c115609bef6ca69b6eb3946907df6a" "7515c07d9c2749d1343815252ff3fd6f7d739881ade8e4af449b77149e4488b3" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (no cross field)",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.size._f "caller of a changed block" .pendingPasses (.root true true false)
    "184b08ec1c68807cffcdb3404cdb2e19df236ca302ebc5b19a11d8296b3d73ed" "49d9aa883c3b9ea8747f23e8b1c7a3c40df13599d0f2c1cd0c37eae5785ccce3" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (no cross field)",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.size._sunfold "user constant" .inherited (.inherited [`B.size, `B.size.match_1])
    "21dbec313e8724b3d0f337a66dd05d90119f32ad96b8f488a828e8babc9fab8b" "177336a18774029db64c14e9b34c149ca33466cae75807e5c0e424d04eecad7e" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.size._unsafe_rec "user constant" .inherited (.inherited [`B.size._unsafe_rec, `B.size.match_1])
    "10db0a8d07fbaab0a3f129cb6b2b0dac85498320237c80b1aef4954ba06e52f5" "1e852821fb28dd26913efcb09040f5f487cd8228bdcef474bd48820799376ddf" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.size.match_1 "caller of a changed block" .pendingPasses .unexplained
    "230d63f362114454990af83c966ef48bdee0be34b3a2a7372f21ee9d1d5cad7f" "25a096bb8af14317d74331bed32d66fea0332dfd0ae659c748acc80139291599" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.two.elim "user constant" .inherited (.inherited [`B.ctorElim, `B.ctorIdx])
    "6dc7b0c4e784896aaa22009c69209a16c4d98a65f6d123cbc167aa22350403d3" "634c3c5c6637a8cccefe63c70a06648cdfc0e55f455d488eff7ff4a27fd62514" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.two.inj "user constant" .inherited (.inherited [`B.two.noConfusion])
    "e29bb0e1be29d64523c3f9d32ebd3fd9ad6774daff10258cd121d33156ad0b11" "56898090ef100d43b116e51e23bff3b4c801b3593cb6110f7ed761bbd200d93c" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.two.injEq "user constant" .inherited (.inherited [`B.two.inj])
    "b8bd7a8e7769362cf1706d1b13c1af4884f6c857f2b6e147f7f19d1df5f99dab" "e0e5820799e12a454219e7df691a5b39a26942109430551abb0003b6775bb3eb" "",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.two.noConfusion "user constant" .inherited (.inherited [`B.noConfusion])
    "9f658f381624819d2622c9359ee320a81a06ac2435d30dd4d24ad6e9614d41da" "362d49c424f92c18d7f2641f3cea721c6792028627a9257f0d937b78dfe2d4a8" "",
  e `Tests.Ix.Compile.Twins.Proto.C3 "can" "src" `P1.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2efa4bbd958d459004f3a93a7400ab7ba98da1688554df3e17a1fcbd2439a636" "757541206477da5f1aed7a4f6069168ddc96ad6897815cb4215d140048bd3c09" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C3 "can" "src" `P1.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d2d89c26f75ac727358474a7f94e4f3243cda39617619200efcd322e701c98d3" "a0d6a9f7105a2e25f72767aa82e60b9102aa3a36dc698a74ffa13f4644e264d2" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C3 "can" "src" `P1.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b39239fea24258438423f0a464b8cb32cacc283668fb10d77328c32e0ecd90f3" "43a1bbd268cfc7e918ba0b1029244ef4b94277d7ad55c112ec6c72d09231cc54" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C3 "can" "src" `P2.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "26e056cdb9eb90cb0103dfebbba0506eae6ab1fa8b4e892ba0c478e29fc7d3eb" "fe0ef7c47acd826641679345d88ce32d6135caf09230ac971cd6c06ce0952de1" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C3 "can" "src" `P2.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "02631bff3dbd7aec90361b15db1201ea59596ce01c9fdf0e8249a4f142b0c0ec" "f43bfe52374537caa6bab6039bb47e348205dd64f3ab201706bf0c920c4c6c5a" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C3 "can" "src" `P2.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "df87562805b13b3da098f668c41c2e2a1fa7a34c8c6955da0a176da010716375" "7b17790983f970ed990d6887a9a66dcfdd2d2d1f3269f5d84e966d6f9afd84c8" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C3 "can" "src" `p1 "caller of a changed block" .pendingPasses (.root false true false)
    "fe79fec6d1b0c2a7a6511dd85a3ae5407ce9f77705e235b76cbdab970db69667" "f05a5067cb7234e0422da400d9bd4fa2a9a6d12ac0f21212a60de263cabdf944" "value.λ.body.fn" "user of a split Prop member recursor (WB PropSplit: universe count; images, A3)",
  e `Tests.Ix.Compile.Twins.Proto.C3b "can" "src" `X.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2efa4bbd958d459004f3a93a7400ab7ba98da1688554df3e17a1fcbd2439a636" "757541206477da5f1aed7a4f6069168ddc96ad6897815cb4215d140048bd3c09" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C3b "can" "src" `X.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d2d89c26f75ac727358474a7f94e4f3243cda39617619200efcd322e701c98d3" "8c91a944c6505733a4f525d2b3dd0dae7c5adad9af49ced202f90c5b8ba73866" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C3b "can" "src" `X.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b39239fea24258438423f0a464b8cb32cacc283668fb10d77328c32e0ecd90f3" "33f4863c8256713a69dfa6a0a8444028a3702f46e37f9eee0cd6dd8398b1a1e4" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C3b "can" "src" `q "user constant over the block" .pendingCollapse (.root false true false)
    "fe79fec6d1b0c2a7a6511dd85a3ae5407ce9f77705e235b76cbdab970db69667" "f05a5067cb7234e0422da400d9bd4fa2a9a6d12ac0f21212a60de263cabdf944" "value.λ.body.fn" "theorem over a collapsed Prop pair",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "b7026d7e4027e86fbe090ab636abd8a416c3c971b1d812279d35834decbb2206" "d21ddd05d636f844de163fe5ff3c0ae7a9fe49623a4d8044f70891ca4bf74613" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A._sizeOf_3 "sizeOf family" .o11aPending .onlyB
    "-" "36110cd2e8e6fb2938574fc6b5491a1af20c3602a899dc7fb60e1972784a9fd7" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A._sizeOf_3_eq "sizeOf family" .o11aPending .onlyB
    "-" "42d337e078053600f22d2f6fea2ae0adfade6b64bacf1bda325652ce68e95de8" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "c9d5273c0cd7358fdd658363e800e780d218f2dbb4a459e54809caa2b5771f70" "5e96e26f1dd45f4cfbe51966f0f78fbb3d1d4c2648face40b909799e21b2495b" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.below "block auxiliary" .image .onlyB
    "-" "91a28ffcb5f56be00705de97a94f11381b1b728b8a48bf9a3db14947c8852e4a" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.below_1 "block auxiliary" .image .onlyB
    "-" "4c1ce33b261f2cae0d311e964844e499bc279b18639374368fb2ac14f3794be9" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.brecOn "block auxiliary" .image .onlyB
    "-" "101a1262072c241fafe779f7d9c9b95943360e1719cb505727376b242ed63f15" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.brecOn.eq "block auxiliary" .image .onlyB
    "-" "cff3047e533c51d61936b58dd97ecac65c1577e3a4af3d0d4b3c07fd6dde717a" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.brecOn.go "block auxiliary" .image .onlyB
    "-" "31c4e62e6a96fb006d184073c227f84d56b7c3e8be12c9f3d7add6fde2f2c440" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.brecOn_1 "block auxiliary" .image .onlyB
    "-" "784ce6e8ca906b0a43be68efe5515db6bc763f9a5e7ca5efdfc877fab39bbb4f" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.brecOn_1.eq "block auxiliary" .image .onlyB
    "-" "38199ce4669f45f08fd939f42b385bb6a6bed7b033f2adc2580b32dfab4b780a" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.brecOn_1.go "block auxiliary" .image .onlyB
    "-" "428529884300be0c4637b83aabc365aad465da6b7e9229f32630d7323bc95690" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.isMk "user constant" .inherited (.inherited [`A.size.match_1])
    "46fcd8066150788af73325baeda80e4f769a8e0ed4cffe6676f9210fc92c6aa7" "ac3a30bb6fe4cc1549dcb831393d3fb97a8ce3fc5f399e548e10540710b048eb" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.mk.inj "user constant" .inherited (.inherited [`A.mk.noConfusion])
    "a56748a2d93254e4060a9e9cb23d30d6622e6139eda5d5e17b09d21d00d2fbcc" "f00c5f2afcddae630d6cc06ba722be8f9800500e9e952a62faef16e223d256f6" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.mk.injEq "user constant" .inherited (.inherited [`A.mk.inj])
    "89791cf3e44a17692aff1bddd0e108f5b0332e2271a65c71da6594eb1cd20c34" "b304eb0bbd5e2d008befa102c50107d6782af49fc5d2d8d30f198c628dd0b44f" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.mk.noConfusion "user constant" .inherited (.inherited [`A.noConfusion])
    "8ffccbc5764cc9e8a2c4f8332fe3f4c5777b81a73fad30f4dce98b541d9979dd" "7e98cf4a6fbb82c2b04156a78f93917206131d182a6d3cf99f49c2d8e35b3f37" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.mk.sizeOf_spec "sizeOf family" .o11aPending (.root false true false)
    "62da2845006a89ddbf242ec098db179137bec49fd23f804e990969d2cc35c5d3" "c47e4738b2c89a7c1a32c0466f3694cfa40cda5127f84d5b82ea64e19fd5eb5f" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.noConfusion "user constant" .inherited (.inherited [`A.noConfusionType])
    "e33da13f8a61384e608ac707e002e06475c9f46458d8d67683c6ac6e3ca350ee" "fa43fa46b46abd4706092b08394c6d01333002b89b0087776986ddbf4bf0cd62" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "030ae1156180b1ac49ed4f5eec6a82408207719c56bb8724462953ced6d7dea4" "9a49dfadf6985009d708e56ae4505210b53d0abfda8152b37dedbc7a5751f3ec" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "001293f7f7890c8941d95ddff31e3d9e6a4bba42204d00a8a9da983677fec23d" "c6f4c9ef77bf9bb5326f5f668dae16b86df01b495c9565c39c55678c2966f57d" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1ed4553a14482ddca6bdd6edad60854958ec2a5487f219b7ea2746affb1e8b0d" "f5d32e768429ef56dcfd352f7c03888b2524947c48be691507328bf134e6bd55" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.rec_1 "block auxiliary" .image .onlyB
    "-" "c7f59215d14ef2b35ca5bbfd749f16dee94336156e2fcdfcca2525ddcca640c4" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.size "user constant" .inherited (.inherited [`sizeL, `A.size.match_1])
    "452680a03e8058a3e5013716db32bb59d45e11d8e1d3101e7d3faa5c959f82be" "c88da611928832fbe11b200914df7ef289814bc72e5b573a8fc040c7d254e9e6" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.size.match_1 "caller of a changed block" .pendingPasses .unexplained
    "b4bc96201e9f0fedcb358cda4055659b1a2092b713b6e8b282c96395920622b4" "1641b08d233a60d21ee92e697a83aa3fbe23d2b82df121a658cda2a9ac27c112" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.below "block auxiliary" .image .onlyB
    "-" "b0782747033c62bdd93ce0f6e1e54493b17cb7634107527fe80f240ae973e2fd" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.brecOn "block auxiliary" .image .onlyB
    "-" "922bbf33b177831e0ecbe06d0fccbd2b40428e64db7e38b38a64fa633bb10e59" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.brecOn.eq "block auxiliary" .image .onlyB
    "-" "877826a718d6a20dd2f42c33cc100acfd2c9e36232b8656f864a043c75463cff" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.brecOn.go "block auxiliary" .image .onlyB
    "-" "f280f4cd05ec7ca01893c2aceecfe2a89b1f0a1cf31c8c06e73102cfa9d1bc1d" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.noConfusion "noConfusion" .pendingNoConfusion (.root false true false)
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "abd3af6627f5d3c14eab547715953d68eb79793adee7b6b73ad6b4b0c82581f3" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "a13871a9d6c0f80bec0828b0d0bb5b706bcaf3036c0fd63791655cb1bf8a9100" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "62097ef059b0e99d2abee440f8691386cb2afd54beb68a2cf3a336a726852a0b" "38a0af07b0206343309225612792bd3d2c1d87b1b9b1e9c54c9dc98ee08115e1" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dfa05d5f71d78161d48645eae61fe74366ed0196a36d361827c4b360c8af6812" "239c0dde0c354de1bb9ac55d18211c95299ec5562eb98e636350c6c2a02a7730" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.size "user constant" .inherited (.inherited [`B.size.match_1])
    "c5c0c7f3ad8b6d7c3a2056d6b8a5c5a9923bae0c31f221425edbc4bfbe73573b" "cdb8234c000fdf25bc007af84894dab3409e9b68d22451d53271564233705cf4" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.size.match_1 "caller of a changed block" .pendingPasses .unexplained
    "b1ea810b383f4dbd7b749e796f7db68cbc10a01f96acf7709d4af3949d8bb9a0" "4129c74ecefde87ab2bff3f2904acdc49e8aec8740d1549bceb1afb47c4f0444" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `sizeL "user constant" .inherited (.inherited [`sizeL._f])
    "57fbe43a16a1109869dcd6a6717bcb4f4e8ab73a49f60118e8ea43704ded0248" "3fd9a7f0b03ab947fc7d900914c87693ce3a943fde578cd93758d2ee8a2e7859" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `sizeL._f "user constant" .inherited (.inherited [`B.size])
    "7c09a7fd2e15a49a6a69897e939217de66dd4ada7e2bdd5c58af911eb62ad9f7" "df5a308166245c3ac7dbe39bcbd2e1ecbfee25f251eb6916c84ff9d8a7544ad5" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `sizeL._sunfold "user constant" .inherited (.inherited [`B.size, `sizeL])
    "4e5f0c87c518dff161c783acaf4ea4708ddaa0e3413ee820cf70797b1a3aa189" "409c92b7a0ff46312b27666c0216b4dffcc1eadffc0faeb09fef078771721c04" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `sizeL._unsafe_rec "user constant" .inherited (.inherited [`B.size, `sizeL._unsafe_rec])
    "4fec5b5b9099ced16ce122212e937c4ae5e3fc74718599a5993d74282c720efa" "50d73ddbbf42db25dd68fcd0e1d10b03a4abc6c1ce886b9c275fda7743454f27" "",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `useRec "caller of a changed block" .pendingPasses (.root false true false)
    "8f6c02851a5204712eb85557310e53ceaf31f54c90254c741312c0e780fe327d" "7aeedf4f57b16518b3a1bd77269d310bfd4a003388820b7140099f3bf0a6b60d" "value" "raw `rec` user over a block whose nested auxiliary evaporates (O2)"
]

/-- Entries 800 to 999. -/
def part4 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "f3f9cc6a6602b8596c5bfbbc20987f4be2892697fb83368bcf1e2283b3f68a7b" "3065cd9acad534a6fd9f24cd399806c9e03b8a4aaa49b7ea7e324e3bf081fd59" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X._sizeOf_2 "sizeOf family" .o11aPending .onlyB
    "-" "a25eb4337f46d5b6292859c118b597ab4504b69a7385d60d1036766c75768823" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X._sizeOf_inst "user constant" .inherited (.inherited [`X._sizeOf_1])
    "0bb01d3cc9090441a4b6e2ebc8038a1ff31e3e06e850342abf7a5be8e27837a3" "26b433d08ab2345ae0ee9f95833f95fb9da3bc1a4f968bacb74551ae3d5945b5" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.a.elim "user constant" .inherited (.inherited [`X.ctorIdx, `X.ctorElim])
    "16107ddc18248b7ccccad13cc7b76b39febcc21962b84984ab8dd2070a21bbe0" "c75198d862f70349fc93d3883e2301c8028705585c85274afd7814cfb80cee33" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.a.inj "user constant" .inherited (.inherited [`X.a.noConfusion])
    "3fb46b0bb6ee82b33e855925ffa40315b616788be62d07411c4ffc45f51565a8" "d2c7d5c9d625bbd92169ae55fb85ce0d8afceb21236488e38ea22089bbd07848" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.a.injEq "user constant" .inherited (.inherited [`X.a.inj])
    "1917356cd419691dc94a7a54c0ec9781350524e1244c139252f96b6e9d8c7a20" "4e2910d8eab1e269cc0435b2b18d74948a4385560094cd24445193c75eea540a" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.a.noConfusion "user constant" .inherited (.inherited [`X.noConfusion])
    "b0a8929138060d1c635634bdcfa7cedd7c2cfba0cc376de8c5de511d3cf8cc5b" "f1a2109cfe6e51882ded42fe36533c37904790acd0372b1547d3eb4b26cff2c7" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.a.sizeOf_spec "user constant" .inherited (.inherited [`X._sizeOf_inst])
    "853a2628d1ceb69d1a65b68133be82b294e6575e9d0458cddaf8f2b5f57dc8fb" "4b36d340ce269a600d50891be6ae5a7280e18e5fa6bce619838bae3bf41a5f3e" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a17da90a847d92e8024d980f152101a3ee8f2096baa675ddc6cb69732b2d1ebc" "c285ec21b9ac97c61d17ed6637138e172c9392126700a2e246f27d4ce8808778" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fd85ad262719d83a12fc1d950e9cbab5a15eddf153ec38dbcd5fc507216927a7" "7de70c7cd8763f5d9c2fe8d82c4607a9394134be12e8c6a238fd838823b0b44a" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ab8acb574825a6d2c00a02642757cc90d37a478525eab15ffd76f53041572b70" "0a2b7d64c4838b3c2d288531867c0bb35e8696aeca3342796a78b20be4a1d178" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "597541cb7d1515de8618e8ab7f7f7e0f4f5693cfb3ea6be3dd1cb1fd8891e662" "064bc2e72f73d385c43914ee836d339161cd28662c58d3d5547ce8b5b0a7874b" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root false true false)
    "937374ed09b8b62f36ef75f06f1ee46dd487c7a9f3e74db919bde48bb76b2cc6" "c2d4661d41cb812f18de5092c847722e9806f220618586cc56e8cdfbb3437852" "value.λ.body.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.ctorElim "user constant" .inherited (.inherited [`X.casesOn, `X.ctorIdx])
    "f3db120744d25a57d5535442d6bb7d0923b45b056da302e19f82067a40f3f702" "42f88d1bd9a21685eb392c9496827ef142d22da18bb3b36fc96ead1d39603e72" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.ctorIdx "user constant" .inherited (.inherited [`X.casesOn])
    "2613f00a4d5923be077387ceeb87f0fe68cd361ae987bd818e066f6042264c17" "196fb28b5c37f4f0a9e1ae439f40f0042e492900446bc51a7ad3c7f343fc4173" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.h "caller of a changed block" .pendingCollapse (.root false true false)
    "7ab66120eb546a328d7a77dc24057c2590921b439880bd534377f46929624447" "49ebbf31bb4bd9aeb4d8c196ef434a29c09f703b71a83e12dea8f24a3dda9cec" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.h._f "caller of a changed block" .pendingCollapse (.root true true false)
    "c0ed98ee378360d330b40f22a2fd2b9a06153d051825644cec6ae0333f7250b2" "2cf15299c74f86ce42cd3b7ebb4c9d4ac0acf49ced21f56cb934c95bbb028781" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.h._sunfold "caller of a changed block" .pendingCollapse (.root false true false)
    "ca27ead5b84f96c21500cca4e0522c912e2547f9f9045e34b242979270809eed" "b85f4f6c13fe8c756ba563634e0feb45dd1534004e2c695c551645d06d2f3298" "value.λ.body.fn",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.h._unsafe_rec "caller of a changed block" .pendingCollapse (.root false true false)
    "9812e80ea5a87bfe8c706f22bcbb0088aec3f8dfdb907bbdef65aaa4271756e2" "0013321c1096c1f89ae02560d0caae920b9e9bfd71bfd814fa1f1c363568fbe3" "value.λ.body.fn",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.h.match_1 "caller of a changed block" .pendingCollapse .onlyA
    "8456b93a61151feea7878938feb7e719ffbef279f28f05c3e798f036ff56fa5c" "-" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.isNil "caller of a changed block" .pendingCollapse (.root false true false)
    "05cf888a8c9082b817f58d65e3cc02030d9a691139c71d7bae8c2b9897527410" "e5b6d064c80ce67a85c4f5f75b6367f9a250898465116a7de618351afb095d1d" "value.λ.body.fn",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.nil.elim "user constant" .inherited (.inherited [`X.ctorIdx, `X.ctorElim])
    "bbb6ffe937a7d246d1cd455b1e4f49eaae681c4fdeed60078775e57fb5a1dad9" "885aeba0ee1276695f887830b870ba5f30bc5939f7d81c67e04143ce9985139c" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.nil.sizeOf_spec "user constant" .inherited (.inherited [`X._sizeOf_inst])
    "a572550a6184263f6d3999ca82aa84c41b6e33ef8fa4c1ab4a4b72e95496e4be" "54b4288db5d14dfa34199cb58d10ca65aa4ba1ce70d219649534ee53b4644389" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.noConfusion "user constant" .inherited (.inherited [`X.casesOn, `X.noConfusionType])
    "567f68cba689df3ecee088d50c35c5224bc83709602c1ec997dbd49835743974" "ad1f01e0b43bcddb903a7578e07b8dc94139187e04452c5398f67da4f4423972" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.noConfusionType "user constant" .inherited (.inherited [`X.casesOn])
    "2028e58d86f9a54b9e53c4f4201b53ccac824e2a3733a06ff4c6a43d5d859b51" "5d8cc79549e7987db34159f9e5b36c853b531ad363fa70440bef847652f624e5" "",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c8322e03d558f85a8edc7fe68524013880ad0bbcb7dc890136d247154b230992" "df681a33a70885d2467f0443ffbb11c3f604824a24a4701b09dd0219d2cffb23" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C5 "can" "src" `X.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "32038f41f6815ac7654830d5262dd2880649a594097cc8af729505ce45c84ef9" "365b5efab9c077da18be5bde39551085bacabd0e875002da8e1ce84bda4be760" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "3b894264fb2b61fa899db79e1b64ace46e4c3391452a5711668292b060f6fffa" "985ff08fa8d8e09ddbd17874f2445dd1f3f85871e39cd2cc893d34d035bf3939" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X._sizeOf_2 "sizeOf family" .o11aPending (.root false true false)
    "c0d565ce645018032c7aae2532bd445df402682958293efbd1c1d5ed84832a01" "176446dcc09322674d80c85aaaf0fed03cfe9101bc64a26832c353bc438131be" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` over the split block; numbered names pair in name order, so `X._sizeOf_2` (over `List X`) meets the source block's `A._sizeOf_2` (over `B`)",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X._sizeOf_2_eq "sizeOf family" .o11aPending .onlyA
    "203831d813d2dd11fdb6657a41dbb43dc270341bb11c039dae14f3c436c1dd12" "-" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X._sizeOf_3_eq "sizeOf family" .o11aPending .onlyB
    "-" "8c3d5c60cf7778f688209b71df25948bfcfb2d650b0b54da4675a6e5aa7239a4" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X._sizeOf_4 "sizeOf family" .o11aPending .onlyB
    "-" "cecdff16d6ada8becbc5bbe3f4bc8fad301798755455bcbb2c19635ab096f020" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X._sizeOf_4_eq "sizeOf family" .o11aPending .onlyB
    "-" "21f302727c37ec9d8f63614ec36d9cd84de11655847179f8a32a5d573f4f5eb1" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X._sizeOf_inst "user constant" .inherited (.inherited [`X._sizeOf_1])
    "468712bc2de1630f0ac171407ec951df386bbd97f23749d2155361d355acf7db" "9ba220135b636cfcd3103987d63805193fe8769e81bca67b5f7c9000f8467824" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "393c19bcfc3d36debd4a341f75d8d9f92e1565f200b7eee52aec412d7576dc80" "87204dd3ef5f87d5aab746826f1541c203b25d6aa307c28e7475486cfed1ea1f" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.below_1 "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d7f5d16bbb3c95c180ccf2e4fc1be40b70d3c86cb5d2017748ff4fc9abb5e306" "c3638aebb88305b4e2b92bd13adbdf2a8cce0444d4762491caca86b9e1f54df1" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "708995f2027a2687064e5ce8c97e8746ca517fe0c46363bf775135e674447f37" "87c676aff09edbd436a0b360253062a15c90ed25fc443fbe153992a0718b7bb9" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "326fa2b5b47d23e5d607f0c447c0bdbd4f53ca35962801619dc3e580f991b329" "61dd69e95c2fcb23ddc97f2122c0988d59280a1efd08d97f52565201049989b3" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2fa3dba45c3558e1e33fae597b0aff662547030205229969c417681aee0fa2b9" "a792294b5b4f6eab16438a4c7c9b33b663ee1837d38118ec3bd331fb7b436a83" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.brecOn_1 "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6739616e5d84bf5a9240792f0588464613e15c9a479545a31b4acad21081205a" "23241a7ae7a117e26c5ac8bf5b07dc815792e0cae072476653b793ab69172edc" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.brecOn_1.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0e365d4cda30bffdafe0e6576d147fc6fc288cafa2839e85680713603bafa0f2" "abfd8503e6f42316c34d681a4448ff7d06627191285d4881f476cea00ae1931d" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.brecOn_1.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "bc2cc1290f485c52fa239c5176521e5ca35616fa432ecaf10746e5dada00439b" "c7f7998ec5cd3a4e09e1cf01545908fe85c0c64e8fde7cc33fba1a1b95752f74" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root false true false)
    "b5129a4db9760b668b3ce4c54bef6dde6f2ae7289e7da1820aebf54259d5c95c" "aa5294a61e636d9f8b9b40d3221b21df44c1c09133fc6472c800a8fa8e2bea3c" "value.λ.body.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.ctorElim "user constant" .inherited (.inherited [`X.casesOn, `X.ctorIdx])
    "cdf71ad7133b27c4ad42bf2a8913c0c166291e291e0c694cb79f9604b5f527d2" "01891a9000315265b2065b0ea36e9838c08426f294e29187aa36593004646eab" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.ctorIdx "user constant" .inherited (.inherited [`X.casesOn])
    "c00129f0fdcc04b1f23eb5d033abc1588e2b70f6e2569ce9b6bd5df9d12f4b1d" "318d7b7597afe40d4ed767995ba25dee8d6ce55cf124807f6d0f560f206f2194" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.leaf.elim "user constant" .inherited (.inherited [`X.ctorElim, `X.ctorIdx])
    "787244bf421dd3dae973713845b31ca206d9f62ac53ca92dc428effee645a1b9" "1070795a89583cb555c0e304196e0279d82306135d0caef34f3568264b6cf5b1" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.leaf.sizeOf_spec "user constant" .inherited (.inherited [`X._sizeOf_inst])
    "fecb57ac5ee4d217b6b500abc2c76553bc568e58d520aaa1c107c8e31a889527" "413914a3589a3d83e9f71338491d6cb7128a287aa9eae89f88be11be284537da" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.noConfusion "user constant" .inherited (.inherited [`X.casesOn, `X.noConfusionType])
    "9467af5e6275aca62adbb52893986ae8fee0133cdd61c1f9ebbd54110ef8963d" "b4080636b1fc2fd1c72cccd535c2d97c56af3355aada93a5f7f67266c6a7c9a8" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.noConfusionType "user constant" .inherited (.inherited [`X.casesOn])
    "1ea2dbced6cccbd13cc2fed49624085a5ec614d60ecddc7d534b34f3ab655fce" "efea47ec89bfe3948eb0b0385e2baf9646f3e972a6cb64f7f1ad58600459e3c5" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.node.elim "user constant" .inherited (.inherited [`X.ctorElim, `X.ctorIdx])
    "40ddd9eef32e24ee4ded078992b1037698c1ac9011878c9b630a0fdfa502fb18" "6bdc183f5e3d097a041b0ee16fb34eac0c1126681bc9bf2647b1837117b10c33" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.node.inj "user constant" .inherited (.inherited [`X.node.noConfusion])
    "2cac384d7ac546c6d236663e5c81f0bfadbd463e1311d26cab8e0ee51b726791" "570ba64ccffa3d5767ccb526a4b75ab9075909142348fec3b0be643c830354f3" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.node.injEq "user constant" .inherited (.inherited [`X.node.inj])
    "0898dda0d47e92d050ab5c93d410eb4561621824d2f9b506322fd7985a67e162" "24f5ded008758deed117c7e263f75f3e4d460a6f1b1d0eed4f1647650aa2ca1c" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.node.noConfusion "user constant" .inherited (.inherited [`X.noConfusion])
    "3b97266ece91e440ed13a1a4fa7c781d59f3ad93b4ce70eee7d4583871348852" "e2008047c54d1107ebfa632aeeeb3ec975b0762f4e00214de244b1e4a9ddf6b6" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.node.sizeOf_spec "sizeOf family" .o11aPending (.root false true false)
    "766d18254b7fe03d966e71b5821070ee77821ca810d179f405ded4c101530f17" "1022b6f55c92e7b990d8fb796cc745723f1d8ea8fa22678833b4495ad353cb0a" "value.λ.body.@2.fn",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "71e319881bd6ac8553779c53aadd388f7929e338ae20c90950fdc5d38c78142a" "aaa265cf1b22cc4d7214bf68b6d27d665939e2395b5da72eb72322031cb42e23" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c997c3f635a8f7df1d6b74a1328fbe386ebe7e057aaf84e2a0a0aecadafc13d6" "e58018a42149877be16f046475b20dd0e6ef7b7f71028a1ec12f2ed676c65166" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.rec_1 "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "257eb892f1c8b97c2e18a13a2f390629e3a9594fe2cddb6c0042e3004e633d56" "7047c78981dad793438fc076e08bd6a65b22dee19ce8aab1a76a1e4850451079" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.size "caller of a changed block" .pendingCollapse (.root false true false)
    "df9a1e202e7159fc0eb3faa141298171578ba209326c1308a7f646675ef22124" "6108a315aa49de15fe96309e59bc50fa2c3d22d23d7e4bfeae07ee1879d6d421" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.size._f "caller of a changed block" .pendingCollapse (.root true true false)
    "e1b2e6e6493ede7a08c11159867ee70d0a62b9d86d4e838117f0981f10d797f8" "0c23b240307f068960cb125261c810260a921f19cebb2d6524c1141d5a765b7c" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.size._sunfold "user constant" .inherited (.inherited [`X.size.match_1, `sizeL])
    "0db65e72c9423c5689a068bd3e74933157a6922151de8211058c3b392902a5e5" "0bebf38118fe7d609235a75ca5063b338f94c51a518cad4eee1da38efe5a4b28" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.size._unsafe_rec "user constant" .inherited (.inherited [`sizeL._unsafe_rec, `X.size.match_1])
    "307bde7844f927e0e89b1a3cd617c093b241b6d80620dd56ee1826fd37d28325" "cca965d805edbe965f54b5759b744659cb7f7f6582e9e60633ef344f4f363145" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X.size.match_1 "user constant" .inherited (.inherited [`X.casesOn])
    "2422320aa671b881b3e541524aae2380ca5f0382b97419a16afc01bca9f55f35" "1bcf5426b965b2d082588d8c5da557eeccc61e46b1cdabebc26d598629c72638" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `sizeL "caller of a changed block" .pendingCollapse (.root false true false)
    "7b6608b149fec240854e97969576ad96be59e29b5818cdeda80d3bd4c7e0f092" "6d17c51811a9b5d475dae7aee8e86a7753c634d73d631808a6c029aa8e13992f" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `sizeL._f "caller of a changed block" .pendingCollapse (.root true true false)
    "037b5de95dd4ac848ea561b8f9a4214f47c596a843db366f7dae3d009456d2ba" "30183927ded7446d9381eac438342ace030a0f6666a4992a646a9369e2558b5a" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `sizeL._sunfold "user constant" .inherited (.inherited [`X.size, `sizeL])
    "328e1c6620768a98be905083dfab01a606c5147e5cc0f98123862e76ed34c385" "f33e7560cce38b1a06f0aa5fc33bb71e5d0eec413cf00caf989db61840b219ea" "",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `sizeL._unsafe_rec "user constant" .inherited (.inherited [`sizeL._unsafe_rec, `X.size._unsafe_rec])
    "6b1465d98c72bd70854434743bd7eb0804cd87e3b353d3e5b7f7101e45ae2c8b" "8badaf5a31e92ba97ff6f55a6f299a4ff92590edbc5025ef4453014645e8ff20" "",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.below "caller of a changed block" .indPredBelow (.root true false false)
    "53acb2b8608ba369e98037abc7daba50969d9b44036ec45760b122b10f0e17f5" "07551a4833b86bcc8b0c2d998792971e6549f2528c522f9f44efd2bf4d5e7f55" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.below.base "caller of a changed block" .indPredBelow (.root true false false)
    "c87b0efe1f0c37dc6f34dc5cc0bf97f9c3ad261168031956ba9462c5b5295c95" "8a9a92d6bcc3de41d31ea2029f8f3d98bfb06e9965924fe6a5b71be559c9a2cd" "type.∀.body",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.below.casesOn "caller of a changed block" .indPredBelow (.root true true false)
    "71f9791ee9736deea546502882c6f1773ef55643f357e6e6b5fb94ea75a8e832" "8bf3b8ebc5070069ec9a71f1fd3c01c021c90251e3157519ae7ec267a0c7e37d" "type.∀.body.∀.dom.∀.body.∀.body",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.below.rec "caller of a changed block" .indPredBelow (.root true true false)
    "f9271aca22af3a01ae912788d8070d1b8c1c3dfb9c567c8792d949a793d0b3c2" "1c52850461e56b15fae7a8ed641add5ee309d7bb845df3b95971574195c7db5f" "type.∀.body.∀.dom.∀.body.∀.body",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.below.step "caller of a changed block" .indPredBelow (.root true false false)
    "8fbd9abba04bd38433cd8447a564c7a1a4047ee41c78657b132ae656863cc205" "67e48a0d358bd0134d087f51815faf10970b2696ddf846e16f70192a82b90011" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "db3c94835f1200bd20dcfc43ca1e8a49177d7a2a02476d24468a5a62d4db35fb" "689380685339cfbbe7efe75ea82da4dd53d4ffe68ee4c2be57367155cd2a09ef" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root false true false)
    "b461a3370e27baa9b3450432894208b316f0c57db3a4becd6d0f52e8dd909f12" "810adf606cb64142d6f1ef0c1f55a140549523b05c9f0cf091f192c980c88047" "value.λ.body.λ.body.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "211728abc24e611e9c9b864cc9b752cbcd4df9730e1e2f4a7a2a39253491558f" "125c03f248b0cc3bd39eaaaeb57997540f8ddb14933e9e84ee52aa6a093cee71" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "109f172da8343cc4e32344a375c665cf98c72748a6bb6021ea769b3a46a765e5" "cae15bcc9b797b18394108730679be660f7836d0ee0d29aeae43ff4ef8abe2d0" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.self "caller of a changed block" .collapseArms (.root false true false)
    "9286fa32b14a78f4a7c1928f9065999665a8963b7881d11a88626b05b1bc7275" "3271d21820dce2f9fa8f7e1dddbdb97a2aed5c8365dd07b8df85d456fdbcb753" "value.λ.body.λ.body.let.body",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.self.match_1_1 "user constant" .inherited (.inherited [`X.casesOn])
    "9fc155524c8c274610c91f2c2f35f30a782532ba8cf4ac397ebf57f7bf1a7326" "0f72850eb03ca9367f76e013a1297c0b6c6537005aec7029da90c550966d1cab" "",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.self.match_1_7 "caller of a changed block" .indPredBelow .onlyA
    "81f827493b8098b3c94644163b3a2a0728dc6d134e195b285c866f94be603b51" "-" "",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.self.match_2 "caller of a changed block" .collapseArms .onlyB
    "-" "663d3cb6d65560f1ef9ac7b09f9734b5918356dc2fc842065f63e1783a66ccae" "",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.below "caller of a changed block" .indPredBelow (.root true false false)
    "ac48626215f58b84951a6200edd8493cb0e2b1729da0cc2a5e9d951a80e63b9b" "179cd78213bf2ba33a6506fcd3175654a51afe2864e424f2933573b502cecbae" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.below.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "f58796a36b378f5f645862c885654f70e05d00636fa109ec10341de74486b97d" "e6ce8a494e906c592a2e8b6e5bc2f04115d7ecae3f4b7f1ceeed061ca2cc91e6" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.below.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d63d7fef20c35856884e233f82608208d06c952a5ab0f732e489af9fa6c42bbb" "b3e72e2686d1c5b07bf1e0e0d71e3f5b53b7c8812e41b9363e2adb5228c63a78" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.below.succ "caller of a changed block" .indPredBelow (.root true false false)
    "4ff4a7b4777bd8082cc27eaa028e1683077ae00a3a10b236ec3943d28c2384f8" "acb69e39f6b06238a624a92875cf1b5a54b02a997974b01834474d251552845b" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.below.zero "caller of a changed block" .indPredBelow (.root true false false)
    "14e1b660357f63a1bbd9c10511890ae57508c5b9da7c8265a01b2ff46acc954d" "4d188b115de84543e8eda21cfc6824155960ba9f497d8795d74ab9d371ac95d1" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "4b2a2e44f0571d15525d73bbdeb2b8f76e7a13e62d75cda44fc2bd5f8e013136" "8f8d97197e37a2c760ad22976483785d6c17aaa6265849e3760022fa209ff287" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2590c636307da2bfce8235aba20124aeb6d62b2471ff457d697502828d690f3f" "f92b61c2d92a4163bad2c56ec115480c052698fadfb9317bb36b10a9c777d1db" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "99fff1e46e8a41d7068aae2b7d37f92d11f8843d67b2ecd2f60d2ede7c6ee32c" "db994b737237c98cbb8f674903a30a39915695f7c26c9446b08f9a9372947fba" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.toR "user constant over the block" .indPredBelow (.root false true false)
    "3bb054b90e0582df85c92e346ffd1d629209328e85a6d36616531ab5fcb306f2" "ef73151e365e19a06fee00d3c59dd8170c139049a553569e13a33d882adedd72" "value.λ.body.λ.body.let.body.let.body" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.toR.match_1 "caller of a changed block" .pendingPasses .unexplained
    "34ede45369464ff064e993cf08f6c7292f243260d2b78bb48c657b00eae2bd45" "22edcae78b0846e4b30ffb5a9c06f32472fc0a52c85ffb1916c2a054ac8e77da" "",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.toR.match_2 "user constant over the block" .indPredBelow (.root true true false)
    "d4fd427576f9b54f7c46c99776b0c0432d74ee8979de5a39e01c7908f4003eff" "f6cb28d164909b24d38b89c74a243fc67d1fda9079f43fc6ae4b9f751a404b50" "type.∀.body.∀.body.∀.dom.∀.body.∀.body.∀.dom" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.below "caller of a changed block" .indPredBelow (.root true false false)
    "4016a00cc584cdb48dba00fd8bb3a3d09417dc143ed5429a3d18c6cc798d8d5e" "a76c0998dfb44daff9c6534b3ea2071b808f095f78910f2e53e98d5f1e9e9b42" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.below.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "4b23db824b280ff64c8e748b0ba2298ccd71c24f906a06dbc78644ec25ed58af" "4a307b54b1a214bbaa4bc875a1c0a0ca6de5f069bd65f8321fae2917990be911" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.below.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e0e5c9ee44f1c393da38aa0e9fdf8f05bd1886d700d7c51c7cc7f6137796e9e2" "04a65394df9f25cae07ec5047259db74f74a70c3da57c89b1aefc08a7f81d787" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.below.succ "caller of a changed block" .indPredBelow (.root true false false)
    "dacfc9a5799112ec4cafd0644456d2edabd94af27c74a76ea433b6e47431a690" "885c97b5a3c117902c18b19ba190a29ff23850d59694ee3636b865bba382330e" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "4011e1b581a4ff433da14657db54a13f47b18152a089520816a44d14af83ee5a" "788c5994b4fd708dceeb3de2535306a7be392daa71f9221d53f90ba84ade49db" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3b3a8bc6d340cad30ef70d1b96c853df855687be37ff89894e460327b0c12823" "718f1cc35ca5b442282ae1f99925b30ae7657c1be4480f5c03c05a23f41a1b0e" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b88f150298d041242f67e295f8732068189564960d7bac4df24672f0acb5f508" "9c387a550fe34dcc0e98ffb8a2275f6a9d89d69e3daf6e764d7931e8ce81ed25" "type.∀.dom.∀.body.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.toR "user constant over the block" .indPredBelow (.root false true false)
    "be619db32fe0d4ea5d256ddc9db477cc9769a6c29e9c372778aeb990a0b9bce0" "f3338fe7c772c3574e479c775b4ad53db0e2ac3d29bcb049dcf2d9c726866649" "value.λ.body.λ.body.let.body.let.body" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.toR.match_1 "caller of a changed block" .pendingPasses .unexplained
    "e4b667c69875cc9ea27011ff8ec1fdfce9fbf9a7a37336f47e62e86334911555" "5b87208daeb37f912524fd911036408e8bfe6083993050e63e1c228bcd1f2b9d" "",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.toR.match_2 "user constant over the block" .indPredBelow (.root true true false)
    "4e63421fe9885ad5f4197226213dda9164e3c1c9f129abe4abdffc5f35607998" "6fe9967e4d4ec08c59e3d9c716caeced8b838a3541e1c4071f5c95290d0c11ca" "type.∀.body.∀.body.∀.dom.∀.body.∀.body.∀.dom" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.below "block auxiliary" .indPredBelow .onlyB
    "-" "788ded5bd37dc690f2c95e126ecc6de3144b51e118ecb6d61e67712d0d7f4e55" "" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.below.casesOn "block auxiliary" .image .onlyB
    "-" "e296e146856ca61b65bf05712d06c16fded55ec4669e4a5006ebeaa085411e96" "" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.below.mk "user constant over the block" .indPredBelow .onlyB
    "-" "f66485c8c8a0314138f78bd71c107d24279fae3c344eafca722c590b472133f1" "" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.below.rec "block auxiliary" .image .onlyB
    "-" "35c7ab093484aa95c0b3bc4df1b16c0352ecbcbacafe35bfb393eb2af8ac08fd" "" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.brecOn "block auxiliary" .image .onlyB
    "-" "17f3b89afaa2bbc10ede5fe6f0414e6df29ca022a3e258b3b269d120b2aedcb3" "" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "312653bb0fa327f09917c16912fc34232a5b481cb0e4e95fca4c17c5da6c4d02" "3f1ca7dc8394e10e198f95e48935e82f6d7b026e88e20d191fa915357243975f" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "85f326c3eb67b413b645fd59e81934002f99067c8991600d2977004c7a113b09" "fc21710c960e0ed4de743110aa24c96afaa53502674a38c1e5240788dbcad4ce" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "312653bb0fa327f09917c16912fc34232a5b481cb0e4e95fca4c17c5da6c4d02" "8428cce36d65ef5b97c336822aaad5497d76f38a9e102d27da86536a51083941" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C._sizeOf_inst "sizeOf family" .o11aPending (.root false true false)
    "91fe08946a3682f5c478201ed18493e1a93b178a956790722e289a48104d1411" "2dbebfb1fac3b5d4b73ab3f78e701cc0ebaab9df52c0dac8768ea14ec05d0420" "value.@1.λ.body.fn",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6592d6b48818dbd9faa38a6d7a6d6605e1d1b570be9bdcfec1ecaddef860dd5f" "a0e4f22c6582e6e416d45942fc12c02fce1f00e7769072e0e22d797a30cd5857" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "18f208088e87a88bec0c4126ca8b2dbaa72b79089e906bc4f9a20588e0f6bcf6" "912bd70b8882a0a8edcdedd4bacf227b2ee414c53361472a78a435d23014fc4d" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a3ebe2ea2de1a87beba846a93f66b94045a9669da5a0ca109a809f2f34fbad10" "de4e80676d1747d0fb4885472f5826e9a0cf2d05130427fa0d7d11071de9948c" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b68b3f48312ceb93a4fe4c3418f611e657f9d2da65b200d7e528ce8eb6827444" "0a44589caea0780d7661277e49d3038e452a247d1063563cd894387113afed94" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root false true false)
    "f3fd05ba1dbe2484d997b7227533dd83148dca45fd75b452c6db1146ccf84e69" "b72a03924d3972205ad69e5834cffa1e84f2045463422120a46b4e202a293d30" "value.λ.body.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.ctorElim "user constant" .inherited (.inherited [`C.casesOn, `C.ctorIdx])
    "471b38f71db9f7f88847f579fdf823d1f4c163ba0f0d233f25e28156fed4ba62" "8a963951b6bcbf7f1489d525d82a3e08da9ee06a5f74ebd389ce7736b452422a" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.ctorIdx "user constant" .inherited (.inherited [`C.casesOn])
    "e9be2bc93c9281f14765682407b6449e5fb2536390d8490e308ac8ed69dfcd11" "7b07082724ac4b3bd5d9f8dda5f506dda22b8367053e4e939565f14df1ce811a" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.e.elim "user constant" .inherited (.inherited [`C.ctorElim, `C.ctorIdx])
    "82c9f61017a5d780cbf81f57770c41d45a833794dd60bfac4eb19a4088184c27" "01d01359252339cf4423e279e7a6740e338e1315e2d911f12ed6da351b9c4537" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.e.sizeOf_spec "user constant" .inherited (.inherited [`C._sizeOf_inst])
    "a56bcaba6f9e79817580fd8308d592489008db84da4950b38a90c9a3ca2d4c65" "76305e269fdaf43221a49974ad82e3423339731c27596657304e6b7a72902d0d" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.h "caller of a changed block" .pendingCollapse (.root false true false)
    "ef3f42aa4933f91d1e97c7871161819cd186d33a88eb130ff1f1ce4420658793" "0954f9483357e095ca2c420677b3c94c8973f6c49ea9c0561f36aa750e34cf6c" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.h._f "caller of a changed block" .pendingCollapse (.root true true false)
    "22f1e66272e97f00fe448a7e59fa5785a374e1f78b5664f66bb742075eec61a5" "84920c77938a34aad054ccef858d66231c8c732c08163928c1f36f55f07460fd" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.h._sunfold "caller of a changed block" .pendingCollapse (.root false true false)
    "39e0b13ddc6b00cfbaba5508d58a2b9f4dd6d707c15578594a95b6ed2ce8b772" "c36e582ed7ad97ba610bb278b7f8e3ff5c4bf4a70eec2056bdf873289c85dfd9" "value.λ.body.fn",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.h._unsafe_rec "caller of a changed block" .pendingCollapse (.root false true false)
    "ff2a0bb51bd71d070bfe8e350bd9037e1eb1c9b3e307d18dbe8e1db18d188e8d" "138ec671bd1fc6e3f2f0c6fbfd52b44d42796a50fd9aee999b294f8c1fb6be8a" "value.λ.body.fn",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.h.match_1 "caller of a changed block" .pendingCollapse .onlyA
    "856283511a4232444a404808f4cb07165a689895bded843f0ce706c9b13364b5" "-" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.isE "user constant" .inherited (.inherited [`C.isE.match_1])
    "243f5b6f06b162e0c6f0595c603e0501ff4315a5b7aeb58a6ba41c6cba1a6ffa" "fbc68a68441ae15f81fe765036c8ecdc7dfedce379cdfcfaca91660273e16954" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.isE._sparseCasesOn_1 "caller of a changed block" .pendingCollapse (.root false true false)
    "31e338a9289e341e86cec47d0b5e2caa25ddbec4f73ec1c7d3f6786b3304a79a" "95396dfb282460e864371e56a3555a84b06ce9147774a316760f30c0e3afae26" "value.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.isE.match_1 "user constant" .inherited (.inherited [`C.isE._sparseCasesOn_1, `C.ctorIdx])
    "97990fd887ad696242a20e574bd8584143b100bef28cba249c79063725a4ea89" "5930653a00ed33f8aad10a822860a2b9d9da093f784c2ff80fbc38585be5c990" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.n.elim "user constant" .inherited (.inherited [`C.ctorElim, `C.ctorIdx])
    "ba35f5b8bbcb261105385fc0c1450a93871dd18db696c5374258849bda16a9db" "cd40b7bee2a62b83e89eaeb3414833b0a9548ae670e917e637616552376971cd" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.n.inj "user constant" .inherited (.inherited [`C.n.noConfusion])
    "5261432f246e7d049271e245bec5bfc11aae72507a6949e4ae1404cd863dcb47" "ed45c66fe6405062444b9eb76573493b514442828d081536b2badb150cbe0190" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.n.injEq "user constant" .inherited (.inherited [`C.n.inj])
    "e1cfcc108ee8d778870e9eea8a2b56733f245d8d87c5d0f7e733da10ccdc6f8e" "2a426282937032c6f38240b180778d734b34d2a89badfb7878326a05b8b402b5" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.n.noConfusion "user constant" .inherited (.inherited [`C.noConfusion])
    "f72ee5ebd980711b29285a228787e0da55ff2f4e027b6f5a2b790d15c3662096" "b19d08efabe493d165f4a3d146ed41c824bc211241412304474b7a54da82f1f2" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.n.sizeOf_spec "user constant" .inherited (.inherited [`X._sizeOf_inst, `C._sizeOf_inst])
    "53cb04d58b9aaaf53b7b54cc7110020950a5864528d0d9fc48c819c9eafc86d4" "fd62962f3018f1c04fd51008a77f0842d97cbc85a9f942d2fe509a4df24128c3" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.noConfusion "user constant" .inherited (.inherited [`C.noConfusionType, `C.casesOn])
    "46455d14178d43dbb20ac69e2467cc4fe1ce853f6ef57f4db2455e706413adf8" "1cd6267b96a16e9e5ac4f3113e389375c5ae77fbbd44bfe375423ed70f8667cb" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.noConfusionType "user constant" .inherited (.inherited [`C.casesOn])
    "a9b26c84bd9894e5099db4a91e7841a53bdd91d8da391426578c17ca2c656ddd" "aae1fdc729824c6e3a668a4fa473b7e7bea7d0ef5fd03b5002f70aa1de6782ae" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c84b13272edeb24925d656bce950f924180d9364ce5eea6b00eb45201526e154" "06ef6b703cd4afcaba7654297a591a5a9cbded813638e5b28bc3a0ca4f63659d" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `C.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8f13608c4f86cee45f69d66cabc4adaf8fffb40022460077ea455adb01ed7adb" "a260b1d75f97387420ad333375cbbcd5902840ea42d51341d234f5af9fcab179" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "4df3202436ffbd70a6b1d5c75d7ea85dd0830c7e39e20e3970fa53d5f37b787a" "2edc2528b2d1aec786557670b61916a21b523c878bc0f2e649077a328ba408c2" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X._sizeOf_2 "sizeOf family" .o11aPending (.root false true false)
    "8ac1ffd7a325a4cc834a0db80f114b18eb64eecfa0788eddcbb23ccb1dc11022" "e7c27ad11ce227f653dda73bb886144a2d8beac974319476527e359dbb05a31b" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X._sizeOf_inst "user constant" .inherited (.inherited [`X._sizeOf_1])
    "ad41f074d6cd167050a2d658c140c0ea24d874307d19f62c1c590d197a92afc9" "dc65430879c204fbe617511a158c5ff37fd7eb70f78cc29900b1d955cefc0387" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "f4a50e7d05b1d1b709bfc1e926d7b50e4b42c04fc7669c57cd54cfaa213bea2b" "58a9ca0b5cd41e686933127bd126384c606220d082932b13b65550eb767a7caa" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "402279f60af6fbc277207c1bc351bfb8c45f2f02854eaa4ceaf1a7827a94f585" "517d9531b7448e83ba4bbc9b1159d25983de40f0df4192263e478abe482fadcb" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5f4992ab19e74ee1fe40f781f0bb307b2ba142ff9a1b31414c3153bbfbaa0e52" "ea85ec5534971bff0abfb24bc49c96ffdd021c8c216516830ba62edac165fba8" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "79659ca1c5d6856dd5b89842d6d9b208f6d92a011569f33e8e683765a4005063" "01b9f907f76d7cf82d2069e8e03975cbd5c64da50812f2b360fba81d285959a7" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root false true false)
    "f0b07f995a472afc5818d30b96df272fc18416b32b4c6e83e8653f7cff35f512" "5aa7c9732b647101475a4d8d28707dd17887caaef0ba782384dc99da8f0c3081" "value.λ.body.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.ctorElim "user constant" .inherited (.inherited [`X.ctorIdx, `X.casesOn])
    "1d691a3fea45edf55554e36348228c671f49d32e75af8641d14bd67f9c3b5f0f" "357230a1e8f3d48b010b7d428f5be42da95a3890acb12925d59a7991e7c0f3d2" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.ctorIdx "user constant" .inherited (.inherited [`X.casesOn])
    "7419dddaa67dea7842d13e024e33b377869ba44600c6962f62deac1cf5722509" "9f1ff4c283565ea540040da42c9689e3dedc031a4c16e3df52467accbc797391" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.h "caller of a changed block" .pendingCollapse (.root false true false)
    "1b61c85dcf983bfcc24851e64f90f5f7462be26d7ec34faa618bc0760a80703c" "eebfe1edb3a39dcf09f2cce5ab68a19a51829df928dc9794cba1a8bf748836c5" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.h._f "caller of a changed block" .pendingCollapse (.root true true false)
    "f359a3763db5d670d50f9dba49641686aaa107206a723e0d8ef123b0af7ee4ed" "0ed1968f0a4d68046e6af2e382caee31059d5739e2b8538dedad16052f01bc6b" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.h._sunfold "caller of a changed block" .pendingCollapse (.root false true false)
    "76c59a6db313d0db52ee4616e35cde1b193960a6f4cb2f6d40f14a7db69426a5" "745656e0ee22368b09ce7c83cc074a6c39e3420a7e40b64badfe0abf96cdbcde" "value.λ.body.fn",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.h._unsafe_rec "caller of a changed block" .pendingCollapse (.root false true false)
    "d69c095f4f8ee5699b67a9a77f52d767ecba8c310570a7a65e139e2f587b50c3" "b29beae6316652214f85adcca5a1546747201c14e97f4b757c0790cf5f75d520" "value.λ.body.fn",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.h.match_1 "caller of a changed block" .pendingCollapse .onlyA
    "8e1389c66d0458a032df670ff10633415c00ce8a2e46ab207a2173447c866fd4" "-" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.noConfusion "user constant" .inherited (.inherited [`X.casesOn, `X.noConfusionType])
    "651f6e39a1359126951895de03225018ab50fd85caabcfd26a22f383395ac5c7" "b971b438ea7ce9586def6da7b5959434c0ad0f12b0c826c581217a33c6d5b24c" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.noConfusionType "user constant" .inherited (.inherited [`X.casesOn])
    "296af3989fb1a9bbf97a59d656f36fd9ce3a761d4b39b0cf86b6e9352e68fa18" "dda562bfd50d237c8d20edb760a8b61c409cef8f320dd0d4765e8600c6aac963" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "21bd436add8d2a123217186c00606ebe19f6c150d57a38100a7bb7638e3b45aa" "ab2189a5a647556d0c675f52347b2dc822c367749cedb98aaad50e95b147cf50" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b0179d12aacab6290d221a78f05017fb716f2cc2a1aaa71bf091f0d8da6777a8" "791c072d8465e745cd3cec463fa89f4577e4b0f4e7f9c6e6f8617bca364a1333" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.s.elim "user constant" .inherited (.inherited [`X.ctorIdx, `X.ctorElim])
    "b842f09986bd8205863da45ec3abb5cd9940718cf3ea08b5f752b0fc0e1724ad" "2206dac49b3a511f8e3312163f65e6e0f78d47a7b8566470c12df72d7c2a0e6c" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.s.inj "user constant" .inherited (.inherited [`X.s.noConfusion])
    "17a89cb6f7c0554559dffb423aa094e09e2a1941b9cc68fd75461cbec785c59e" "2f88e5f13ec4b702e37219732568e11ba994e2a7b6691b5c0830b82375db98df" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.s.injEq "user constant" .inherited (.inherited [`X.s.inj])
    "a051501e65fcf2cde163af7b6bab4c5673da095f10c10244b19042ae0aa8c4d7" "bef07c557385cd63aa1a8decea6e722dd7d19c3a0ac4b5738badfeb73ab13368" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.s.noConfusion "user constant" .inherited (.inherited [`X.noConfusion])
    "2d521d1fa99a3b74bfaecf8101f69172b2a4d26d0873cbe692f223e2a451d2a5" "cc02b3e015b9c04bd6b446bb22840111ab16ef21222a8e3e63636d98196eefdc" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.s.sizeOf_spec "user constant" .inherited (.inherited [`X._sizeOf_inst, `C._sizeOf_inst])
    "a3b1225ae3473d9d3271495559449a3496a3fb272c503853962af6d35a87c83c" "da2178735e270d1e3c5f87be18a2dc09fe6fe52ccd11f621405b920466359563" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.z.elim "user constant" .inherited (.inherited [`X.ctorIdx, `X.ctorElim])
    "d028eabb3376dc94cb3bca9b2e91a8495ecb7e08da0259e10c9382780f5d12c3" "f5f5a0721b98bc3b4640c38c550545052ac3d61f45c8c73afbce7c6b1ad6440e" "",
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X.z.sizeOf_spec "user constant" .inherited (.inherited [`X._sizeOf_inst])
    "1c5c0e6939b1ff906f3f6e9c08fd919cb710d43979f17f8b718f3d4fa1d0a2ac" "93d2881c45b1b27520c7a4a18647425c18660298402e7c2bf6fd52fd3bc722a6" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "f3f9cc6a6602b8596c5bfbbc20987f4be2892697fb83368bcf1e2283b3f68a7b" "6ff4c385e41e3e32806ef2c225b61cb33d09a17e3989bf3157aa4f480da6bbf4" "value.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X._sizeOf_2 "sizeOf family" .o11aPending .onlyB
    "-" "a5854b24dbfabf9563e57fbe83915173d29073bb45121457ded4aeda09b59219" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X._sizeOf_3 "sizeOf family" .o11aPending .onlyB
    "-" "68b2d29f7bedb6a0a94e4fb2c2863fdaf4571e224ffa1c1dbc722e2767d85b49" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X._sizeOf_inst "user constant" .inherited (.inherited [`X._sizeOf_1])
    "0bb01d3cc9090441a4b6e2ebc8038a1ff31e3e06e850342abf7a5be8e27837a3" "ba1ee4119c99f81a42fc904fc2cc1a9039109f07b28f58f6996399f6a79a1b15" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a17da90a847d92e8024d980f152101a3ee8f2096baa675ddc6cb69732b2d1ebc" "0fabdbee5b8a06028fb8f615c238f1b4dc81957da2a7ecdf2e08223010cdf036" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fd85ad262719d83a12fc1d950e9cbab5a15eddf153ec38dbcd5fc507216927a7" "ec4242ed37ffdc22cf751c0b42e622b10b6f3ba2bf8cec68c4730365d4dde417" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ab8acb574825a6d2c00a02642757cc90d37a478525eab15ffd76f53041572b70" "106296651439ff150257c33df7988673d2a47a201a5d623ede59d19c97940e0b" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "597541cb7d1515de8618e8ab7f7f7e0f4f5693cfb3ea6be3dd1cb1fd8891e662" "f88284524b7b53c0d33ada6389d7c4d07b35dc63cb2ed80513e485ec5267542a" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root false true false)
    "937374ed09b8b62f36ef75f06f1ee46dd487c7a9f3e74db919bde48bb76b2cc6" "df7c830529de45d5c79a12499e8d6be5c327e9454979dc0cc71a39c84cf1c60a" "value.λ.body.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.ctorElim "user constant" .inherited (.inherited [`X.ctorIdx, `X.casesOn])
    "f3db120744d25a57d5535442d6bb7d0923b45b056da302e19f82067a40f3f702" "43b856ac95282ed2a7d15734a130a9947e3f15a525b79ae3cfd95c7e913a482a" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.ctorIdx "user constant" .inherited (.inherited [`X.casesOn])
    "2613f00a4d5923be077387ceeb87f0fe68cd361ae987bd818e066f6042264c17" "06b6974564c1d43937a48bb2ddca3a3b86c5089fe07ad70d3278c1403cfd1bf8" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.isZ "caller of a changed block" .pendingCollapse (.root false true false)
    "05cf888a8c9082b817f58d65e3cc02030d9a691139c71d7bae8c2b9897527410" "5c566cf0cd303a7c8b3ea22d16324eb70d8a68c3cb55d3b649e1d16f01bf29e4" "value.λ.body.fn",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.isZ.match_1 "caller of a changed block" .pendingCollapse .onlyA
    "8456b93a61151feea7878938feb7e719ffbef279f28f05c3e798f036ff56fa5c" "-" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.noConfusion "user constant" .inherited (.inherited [`X.noConfusionType, `X.casesOn])
    "567f68cba689df3ecee088d50c35c5224bc83709602c1ec997dbd49835743974" "ebed579f5bb52537e263558b74792b129356ec722db4c3a274395c2c19a0c39f" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.noConfusionType "user constant" .inherited (.inherited [`X.casesOn])
    "2028e58d86f9a54b9e53c4f4201b53ccac824e2a3733a06ff4c6a43d5d859b51" "3d28e0aa2c90a409d92ff21b4a7c2febb9ea63fe8daaa0071d8746895d242121" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c8322e03d558f85a8edc7fe68524013880ad0bbcb7dc890136d247154b230992" "8a039ecd14d4291031dd791c25edd99c140cce9878769e09958d7702e1a8e026" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "32038f41f6815ac7654830d5262dd2880649a594097cc8af729505ce45c84ef9" "6a3049d3f9938738c6d1428915677c005108f6defa8bdf563f484f455b7cab89" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.s.elim "user constant" .inherited (.inherited [`X.ctorIdx, `X.ctorElim])
    "16107ddc18248b7ccccad13cc7b76b39febcc21962b84984ab8dd2070a21bbe0" "d8360ee26145ac62ffbe16a44e9ed39d5295177b2fa10f39a2fee2de7d645e22" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.s.inj "user constant" .inherited (.inherited [`X.s.noConfusion])
    "3fb46b0bb6ee82b33e855925ffa40315b616788be62d07411c4ffc45f51565a8" "63cb4439bb84c47f1618895e926965a812fcca4217b13bc188152ec60e30409b" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.s.injEq "user constant" .inherited (.inherited [`X.s.inj])
    "1917356cd419691dc94a7a54c0ec9781350524e1244c139252f96b6e9d8c7a20" "b21c3dcb5edd9df35ba4713c86def9d020097ddb1457a9f39222ab9236a59594" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.s.noConfusion "user constant" .inherited (.inherited [`X.noConfusion])
    "b0a8929138060d1c635634bdcfa7cedd7c2cfba0cc376de8c5de511d3cf8cc5b" "2573834dc0678d6f7cd2d4bc5000eab788d2dc6ff68b8f175f5cbd6fc8b97159" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.s.sizeOf_spec "user constant" .inherited (.inherited [`X._sizeOf_inst])
    "853a2628d1ceb69d1a65b68133be82b294e6575e9d0458cddaf8f2b5f57dc8fb" "3010c5e9e181d5350bc0ac291762cdb97aada24463324325ceef9b5181eeddd1" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.z.elim "user constant" .inherited (.inherited [`X.ctorIdx, `X.ctorElim])
    "bbb6ffe937a7d246d1cd455b1e4f49eaae681c4fdeed60078775e57fb5a1dad9" "37341c58d3597a37d588b31bc1ede4764f4a191e5a4ae3139988314117f727e9" "",
  e `Tests.Ix.Compile.Twins.Proto.C8b "can" "src" `X.z.sizeOf_spec "user constant" .inherited (.inherited [`X._sizeOf_inst])
    "a572550a6184263f6d3999ca82aa84c41b6e33ef8fa4c1ab4a4b72e95496e4be" "4d9023194f78c32bb718b1c52753039310738a9ec77333f7dc19cf133766660c" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "3fd79d6295e2750e0d18de5b6cd9d75489830c72a379ee3ef66ee712b6079cbc" "0568bb50f61b112ca13288f082b1920a3aff93c887ef44db92c1b3b1a20e50f7" "value.λ.body.λ.body.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "a1d896f3080d0d531fd0d0a1f3dff7f06e256f89f2a75b440d1cf5f0a4b58ac3" "4ebd977e8266bebe8e9ee7cb57c4fbca5bb5c608cc2a26fcee42353611c4f7fa" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.a.elim "user constant" .inherited (.inherited [`A.ctorIdx, `A.ctorElim])
    "7d07cfcf086949c41a384a6c47b563d5fc57e2e26cffca6fdcc5bf507a6d7f5e" "017199c3bb225c627baf34f09ee7cfedc1826b28aaf266b7d5bd7a9734d3d2ea" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.a.inj "user constant" .inherited (.inherited [`A.a.noConfusion])
    "8662ba33bc9031c4513b7c06d034a79a5365ff8bb803b9ca971b6fbadf9114bf" "ae47bca13da68499d7abfce35514a85d308d25d961a2dc8397d9bc672efe4e11" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.a.injEq "user constant" .inherited (.inherited [`A.a.inj])
    "fbbd79980458064ea5cdf3d83b56726050a86f41aca6e4477519b6a56f7300c1" "c00529cd527ece48fad2b70fc153e70b392f00f80db22d9a0543e43f5ead8dc6" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.a.noConfusion "user constant" .inherited (.inherited [`A.noConfusion])
    "60058ce6072e4f6bc1c4c1818bd89f2d25aa8a30e7a699e8f42cb3c827df0df3" "e05710627cea5559126be3e79711021a410b185850951867a3b532aae5683a24" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.a.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "204d851c73e29e97ed79ec34676ab30109f86d80d438d3249f722938d7f5d09f" "8576e3f9b0bda46111ca555e542cec5b5c6faf4d3881e4274df0b255603dfd0f" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3635caecef138b7c291e8f63192d852092f9cac21a5d58a4f8576017fa6aa6ed" "48a7790bbb69f0e5f94e8d85d74044e6d50a941716e683f167ba63c6b6d81c82" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3a24af0ef3aebf3693c541e110d8abc41d05a3e556b6f43afd7cf6b126cc74ad" "3cbc2c01dafd05389c25dba48d9578c266b074b5525ea1b3f5c01892149316c5" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c45597871edcdf0f86bee0605379bf84d5d1cc2efcfbb16a0454d45951406eac" "d3eaa8132eb775787fb424b4a84772671a1a2469e54406d226549142a4052d4d" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "445126f1411307c03771a7219bf1400511821f4513fe3ebfb52df5d16cd0fec3" "5ba59c80129a46b3a4561edf5662fad5a6af6715b3da5704c0abcad98599cdc8" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.ctorElim "user constant" .inherited (.inherited [`A.ctorIdx])
    "024285c94875f909fd6a91160de5b24090babcc9090e48c1517aceeb3f29e220" "b8e120283f4ae171a0b843ad1686fd517090e4b9fd8eade5a1130829b4af275c" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "bed8953c913052854591201ce10e202266883099db3fe7fee91a82886660433b" "6d7394ca5f65e9920a1c1de2bb54349e3975a196502e27d2b110948c712d45c6" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.depth "caller of a changed block" .pendingPasses (.root false true false)
    "6b89d0d2e6de373c3c955e16a54e64d2a36d38bc13bbc28810893aa3515c811f" "3a4ecc5b9134ddc78e184651b4a400c800e4ca0d74aaad7275f8aa8d13c07f16" "value.λ.body.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.depth._f "caller of a changed block" .pendingPasses (.root true true false)
    "8fcb310ec4de65102343f86a9581d01f163665862a4716bd49277468697d434d" "52093855bd5b791fb0317fb12302bd34716134f6f41e7f2b20495b4e76a99033" "type.∀.body.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)"
]

/-- Entries 1000 to 1199. -/
def part5 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.depth._sunfold "user constant" .inherited (.inherited [`A.depth, `A.depth.match_1])
    "e28d8f1382b9a037a12a52ff4416a54433b84e70baf9923a0f6fe8db63965460" "835cfae235d9b18d581069f3049093b7801c0ab6d5e4e054b899a5607eb45a22" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.depth._unsafe_rec "user constant" .inherited (.inherited [`A.depth._unsafe_rec, `A.depth.match_1])
    "407a01dde5dd2db7163931aafbe789267268d6019b8c86c79051ade3e3574d91" "b09deeae8a5914794a71a9c3d28860328a0b65124cf00b66f211b8af351b267e" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.depth.match_1 "caller of a changed block" .pendingPasses .unexplained
    "091a409b502f54a4a52721ddf2351f80537ef7dc995be049c85450eea801d6d8" "7f5e02ff604ba7d56141e346d304b270a4ca61dca344c00ff89b250294327df7" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.isNil "user constant" .inherited (.inherited [`A.depth.match_1])
    "014f30f2e46aabb8a590040195401486c33b6ae8cd2b500daa13d85c6b215788" "aa72636da71385cfd6d22296ed7788092d609848ad8bbb857e8e1be338187466" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.nil.elim "user constant" .inherited (.inherited [`A.ctorIdx, `A.ctorElim])
    "13b28453d84cfedb93e1ceef97105ed1bbc5db6a45e72992856933be1ea64b18" "678958b8700801196c8265cf622a0666ee4e5b34504838f69e6edb46b67bb05d" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.nil.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "63d898cf8525d6be264fd0d7010e8997f947bfabdc9e9e9f2fe2baf88f9105f7" "285f4ab655b4b30232718f383a7110b92a8b907818e588102c556f5b3cdb0632" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.noConfusion "user constant" .inherited (.inherited [`A.noConfusionType])
    "f8e3d20b7f15a29c4bf3d9061d806d7d4e5c08e48c208d1127bad3400c5fba2c" "a895e10cd9538a7d52d8baca488d6f3dbc3283484e405a23b848218f64cf25df" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "aab05adc2da6d7ebb27375f2c382c16b6c99c8f0a56dfcd11c32b019d93be275" "32f08bf2de04f4276203942425feb742fdb3d5aa59a0de042dfb4478af44c27b" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a01edc74ebc4071abdd7ec7f35cfc38da692245a9764e5d98f59204dd902aa86" "95cfb2f4803902b089395617c9b16ee347c8079b759aa28d9e4348baa1f27433" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6b0e9178d2044078f7ef5ed01f0c0deacd961e2aa43ae44fc31ca2eec9026e98" "561e81efbc0c1ce6c990b30966ec94db6ae98c476a0f6110fb1f0063b0184f95" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.below "block auxiliary" .image .onlyB
    "-" "cb6f32f746d2315981cd805fe676f0eb97ed44a21fa27ae8eddc4e00948128dc" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.brecOn "block auxiliary" .image .onlyB
    "-" "7b6b5bb433c778b54f1c01e9d9a86314d23bcc306b6396eaf86926b544e9174d" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.brecOn.eq "block auxiliary" .image .onlyB
    "-" "8848be1857f85e351b18ea9190b9cc81d88fba40571252e6605a80f7c495be10" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.brecOn.go "block auxiliary" .image .onlyB
    "-" "978d0334cc26b28bc30387abccb3e498a0d21e0f60a906b896c5a1c66cb8c4e6" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.leaf.inj "user constant" .inherited (.inherited [`B.leaf.noConfusion])
    "dcc19ca4c75834e1774f3ce896e9b41cad3dd14fa46002f8951e4bfb59194d18" "04d75c4abdddc6220c48c3cf03d218c8a2ce94657cc210db94a03f6204aa3e29" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.leaf.injEq "user constant" .inherited (.inherited [`B.leaf.inj])
    "a44774ac6f15c185ba511dc9857e8087f05361b024b6074dfa355be79e6614e6" "227dddcc9caca9a4b31e9598169ddd7c913bdd2c6251cba341aba437846cafb0" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.leaf.noConfusion "user constant" .inherited (.inherited [`B.noConfusion])
    "1c356838273129df95934b50a190932160a6623e0c4eb7e21f71ccfe8b244f24" "b4202149637b3ddee1f5698f0517e27c11c81d8a7b1984a84d7231c9b0275a49" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.noConfusion "user constant" .inherited (.inherited [`B.noConfusionType])
    "96cddcc036cc224c6d5c34976ddf0c5b9cdb9c2b980c482ce130deecbd2f3a0d" "f8ee9459fa4fd9a18dc674303b4b5bf1c2382a54b386737cfd83f0b1a04b2392" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "e1292b7bfc5fb1088a3cb272660b8ae02d35d7a3ad8efdd4ad0ce4ec30796898" "b772d3d443e93f9a6d52725e90d3702d01d6790aac709b05bac4c006ab45623a" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "bfb8e5d06d05119634683715ca38516ad72168f4cd48a90e040e283fcc972d0f" "aa76e778245b7d6566c448c201f469073d89b6c7e25bceb7f059266f278c9d98" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "47b5697ba4ecd3f89b0f7a9677b49a14c16ab77388bf859df38b7904c9140535" "da75c532660f0082f01d817f689895a4ee4cf6a962185ccaa67d117490b0fbbb" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "dbf6f920d724fdaa828433051ff7e85ff0f1d6639f32ed024285044487695b75" "bbaafd707792d73e8900dfb443dca97a22c5e4318921813d74b1e222b9591967" "value.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X._sizeOf_2 "sizeOf family" .o11aPending .onlyB
    "-" "a88bd4c1a78e0f52e65752800faf89c207b21bbd4f8a89184e3e0f9b4ee14cfc" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X._sizeOf_inst "user constant" .inherited (.inherited [`X._sizeOf_1])
    "af2af752ca560482f21b862fb77d5997cc57cf476840d78f8bc48792c204d991" "610221fab2b025ccc13d60d5a0a141ecf02f096cb4ae31d241389fc8262a21da" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.a.elim "user constant" .inherited (.inherited [`X.ctorIdx, `X.ctorElim])
    "138aea3af0ab2beb2078b7e92de1eb47eab1e0054de44a0009d40caf4c67bd99" "096bcc45426f150aa924906eda6b887b991377517d2987c7c1d3abfdee4770d1" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.a.inj "user constant" .inherited (.inherited [`X.a.noConfusion])
    "a101c579e64c3ecec51014916e1b9900ed32b3d33c606cae7f71150d9a05ae75" "8895f53e8c2b1a56501f0f195456180b8e6f17b942ab07d14870576bddcd3abd" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.a.injEq "user constant" .inherited (.inherited [`X.a.inj])
    "2f20f984b877e9b212b11144666b4ef651f6f5a2f211028781d8f1e3a69059e9" "6acb7a9857e7ef78fc86d2c48f57016fa37334ee172596a6d3d7670548b3839b" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.a.noConfusion "user constant" .inherited (.inherited [`X.noConfusion])
    "5036d4cd71659292935751c4ac9434d67274830d9c73797b2801b5179ff155ed" "9b1fa06e4a0d51a93e92774ff9cb1a24a91973815daa028e37a9a670b34efee7" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.a.sizeOf_spec "user constant" .inherited (.inherited [`X._sizeOf_inst])
    "52c9e6b3c5b5f9c0b43024870b8f0ca34932747862dbda8b7e020344fe74b72a" "93028011416eaf6dd578de04c8ce029f361a4268c24ec3543f1805cc299be84d" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8820e266093adfaf384788c5097a41221f86e15eb11fc98831ebeaff8993b74f" "bbfafbc4e5717a2d1a730b806c13a3e2170d95dd66a56411d8eb8a3d50e5db01" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5a405f9be4146334e6b5d61c72e8103c03a623e484183f267a8915a47394c5fc" "ee347ba140e067b6888b14db3c9d8e3df3b15ba2bec2cd758bfd5f2cf7013f65" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "031d26dc602b3acb96fabf685508acc37e9ce6b84eda5ecc80800c0f2f71c76f" "d8ab4ede74113c4675bf836289b52cc438c5b8131e2123b38cd39a455bcff048" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a481640a4ce0c76be876db7227e3ac2cebcc6844bc5933d9eeafe1fee166dd60" "d5aa73e0ea034014dc3badb83d0dd8323142e38a29c129eba40205ecc2b22474" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root false true false)
    "e0bd61e3459b909fdf3f6840d85ff4538b95a4d669dff97cb6b2a9c477ad3614" "1083d8916b577df11d0213ed9400909165e5cfd044499ae56e7c14113b67cf28" "value.λ.body.λ.body.λ.body.λ.body.λ.body",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.ctorElim "user constant" .inherited (.inherited [`X.casesOn, `X.ctorIdx])
    "e9cf4f92aabc14ee33db3455501a12d20a1f8908ca668c16e8d4ca22292242fc" "73d2b4987492099ce399adbf6a53d4df1d5b6b1135ca8ac0dc4c28db538fd978" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.ctorIdx "user constant" .inherited (.inherited [`X.casesOn])
    "91b93227ec18ffbfb8f5e1ed988757ca68f0de5ecafc7bcda70205637ac72fa4" "b8e2afddcfe6b928859c9d626b68ee9d4b692f568bf95cd810f13ed45bfef242" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.nil.elim "user constant" .inherited (.inherited [`X.ctorIdx, `X.ctorElim])
    "1cfbdf20e742ff1b240302f51374880169fb65e443abf457d38d93238eb8042c" "15789cfae811c5fc4dee32cda6e4afcfd53ca56a6a4a80750f911825d9ef4794" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.nil.inj "user constant" .inherited (.inherited [`X.nil.noConfusion])
    "730b3f2b1ed8deb5816e8f0ae277b11e32cc0960793c892365a6096066eb85a0" "c55370667d3a34579fcbad2645eedd81922ecb07f0faaf18fd0091bfd1a97865" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.nil.injEq "user constant" .inherited (.inherited [`X.nil.inj])
    "c416959fb00dfc63ddb155b5841e8ca75b03aaa9b7916a24833e376b87ea9cb2" "caff6da4f262c8fae7d0eb9ce43e9f3a2f61fcef63c44cd26dd5f766a57ee369" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.nil.noConfusion "user constant" .inherited (.inherited [`X.noConfusion])
    "97cebde4f8c0da5deb92202416be63cea9b4360038833545bdd7e611788ac414" "621b2e611db3420d3f24a554a704e11c527bc0e041bd5a324a1c187245acbfdf" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.nil.sizeOf_spec "user constant" .inherited (.inherited [`X._sizeOf_inst])
    "7f27967002282d98122b4ab8f3603c84aca94a250420f59807b493cc2c732bfd" "841dbece80fef8ec1b3dc0f8218ced76da5fe23d8038fa54897ac27da18399bd" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.noConfusion "user constant" .inherited (.inherited [`X.casesOn, `X.noConfusionType])
    "63650d74af08a8656ea58d1d8908d5d9dcbfced02f395196cbf03442b517f5d7" "14377b0b5664d5233dfbd0e8403b28b65db10299f6689c5a35fada7b113a771c" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.noConfusionType "user constant" .inherited (.inherited [`X.casesOn])
    "9cd4d7eeda28cb6ac9b9d9d313c7c6961c9a1c0836fdc0d5d20b994d646e365a" "8e05cd1a3cd533559c4d44cb56126e6ff53d81ed239c7c9031f4f9360de0cd46" "",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "47c2cf9b529effbacb991502b5495aa849c5a885a8316c7802c72d26f04ee218" "8129c3e636d2957e3441df5bdd5ad6c1333b510f4238b23ded2fe56386e3dd9b" "type.∀.body.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9b "can" "src" `X.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "267e1a345abac33aef84b51b4ed6ad2bda9d618b441874175b02b98471fecaea" "4e87b85cb68310a4274bce7bba8541b7c244cf1343de88993f76fdefe6a98e1c" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.alt.elim "user constant" .inherited (.inherited [`Alt.ctorIdx, `Alt.ctorElim])
    "d6c7a7a2b870795a4e276904e4090ae93fd1a1f1c5ccc382da00511ea2f342ce" "035f155e4baeec1ae29f86e5556e9840abe151274a2198598047dc4e990bb2d9" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.alt.inj "user constant" .inherited (.inherited [`Alt.alt.noConfusion])
    "06552dd6acdbdcc49192a4727625f9aba22581bb2a74fb97179233ce456d0402" "c4e9390d878eb4d0874bc23111e1064e88ecce4bb010583d925b726a4a85ef0b" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.alt.injEq "user constant" .inherited (.inherited [`Alt.alt.inj])
    "3116f19021ca369a471e8b475ff4544b67e4dd9df0c5aae49d99acba8c6fae1b" "1b4d2cf8f152d1ddbc34352ac47480b5b773f7161936759897099421ebeeef10" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.alt.noConfusion "user constant" .inherited (.inherited [`Alt.noConfusion])
    "7883033ff85daf66f1d820bc5c450d0feeae4746de05267d550ebdf38b2a6dbc" "fe776b33aa99444befd5f3895d5df76f0c1dab1796f3c6afdfcfc2ba8750463e" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "486d625b50b8ceda2ca653be4ee5686669f4694759981a0a85fc6e5e089af90d" "78231b7e1a3902c669fe380fffb0c9f9b6f85d27fb5a525bbbf3544e4fa3f667" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.below_1 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "fb660b5e5d040cd84a8d2b2d29a9930e1640cef4bcff724db9c7cafafc5f7225" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.below_2 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "3e0d32bc42684e290ec3b22156df38bac285b635b572af78b5f97a152e71f353" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2a0929e7d30a78302ecdfd329d37da170cd4c99604527ef349380bbe44771afb" "4685034cec3e6a65b87e76b33c0ec563a955e15ca06d4f3350da4507a7173993" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2b22010711c6f47aef5614689465a86f85b3b272b95be6ff1644d77dc8c575da" "09af993dcd00dc66fc378f8b405d0771a13192d65f9ddc9766071b693fccaa67" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "77d783424a12ee314809461a41539a86f3f584679964d8106598a2494dd64412" "e6b54ad3f52b2967d96b43ac924ecbb71f1e926e828ef48e346bf78795526d04" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.brecOn_1 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "0edbc6435d4ab27f59b370b4161a2b7de9fb9c61ac0a8799175d52329bb4e1c0" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.brecOn_1.eq "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "4e29696ce1fb3ca4ba8dcfde988a47abc507db1bf08dd31ec83464e8f5eb23c5" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.brecOn_1.go "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "67cc4e350864adad6ade520280b223ecf17f410139dbf4a0fcd2b0941831736b" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.brecOn_2 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "f78802c3b94c7125147e7dfb8c3739f4b1c40e625a207c75402c4170b45c8cff" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.brecOn_2.eq "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "a3823b05179d27108d88f75192ada113577a6663b99e9c8f86dd7b834757a552" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.brecOn_2.go "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "8288316fcf4d3ad6ed0ef295f8ced00ecd1a7523202cebd45140d618f997f07b" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.ctorAlt.elim "user constant" .inherited (.inherited [`Alt.ctorIdx, `Alt.ctorElim])
    "ceea536474277e809e900367c140788c1bf3ce070b79ea4718c3aeb8363efd7b" "702e07d04175a7067be6e06e6ef5bf58a28492238ac639e9ef3ad716017c51c5" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.ctorAlt.inj "user constant" .inherited (.inherited [`Alt.ctorAlt.noConfusion])
    "489877745fa8219e298e95f88aa0f2f64b4610f984b81791d1d4e7887f4fde8f" "c5bd19cd6bcba89e3ab4f0b1463d1005f580916a064138bd0043d26eff6ba2f3" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.ctorAlt.injEq "user constant" .inherited (.inherited [`Alt.ctorAlt.inj])
    "fddc6f115371d5a9cf1fe4c1d61649963b5172d49f447a2e2a18139904a6be28" "93e56309cb01f1e0ba060b62833cbf1d10c8842deae10cfb6ffcad5ad285ad39" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.ctorAlt.noConfusion "user constant" .inherited (.inherited [`Alt.noConfusion])
    "d0fabff05bcaa83e62ba96e828823530d4132953da4efa57292c7389fe6fa25b" "be04f071193168de3262d8443191c6b8c4cec78372923f74b6907b56835a8a3a" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.ctorElim "user constant" .inherited (.inherited [`Alt.ctorIdx])
    "b569237bdfdbc7000b104d66743fba44582d145b51e9342310428b1b4fa868d3" "0b4466a6b1aca632ff64f44f7532702ab909350d7d41c08edcb5d6bc4df1e11f" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "01a8449867f864ef198711e8409798746db0abdd92175695ad25d504756f62ef" "0ab05eac9b30d8f23f6d1adf574ce10dc9cc1ce051da9d7f7adb5940d196b836" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.default.elim "user constant" .inherited (.inherited [`Alt.ctorIdx, `Alt.ctorElim])
    "c1dc9110f8aab676b1c8ecd159b17f5656e35ff21905370c63ccec8573e0a690" "fc8cc6e8063b324c68ba8ac0aff1517bdf04cf4dd91588baf489bb322b4f9ff5" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.default.inj "user constant" .inherited (.inherited [`Alt.default.noConfusion])
    "28858b74d797860f22bb17029e2afef0dc7580add4f053e616662e72f0618a2a" "7531a3d46989ad9dcdbeb77a3f9d3d6a2938a6e82a71d05afd530409409b3773" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.default.injEq "user constant" .inherited (.inherited [`Alt.default.inj])
    "7a0ce085512d9b90006292d27a051d1fcdd0d0b7439ff0ed3db55e2399c71587" "d2a207826629651b921ddf538afece20dc5216b1805350744d0987549ab5cead" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.default.noConfusion "user constant" .inherited (.inherited [`Alt.noConfusion])
    "43e4b9ea4ec038fb5c865681cc27866879c9f60a6ec038e4a3404e80c3ef209d" "f28116cd61668b778fd2f8c8755eddecb59f915166f316892c3d8bd60cc58193" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.noConfusion "user constant" .inherited (.inherited [`Alt.noConfusionType])
    "aabcf80aebd12c70062c017077f9b90e76b0b9577072acd4168cffa88801641c" "4ede1bb2565cf28529c48a442969480a753d9871b90d283ac95912b66782b283" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.noConfusionType "user constant" .inherited (.inherited [`Alt.ctorIdx, `Alt.alt.elim, `Alt.ctorAlt.elim, `Alt.default.elim])
    "3a6447a35a4eab05d7bed56f236832d07fe92b993a573f17bc562d9f93f43810" "3d33654c210477f13052ceed61f8171424bbc1182d2a5fe6b3c45c15712c9203" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5ade93d22bb6305b4d2f01727be452b898ad5eb109b332b0106424b42584317b" "e8748a750744f63964ad0e4962665ab68487308623e1525ddcee23931cf8cccb" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3b6d58342e634f13ea61aa6db3e8e534c62eb467eb3e9074cfaa799b58cfe4f6" "133a53b8ee9b34c74aa522bf3f0140a251360f993bf01318ce564242a3252af9" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.rec_1 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "76427c3980ea0d2b471c55c659df193fd8eb7ce5b6142ea49613b5fb04ac334f" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Alt.rec_2 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "9b74dcc728de79f4317cfd96efb9edbb8a9b5cdcfa83519560ffa8f339ad1537" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "9ecb770bf891c0c9a2194e26bf49bf94980a13356013dfba99a43a61678b6a8e" "bf74ad2a84cbfe6890c3b3124d2b434dcbb4e89e09175ca96ab371b01d34592a" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.below_1 "block auxiliary" .pendingSplitAux .onlyA
    "e7af8661717251fefe2b4275190bfb265ff98fd40e8015e3e0e7383ebb5e52de" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.below_2 "block auxiliary" .pendingSplitAux .onlyA
    "4002c293e4c7e3061666e1bb5126b7c345a71beb21627fcef4d499437879954f" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "f88f35b83435476dbdf1809a152207784b75ee33eb8a11b49c80e87c7d812ed8" "8ebf18c941b6f285d5b1f32f7f921382aa47c72271fca6561ef4452c37a4a0dc" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ea3f990d19e4523b72027a74bbcafa50334cc06e4eea809bab5aa89e7acb690e" "58519ab2ff089eff58406836e0baba6d252245088e31d23b8d10201b1b0d24fd" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "eb1d010944b0de472b9ef47a15abe43a93059bc292cd36b351ae920785110b7f" "52c0894cf8f2b37f74c57b25b1cdb1326c51f684a61dbc81beb8ee3575d3b994" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.brecOn_1 "block auxiliary" .pendingSplitAux .onlyA
    "53cb324b3a838bc1d6c1f02d0dcc0343040e030c1ca9645da058b31cc5b74017" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.brecOn_1.eq "block auxiliary" .pendingSplitAux .onlyA
    "7111a78a886fd40a713780c5c5f12d7bd381f45205924c424f6e386805ef3598" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.brecOn_1.go "block auxiliary" .pendingSplitAux .onlyA
    "73b5d657c2eba0ebade7bac190416b9dd3204e8ec7fde26145b32c32b4a4aefd" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.brecOn_2 "block auxiliary" .pendingSplitAux .onlyA
    "5ecee3e50b6fbd1e65fdd0f75d0e26cc2b72e3d49784eceda321a93ca9a778c5" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.brecOn_2.eq "block auxiliary" .pendingSplitAux .onlyA
    "0adbfac62cb6971cec49b039a2773097278a3513a2c254a42b9fc7724011f957" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.brecOn_2.go "block auxiliary" .pendingSplitAux .onlyA
    "9ebdef78f8555d5bd5313629092016f93e36bbc6ad50a94c86c8495af1e9554d" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.mk.inj "user constant" .inherited (.inherited [`Cases.mk.noConfusion])
    "3bf5a095fb65f5bbd343b2b7bba00ead69c3c95476872c86c3d1cef232c8e09b" "1f4fd469fa65e19e5f0d0a0244871a195d60cf3a5334a94479ac7bb11c781a64" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.mk.injEq "user constant" .inherited (.inherited [`Cases.mk.inj])
    "a0f93cac72a6271a321fa6b98aee408183e1d36bcd03dff38261ebba66702d92" "0fb1c57d1250ce3e274ef56336a1fcbad8f4e8d2a78bc290aa0f182380286a17" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.mk.noConfusion "user constant" .inherited (.inherited [`Cases.noConfusion])
    "b8aa8177dfd5c5d01f2720ebe4f9568c2f72bbabf174fcbf0884fbd3a49c0719" "2a46e9f1ae1ce7bee4bfad77ba516805a26d3144d445859ca3b2da63a977abfa" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.noConfusion "user constant" .inherited (.inherited [`Cases.noConfusionType])
    "be4149ee21346026e7ea0ac9001b7debc8a2dcad1ff82ce8fbdb3bac93811c82" "05df2da9e7714d2f651f874bb470181eda399ad96a0ebd028ca033fc4a67fd2d" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "a25c407e9797f562b2dc865c5f3001dd4a58a37aa5ed9d185555f5b962ac9f84" "823cba475b10bccfa10d76d59ab700e9c11af5fe10b3eaf6e2be931ff4ac41d3" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ad005de1965cad26a22a71124d33ca0b21b208f97dac3d09c96fa5e107b75d75" "f5c614163bfeecc45c0f9ae6c12a6cd1780beeb396c6d713a7134aaa571a1777" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "769a488282c06d051de8f2d94041dc38ce4101792ab1f893e9b40a6ffe236b9c" "c39b91efc74028a5ee67490717a70cdac7a3a0cd98f81b0ef26316ab6960e202" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.rec_1 "block auxiliary" .pendingSplitAux .onlyA
    "895263662d1bfd1e22c603a1e78b7e512bb173ff3a8571b294b2ab959fb714c3" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Cases.rec_2 "block auxiliary" .pendingSplitAux .onlyA
    "4b28234d62306094e8f81e340a3df870e00d3cc1b45ccc15c103e4b54d1ef703" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8b1b0389a2679f2b8e20147ce72219b547ee73231eea4c5b63f0b6042d713c73" "fe5ee7c06f1ba5e9011bec8c15524e090ad0d9737ac92194d21d56bd9376e38f" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "47aa4e666e33d3d3aa29bacbed27cfcd52129bd0bc5d50ee894e2b1673040318" "50ab261c0ed224816063f044b24a3790ae7542b805c819553d68c9dfcdd6e698" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "87a658c6a8949d2eb5a422bae665131bce5315049c17d51ce1771ec974203196" "c672208f542e131bbfa0b3db2c936a269c0948066f229a90ca1e0a87ffbaafa2" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0f9c0ad41ad041f5ed90306303908f8e37afd1cc62a0361bb2e9b333581d23a6" "a10574599defc56b36fef264f06b734a10076c99d4bd3c4250f15a5c7b954999" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.cases.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "10e7457876fb38a2bebc206938a354da8245dfc3a51189d75912e15d70b63eae" "e6e4c2d1480a91f004daebac26621a1cf752a46995a0336c8bfc1d3f06b11911" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.cases.inj "user constant" .inherited (.inherited [`Code.cases.noConfusion])
    "293108548d92376a3beecf4a3de95353af28d79981f5770bb1cf92af108f3c6f" "6a429379964ee0704f8d22094184f56ccb8863246ab622c186604f1c93df67f8" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.cases.injEq "user constant" .inherited (.inherited [`Code.cases.inj])
    "8458da40ae937d67ee48198dc0d7ee0ac8a821cc7f7d86254f5ee39267c844bc" "43d9f81ee9442ffb9160296187de7fbf621e76c0ccee43222c76d55b6363f94f" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.cases.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "99d7d96ded00dd0d5cd9ccea6cf6b601f4ee042e807268f832f60ba8e32dfc5d" "21eed14dbdd1dfe8fc099ae96d0025bbe81467a9e84917bb8cf218eebe292598" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.ctorElim "user constant" .inherited (.inherited [`Code.ctorIdx])
    "ad29bb6e5eb5de851b1d58106fc6e2cb1ed01f06ea3920501810d5e5a061fc46" "d89e33897fce2dcbac964b651dc8a3ec438e94bf26a859dc4c4aff6cd41cae2f" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "2ee5698be84376daeb27945c77ccc157f5e75940a28066e149f139f84327363a" "c1d8f787437f1f7db7cd66eb52d2ca5c7e1607996d21fc2546116f17aa72841e" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.dec.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "850704605f32246fb9b48251d131817ed1e24dc364c04b87b8d011a10af072d7" "61354ff421f37c30638c8dca5c7b233970757970c095ae15752341ddab8a652f" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.dec.inj "user constant" .inherited (.inherited [`Code.dec.noConfusion])
    "4db9b54d0736d9adf53dae32e2e1a728dd35c90f0255a943ab77e3a32d62b411" "ad8a97a9b589ba20ce191824c352e22c45aff7c498ffa31079d82abe61b1d5fd" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.dec.injEq "user constant" .inherited (.inherited [`Code.dec.inj])
    "c51fafed3853c47449d99cf5e9dfb558d69319df31c98b0dc6e553fbca010742" "2c0507457c3313ec148af6dba1266017c0a40c78a8e39ce2226ddd68aaccde02" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.dec.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "05a3697f5e9eb4337dee74ff55ba7addd629a262d8359a48118f5e2ba96dbb76" "e2c1f9ef75353ccde8997e9e26433ea247402fa6c294fcc5d0cd7ee604a07a4d" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.del.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "912b76630f6c4474e902b8f430c2e115208167ecba659fe3b6a9676bbcb5d265" "18cf87f5e1479aa51b186115bce9f71ef7adbcbd235632b2b5a7a7c71f053166" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.del.inj "user constant" .inherited (.inherited [`Code.del.noConfusion])
    "1b8319407254ecdf36cd47a499916c7f35bdcf9fa08f980a58e14469cc458438" "a3d16c550e028d11b5280aa97d50048d5b8839b7fa3856f8ca68f258b271e639" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.del.injEq "user constant" .inherited (.inherited [`Code.del.inj])
    "d0a010785ccce2f9ebec3133aaabf1ea8b8a7b525346c0ce6954a7e5785e99a3" "a1902eda24bd29d12eb0054262d9c35695f5d09fbb92ff4be5b07ead833e8f44" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.del.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "7e3eb4063293d85dffe1470c0215889c7938c0b9210a5d2357f67bafaab83124" "72b41b5c66cf5de646ca6fbfa2968635d7f1ca340bd0ba6b2fed49a30d3d3f1c" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.fun.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "818ddfb12c342813047dc0cb599892b78f61c65d9e73ee93af3d599e764ee4e5" "383737b59b6fcd382bc508213857d9fb305b105c2181c0cdbf066cab92b526d6" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.fun.inj "user constant" .inherited (.inherited [`Code.fun.noConfusion])
    "d8d2d1b91b606d8027d6a82a1af7029a73ee82464a687dcea1159dc878637ac2" "339ee1b0e1a7dee08866c9e3a8753ceb30a933e72deb3f52935d4b0b6456d540" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.fun.injEq "user constant" .inherited (.inherited [`Code.fun.inj])
    "d84d0883b55c2ca7ee9ac70d94928fefe783a0fc0095088c62292c3b4e783538" "4ddb6c30463050ea8946754b6fe51991f602ad633ec4cc6e1caba69dd3c38737" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.fun.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "c1f0181172f20d8c724e32ae2539cfc8a26cdb7ac4598eba81f0c3c0e720a649" "094e3f787be77ce4fa807ae550a02089e92ffb0ea3bebfd9254fa6c6d7270f34" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.inc.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "896465a26cba7bccd9f10231dc908d492eb7c9073fa6dc1d5ef9a97e509b76ce" "c49c971348c1c545ece4d2ec38a8689cbbae00aa4644a2127e06c9b95623ac51" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.inc.inj "user constant" .inherited (.inherited [`Code.inc.noConfusion])
    "5da6d9adaa38be6f9e0c418495d2115211179c22106477f12b35e90556cf4d6a" "738da4cef5aa77e95ec57be79feb635a2766601473b1ea63788c8569683c2311" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.inc.injEq "user constant" .inherited (.inherited [`Code.inc.inj])
    "b2859e15fef266e1c098f89ea66a85f3a81879c82d88d8619716b1ee99e0e64b" "ab833b72b22a020545fd351014753115f8e6c847fdde6c3652264282a5b1c406" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.inc.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "f782c865ef37c063d39ccc0c54a1d483cf753277b05cc0a0c86a5c9f54b89ac3" "c6b6906604a41b7f7ad422d2ee4ce02946ff232ae7ef3c1f8ae153d55bc7ef28" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.jmp.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "1dfd8041eca4aaba62adf6848661cc096ee5c302ee27cde31fc66b883fe4d003" "dd46cf4e87db65161da6a6ab2417d8eb59f895e61d5194276e3a9e530a2942ac" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.jmp.inj "user constant" .inherited (.inherited [`Code.jmp.noConfusion])
    "aa4d1b5a751150e98d5add2a763abe37deb660cc2bf4d34b18863542dbf8adf4" "d1cab66957c2adfe623c666761ddd842fe9b1d5bc35c922208a2f9c1be2234dc" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.jmp.injEq "user constant" .inherited (.inherited [`Code.jmp.inj])
    "7dade2f0d4336535b2f9eab3c7eebe1c1f26e2519baa26f29e2ce34dffbd9d20" "a6975d10751b60372ae64ff2769ca6a440a9bb867081dda2497d89bab817967a" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.jmp.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "239c121ecbcef0c3e0f3e430406eda2b717d7ad036122c7cdad31fa84d830f1c" "7c3bae44801462cf289c84e9823bd45c9de3b9cf79f4c284d739e6ef5a7e486d" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.jp.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "84a2ca1123f8a51c89ad9b7687139f30219ad1399c5df27b0b0a7100204c1ead" "3e537b4da80e678718bd3d74e5305b615da24e0ecc534cb93766a47ab643f72d" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.jp.inj "user constant" .inherited (.inherited [`Code.jp.noConfusion])
    "de1221e8a9931a905e0a9e995542befa3fed5cacea9ce697c269ee8637693ae2" "3513a325a68bb12eb99b40d9deee4f99e723f4bfd0e9c06c659481f9bfe8bb92" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.jp.injEq "user constant" .inherited (.inherited [`Code.jp.inj])
    "bd1f6be6788edb798dd8a1a68212d3e3b8f192a0b3909a309ca79796bcf54a21" "9163a598450856b520349f7d4fa13e8dcdbc56799870fa3872cdc6edd70b3dad" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.jp.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "f071097cb30b889767a1aee7d4d4e5d79ed4655b5619ab41675726a7b8b2e6fe" "68b70f37bde55f6624e00e9b27b934e0c4d2b8e83ad596e0820b3f425ea3f953" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.let.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "f7762e8719c34da3c43468d182e1f477604b00b375c723d424d19d2f82b59ed4" "38848b12fb2c43562d9828aff328f2af766fba32c83acae92c38c67b6fb537c6" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.let.inj "user constant" .inherited (.inherited [`Code.let.noConfusion])
    "19e455ec0968598f7bb3628d3cf541b9397e2283472f7cde0ce575ab1041e6cb" "7916ad8712f231562db14cd0db851b5aedbce44b8abc43a87c3057a5c818287a" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.let.injEq "user constant" .inherited (.inherited [`Code.let.inj])
    "db832ddf7a4714cd15835666664fe80321f46d98cd66124c0ec2695d7c063607" "4f2fe51deb8ff7e511ce97ec733eae73bf3f7010927cac4abe06e7067b0717c6" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.let.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "14a60e3130b04f20b7ec667f725c5fb9dc39df8152a770707750930f2dbd8c6e" "3f0bfd9cb88784369440dd7b7fc6ce0d9b6786db702973382d24becefe02e040" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.noConfusion "user constant" .inherited (.inherited [`Code.noConfusionType])
    "872dbfbe7c056cd72013412e953a6ba722f4fcb8aa674f38dc34c898e8939dc5" "ac328093e5c3dc73b90c2c51ee3912ee3b04efe48915aa436493ee008674c29c" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.noConfusionType "user constant" .inherited (.inherited [`Code.jp.elim, `Code.oset.elim, `Code.del.elim, `Code.sset.elim, `Code.unreach.elim, `Code.let.elim, `Code.inc.elim, `Code.return.elim, `Code.setTag.elim, `Code.fun.elim, `Code.ctorIdx, `Code.cases.elim, `Code.jmp.elim, `Code.dec.elim, `Code.uset.elim])
    "64e1897673f62b9b484d63be007a377fa432eef8dc9c8526e9567f1ec937a5f9" "50a3a65c953b7484aa07898cb72233de86a3b58e6e5aaf0440cd5b1421a0e70d" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.oset.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "af3d80e8e727b3be029a551357870e127bb596f8578b30c7d7220caa89ad78ad" "8a4193fb9867f8dc1cb5a9bbf781cfcd2b866574228c7ee59772712183459073" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.oset.inj "user constant" .inherited (.inherited [`Code.oset.noConfusion])
    "c8530535471db8f37d80fb11f92565e0e13ffadb078013664b0667c461dc29b2" "e8949c73044740b3f8b8e9e71e6fb2c7820b26240700cb721cf50921b907f4a2" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.oset.injEq "user constant" .inherited (.inherited [`Code.oset.inj])
    "4af737cdc23eeb4ccc10b9b6d362067ca695f0a747c59ed30ccbf425cbbf46cb" "1d91d77f86f0b8e540c0e5cd686d58a3789724cade796615b0b927865164e00f" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.oset.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "5ad8307dd74a52cca68e22cb09288b0c625340fb866f18484fa41b839b9c6a3c" "e775d265e872b12e922c6e5412ec4abc6abb73bd6c18882cb243283903a595d3" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "41442b55e8e872dbd9d0faf5ef6f1b0b28534ce26cb6f063e838411cb6bab1ae" "ffca40a88ea9cb00a089e9a2dcd0aec1e5d73f16395937a5ce850577b0b2b7e5" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e3094f26ecc5f43b146eb29ff7ba98bdb47931686ddb192e5671167a203309fc" "8702fee56f282365a1d7646cea1e7b603e20a0f41a76d9924c98014bf0a214da" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.return.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "31287d787ad7c61688dc29ce1f832353c405e2602e9c14a4502b2b0e2e8f1628" "32275b8fec7547aed70bd33a25104a9c045a4ccae042a8dadccd827bbc44881e" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.return.inj "user constant" .inherited (.inherited [`Code.return.noConfusion])
    "c8e8a1a5cfa14f8ee68e9b793493bbf50837d6a1152e89f9c4b542a399c3695d" "45134ae2c6d22998c52856162b926a10c5c58d979e3f23a43855082ea1a1ccbd" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.return.injEq "user constant" .inherited (.inherited [`Code.return.inj])
    "58ae08fafc21e10f632c1b3084df90eb4022388c0d7eaf976ad39157502bc12c" "8a0f163bf7519d2c94ad1c2ab890bc7922ead55f16d367834453e560a7343396" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.return.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "e2b96ee32d9d5d498b8b687cd96e2097ba6edd7b0000df5dc885420418138a7a" "91fe94a5a54c1d40d3f7342fb84a5624ab92cdd5f8b9026f1f76ed2836026c00" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.setTag.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "4324d0ece479757fd030adbc79c7666ec7bb83db9a89e0720100991ef90f0fbe" "3c66e7460b457dd7a70716c4df017ae9fe5c93d0bca803c279b017a8e6f66d08" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.setTag.inj "user constant" .inherited (.inherited [`Code.setTag.noConfusion])
    "a8c7c89f96290cbc613d89e0aca7f079b97fd0b6651a6e63db855049c9fe32e3" "38c46ed52fc37800248efee577f9df590645d1550d9a77ea38f28a1d85baa978" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.setTag.injEq "user constant" .inherited (.inherited [`Code.setTag.inj])
    "46889f74fb0e2e4b6b58a9a1adcc1ee9f83318a752ea09dec1e99e8eed56a069" "92d120dbe44ef2fcc9f5de9be939014a7c6e7e210152ffea462e7fe4112c9b78" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.setTag.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "3a2a550e5ae74ddd7358aa07a9f8062992df7ee43da9cc5e9827290ec8e3ffa4" "a16182ea422d1da0d00f1265ef8d114b6577717ebd5cf99774c7b45377bc1c58" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.sset.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "41bd01a184c1309150f21661506df7d956150c23b49a477ecdb008976c72ce25" "54b00c177c8c7c6528aeff5e92816d96b16adb9e4862a225dc42737d670bfccb" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.sset.inj "user constant" .inherited (.inherited [`Code.sset.noConfusion])
    "5070763c6e1d53e75ced2ffa7e86044e3d34f766d639cc67896716877fdbbb80" "9d81eb0ba89c57200ba1f643f11dbecb53c433beffc8a3a49049632a7eccf62a" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.sset.injEq "user constant" .inherited (.inherited [`Code.sset.inj])
    "6672559e2b07dbf9f4614c353a1a5eac3d85c20aadac59ebc3bfedd320b4c71f" "5a94ebbe249527d98adbcbb2eaee9c07da61979de9ddc078783e1275c8c297f7" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.sset.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "8b5390632dcac2e7d838bed2418c356b23114d4c33a2708bb89a487bf4f4776c" "8ea355521c504f7b19e1baa65c9895d4d301d2ecfc0a1ce5830e4833f749710f" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.unreach.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "de837c385f91d3fc43755029a1f52fbada882e4d767c227c4c7872eee58beac1" "b820670a3a78de89157351a4a1584ecf618fabaef26dca7a8e79d6b48bbe79ad" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.unreach.inj "user constant" .inherited (.inherited [`Code.unreach.noConfusion])
    "30af5808e03c73599239d2d8cfad524513cfdd153950755cf451d79c1883c27e" "b38f654e87781ab7677d74d12f291732ecffa6191b8fbc9c3c29e1c59bd00f33" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.unreach.injEq "user constant" .inherited (.inherited [`Code.unreach.inj])
    "12f2c9125579cdebfe14464ab8f8a1b5a99f90e7ce316c850af7bf82c9601622" "744d5711583d78ab0bbaf1e7f233517d3dac87ab394cf01ff2419b8459f6e49c" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.unreach.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "0bde6dc7c36f8bc80f0405db0bd7e2713f190d2c15d9121c47d5f92480fa7790" "6345aea5c7f8c0f836825ca5ef2eb4b18b23b1c604f5f8b931e5c7225347481c" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.uset.elim "user constant" .inherited (.inherited [`Code.ctorIdx, `Code.ctorElim])
    "10845caf4aa17d0a6405e2807b2ae9f34331d72c7d2af13fc386b747825ef547" "12e2e0c9a581f152375083843ffdca6772f6de075ed98c1dbae737744890f540" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.uset.inj "user constant" .inherited (.inherited [`Code.uset.noConfusion])
    "57a46e414d8af2872fafa159a890b892a5239d80148d6cf74cb5a19bc16b67e8" "0b52292c0d799804c2b0d18e7631a4e358b66fa3dcf6174a6fdfc18b7ec5531a" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.uset.injEq "user constant" .inherited (.inherited [`Code.uset.inj])
    "65eab469d5e843b1047a38a2ef98993d834bea4c25d52fb3d4b37455477a533d" "ba55a8271d2865e9485afa36aa35bacf51e826fdd78dc33ac5700313afbfd766" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.uset.noConfusion "user constant" .inherited (.inherited [`Code.noConfusion])
    "eccd2c12fd9becd130ffa84999a0dd54d13ab85509b592da562287bc0b59b2be" "30d44d31b70c22419cebd367f5e1b234de080ddac92b208568982f8f3320ccc4" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0f0e51c988f02681178841819e29317a0e09cd7d6318abd7af8224e7a5200630" "a5c030b39f7f70cafa0cd58ab1ae2d98493a5d59f118b738df2dec63de1537e9" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a73b1be089af845be9889d556ee8a427a68750a899ab8f922238e48ed0453a02" "5a3680a51b333f9760f5c219cdb2ed05c4f4a15d410a5b22877a79d198dbf1c7" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6fea987cdf441af8b64477a6b6b65bb0189643aac9fcd87f9eeafb0259f4cee6" "8cc2a715911397bbd6f33d8d0f0bd8472c8c70a28a62c388b608200f576535e8" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d236bddbad7f98e5b583eebac82263d2ff20bd3fe44c1f827853816ca1b94d10" "3fefa4efc285ed214c7e688d76ff323a92c8b55be91808fbd176bc406829e714" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.mk.inj "user constant" .inherited (.inherited [`FunDecl.mk.noConfusion])
    "32ada5efd79132f22ad6c0162a355c6231721a3c106081e50eda0093c8bced4f" "836bbb1920c9110d709bac7795d645e03c6462bd4e4f9d42801248deb9a7e7b5" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.mk.injEq "user constant" .inherited (.inherited [`FunDecl.mk.inj])
    "02cf13eb1d286c4f77f4634597a37412f20729ec0cb1d733e5de8174a2ec773b" "f75fad60e0d58540e87f0deb9329ab0a24e4ec4f8469befd1a58840efdece5fb" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.mk.noConfusion "user constant" .inherited (.inherited [`FunDecl.noConfusion])
    "4ad942bed7c02da235a9ec9ba83d972388220b0ff05e28035cd975d33bfbcba1" "f0e1b3218a1a2902fb693d278f449a5899a81ac9277b7de9dc25211843e76950" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.noConfusion "user constant" .inherited (.inherited [`FunDecl.noConfusionType])
    "34cb11513daf706f7eaafdcfa40f5f778631d3b2feeb528e08236c396f4c1e58" "f14b81bcfd4664162f2cf9a2743c9a4322502e9f75382da78cd6e4afc16ccf19" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "02be9c3df0675a118ec0c196445de867d135d8e29c7e82c3355657b66a07a33f" "ebe42c0410a0bf49de256fdb20d1626bee2ebfc24a81889bf8142e27f1458512" "",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2439b89a0a9b40064420e3f55d08a8e2dbf4ba471564dd8e332a252a08c3657b" "14285604bd543451b3fc67465f69f8203ecab40cf8e25d08d5a896ee08a19578" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "22cec169f321516bfd700476c0cfb7b2ad0ad2f212681e177961e9392e4140a8" "8374e9aef85830ca5bde0553611fcb4a18b87e59e3b4aa9c2dccb77b1a39386b" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplit.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "873254c9ac47a363273b8ea39afc3c961c7f36e1af4123959f98fbaa3155168c" "48fed7f2db0a5e62f55dde30b54ce99031459fab5ffc38cd8e99458e55f3a6ac" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplit.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5af950abc9a85c8cb16828e8390610b3f2f7651f88a30dc4fd81a81f9692414f" "9b61a162b642a23c0d716b81df780a9fd9b34a4c9b7d3837029c42e242d76bd3" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplit.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "f02e227e9cd45742744d8677c4ce5c7927c057551a5eb74feefa68f6eaa41994" "44b03bfc86293d6843993c3153f4338c6475808fb8caf2fc961e37808ac98626" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplit.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2e2885cd1946d40bcf4a1e18590e902780384d2b8353450ad3cb0a6d19f35ee2" "d78af1510908b03fab80dc58f02a8284c9047d15622ca5f38af3018257bdae4c" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplit.mk.inj "user constant" .inherited (.inherited [`CooperSplit.mk.noConfusion])
    "02034e1af99cdcb6a7a6cb8afeb728e705c50ca795a5ce4611929a911ec48814" "51f367e41a9e442aad0727c99caa6671a422b17e7ef2e0d81c11b437ac78e1f8" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplit.mk.injEq "user constant" .inherited (.inherited [`CooperSplit.mk.inj])
    "4c1a48832e7be8370b9fcb2083c084ea0f106dc63a885aa12501be227d9c9919" "2e5ae9279f16ec973f08040d1bbbfcf38cab8159e9d955399f45d6a22963c75b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplit.mk.noConfusion "user constant" .inherited (.inherited [`CooperSplit.noConfusion])
    "179b34f40d1d6064db2b484d082990e2e01e2523feb03b5d982d018a6bbdc2db" "d2afc008950ec1d1b95f2ae94598db452e4f95ef64ed08dfa77fac6d3d133a71" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplit.noConfusion "user constant" .inherited (.inherited [`CooperSplit.noConfusionType])
    "81ab1147df388c6624d85d19477d46a3f34b34104373782c9b758b39c8f9e1e0" "d250f8e8fa5ac76c45a52e92d9198e4f004da90ca0ab6a4197fdf2969c956910" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplit.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "5d887734f9962e4dd492e1eeac6a0cac2139ff46f1024a816fbe694fc3752e99" "b494e4c87a75cd6019417039d9917beccc66a4333b7af7bffacf7abafcf0a31a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplit.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "93c52c5450a7048c0459bbc12e6616430f505dc29a1e3abf8c4911a77ff24253" "745477a7ff233d36b6741ce300bc82d05034aaee9b025172144e2418023dbc4c" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplit.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1195a14e588bfe4d152e938e8e7c25e94c3c2e021364bfe314fb6e4b46e3540a" "6405f9b84a7da760d6e1f2b23c2177b0615494726e8c5b9e798f4749a02ac3ff" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1431bbfc1c3cf4e84e9dcd710793d9e1c60e251edbc6ed94f7b55a50b89648c8" "ae41e62bc31c63b2553d89f96aeeb0f51acbb0f3a27de5ff044e8f4c1675d60f" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "57c4c9bfc7251849f9b3999533657e675dcac4c0eb9f74193f4dc587eefa5ae0" "aa7a994d1806785ea9ba5ed1a291400fee94caefd5676a0c41fb6b0ec74b5f68" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "53ba03c9f509fd6c5f24fea709ae94f212de1387fae0912132ca91867ed756dd" "6b3f0fd48b725e777fff627ae50a5db8f063441253987c6ddf56f8ed9ff03830" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ff6f5a2cd1f996b47425866fd46ac7ee389ba13756e8f77a92262b72399d0f05" "6122ffd90cabc457eb9399ddb727a9fa7e55f2680433a0b71f474fed11345d75" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.mk.inj "user constant" .inherited (.inherited [`CooperSplitPred.mk.noConfusion])
    "b13d8c28486d6b23b9fb5b71dc6ddde80098cad7295baa0d0d9bf2e488bb61d6" "15eb3bcaae33674bc8792a0eb59e256fd775773bc188157c86c9cd3c3f5ee51a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.mk.injEq "user constant" .inherited (.inherited [`CooperSplitPred.mk.inj])
    "f7034bcc3db311eea8917db5ec60269b475feee568de2d367cc0932ea52074c9" "bfc41af90358fca8e312b758e372e1085d105722e08f75f9d940a1e5b72722ce" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.mk.noConfusion "user constant" .inherited (.inherited [`CooperSplitPred.noConfusion])
    "ac6539bdefa924e8b0757731aceaa252e1acc13d8d4396d2db6773bdc906159c" "8ea2783e0a7018e2d941578c3b623bd52e94f01d55a35b161c5cb255d4e8e94c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.noConfusion "user constant" .inherited (.inherited [`CooperSplitPred.noConfusionType])
    "2cf6b6c00302a129c11a8415ff90ced8b9471afb5fd0c0578dd28327a22db430" "a5cbca08c318d6599688db5851596869331034f14fca3483cbc99b35239b6e77" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "e56349758f26ec1ef89803c18de16e90ac52e7f97aa6d0876ee7cd7beb27abf5" "710632c2b787ee587e921c4982e82646b47bf47eac1343862e3d416207bad675" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ba4f9388a1c3ba73825cdd16800b3ce735981737db877028c987605b1e4489f0" "4a2c972cfc23dccf1b281e3bf8af965727b7a7645ec57968bbc818eb902788d2" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "354694e14c1bcb2919e3616d6cf78482872b39bf60d560446edd9d9c1cfd4f19" "3b948c4698a62e8457471580bcfcf12143eb256f6d3bb9e4552f7861c4fa7883" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "9a8f3ed5e18e48afb2f670c84372442b702aeaf556641a6b41e90991e5469692" "1202d54db7c52f629fcc2ce8af044284520d1ac36e6b5ee29be3597c5277d9a1" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "37269622b61335e50bdbab807dd1137214510e067ba5c76cd2bf4da2b43b6668" "2d3792c9d83505a0c6c93bdaccb2a577184b9d6eef77e72c05c2e5bdb9b76d0b" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "056dd4cf529e7316f54ceb273de18a8d8a386ab581cc1bd307a0f34669091f25" "0a7c4be7e7c912bced588302603eba647ef251deeec83ee4160ce623be44fe29" "type.∀.dom.∀.dom"
]

/-- Entries 1200 to 1399. -/
def part6 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1dd50a3e97f1e4eeae1956d5937d50008d26be118b14aeb456cea5df665a1b6e" "391b0cd1d90be887211ab066e4eb7ae66912bd16180c771d1816f2e53f7cd166" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.ctorElim "user constant" .inherited (.inherited [`CooperSplitProof.ctorIdx])
    "781536b5ddfa21b8b9300b78ed0e1aff91f8431030ac4a9fb42af02fd66bf6e4" "5562d4ca1bc2c58cb912bf6603e0841bd903668381590920cee55ff6f1c7d7c1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "ac6d4ffea3103a66381483da460447e726c9ca6b1deae0f7df148a7f1c2bf44e" "10e3263c0be02bf1d44feccafcd96dd6f83718e0e9c5cf7af3e60dc57a4754c2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.dec.elim "user constant" .inherited (.inherited [`CooperSplitProof.ctorIdx, `CooperSplitProof.ctorElim])
    "333b69b595c8ec962d7d45bd044d27789207f9c7415708ff2915a9e0f0701791" "90aebd376fbbc9c88d7495cad43f236e4353eeb64a3297754fc2a2f333288a98" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.dec.inj "user constant" .inherited (.inherited [`CooperSplitProof.dec.noConfusion])
    "598539b1132564d7568ad735228fc7403ac3d197d93d766930ad5d66916387fe" "94c5c78dfdf63396a3e10003482cd93587405fcc9e4f100504401c9fa082c742" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.dec.injEq "user constant" .inherited (.inherited [`CooperSplitProof.dec.inj])
    "9d3db1ca53bb762d43fe9fa3aa69022e0fd64c7986b87fc446716bf8bd1a6f28" "1bbb2ee6b01f9aa621645ac4e34a88803ddda4d7498e6292935c69041b2879e1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.dec.noConfusion "user constant" .inherited (.inherited [`CooperSplitProof.noConfusion])
    "553e7218bacb64515e9eba6ffb2e4f4213fb58a718bcbf27e965b474748e1ef3" "012923f6466a28bce1285384f3392b8dd9008fe78baeae9d5cc0c830c8a739af" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.last.elim "user constant" .inherited (.inherited [`CooperSplitProof.ctorIdx, `CooperSplitProof.ctorElim])
    "0ab0203ae6b57fb3d5ef858a81bb7343147b3fe3779dad495d5944d7db9830d6" "7d6738ecb868f62ffaa1026a1ab02f812834d0a0311a1bfe5f129750a3065a6c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.last.inj "user constant" .inherited (.inherited [`CooperSplitProof.last.noConfusion])
    "e0907ee1674c13901a26c0445e71cfce8c050c5ecb5435cca62bd98eea03eab0" "3c518adbd72e04f4e9bf50e2e4ba342686e9a87569f8e5867050252552418807" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.last.injEq "user constant" .inherited (.inherited [`CooperSplitProof.last.inj])
    "d6837e13739705f7ba2633ef98237aa2b4b953c38e794f16b5b48db56c8b7a19" "0e495ff2b0df0953c1af58f549d8c23b593453cd8361babe535ee7b6b364d588" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.last.noConfusion "user constant" .inherited (.inherited [`CooperSplitProof.noConfusion])
    "a8ea03234096f29608083b8c6bb16c9c6f020a72231ac50d2fe624d7325e7286" "01e045b79bc8468c5409279e9acdec35e3f457e44fc4256374e4095a55b5cc4d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.noConfusion "user constant" .inherited (.inherited [`CooperSplitProof.noConfusionType])
    "16d90689c4bbe0f5648e4b341c33ce402fbc1eb34f8dccbca7d1304323b45cd3" "2dd0681d92102b5fcc065863347a4af9b731927e3779547b7c16cc0d43b097a2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "b16fc15c920a1e8745101aa2f76d539c779cd027a5e92c25360012436748d98a" "e36a68e0fa4275516048a7db66771aa4054d93ed50727c5c1e9ad8a953b87975" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d5692d3d88f83f61c8bdc8eeb5fc021c4d9df8f2474ce306dce2e3ae191145f6" "5a0976fa9326dbc5d83c24aac99a0b8acf492830f0ca69a27750accf1386249d" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "baa151fcca4c743d49fd73fd3a536422bc88cf63f8051f6f170dff33f8bf7922" "3a2fbb742ef76cad2ab2344afd840c65b8137bfb48b5de78735291ec755b709c" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7a5a1f21f3f73933316a950f7e7e64dfe9271a980875dc6dfe7fcc61cddac9c2" "4043b0e4088c83c039f18dabafd07e7a0d2c8e9cfad62899449f73e73b6e0124" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.below_1 "block auxiliary" .pendingSplitAux .onlyA
    "1e11a78e718299dbf8e5df961e0ae36d22e7a7199738110dec800254daaa018a" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.below_2 "block auxiliary" .pendingSplitAux .onlyA
    "bc149728478254e57d6037e94f7083a9c3b3ff0ffa32cb18cf472828950d4341" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.below_3 "block auxiliary" .pendingSplitAux .onlyA
    "afe93fc9bf991406ddfd707638ea79afe66f5c3eb805540c17fd3026f4e77c8d" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.below_4 "block auxiliary" .pendingSplitAux .onlyA
    "ef26902d198d418b8fb95be225af89f279acab3affdddb3339853e7895e511a1" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.below_5 "block auxiliary" .pendingSplitAux .onlyA
    "e0ce27994d599a135bcad4bdc4d1bf6333c5d51845ed024dbe4a0a2de8bb5616" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.below_6 "block auxiliary" .pendingSplitAux .onlyA
    "af691c39a9c45571b623471e712014b22eecf1a64317fc0fa29d2083d50291aa" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.below_7 "block auxiliary" .pendingSplitAux .onlyA
    "96eac4719e6a52fb19c2b37946ede173862b20e07df45c0bc809943b31fda23c" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.below_8 "block auxiliary" .pendingSplitAux .onlyA
    "0017d03004c4a88b6b97306989b9ecfc1ee65b493b0599d053389bb3d8db54c5" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.below_9 "block auxiliary" .pendingSplitAux .onlyA
    "970c8360cf17a3c8766db50db9d21b1d63a93180d44d674de9ed567b1eae37f7" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "df7c467c4d20ab0bd6a41ca24810d17b26b30092d3ed8df2fd9d193eb413b201" "f9c01790887349e604e7825f1d2362a11b771d2a5e5b41bfcaabd3a39cd31e1d" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c83fca3b872e0cfb702c94af67d843f170ffda4b08569264a2d32742260f5f78" "f96ee430e71fab2f63ba4170caa5c54c2a1e3c972636b22eacbe35b524bedc16" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c0cbb71e3eee664011800fbec966dc3851a2185f1af862b80e57034b1bf296d8" "e4ad46381c28efdb053e6b2198cba44464c2d992bc31bffb91c283b15f4da9d9" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_1 "block auxiliary" .pendingSplitAux .onlyA
    "e582e8674431084821f2c7c4e5247026bd11b25018c427c51e9c15fe751ff22e" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_1.eq "block auxiliary" .pendingSplitAux .onlyA
    "766c982a9fe92428da46e76353dbe940e7db9cd299977244235dfafe1572cb9d" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_1.go "block auxiliary" .pendingSplitAux .onlyA
    "1b4c5a477117375385a217e864ab9ec827755bb42edc38add0e77d1d03d4d72a" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_2 "block auxiliary" .pendingSplitAux .onlyA
    "0167295283ee890070f57d1f9549175c27b2a38c928d5e9bb034e61317d50d48" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_2.eq "block auxiliary" .pendingSplitAux .onlyA
    "9531056dfeb156bed4c1534878c08948dbd74394ddc4dc4a61f351b90257dc91" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_2.go "block auxiliary" .pendingSplitAux .onlyA
    "697fe30600b3014cdca9b29e9e501661ccf262061dd4e72964fe93ee4bbc9525" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_3 "block auxiliary" .pendingSplitAux .onlyA
    "b1480338f6347454f192f26b383c2e45c7e9bbd8cbd430dabe47d45c7b42ccae" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_3.eq "block auxiliary" .pendingSplitAux .onlyA
    "f1dbaf98df1430016368290f1d961c9385fc7a2c54f2c715ab58f3eb92551c39" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_3.go "block auxiliary" .pendingSplitAux .onlyA
    "e564c3e83a52273f016d8512b85717e28fa602e9c6801ceb602fc4e84b6733fc" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_4 "block auxiliary" .pendingSplitAux .onlyA
    "9667ec19f29b5dece39b59d8201a669320388527b5e7c86707f08373d7c0ac14" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_4.eq "block auxiliary" .pendingSplitAux .onlyA
    "a47d3e4473826467aaa76efdb546d7d5adf810e89f09a598feebf6daf26456e3" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_4.go "block auxiliary" .pendingSplitAux .onlyA
    "05b97b3283305c5f406bd294343dee8a68e46677caa46736d39a923aede51778" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_5 "block auxiliary" .pendingSplitAux .onlyA
    "bbda6ecc34ddc3e4e938dbba9c6a4434e860794d842c166661589e3fe26302b8" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_5.eq "block auxiliary" .pendingSplitAux .onlyA
    "99c28c99ad6d87151a75069306295a70802eb59ec54ab372aac829843e32ddc2" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_5.go "block auxiliary" .pendingSplitAux .onlyA
    "cfebf4230474a5a9c775b5b7aec16e8312a72e37127386079f9a000e45b2e534" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_6 "block auxiliary" .pendingSplitAux .onlyA
    "b5bd778390aff5825ef9ccebae03a0d812ba58ecfd91a0f4e5d445306618ea0b" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_6.eq "block auxiliary" .pendingSplitAux .onlyA
    "208045fc6328bc17704c968e054d46ef2be5745763279cb7c16413cb077f2aaa" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_6.go "block auxiliary" .pendingSplitAux .onlyA
    "06ea2d6f01894db5d896e731c5b8c9b73db0b7454518b47ea98ac1a75a8ae2f3" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_7 "block auxiliary" .pendingSplitAux .onlyA
    "37f2750e239f7337b16270071449687fb8f7b15c44d909e72a776183b48ca9a7" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_7.eq "block auxiliary" .pendingSplitAux .onlyA
    "d4117d00a12a9ec6fb64eff466834889ff3785261fbfd2def3f6e326dbcc3c4e" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_7.go "block auxiliary" .pendingSplitAux .onlyA
    "83429dc492238d4f1b5651573a1ff97714ba1502d34be6fa6774e540a65daa9a" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_8 "block auxiliary" .pendingSplitAux .onlyA
    "738e43403ecd72b24cb4c30dc6b750152702774f9a7534344af3fa61f035c5b1" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_8.eq "block auxiliary" .pendingSplitAux .onlyA
    "ad266abd4df47447527cfe391b40b4fc0f35f3751b98e5f44ffd8098b3f872dd" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_8.go "block auxiliary" .pendingSplitAux .onlyA
    "baa439c0d6e5ad47c77ddb3437a28bdb88f920b28e321a86664444c30782efcc" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_9 "block auxiliary" .pendingSplitAux .onlyA
    "050771282dd165668c84167f621eef25c7a4b03dc9c3d9aea3b0d9e6201dfd49" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_9.eq "block auxiliary" .pendingSplitAux .onlyA
    "4e4caf7d6aa6682ed1b939ee6c678722b5d36de7722cf494328a24c6eb03b49d" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.brecOn_9.go "block auxiliary" .pendingSplitAux .onlyA
    "ed824f826c7851838ff9480a3acb67c2ec5997e2a73165df4c24640a10d326e2" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.mk.inj "user constant" .inherited (.inherited [`DiseqCnstr.mk.noConfusion])
    "1ced1987db5ec0657c8bbcdd99438feb24cbcd258ba85737621987662f32855a" "15a6513fda8776647ade0ef5cfacd052fa39c7c4a13ad6fbda7892a1939dcfb3" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.mk.injEq "user constant" .inherited (.inherited [`DiseqCnstr.mk.inj])
    "4f8c708582093ead02778811189b769343507e584ea1e50a6d5dd0ac7b6ac5bd" "61439ceb84a646cebb42ef76e965ace62aabbe38c3be3512b8657c08c8b5cf9d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.mk.noConfusion "user constant" .inherited (.inherited [`DiseqCnstr.noConfusion])
    "e4a38124635f08e05f3e3be13a6a51942fe91fcdde8aea33499e6b5623058c3f" "75a8665699c8c65899ca9dd24f8c60ca0e2f0a201fdf22bd22f17c3a88d35e59" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.noConfusion "user constant" .inherited (.inherited [`DiseqCnstr.noConfusionType])
    "ce45835812da6129a1aaedf3926dbccaf0d81085b8b4e914b170aa2eac0ea306" "d86ae346f5f81bc25e4b0a8c2ac006761dcaae9d6f20b8bf66cdd7c3e41d7cc0" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "81104db8bf8e3ecef62baf08032615a1d93fde8ad4a14efd22e3ded763f610b1" "638294dbf7650368c371fd0d1764aa56441548bbba197911ac7e1a84b2b22018" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ee4b75857abd70172592d291fcd6b12e0fbc5d29af66b4e880285d7ef48ed31e" "7d9d2b555734408d889ff7a827c20500ec64f4863b90a1c2a3eaf311f00e9338" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5afe86d6ba419273f0d2e56d0fe34e85d9398606a04c80a290d78b6dae5215df" "f20ae95a437fd10c67adade069c45ce2b0aa6acec233300ca11daf742e093c03" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.rec_1 "block auxiliary" .pendingSplitAux .onlyA
    "ddd6e57726bf756f7dfbc847fe365904524e239df00da39734a2dc57953bdb66" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.rec_2 "block auxiliary" .pendingSplitAux .onlyA
    "ed77126db708e22c8dae7761d325522a01f3b274d49e52f3e1091261de8a3c52" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.rec_3 "block auxiliary" .pendingSplitAux .onlyA
    "af139c14b6c2469961c427e03f0ae1427d7a5159d553bc85af3b39b7ae11e277" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.rec_4 "block auxiliary" .pendingSplitAux .onlyA
    "6ae5679bec70ecc6dae63214037c8aad16ad16199d22c4ab1e4faeb1e45f98c0" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.rec_5 "block auxiliary" .pendingSplitAux .onlyA
    "54af9ded3af3bcd087134d11b65e57dfa0849cf40ec6816d8840aea45b3ed643" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.rec_6 "block auxiliary" .pendingSplitAux .onlyA
    "dcb5cdfcd9098e0b2954534416283059887fd5700f37dcde0b1b7a942a090d0b" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.rec_7 "block auxiliary" .pendingSplitAux .onlyA
    "78d560ba6510d55dc5c28cf132fac30b27c6a243b11aea8de4b34999a2830038" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.rec_8 "block auxiliary" .pendingSplitAux .onlyA
    "6034954432a767f908e42f776f5305614aac904444250ce2ec6313fca5cd8eda" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstr.rec_9 "block auxiliary" .pendingSplitAux .onlyA
    "754b6f7ba88ce439a1c156a77627571a6c2887460085c211e87eb36d5deffa21" "-" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "012905cfcf5a1bfb9edbad73b18d5cba3efce471bacbbf53d65152711af55fec" "b2fbda7096c46f6ed93adea72e776bc2607441749345b4e1ffb6b5a28d52df79" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "38d5e2c32fcb92df4073e6342a6fffc93ad289d401105582dc08c6724a3a5efc" "20a60bdd80470bab31df5171b7e04c64d74e18040c21629c57f7cbd2237de8eb" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6168d13fe3f404d5a6f62b2d2c106cb588ad217413388cd413567ec85b03697b" "f5f2d1063bab5387d74bdaa4cc8ce4b3f43580e4c1a182c6963e0a9ccef48974" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "38b87d091b78b9282e71138f8427db36323d2c175c89179a0b3bee67a7714ab2" "e7a13c18fdd5cfad0195effb650654ea4527720259f3ac13608ea3a34e55afdc" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.commRingNorm.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorIdx, `DiseqCnstrProof.ctorElim])
    "016b1a215abadf57111911df0bf5a4b6ba30f35d64a2b4c59a5f2be870ffd927" "5d9881d22668c07efa66af0dbf96cafb900145b4d5c0e51e087d13d0e5ae3d94" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.commRingNorm.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.commRingNorm.noConfusion])
    "b8349aaeed382ed087310c165d24f76b26d635953ef8dea99d68684c1257ff83" "722818c1bfaebebff5466b752ccf3708ecf63ad81991dbca13b2e36d72bd786a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.commRingNorm.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.commRingNorm.inj])
    "65e3b7c2b1f4d64a7c1db4bd826f9326322c00e3a3132858e04c7da9d1387130" "8bc31a6a74c72d96906ce545bbbdf902b5a001960e8fe845c4b9fe43c0894691" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.commRingNorm.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "5cdec88bbd72aba10a11ef00b99f17a26189b1f55565969fbc00ab0814e85ca7" "245dd409e4b8b5ec90fb12a8f66e45331479f3540c3d8d0be708d559fc9a61fa" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.core.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorIdx, `DiseqCnstrProof.ctorElim])
    "94a1461c31efda5937d6c09bfd71ef53253c47274272b32016cf04d416283f9c" "54cacb160897b75f5ff0b3cad31c2a877c8f9b9a47768537ad8864abd7a18f89" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.core.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.core.noConfusion])
    "03d0283bc4aec2c11512cbcb821f5f9bf4578c8e2b5d252bbc5622eafacba1ce" "01d5d3d85e075daf59899975520a433dca2a882bd03b5973b64d9a25c07d6ed6" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.core.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.core.inj])
    "c2588043309d76e05b79aced326fe56a7019a2c6d9ce851d6f956c1838af5623" "e95b94239332f4d7db304c279d2fd3e7fda60719460691b524b3415fb4b15f3f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.core.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "653ac66e9766c4659dd4a907eed884676099b3e041af23291dfdcdf8a41ac0e3" "59c983514d7ca6ffdea701308bd1ba844892ef198ff89c070c201118293280b2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.core0.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorIdx, `DiseqCnstrProof.ctorElim])
    "e200f38e3391c184f13fc7d0732ce096df8de41bf6eb64afa303eb6f0e2c1592" "333ebfc7781bea24135b3af0907691c0cdac950358be57df3b29b4f4a7a17b67" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.core0.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.core0.noConfusion])
    "2a6a72bd1411b460131d073fe8bf429522dc3910c322306d1380cae33a398789" "db5c1db222a6376a613b84bdf8fa39ea641727e260a99916f04836f28c7b6f60" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.core0.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.core0.inj])
    "a3550401220272d35e9a966a921b5c019619af5545c8375ff5ccc772aeb471cc" "3538afc8da2c7914f6810dc578516b97f5161b5e988525c95b3b1b5a7073f85d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.core0.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "1e1fd60ceaa1574ae368da8b562bef9a3ac894fbb2e5c5cba2eabe502f9f1d6b" "f0d178e034051e1189cbf707f922c233d30b4113586ddb775a8fb9c522193ce4" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.coreToInt.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorIdx, `DiseqCnstrProof.ctorElim])
    "03d0ca9978d43d5d13df8da72e30379ff57d28bb6b5680dfa42e5e9ad2638a28" "d0b969568e73e0ef1c9decaece496d965fcc7582ef19091614614512af3c41dc" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.coreToInt.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.coreToInt.noConfusion])
    "c37f3a4e12b99d1b88801e6cfbe9698122e3498064cab6c93e164021846ccac0" "39e1caa32ff3cd5bdb039897b35d0e307074c7716ba84a6f8c4d0ad98ec46a35" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.coreToInt.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.coreToInt.inj])
    "e5296962337058fbf342b75c2f71ce1710f9b23a68f20ed5ab47edbc483c3cf6" "8231db4f4779f2aa87691b2f7abcd4ddce4cf1f84e51f880578a50c2670f30b0" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.coreToInt.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "636a998a7e741308e62ef5530e5d105e2002279ab91435c554a70df045a8f698" "d3081ba5e5b9b7e2d8d41ca7d66b34f0609fa1b5793a9621f53c34ef6f4da14a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.ctorElim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorIdx])
    "4407927f7cf63e0966ea25af7034e39b938b7ee22fe2b183f178f7e0a3390c9f" "680620062ad6f8d061860032c5fd9b1ee4352c9a94268186a167d9d726b0c0fa" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "683f76111caf22f8c22f19a11dbb4bd3af38419c312afd8c0a1ad2fa329262e8" "46582f0bba7367133f31218fa2459a12f0bce5f30d7549aac57b9595de55c8e0" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.divCoeffs.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorIdx, `DiseqCnstrProof.ctorElim])
    "a8657ffecff6327d3255926765f1e2195b719ae12f1f927fde980bfb56a15806" "2ee560c067dc3546f69f6614da2d799fdce69ad0c0caccd28c7e5978455d52a3" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.divCoeffs.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.divCoeffs.noConfusion])
    "ee3446b0b0a692a16988d47433c965419f2126f1559dc6d03f2695fd03b5a10d" "10f5dcf8414553b8263ce397b61b0b3a22ecf2a77ff9fd3f4985295c4a1d30ba" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.divCoeffs.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.divCoeffs.inj])
    "70703143c80b39ea50f0770df766effd35902eaf5a341ed9d313d9bea7dda9a1" "79f83c6fc2393b306cb332ef9c93f667f630214479553af6e4788c4fa4a60515" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.divCoeffs.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "fb4b51fe5183494a2b0863d5f6ec192de5e1a6310f60c372ce7eea891d86c81b" "87f74a2ad3733696e4e46b654276e54fc921c694cc3c0392211a50864de5c10f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.neg.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorIdx, `DiseqCnstrProof.ctorElim])
    "6c202cec7c742864270503029ff92a8093722c3415c98453ffcd96ef58fb4132" "9e4840d53dd846452840be64618771e787f5302899f4fb489db53063ce5499e2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.neg.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.neg.noConfusion])
    "7ff74fa6a751b5163cb60845214ce1d79011a913d85156b5921b022eb9e700d5" "28ac668892cc43ffe27181c0aa15c7f6cc4d2cbb29a515d97a36f8f2bdaa42fe" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.neg.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.neg.inj])
    "37f5ac5ac691b9c339225c819c001ac8287800ef3a3a4d779ff56b85787d913c" "e4142497365aa24928ddeffd087073ec54d97d26b42e3c4882387555ffbc21cb" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.neg.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "932a88eb4dfceda107316dd9c4142bb20e353f3b1b7c935ff5366f83cbb85d31" "6063d32042b72bfb7ca527f1b7fb18b3d74e660b8189e676bdd27f1f9eb18792" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusionType])
    "c83a936cda4c3d6668257c6e40d100d0af6de9f84998e30bf99a72f552d52de4" "8bf79134f5ee223a2271088644244efed93f0d0b4da60e9dcaa8b3a6492069a2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.noConfusionType "user constant" .inherited (.inherited [`DiseqCnstrProof.core.elim, `DiseqCnstrProof.norm.elim, `DiseqCnstrProof.subst.elim, `DiseqCnstrProof.core0.elim, `DiseqCnstrProof.ctorIdx, `DiseqCnstrProof.commRingNorm.elim, `DiseqCnstrProof.divCoeffs.elim, `DiseqCnstrProof.neg.elim, `DiseqCnstrProof.coreToInt.elim, `DiseqCnstrProof.reorder.elim])
    "88edf446d2a6b732a28feea3b3e0ad4fb927e19b83e8e5b6926357268d53a656" "7b0804ad6d2885eca57b9f30b6c3e3f950ded0f70065d19f9d8d2d97b0353c74" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.norm.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorIdx, `DiseqCnstrProof.ctorElim])
    "2879a82743f17fd516c41806706d4e17a748a0061bc2a20022f10d0a6e539e19" "5762eebee3c54c913fe1745c112fa2c85eda442af8d0b1b437819057a7b0ab10" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.norm.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.norm.noConfusion])
    "ea9c00e49938fc265678c64fb4e0ac9fed1c6608ba6f1b5cb62237ef279b98d9" "444ee66f859c4120f4e44378012ab5de827cc919fa752c54a151feaa02199caf" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.norm.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.norm.inj])
    "d313f2844a8f9cfa87a241011835c33de6dd47cf8c18d4a5dde9dc16bf6804a2" "f27e67e8b8e11c502583d05952022dcfc84d8e0ec5af6e58317281dc851e4567" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.norm.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "0e8e2708bd9d10cb466f674d41095cc09925f6d4306c0234865f58c7468eac1d" "e5bdcdffc1be8bc95a1f3fe3e64fb51af873e45982c661f4a79ad19b428e0410" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "17280c4739ca677cd53ecc779a6da7d2c6384b77a0b3218caadf331936c7c10b" "45e3af2aa3b4a596e04d62f7c97840029ce990af81d81bd8b3440431d7801c2f" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "90f5648f27df98e6bc543e9136d94a135c2ceb210998a949057f577cab2b58b5" "313bc771426d8a2e24acedb9cd2d8e762febd15202a425cbc246460d7c8e0bcf" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.reorder.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorIdx, `DiseqCnstrProof.ctorElim])
    "6161a9c5fd075a1588ebb1e78dd1fa86942b292d54c7f1f4b2bf25706f60107f" "eb303be93aac49b755d1f9ef77f1ba3337994df951b4021977b99003270b760b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.reorder.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.reorder.noConfusion])
    "635dcb91f1d242447b32012e8094caeb1c45ad6533683eb008957970ee73f42e" "a4e80a0bbe06ddec145e999e5ec099c6c523e52b8de3504ba1a990630946fad0" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.reorder.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.reorder.inj])
    "1748b9b25597ff870190dd262d98226ea6e1f3d75e41fddcf095280ab0721845" "8c1c16ef6e51632b425b639b57311671921374efbcc846c6a681c817fb7d3034" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.reorder.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "336bfa961248c1c0fae230815aa76f972989d1879e8c4f3a88bfd8af4a0faff1" "783e33a7063ff112cba7476e603c46533e2c097c6ca64d1be137ffc42804d209" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.subst.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorIdx, `DiseqCnstrProof.ctorElim])
    "30ffd2838009003861fc6305e26311551000ff58798848be247f3bf539a765f1" "a86eae2849c89f3eaa82a5836f096b8d0744844b5cac73b3e38e17f495b44eea" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.subst.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.subst.noConfusion])
    "8837e10cc3f7473c7dda27b389e47ebd5d3623e2b0a015ec7f5a981302f38eca" "cf1100535ee5e3dd6e1e38fdcd920203410bc2a84a15eb8a6b4519c125c78115" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.subst.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.subst.inj])
    "f5055c94b47f5e302e03810861420739266cf73424873fa1a92ecefebb2f276b" "343e848533f3fc72ac002bd00c828bcac79676b20138be2341e9899dc2f91e23" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.subst.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "8ec74377dd4d243f3e1cd7819ebe31fdcced3ca0599cfd0d005f13a305ff9168" "1b3b22330c18942626ea37bd5ad6dddfec1f3b0d92a21502ba7ff935f8b5e461" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ff6b72199ba6e9e31cc9ec9e87090f79d3cc16279183a215efc2b5ff43b3bb5d" "5eedebffbfb23e0440416d8d4d120a5a3dd5baa7400a628a15a3e1eb782bc68d" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7b5caaadd0b2d803f938f6c26fb9194f2fd988d01b891c1a644494d72d38de4c" "08fc264aa2283baac6b709d09e65c7ab81d43d1f93500a9cb9fe813472cea92d" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "9da85c267d18ba51b659fb43d13cda1a3821673593da2d1c091c0b9eb243935d" "30b9476f2d5bcecadd4b116fe56dab43355f3640c629c9bc9a853727dc7d0b50" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "26c82ff8cd5eb8bb29ea7c85301fe75462c018b9c96758a30cdffcaaa5a9d1e2" "403ddfffa5c5cf4bf0cc545da86388e5ab64d362488a025ac2414158f3eace9c" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.mk.inj "user constant" .inherited (.inherited [`DvdCnstr.mk.noConfusion])
    "417b7a47599f98dc46e244fcd6065ad9f820d7a33a2ac826f05672d04e7c83b4" "3aeb7bd8052f27f26caabe207d908d26b3efdd52a2cb6d35f15ca84db73e0990" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.mk.injEq "user constant" .inherited (.inherited [`DvdCnstr.mk.inj])
    "71a9f0f9e5494ea5a4e1918650e60b154eb58e6ef73d5167b9d0ad7f1734cdcd" "1426c54753f6af3e0f0856775c95a1a29ab289778dca40c7b0cba16efa672511" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.mk.noConfusion "user constant" .inherited (.inherited [`DvdCnstr.noConfusion])
    "7fb76ee99ad884d46084f4d8df3c74f9596e23a8290cc0e683f27a0ce19a2a72" "d80142be500ed3b8d8f5b6a6244cb6a7d7220c208edfcc02bb609165e5a38c21" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.noConfusion "user constant" .inherited (.inherited [`DvdCnstr.noConfusionType])
    "4cdeec40fe07462857747506566512629539787cf611d42f0590609c5e93408a" "4f9304c087fc43d4dcf1653a4516a0e29b5d0517f6438cdf0c3c4c1552e7acdb" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "d58f1f376214246d01e0e9a25a6e2d5ec42f39fdc02ddfde93d3dee00a51519a" "ad056ec6474cd8c259028313498b3691f6aa6cfe002b0b0b509501a8c4a02a69" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7be3d552273f057b527ae139e422d1ac129ee6ae8eb74e65748ffc47d51a9143" "1f86c8572aaeb0c98602c5a4f83e394000daf2891e2100f1a17d81a7639f7b25" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e2b2e0febea7c088ddbbfa99d0318a9d50f89527ea1dc989318133c8123efee4" "089bcf64684c025558bbba59aaa6b281f53e21f426cc2ea592ddd02f2c380a26" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7ab5ac7dec10d5569c079aa528c0f3f2191b222c18cf71fb60ac7757363c9b0d" "8d4bf95f2e82d8f2209e03bdc427866038127c606808e88c182d3fd695483463" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a0e2646998aa1f6d8ed60d56c171fbe4630d0f6c1b2578b2f3204affc7a9ffeb" "e9ec61ec6466e2165f5f771c7f2e02145e8eae10711e643b694e2d8feba22435" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a815671b1358a7c73436dbb12072428be6c86c3b4138903e3f3614b2ab1050c5" "6b804cd1c6a69706acaff48a3bf1571bf2d1cccd98ad6fd769219902e07d4013" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "04a34aec95e3dfe62503bb971ec257b00e4f5227361d448798d01579d68ca404" "4b0cb8ef455570ed7e69902228707dc8490eefd0b4794323a6f2c5bdb5a3f295" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.commRingNorm.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "9084501443269e68944e469813516420dd0391f68966cbdd5ac26ffc41f8a43b" "7a415092c69626f64b8dd29b6d9d0869e340c746db3174dfccee2fa881ee88a3" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.commRingNorm.inj "user constant" .inherited (.inherited [`DvdCnstrProof.commRingNorm.noConfusion])
    "94a8e05ce3de0776c8e916a47bd2446f52624edc2286200e3e3d9b3d12e6bcce" "df283f9b522552bd308baad62ea1f2bc4282a375b1f2e1c6a48aaac01d19a9a2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.commRingNorm.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.commRingNorm.inj])
    "c71faed0d4a355b7261766320b3d8bbe0fbab62b6f0d523676d901f3b3518758" "a93bbd329080b326c76c2328e3bf72a7dea2e24b1160257ab2d6fbc9f77bef2e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.commRingNorm.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "f50cb44c09ea742da9a80182a20d13e4e344ac36d31c30de500306afb0f3f8d8" "760db5c224a531627a78f8b7c7fbeccae8dc4e4964ca5eade57d080a6f635552" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.cooper₁.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "39087dd7da1012fa6f427ae07409f35e84585ed216582314cd8928a42c382fbb" "dd2ead17758f969f89129e9efe8c66677831166e0b44a57a4ca0acdadec595d1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.cooper₁.inj "user constant" .inherited (.inherited [`DvdCnstrProof.cooper₁.noConfusion])
    "4b238c389791b71b7a66a83d7a16f3a5ef1e469158314ed2cd440428f6715b5a" "91b858b3a3065f57556904c5f2f0d17c69b6e9d70c1066d6e68a80b6db5fc395" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.cooper₁.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.cooper₁.inj])
    "7867f05e55b2be05210b3822cf900b04306ea447dd8c5dada885a221ddfc0d4f" "7840ab18c17a02ab580a57c78b37c4273eb78522704d740fc19da4767825fbae" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.cooper₁.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "5fe98a29285a2038d9cf71b725d50c5d1087fcb6ddb3122f7ee466a8ec570422" "f4dbe97b6d69a9b2a95adf8cc0e07b3e4f2fe6d58f1961f8a3bb89dbf956e43c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.cooper₂.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "23a931988a9b2065a0acf25ed4ffc188621d4a19467d23af2b27df6db52e50ef" "e9b771a9a591bb6e8c6d05293af24c96f59c3987b324efefc13b0bb39d348122" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.cooper₂.inj "user constant" .inherited (.inherited [`DvdCnstrProof.cooper₂.noConfusion])
    "d0e554c346d73c1717bf0f4af9e0d49540acc4727d58030e0f02779f14dd652e" "ed4c09aef86be6a7ceb437663310ff23ca0aa60157b7b6b05eb2b85f150ef0e7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.cooper₂.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.cooper₂.inj])
    "b961c75460a25f8c335d19218a449372620927aaa283a98cb83f0b0f6999b205" "9f467c5cbf0be5d2eb43aa1bd455fd616c1d8016223ded2cf1ab2785d6e3039d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.cooper₂.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "1df5637f44822a94fbe5e51c1bd7094074661f88e2bf639cbd1a5ae7d2e23c65" "be66a50367610b3273b9d0110f5f4d95440b8d2833faf26c47384d88b04d377d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.core.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "419e314b07388c5346ff6f6002c58537ffe6851e2c1310b795020c5f54d0110d" "9e229828e76eb0bb657169815121e6e015b3656cf1f5bebbbe84f896aab35a16" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.core.inj "user constant" .inherited (.inherited [`DvdCnstrProof.core.noConfusion])
    "6774691d3246149cbd1d665a856b1d71707b10ee354e9c987fd542d920f6a6e3" "9bf853482c4a0fea5e39290480374daf90591adae698ea417f49bc0fb81a9a97" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.core.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.core.inj])
    "ee293a7afc8c6c8100176029f18843f12eda875466a4b1881d32a96765ceb8e5" "30e8a086870808d0baf5f39dbcb9bbd38df36e8874f6f435b09d94902857d409" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.core.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "e40c26e7d1432beff5a49850c6e24c07c967de254d51e04307571e5f673d37a5" "e980fe9f48658b41c4fe3264585d3f6c586c7179e2897f8e3be6f7bafb02791b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.coreOfNat.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "d339c382f78a604c9916c787a64e940e6a70fd820919f9ab11244005c4cd2a57" "5ede3764c09abf3ad1cd3f57e8efc3339f32e3fd57108a1928ead8d5e294d777" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.coreOfNat.inj "user constant" .inherited (.inherited [`DvdCnstrProof.coreOfNat.noConfusion])
    "fd896fc48b98a9bf9fb3127ecb29fc6dc099599626ec5451ea8b2bad1a117560" "97dd02d607adb3d206770e82c7419c0eeedf5afa26e89e481c6fdbe008538188" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.coreOfNat.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.coreOfNat.inj])
    "6d9a528ab7532350100d8cc85e7d5b52de29b9fdbcedf7a292c7a65ef2dd9d6d" "ff930ac929a2d8d9333839dd16596f7856b44056ac4ac3b758ee5a33fb8f5ed2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.coreOfNat.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "e424821752548712f529891c4dc0c4a6853b09094d9783ff7e83f0fc862a6f9d" "b15f28b5f848d177ea9f4e3045e547e7f38583aa9344f584224ba0851ad04c50" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.ctorElim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx])
    "8131fdcea5c39ccdb829156bdb90ae2c8b0d1f50677b3374776079f82ab6a151" "924fd04b076ae1dc6e61641c7572eb8cb5d760b70a79514d48704044c90f9399" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "c5145b9dfbd0179c88a43e62e12a8adf2988e75b2cad72bee921de9b7402a199" "cc44ef82bd592d949070247b7e36d31715ff17974bcc9e861caca2d65e16afda" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.divCoeffs.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "72f66abd6bec1d25b7a85e9d2af04cf15e56393506b2a4a09c3d6d354e6444df" "412a625f60eee9209ada582eeaa714e80f2a1baae0eac3ab39787eaed95858d0" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.divCoeffs.inj "user constant" .inherited (.inherited [`DvdCnstrProof.divCoeffs.noConfusion])
    "b03d091ea9700b0c1b27687fae11e5275351a01a7fa41c602f92950c3e0cab83" "060d30fc587323528fe0380fd4d3e1a9de4e11f97c6a30b1a4cc929fb1cf0447" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.divCoeffs.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.divCoeffs.inj])
    "a80656f92d87d2c6951c293d52ce76e85cd026f215e5aac098922344a66c61f9" "2c6336b6f825cbe50ad4740a07fa09f06039738c12d459efddefca08484e8ce4" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.divCoeffs.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "f5a359ce59e92bec42648233e8bd87abd36efd4ebdb191f9a7ea2a84de14997a" "1f08941024f302ff9b1fe73aed510a234e25f44d2f27beb22892ad31293dc770" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.elim.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "8f771096b793af3cb4699e04f6d24d173946c3b6c02842cfad80dc8955694226" "9cce64ac8119b9b67efd34e9fac1e8a98872dc5ff0495ebd6a14d9175cd5cd4d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.elim.inj "user constant" .inherited (.inherited [`DvdCnstrProof.elim.noConfusion])
    "2c8d7ec1aea6a39acaafc98199be05a4051662a19b91fbb2020a4c5416a439ac" "4da52bb7de2f167a8550ebecb1c1a3282757ec14a96c73af379ce88f12395403" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.elim.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.elim.inj])
    "a1a3727c21ad18ede764bc573695cdf3b114ce4d395773c5e786735294bb25c7" "ef37bd6185d0e1b3694bb93c314a9947fb0cfd368e7462c2a582a23f756cb4b2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.elim.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "fc9f0664ec9560cc1e454d15602ea02c734cab02b8c7326d3ced746662cadc29" "df71de3d5c5ba27defe26b32e6045bf020cc9d9a3fcbbdf5d3ec77cf5a1ac146" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusionType])
    "51e20b9463bb923b14429b867e60ef3e99c6903fa61e91b575d4abdabbe30630" "a90b92c6ab07a03dba47efb19e20d9b48f86ea1a26de1a19c715eb9b4e304c00" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.noConfusionType "user constant" .inherited (.inherited [`DvdCnstrProof.elim.elim, `DvdCnstrProof.solveElim.elim, `DvdCnstrProof.coreOfNat.elim, `DvdCnstrProof.divCoeffs.elim, `DvdCnstrProof.core.elim, `DvdCnstrProof.ofEq.elim, `DvdCnstrProof.cooper₁.elim, `DvdCnstrProof.ctorIdx, `DvdCnstrProof.norm.elim, `DvdCnstrProof.cooper₂.elim, `DvdCnstrProof.reorder.elim, `DvdCnstrProof.solveCombine.elim, `DvdCnstrProof.subst.elim, `DvdCnstrProof.commRingNorm.elim])
    "4a0eafe3fa737ee0c02cffcf0a74d87527d68132603263ddbd772b2191e61189" "7ef85bf4fe95294fb8f9ed084356456562d2fd42c0c054607421902e54051d47" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.norm.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "1202355db3bb39f84e1a09fe028f08e5c652134626163e74e8eaeca0f251feec" "e3b3cc3e12c46b035ef95449fd918417c8e13c8ef77ef5fee78aa4954c5d18a9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.norm.inj "user constant" .inherited (.inherited [`DvdCnstrProof.norm.noConfusion])
    "f8b5176abfa53153d418949fffd6472cd5ed791238862a86ae3be13331dcd658" "cc8f54c25a72370cdb7d8be47ded9ba95a166d0f544aedbfc70f4b42f434c7cf" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.norm.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.norm.inj])
    "f32edca4e771792f789d8bc6ab2c03472cf5ccaaf53416f3dcede90396f5566d" "758859a3ad089d46e5d75cbc750a30fad844c1c17aaa9e1d6ce07033f9d14f27" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.norm.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "90d71e9378dfca18f76f2fadfd4af6b3f4cbddcb245a10767881399bb03dc6b7" "d1e8e9114ca7f7ceadac41df59aa0a5ac8b4292f8e4ccff3b8f0e5d4abe84894" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.ofEq.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "e8088f321de7fb0e315821f91f1a8b1452e5567397214ecbda24032f5a2f49f4" "0e397eb26c892389161cb044b543a8c9b63813ef716827b84076bb64b148816d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.ofEq.inj "user constant" .inherited (.inherited [`DvdCnstrProof.ofEq.noConfusion])
    "1ddc3be26f91696bf631d6f8b7a89c0e04b30094037d2b22cb8ecca8d100a1bc" "c41acc6daed77889581ec31e0edd82856adfcb508d892b2331029d3c3dd8a0b7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.ofEq.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.ofEq.inj])
    "40cb9504a6e1a8503a60e1be48cbf8c194f8c53e112bd4c25814a4d903b9abb5" "2b9071e1605f565f2447e0f8c9ed6c152b9a9bc93ce0c1f2d3bb9e7024471c18" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.ofEq.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "a5a3f07fafd679fbc87465bab325894aa73b93b7a402372289723800bafbac9d" "1f94e9ded00cd86a0ba7cdf455b940b6034287eab5441fd5d055d6e1a42f0eaa" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fb05aa5c3213d21a2767a0bd6db6a0034e5c3b8cef6ad1d08bc8b1ee9e1acd45" "27eb7b3aa2eb3db72ea55adcce2f8b0bbd54867acc9550abad2b6bebc756d57a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "50e08503d21b7353534e822727373ba426a0e2647681dac834d03000c5c23a18" "75a6d2eef31356153cf9e368931ea699bfcf421989e157239765bd40f69aede0" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.reorder.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "c9320d5616e8b8915e929b30d99fcab1b9c2448d2d8b31c935e93c69eebfc908" "0031a07bf121d62c6093b14d0fc770196941954a87c906d357d62a5c7e48784b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.reorder.inj "user constant" .inherited (.inherited [`DvdCnstrProof.reorder.noConfusion])
    "10a18695e8baa9010ef1b69c02da599663249c27644e84f6c0c12ce21629b428" "a0e3cc053e00e83063df4dc7b7fe5ed7f7ae40b2fa1511966dc0362550467c3c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.reorder.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.reorder.inj])
    "19900bf04687fb41b7e0a89778e93a97dd606fc6fc5492a462cedf51cc258dc8" "9eaa958e1c4de67c95e98b3ed6ead31f31a71068069ad9adebf91fed8db2e449" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.reorder.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "a45afa03f3da12fb3a1382f2a686bd98cf0204180a1d43adc98569af485aee0f" "623b6257ccd8c76444fef44d4269dbadba8bc96928c27a6452f002693fa628e4" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.solveCombine.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "46b53f1f27a80b93f0107dccf03d27407af2f57fdfbd4583390e3f96e17e9b3c" "cea519d19dfcb2f68675a6dded42506c95bf624e5a8777e9cad9dc4053865284" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.solveCombine.inj "user constant" .inherited (.inherited [`DvdCnstrProof.solveCombine.noConfusion])
    "6f530b6d97f4a622da4f7843c4d8e3222c7589adb1d46a955ec9378999880331" "a0c94740d5285c7e0a397a18b57d169ebcb4ef0df72a02269fd889f72443922d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.solveCombine.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.solveCombine.inj])
    "90020a85d81ad075d1e7cb20d561635787d7a2076edaa86446f7997212da3db1" "d9e3c79be4964aaaf633fd6013cf5ab31edf0158f533e7f706fd68bea97e6682" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.solveCombine.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "5067a8c44d7bc66eab74b346016a50bc182ce64a9a71bf324714ef115d0296da" "54593469aafcf7ff4e1c77ea0c2847fcce164a6be57974b8e8fdf421b287c005" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.solveElim.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "8190171ffc611ac9ff9860699c8e88f4fdd389878d118fcbea4ec08db709e7df" "743627a417a7c92779586b9d1546676f5478a722ad22542bd2fd388479718e7f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.solveElim.inj "user constant" .inherited (.inherited [`DvdCnstrProof.solveElim.noConfusion])
    "a607402416f3978afd1a180e6f9970268cae7c1716dcba9b3c18e43511193b50" "0fed7ab7379fffefd4de0a178511f2f73909b3eacea95c2ce70ddfb3312c000b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.solveElim.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.solveElim.inj])
    "6acc54030490232c5f3aad2cf2e31f594398c6e51bb53a83fdbe2802ec75e434" "859763fa6500497e2cba4673d5912e62f900be4e47d02506458f4713d1b56f93" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.solveElim.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "46db4f4293c4c3d6ca60468e83758d3a381940587886d4e4171e8ae0005b0ea4" "2ca72dcc066abfa9565513550f875c4717b6f6c0c4d4110a186f128ac52ba45e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.subst.elim "user constant" .inherited (.inherited [`DvdCnstrProof.ctorIdx, `DvdCnstrProof.ctorElim])
    "0bb20f45a52813700f1f8441c30b9aa5c6084b6e2503fb4d00d8d37879b5a611" "bda43f05e15dea002884afe4cf43855f67ebee6079f7a05fcf253b93d3885bff" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.subst.inj "user constant" .inherited (.inherited [`DvdCnstrProof.subst.noConfusion])
    "f492f31caf4c7236606c34c27d082ff0b7a5f54abfdec8daba75fd68c6adcb09" "8045bf0683b3c731d628ed924472d097a1832e109ef38aba4a1ffa5d644dfddf" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.subst.injEq "user constant" .inherited (.inherited [`DvdCnstrProof.subst.inj])
    "4cb8728ef8cc179af17ba41a8f968992a86495d66f39ee33d66e425cf4e48b4b" "6bb84e904d7a2918b867370ae12ff9f9fcee881cfd2d50175a694e6c9370ba73" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.subst.noConfusion "user constant" .inherited (.inherited [`DvdCnstrProof.noConfusion])
    "bf0a070734f21b02f43fd662427c187b9c852daf418373840712e89936056915" "35b3e4f83aab8d6263af8c09adbbeda6f1c7f1bcceea47a2bb6345fa947ccec8" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "9feed257ec970fecf3ce6661b0fd19402bb1c466857194249a2bbb8d3197dc15" "1787d49f5d5a74d4b88861c19017d496239ff492e2893dbcbe6f4aaff3d1abbb" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.below_1 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "920a45b126eb8ff0f62f46ba507ce079871774e0c66a338eec2a5e33b7648840" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.below_2 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "1e3b1cb9a0bf9a285274cdefeff4a3a3cf44d75a798df33449eed1c83df3ea89" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.below_3 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "ec2fdf0f17113786b2c606aab0f09b8bd7f45bc899f86af20859cfed0e7d565a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.below_4 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "ab4ab1c275a5b8f6f5c1b0b7d2d5829f0921cc8db98e3a6e77fec4807cbeef61" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.below_5 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "69d2acd9070e6f452b0ca669bc7fcf8672506145bb8a74609bc9b0b9162eb2bb" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.below_6 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "064364129278e1d7a9fbed21466f7d763787816f3ac691614b54e51dac464148" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.below_7 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "0cda20e898b6941d1428b2bf98c0319aab35d6b8e693b2ee23f4190b312200d7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.below_8 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "fb472c3cb3a772fcb91a97dfaa6062c9d1c0b80ec0dd1c81a510c100c919f555" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.below_9 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "acdcc1782c380ca9d976a38f7accda7d8936710596dc68cdeb1c4bde2039e79e" ""
]

/-- Entries 1400 to 1599. -/
def part7 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0fdbb54ffc99f0bde953000076dbafedf3fd1bfa19981b7f8989ffd8bea41af2" "b0faca8e0e380cfb992323e877cfe51db77f89d0f648fe947c51e7b43fa6d684" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "362508db4078fe7a42529f7b35424c6a1e0914ee4cf1f642acd3becf82e62e06" "040a72f73f129b88836ac85ff2eba43208f7c5e3476365cdadf570b2ad740004" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "86911ab349740fc2abad8a9ec25e8c3b212c3f81a0b48bb219690611055c3a97" "955d94d8b0186292ebc3dd96dbaff0f35a45ae49cdb015024cc909d12728a44e" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_1 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "33a6d4e6bfcb56ac652d8e1f5df34c9e46eca0f15c67f4159585636716332430" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_1.eq "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "53192b9876972db0e1af85cc3c2319611dab4cdd595457378184b7a7f8625c18" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_1.go "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "eff2cde9466b54d33c7731f198988562d3f1929671ccddb9db0d06c217a2e4e1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_2 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "63ed5a7f7d296ee52d5f77a86f9de431a682543b11db4b81773cf2deba89c795" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_2.eq "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "289430b86afa31ccabbab91bde8264defc636b72345ae5e086c9f842168f610d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_2.go "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "e294ea6a7b952cf4a1814fe5c9c5093163f4e00413f0ba4133976041febc8632" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_3 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "df255a166626043c2ee605d49308a595b5a6ef753d57784b968be971926a0216" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_3.eq "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "2d7bb425ba815f68861f94dafb9f1f687ac927e5f16d2c0cf1b071cc788e98e1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_3.go "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "15eabb2ba1524258a41629ab695951c59fd931dca663253574c848a96c52cb41" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_4 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "9e76df3087d9c25895cfed830edc9b241d67ffbe3fc0e2eb82bad3acbebb59f8" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_4.eq "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "d98f46014952955e5e3b4bf9c0abe5f96fd1caf34a265a72325c64f825d1faf5" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_4.go "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "42e4ea91a1925b43b2a0ebcc66fddf6d0d4433f547e1491f24c6a5012241639b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_5 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "46c6d4f24c591f9e17c39b0d8a0e5595474d8a2ed4243d1cdbcfb5920c74c2ff" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_5.eq "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "03299a7e263d11936edc8d117cf4f1e7917058587947d31c23f1183ae23351aa" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_5.go "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "94895d0f467514e735a66378c19aa5e6c2c260b2b68db8405290b2e12f095159" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_6 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "ef4a0b49eb2a75059449a47e6141384bc0f5ec28848b7877c0fd42957d3c019a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_6.eq "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "62d407e72d9790e8d08747df449ab550db94b1cf3fcf66390c6f283b911e453b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_6.go "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "2637ad4ba4db665e4be81021297e718c02d1774e7edbb7158406ac9e6af9cdab" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_7 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "714bae32dba309588c37288c556041e2b66454f30dadd63d8f1bd56d641730ca" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_7.eq "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "832e5113d4e550cfdae8b95dffb718d54f8d5e87a85a6d2308c3a74040f43047" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_7.go "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "c5159fd054207b3edbf99353b3bd297473a5e817ecceb5be03ec8a87e46feb9f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_8 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "8ce317b2a293703cd735c966b6416d66dcbfd458664bad8df4ea2c931bde0e43" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_8.eq "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "299e4a4ce8aa6a0cdfd79be542d53df54dbfc81c4dc0a9e142853caf374165dd" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_8.go "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "68a739525bcd4f7ae70d76c49933297bcadabb477932832e50fa14b90be35ffe" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_9 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "e3a7c68c967ef8361258c6bdefa792d2ebe13a12f6c69b65694ee524c832c788" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_9.eq "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "1d27623537ca8c5da789cb376414f0f12d6c6b72c6f18dad512789a31df1e0a7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_9.go "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "f6c3ae6304151d152ff091b118a39bb287e3c5fa22a5eb8f080f66b07aa5451c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.mk.inj "user constant" .inherited (.inherited [`EqCnstr.mk.noConfusion])
    "94195dbdc5744a1dcd66b5ba5eca95813cbc7f7593aec00be12a58887232adaa" "79290c3fa96cd97a2eb5a4efc5232de7899e8d18925d991e0ac0e8aa5bc79ce5" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.mk.injEq "user constant" .inherited (.inherited [`EqCnstr.mk.inj])
    "6bbc51f9cd6df25dc2e10c649ccfdcf53c6d2b37e20140c249b78db32ce6ef3c" "b890460c165ded756a07897d6fe722631d5de6cb60498fba9f368373e117097b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.mk.noConfusion "user constant" .inherited (.inherited [`EqCnstr.noConfusion])
    "571f9f6cde8f0d01259347c0b6bdca4bc48e9c7ff673ddc7ea4f03928080d9ae" "0a18753cf9c828ca5c9fc8fc1ed9536864ce0bc9b886b951f9d1e5b766fe18ff" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.noConfusion "user constant" .inherited (.inherited [`EqCnstr.noConfusionType])
    "1ef2520d746367d5d27989742a63d84b16cea2720dcc32e7d0bd49cba2fc1060" "779d00694d17bfe0f7cbd434f55cd22aaa22c318110827603e5eda52ea7c3410" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "36f8e7d6b7b63339495f39fff9a174f94817337f5e6239053947e0c46cbc36a4" "0208b731307954c0dc6a2638a278d41a03e9bc6fb39697e904b5cf3366450578" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "696753c18c9cf0f2987e14cf62eb292a46a41eb41f45cd798301cc05a2e64285" "264cec92f748380480250caf30426a66c92d8fd8d5700304d7bc2ff5bd915039" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a6a0405a187133627c2702a82b9c490fd7dc5a905aa0ea2415db7fe5cd8bf412" "ac5ca4db2fd606428ea6cf5338068cafb5bbc1030d3947d16a8d9f1c9b1bc7d8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.rec_1 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "ea270489f0617818bd2f9a3fcdbf204553c8b222b226cfcf0dddf58bafa58aa1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.rec_2 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "7ea6d519083902f6d8a28dc3765fcb8adb7142480893bc79a7ef05eed64a0ec5" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.rec_3 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "94b39451a0680f12c9cf0e5e9b9f27f2e262c10e6f10ca666f34904a8ab1f3d2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.rec_4 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "c6c6d63fb852ef5251536756886131cdee29dde55060128d3f88ad718563336a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.rec_5 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "71073685ad219abbd53db7413f232235196eef4e225ce1a2f6f299a6834271ab" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.rec_6 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "db2c32b47023ed05b0124e99996094c18858162e0b002a5f10da23c414b3879b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.rec_7 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "8ba3f1652ac20e76bcaa41b7fba79ac1101c902e5604ad98c6906964f04dfd4f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.rec_8 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "4e13b7ac58f4f71bf3687ac7353892f6753480ca4ae291607c5fb975f9e434af" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.rec_9 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "42715a878782f14d9f93101d8126985bc1b7c25cccfa715a78e6e449960bf532" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "50ca87fe3965c3f242dbabf6323785193537b385475018e92399f6b0bec201a5" "9f16d5eab49b9e15662158994292867ed1ed23f843e6bd2daadefa1cc6a255a0" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "26dd8f8ee5e7144e448d69da152000953b452eb8de210c65ac1b916618b57c43" "63daebbf238e37e17c35079b395de0320eb1685aeaf37fcc0e7f9d7c65eddb0a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "03c569adbcd44c144ed9d7234efc194ece99a19c732180300e1d61eedbc45019" "8e20ce975863d6d571e44eac8b613da6d8e66d3e947c99095545820a34323420" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "78084427659295d7df7e3772d1279b1d41c3aca7aa533a6bfb2a2cfeee13c9e6" "6ae27037ef940916d531a699af57c9d7a0086d3a409de2ac6b55d557ead618fa" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.commRingNorm.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "92389931000c9f833115c4aeed5ef3d49f9cae17d0bcec808f5f1e2ed289cdf5" "f0d55075267cfa6b2b4aea4019238cb9462eb70a0e251dc3bc4e189e0c2e8a94" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.commRingNorm.inj "user constant" .inherited (.inherited [`EqCnstrProof.commRingNorm.noConfusion])
    "a9db7b8ad1ef495c787bee9530acbc786a27e215d0569b3c2c12e65b6bd43276" "71426dcc6e82a1ef32a5ed40cb4efa8316164b486a019712c3bcebc19a89612b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.commRingNorm.injEq "user constant" .inherited (.inherited [`EqCnstrProof.commRingNorm.inj])
    "8f083e1c844789eac5f14dac47b31f275a31bfb1ca29ab738886c7804524a7d4" "9ae3034fa057a0b99d50df32b21513e884b0b806c3d3587cc75d5e2c6bbca453" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.commRingNorm.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "8287d536bfb2275d97dced90bd131020268639baafdf2b8d7803cd18f9143c96" "528a326812a44f2202de376bacbf10926996a29bc69a142dce3f1bd8753ee4fa" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.core.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "9f53c4aecdb40f65ef2c0f69452406b843ab71544083e9fa7d8a8bce69effef6" "0350db904a7b63f738b21eca272f2188364f707ee883a40d01ab125d0b7741ec" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.core.inj "user constant" .inherited (.inherited [`EqCnstrProof.core.noConfusion])
    "c1ceab400f28fba2edda564db4e393108d1b4296690cca1daa69174586e682cf" "aa366bc5cd5517adc5cb20b2296680a6fe498756ba0431643817a1ff7ee42ef2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.core.injEq "user constant" .inherited (.inherited [`EqCnstrProof.core.inj])
    "bbf644fd2c36bd90d1e942487ce62a270d6adc3b794cadbb0da249f47bf10837" "512cbd3699132b5cc9584c02a2a3fb4b9efdcc38c188419b114aba4c0c6d36ed" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.core.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "164e1dd778a472cfdb5c31e2d6ef78338b32bea637bf664dc6983ce98d097b2f" "d30a3882c83ca5597e57a3cd9de5ef6cdff8006a813f3cc0622adce7703352da" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.core0.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "0230540d513ac3e398afdfe09a5d6e656e738d98ea2f8f38c65429cd67ba4fb3" "bd9f72a494480fb3ebbb26ee43fe489e31b3b1f2c6ba538772b7fdc9f2660d3e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.core0.inj "user constant" .inherited (.inherited [`EqCnstrProof.core0.noConfusion])
    "8cef504f961677d8cdfdbb4e102762ad34bb759caff4fe44fd3232d9c914fa54" "12bc16c52865bcf42cd237dfc1ae5ab1c92f7cc0ac4737e401c943f30767fb75" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.core0.injEq "user constant" .inherited (.inherited [`EqCnstrProof.core0.inj])
    "f10ccb6bb0e3a5bcc3957bac1422512a1034d1b3e1cbbb2c63666bf1077a0b4e" "d9362692e808bc9141e7ecb849460d0c52cc874291923c96cf4e820583383baf" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.core0.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "c0beb2175441b0cb3713db4b7c5a6932301a7aacd878975b2b0bd8a48536e37d" "a178557f6c21950a67c4ff3fe89d63625ee6a3ea7c9bd8a0d900d04f001bd15f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.coreToInt.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "3ce929a235d8483876acddf0003e9b327319a322faa3152f75a7c307708f3f38" "c43c8b9fa4f8718f81129af197ee06e38153a382de76498b63a71f8926ec33ec" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.coreToInt.inj "user constant" .inherited (.inherited [`EqCnstrProof.coreToInt.noConfusion])
    "265d0b04ff7fc54b5c9a941a88c93a41105f3d5f8561a2b5cb674b8436267ffc" "cbaabf74b5942289707a922104f9272b663084f29c5aacd0c982e0ff964ce27a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.coreToInt.injEq "user constant" .inherited (.inherited [`EqCnstrProof.coreToInt.inj])
    "e273b8ebc04917294aed66bf63ffc656dd098b964685df913f0e679e2608f3cb" "af5716f27890f565a2d628749cedf82571927299de6698f44640c511b6128081" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.coreToInt.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "4c251904154adacc30c3d5e282820ceb478b92453e075a14afd54c17f4bc6874" "f1bf2142cef684b92a07dcda1a3654ec09afb5a5d7c4bb54acb5a9efc8422ac5" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.ctorElim "user constant" .inherited (.inherited [`EqCnstrProof.ctorIdx])
    "5d3ca9d5787592357fe32ee93dca32e0c8b63e38dfcff89386961ccc06f1d09c" "0177e627e7e09574d098cd1c48ffcf6816f86c2818f2348aa436b1bf07e0b722" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "c2a75fb83e41c2f4172b99193054859d668006ee938fa235b004666d51f85808" "b33404ccd623fb2f97aec685bc8137f47cb9788f668d749728d641b368430379" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defn.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "faa1f571e34ed0cf4ae67513842bf9f408539e5b109e5582878aeaed31a8b8d6" "5aef98f4f26b63f87edb7ee05069b84fe495b59aeafc5eb11c246d9f6f64e1e6" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defn.inj "user constant" .inherited (.inherited [`EqCnstrProof.defn.noConfusion])
    "d35a4a7381d17495a5fe264b4e8ef230299badd6fa47660e3a7f1408aca032b5" "a12db46522db8e068b242d11802374deeed2f83ebdf3e8e8fe7dcfd671318599" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defn.injEq "user constant" .inherited (.inherited [`EqCnstrProof.defn.inj])
    "65e7b8f05dd7483a7ec64620c1d540066249fa816f746afa77c3699922e61c0f" "d4da40f778df461352799451d67473ded53d6cd24eae868c27baec738a06bf48" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defn.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "d3a5ed825a295c96b002aa51a02aacde9fef78266e7ffdd2f722d493f4ac9a62" "d062f071871be467191f826b3f095bde1a3979d37e15f10ca6317d304d7060b3" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defnCommRing.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "92e93f3a7307e15de956946953593dee621a2eee6e66e1ab192eb39cc1fe8df7" "854084b20266c6a6d74fccb137d16585218dd605f2bb4dc8ce502eb16e85cb24" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defnCommRing.inj "user constant" .inherited (.inherited [`EqCnstrProof.defnCommRing.noConfusion])
    "cb8503b79717d90c57c8159e5a95fa503f660218304a38fa027b8e5c8a1b027e" "acf11177ea1be80e84fdba233c4f2fa6919644976e5b7ebc0b2cd67c446c3562" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defnCommRing.injEq "user constant" .inherited (.inherited [`EqCnstrProof.defnCommRing.inj])
    "d96e905b56286474305b4b6999925e87b5de9ee813a40a8d98b780f0d93e41b0" "9cf3fe866a3b5b8c5d8b11943c9579758c2864b4fa80d4daf58d32e88bda8a9a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defnCommRing.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "b2b64d3aadf4a687d4dea3eca6603d282296c470750ebc9cfd6d7139b24fced2" "65c17f7e9784fe94a6ff627510d513f6a1904c2e41917c69733c129e693e66a3" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defnNat.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "883d0541e0e37753fd73711ef27ab2f9559ad4a10f44fbcc3490843f73ed0074" "50ef4992fb31e4ef1a9d458c54b4c4cd83b933708cfd918161f91329a52aefd5" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defnNat.inj "user constant" .inherited (.inherited [`EqCnstrProof.defnNat.noConfusion])
    "26edcc5219efe6687af72abfd5eb1a9ab2cd85b1d9bfe538e3b9aed2a9c89e39" "219043a2bc80def0dd0014e84e87579bef2b425dfa3714f6bb2987925df29dc0" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defnNat.injEq "user constant" .inherited (.inherited [`EqCnstrProof.defnNat.inj])
    "eeec4b03fb3659768d44d9e3cc21050da2fbad0b29686e40cb418e2d8c69e0e9" "07a7fa31458a55360e10c9d3fdb993690f68d88b4b4422090a10fb7644a4409c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defnNat.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "7da702c553ea9168fca43ec032117359eb92927f65418b6e7c1e6671d8d89e6e" "a0c67dd8023fccf30f6f90cac714700d137fa9b55a11a89c1aaba3110a4b83d2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defnNatCommRing.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "5400710f315f17aa8abcbae1960764bd55340fdc7d1346dc992a2923f04dabf5" "b10f4973ac0ee783979eae7a097f3dda43a1c812211d30a3ee6e1e62c7308652" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defnNatCommRing.inj "user constant" .inherited (.inherited [`EqCnstrProof.defnNatCommRing.noConfusion])
    "ce96af532512b5d66b0305558706b8280df8dc958a2ab29864030b5379047175" "1802e7662cfc826225432ee8575eed325c37cd6e6cf9c3383279db5ced5b4126" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defnNatCommRing.injEq "user constant" .inherited (.inherited [`EqCnstrProof.defnNatCommRing.inj])
    "a91b61a76867dda73b6a5e8a7b8e48694eba2ff410c1f0ecc3f4d317f1b5c6f4" "e88c2093eb1cd5ef37d85014b4ca9b7cb044a1a49f00ae8a0deeb7a5e4e1af1c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.defnNatCommRing.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "1ab87f395c9c0787c87c6e69da1dcec4794597733d3790877b280e662d9270b4" "23e3fe3d49628e8dc48d1394418dc9092e66e98bc7fc8c7bd3df7f9880adf774" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.div.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "8a9f0c076ea77e87664075e63382bdb7b3ff57602e86dea11ce51a9adb275689" "ad36f9094c8c876d62fb4d14f706dfbb66f35f32f86b33680188cead5a66bab5" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.div.inj "user constant" .inherited (.inherited [`EqCnstrProof.div.noConfusion])
    "44bc6996ac5787f7fee046bd0802496466ae90bfa360392595bafe4fcfe1040b" "46a672f711b06e525313589ecf05fe1c1600e7dd278ebc6622bb2259d50c2197" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.div.injEq "user constant" .inherited (.inherited [`EqCnstrProof.div.inj])
    "d118e5f0357de310ad2cfc77f6e4e986bd7e8514c79dd482f66bf436d3cd4946" "b08fbe16ef0714cd4a909819fb0953082ddb8e0921f385d2648296e3e6ee9540" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.div.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "ae5b710b040a19572493cedf80274d32fb66cca814f2abd9fd4568cab89ec328" "e1e2037ae2484b2f15d572571cc3b5945f8eb8a7b60a6f9c8354900e478ecec7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.divCoeffs.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "67f12c077b2cb2135e8a95b06bd499d98ccba622975d9ed5a90b251aee4f5a81" "a79d1bdf44069f1a911d8253051b723a8b3bb20ea7cb2f0650f9e8e704e86162" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.divCoeffs.inj "user constant" .inherited (.inherited [`EqCnstrProof.divCoeffs.noConfusion])
    "9f17e858331804692275bf4be522ffc879cd2a9226308bcfda731c0250db1af5" "bc180e8d9760985c9f9b314e30f51c31974bc2e9ea536081b54143e2d52f1fd3" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.divCoeffs.injEq "user constant" .inherited (.inherited [`EqCnstrProof.divCoeffs.inj])
    "6ac61b76de45322823b55241a198760e56e78f8281e7c3b6b10e7566a1901950" "cd39d517fba3e416d3ed82221a2fc448f661a095acc5fda047d66955d973bfcc" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.divCoeffs.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "cf263417c592fa3f3865fedf1525a019448965e8264fca2805999ed5cee3a7f3" "777cd1c8c8fad0f6422e647a593e7a8c16e9c97e2321fa9b7a4528fafcb3e572" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.mod.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "8778dc2ae360854f75ad7cc9c4c86fc0669c1ed89e4ff07b6e8d350a255a6397" "1a98514360f3984ccc381fc976d67b57e4f0503fba0512da71770e4b0409b48a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.mod.inj "user constant" .inherited (.inherited [`EqCnstrProof.mod.noConfusion])
    "c1f0929a520922955d66327421b5b750b47b00e28cdeae70fa831beaa2035c52" "6a24d8db5643d66f736dd52882a5ab2e3b472b393d96b8909f55ae333f3ff88d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.mod.injEq "user constant" .inherited (.inherited [`EqCnstrProof.mod.inj])
    "d48d63ac3612d080473d06b483359a3661d784e89ddb843652071c67844f5fef" "95efee74d17532800dc75381358be4fb748b84f0640dc9df1526d8dda145a926" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.mod.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "17a576e20792a956ef337174a640e7442b53fd5703aceb0043f7518d4b507f70" "cb697e78ba418d2f585bf8c36536977056bb592182565fa648699b7ca7c5a93e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.mul.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "a12adc3a26f73273b05a2d8e95ab74c4d1e643d8a55074312a88f24e729ba28f" "64c6f697defe81b14571a282ddae6788e8a30dba4e9c6a92acd054ff4ae0a10e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.mul.inj "user constant" .inherited (.inherited [`EqCnstrProof.mul.noConfusion])
    "b7faf0ea436e8854188cf51eeb8cd5c11dcf16668a5b82767962b88176f41c5c" "3996815087b8566311dfdd6452e19464c442dc227885632d18cb93c97dd01df2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.mul.injEq "user constant" .inherited (.inherited [`EqCnstrProof.mul.inj])
    "81afa5a06e2c493e74d7753ac86c608e61517b7652e4611fdde3696bce7ebd89" "c241e8d6f1e5a88b15ba957afdb4c4c9660f9d3fcc48f8316c4c17c3d990d1ef" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.mul.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "969d4657b2895924e0bb03bf34441ee799a7494d1abfa33b4665e4ed61c3e666" "e37b95a18432d052a963ff878a3fff2e25b63c2d510cf9174476508a42db639b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusionType])
    "016c50dd8f79baf2025eb1565d9069f719f321a39adfccaf485888630bb18b54" "745a8d21ddac645aedca60a9bab45c730d6001eb025c2c2f39c7d9090e745633" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.noConfusionType "user constant" .inherited (.inherited [`EqCnstrProof.norm.elim, `EqCnstrProof.defnNatCommRing.elim, `EqCnstrProof.defnNat.elim, `EqCnstrProof.divCoeffs.elim, `EqCnstrProof.div.elim, `EqCnstrProof.defnCommRing.elim, `EqCnstrProof.subst.elim, `EqCnstrProof.ofLeGe.elim, `EqCnstrProof.commRingNorm.elim, `EqCnstrProof.core0.elim, `EqCnstrProof.reorder.elim, `EqCnstrProof.mul.elim, `EqCnstrProof.mod.elim, `EqCnstrProof.coreToInt.elim, `EqCnstrProof.defn.elim, `EqCnstrProof.ofZeroDvd.elim, `EqCnstrProof.core.elim, `EqCnstrProof.ctorIdx, `EqCnstrProof.pow.elim])
    "75242a3319f03f65c8e7d55695a695ce12c9c0f5feeae95403ebeb5179a54858" "10820d7adc5e5557842934a9ecea28f1c22fe76f605d9b19bafe5f81b0232ab2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.norm.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "3b8293c83732a3d92ce559bacce29ae8247ff276ba9e0adb43db4d515b8ff0c2" "8f0bed989c01732e8ae81e5f48638036aa93bdab9d052a79bfd67597b6d40632" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.norm.inj "user constant" .inherited (.inherited [`EqCnstrProof.norm.noConfusion])
    "b83e0fed9131dd1e5929f0f3639217b82856ffb7054cf52868b0db6eb271bbf8" "6334fd6beeda08312af36475ebf2f6488318b82d2f89b1c47b1fedf38a0e626a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.norm.injEq "user constant" .inherited (.inherited [`EqCnstrProof.norm.inj])
    "561ede6511bd88cd3fea753fd3b794bc73f21634f4e9c9bfcd4137fe162f1be7" "1cdbaa85536c80a16dc0024f9656a8d26b358ce68309cb10853f5199af4aafe1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.norm.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "4408b35698b6688d47ce7e0aac0727a65cfa157e46ccd1d372e0f7258702a718" "a1520494f732539a154b7e83556d5dd2ed6e5bef2d58d52cf6ab7712c2cb70bf" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.ofLeGe.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "f70b72e9ea8e61b4d7468a3c40d56f7b7ca2df53a7505279bac47e51bed82b9d" "e36574b09a443004b4aeda487d8b0f343c2310516b6de61db6410751998d1b05" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.ofLeGe.inj "user constant" .inherited (.inherited [`EqCnstrProof.ofLeGe.noConfusion])
    "984a9b39de87a9f4791f4717293dcad2ed73d9b02a274b154feb380e4d407367" "4a81262740c3ef39e4ffad484c1cab293eaab73d59cd2582aad072c356d0b0f3" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.ofLeGe.injEq "user constant" .inherited (.inherited [`EqCnstrProof.ofLeGe.inj])
    "873ac98eec641d78fab7b03a537a6dbec32e35d722d829fa1d73bc41720f4a7b" "99fd8610c830f6be91f0924e84828efdf0af9da02518383eefa0e40ae7cc8ad8" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.ofLeGe.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "9eb2d14950fcb39ff2ac5223786028fda392e22ec4a8eb768302a4dc1a8c7c53" "6d5751505900e936c43c7b0755e6d2c63a3c7ef3bfd2f3d5fa84f2559ed1c75a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.ofZeroDvd.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "53a72787319d0f10d5724785aad365a5aa59f7a1440a23d3e5b622ebe0e0fad0" "c8fc11c88f9703ebbfed642c641e966a9d2de792d1f30bffbe3af836dd56f5d7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.ofZeroDvd.inj "user constant" .inherited (.inherited [`EqCnstrProof.ofZeroDvd.noConfusion])
    "88e86d7f4d6a57f97fe6f3ba863cb5f8e47500f692d5b89e45249017bbf8c60c" "3fd6e29cf5e3c5ad37cdc673536d6f14f07233b6258bc5df88584dd1598f0582" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.ofZeroDvd.injEq "user constant" .inherited (.inherited [`EqCnstrProof.ofZeroDvd.inj])
    "e21754ec5d6f5c28fe694864caf2cb4b779bdd3828dc487733471e1fcf188f8e" "8674caf8aa508fa2e9be4dea9221c9eb4ddbf6b203280abed97e092ed53de3cb" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.ofZeroDvd.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "03cf12d5edeac0a341ac993cc6375c0168a30328db6029272de1adaa7330a0d8" "746a1eddd510c1b2263dbaffd65b42c4ccbccdf2d78722cce6d2b916b4acfcfd" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.pow.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "3a202b812dc50704b73971f69d28fbaebbad36cff0545c1b1518ba878aaa725b" "b46e54612df1896de07b1a47b24341761181370162f4efda1fd1bb109c199385" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.pow.inj "user constant" .inherited (.inherited [`EqCnstrProof.pow.noConfusion])
    "9ce7d9253b007510f7153dca564df7acf73f2580b3fd02fef26c5ae20d175d5c" "6e37dda65e1cbb53aefad74f26d9b5774a5ac73bf575696048072625b6eb90c6" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.pow.injEq "user constant" .inherited (.inherited [`EqCnstrProof.pow.inj])
    "67e741f43606063a5b24d200fb6e6cc45b21bd40314b4b45a72643819bdc880e" "aa1b98f594b307932429b9f7188a4d6983d5bb6ed034cdeb9c4549f5ec23cc42" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.pow.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "b1445cb388b3052ea41cd8711f67334dee13c71dbbe64f38b2157f79e6d304c6" "1f9774757dd61ed5ac84e68c855d15b4cc78e4341d6c4ec90e7d2349b528b5e8" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c3f107e62f266d0f9aa63bdceae8b7a2848b58238a77aaabf3a864ff51d1b07f" "dc5dc643273b3b954f0b23dc05318e4c12d8b35dba2f116d007d56637a096566" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "bd9bd0068f1207728c6dbf58446dbbe4d929e124b9550a990a511dc6c5094ab9" "a67c441b3a685bdccab3525a054334d3f89fd59e8c24cc3bf5f6123992425cd8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.reorder.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "de667ae777d3229974f539869cbb160c91fbd70cee31bc7dffa1ecb5b933c459" "bbc95781991b4a5bc64abafe055e38018e90cb77ec47c1846295c245dc23f992" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.reorder.inj "user constant" .inherited (.inherited [`EqCnstrProof.reorder.noConfusion])
    "db1b1e35ba88442987a6ca29836fafcb79aefcae50d835c5152b963a72c79a7e" "8d7b709910eea4366dfecaf27c1b7a37c8e38bdadc3d464d902d761bf039a835" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.reorder.injEq "user constant" .inherited (.inherited [`EqCnstrProof.reorder.inj])
    "5fb59b9dc31a6eac220293addb4eb31af148e3b604db114ace17f306dc43b559" "44666b027ebf2a97aa76bc499c9ae4d4d86cf8405b380a3f7a77a6434d3627d0" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.reorder.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "261c8141ffdbba66b7a36b30b2e889fddedbf4fb297fc74837254c6e8af174ad" "5b3e6fc09f686978366b814a17900640825a4582379ff87f4c6fbe323771b2bd" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.subst.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorElim, `EqCnstrProof.ctorIdx])
    "3ca950802dc1e29e9891ccc7fb71c2ee69ba74f86d33f4b30b8c9947a5d4760a" "d284d79f24cd80c16d94c63b78abd5c167af46fa79a0d2925a5f459e66bba2f5" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.subst.inj "user constant" .inherited (.inherited [`EqCnstrProof.subst.noConfusion])
    "4512cf13fc77a21ba96b5cc3d0996492ca881d71fcfccdf4d9ed266d70cc6c0e" "5903284eea6147f54c45c26adc68da312015766f595b6921df9e9b1b9197406c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.subst.injEq "user constant" .inherited (.inherited [`EqCnstrProof.subst.inj])
    "84bccd55c06033849f9d7a0fae666c52519845a8795e91bc5e3e598ef6cd556c" "267bafcb44fd09dd3b83d8bc0d401699b3b0518b3e2770e5f45b92e9c75df4ef" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.subst.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "13cf1fe9b9f7f95a43c73410649a58dd6e373e7d66d126c42fca5733e202718b" "bf122a85cf59d6b549b059ab8c2a857cb1ee1db1cbb0b5dc3430330507c2ca53" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ae5bf300edeabe290782f596e980ab4951052c4e212e79e3bb4b8b804ebcdf06" "f6a9babe231dc096dff36b009b226d8da8de9e612922558804a2bdeee9f42818" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "79fe2f58e6ac07c0c2b58f90913402ea5643ec5cdad7addc1851108f1a47f3c9" "07c8b327857c52247e04ed6a2370a3bc192e667f2673ac321ff52c0b3cb2cd40" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dc8c9ff4e0d365971ecec6cfa489b1da5edbd6a71c84a4a873863bbd3fa8db93" "65c853d1bcdfcf0f52481d9adb1c5fc916886788f273408d11fdf3e7bf4c1567" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "936a859cd6fdbfc9a968997a504affd74c22f61f804976b08b94bb0a87d7643f" "9d7f05afdf96adf04d0568c57e344312af8a5fc4929433225b4d8c9d3bc027b3" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.mk.inj "user constant" .inherited (.inherited [`LeCnstr.mk.noConfusion])
    "9c1ebfdab63123eda9350ad8a48e8a0f493e6daeed81f8ccbf63e2abc3f2f87c" "04e8c2ab14dd365b52f7c7be1abbc1ae154064a75ab2ebbdfd9166f9720c86ea" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.mk.injEq "user constant" .inherited (.inherited [`LeCnstr.mk.inj])
    "a4b26e20c501250ab3f6c840c3e9d010fbe0478e8799aef1eacc3e0891048022" "0aa967786641406f916ed0ee9745ee0864ada02ab22cc0b99786819d861efd0c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.mk.noConfusion "user constant" .inherited (.inherited [`LeCnstr.noConfusion])
    "697c1904db5ae157cfd276a111c9342c215b4acdae8be4f447f93196d69db6bb" "84a05eb8b106d5cf6ba9c678948a8cb46b24e6f0ed41cbeb7a4b1e6fa3cbd9f9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.noConfusion "user constant" .inherited (.inherited [`LeCnstr.noConfusionType])
    "f19fd42bfe0add0937351417c754a200f08279f1dad2a41d07c3c16fb206d39b" "8ccb101916054daf7b76a3dbbac7b8c3fbcc0ad82dd4979c3dba7619fd995749" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "8261ef49f3313ced056ac9b1ac4bece5c15b318829ee10ba498d82f09fd97372" "32e4688f96e61da2e42f51a00e7498874f2d693397e3ca4c12dec265c649f2d7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3c71f38c5595978e6023e392572780a65ba7d9b34bdcd657fcc8b82165d5f8c3" "3aa42b6a281c009fff8fea546c3588bae76abee0051cedce961b2a6fcfb040d8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e6ae57b9c8d89dc93a1fab841963905f3691e6a10adbb087cebb24ecf4e63f79" "c64466bfbb951ff69b0b2486d80661198ff01fcdb460455267c696cb371dc025" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "62a88a221a3f970bbb948c4f9c4da334f4b94cb8ef8e0692fd2fd11d0f537e0f" "ad44d38a9bdbbf886be503a74cfe501389dc8d2b25f828486da0dd67f8e4b362" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.bound.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "7b73df5b38576a68104342e0d9828dc84457d471a84085c3edd588413606effd" "71888a056a3573aa09f191991da3418293908779cc567127cbe0303801c52bd5" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.bound.inj "user constant" .inherited (.inherited [`LeCnstrProof.bound.noConfusion])
    "97466a2ecdd49cafa7767ddd2b1f03ad080357ef0a1c9feed94edf7a67e524ff" "db833e60a361302ec933327645ff66bada2c990bc9672325beccd02ee8be6e9e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.bound.injEq "user constant" .inherited (.inherited [`LeCnstrProof.bound.inj])
    "f72d38f95228c1547157ffedce8a09d6270dea943501f6e1df27bd6414eafd92" "3d41a15c27458df49c7b5a2f367a231e053d61f8ab01ed1b25b70b05dbdd5599" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.bound.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "2f8caa76d3b66b85b162eed084774f519fc1e13df80b05bb69a11cafcef227e7" "159fb56f346d85cde4f5e7f97ac699f8569f662d2487f5fe2aa9edd84d76f439" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5f07e30d3ca221ed4cfa6567c20646ce348ea0677b5e6e044f9a16b68defbbd6" "2cf5bf5126a578762dcae80ac0da12e514e0d99c811105f598f7cc7a31a88e50" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "eef819e5b3a1f23419de8344465c75450546960adc656a1d38ab2e97b87ee488" "48e5937f9e9948c2ad7a9016f4b1127eada0f49355eedf5c7958ba339116bcb0" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "91404fbe5acdba843e4ea2006e4c902e8404d9188988b7488a1750ccff0ef42e" "6eedf7ce146d045c89554d2449ed79155f99d7bdf07f54b04088d2ca3d195219" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.combine.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "54390939b87bc88332c7d287ca006577eb9ae6a19740eb4b48a68fc693ae278c" "ad61cc241a22f2e21524650d1afcddb6ce687adb6fb0e441efe86cb8b5d9677a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.combine.inj "user constant" .inherited (.inherited [`LeCnstrProof.combine.noConfusion])
    "8a9fb99ad65c58f3c781adced0ade7f9a17dd92a6c38a59f853611ab38c06dcc" "4fc55bbf98cf53749f6b37716d6294e27d6fdc4dcb0370ea0938273eeb110b9a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.combine.injEq "user constant" .inherited (.inherited [`LeCnstrProof.combine.inj])
    "f9b8dd2fd4adc312be338afadbc6288603310bf64f60afa8f8920ff9e3cfd1b5" "02feb7c0352be6b62c46479c34a17a4809547cbb8a3336d34f2c20ab6aed82a1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.combine.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "f80a170d67ed60e5722ba262f4d13b070c31576adc3a793d89c2693e9c514e37" "db8208effa51d15116199e1824d10a04fb4d7de1c4678b53147f0ef8d0ad2b5d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.combineDivCoeffs.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "83798ddae0af6eede7874946f4ef2e8138bd58174433f38743fb6ddf44d10123" "550b87cfac7885f02d77cb0b8254ec89759fbb7f868caff91c1b96d76dbb42d6" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.combineDivCoeffs.inj "user constant" .inherited (.inherited [`LeCnstrProof.combineDivCoeffs.noConfusion])
    "33e6ba4e5aca8bb52f81cca7af2f80dbe4506b319fa7098f9f063d252c2ae03b" "c679630938ae49df6925fc23470f67a9527d0bedfd953f35217643d6ff1bbe4a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.combineDivCoeffs.injEq "user constant" .inherited (.inherited [`LeCnstrProof.combineDivCoeffs.inj])
    "a60435bf4c5990927d1463a1d8d1d1787071c276fded43c10d5e90cbcd91314f" "a042c717ce095844a400fd78ccc1ea8b1f0c4a24ae48b0a255b44cbf532cacec" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.combineDivCoeffs.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "70480a0e3887577508f105a3f04cab454ef316fcb638c6282b08dd3eaab59a62" "381b46b524860763281015b2f4a29a30787b26b2d862d5c74a46fcfc9e61e7c4" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.commRingNorm.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "1faed749b00608186bbf34a8f10c8e14c12c923a7243cec00ccd4c5260e068cb" "0e2feab50e99ea34380639cbd4c60cf32db8f256c92f814988d5caaa4231ed1c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.commRingNorm.inj "user constant" .inherited (.inherited [`LeCnstrProof.commRingNorm.noConfusion])
    "fcfe3b7021de8ce76450d88774ba950cd6c0a43206c700fa9a949a8862d0daca" "417d63aa7830417c11ee225e0cafdc84527ebf73079059cb8fbe1b47c8834bfa" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.commRingNorm.injEq "user constant" .inherited (.inherited [`LeCnstrProof.commRingNorm.inj])
    "7868e9b7131065d2f0a1c514dcf2c52b0df6a3ac3e27d97399aba73fe43e4af3" "c070a5c746d4a62d604bcf29bc37fa296a9f35ce403aace7719baf4e44440946" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.commRingNorm.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "a243bf74377669c68e029966efe274c80a020676b21e37c4eccb4d1aba2f836c" "b42e1e3324b56448dd4711f65df229c19d75d8ddf8de17c4d74b863b0b313a53" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.cooper.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "e0253821eeceef4d2ff171d7e9f29b96f0a9ac7c744458a663afd6a34da38142" "eabfd2f50520b4f91407235f9c901cea8d394a7ad5854c6c86a9a260dc60a9c9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.cooper.inj "user constant" .inherited (.inherited [`LeCnstrProof.cooper.noConfusion])
    "58c46fb19085a62f04a0696cbed9306f3b51659c7e77758bb07ccd66ef72436f" "7606d6fb04096cd0d12f31efb87200f66a49176497e82cacc01e5297e5566c53" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.cooper.injEq "user constant" .inherited (.inherited [`LeCnstrProof.cooper.inj])
    "fc82ac1343aedc7cb484040c3e27abf7ea5ce2a0c5aa4bca690f5fa6e563229c" "960691bce30ee3bb98c03f83d413f8840e6997bdbedeead3b2a6cd707171b1d3" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.cooper.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "262b453c7eb14f9cd461976e8937668ffd537e5da936820dc10acbc765e5e974" "127f8c08131d4f7c9060e16d1bcd84b774d2772ebbbc057d0b4c18c1f4f9aa47" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.core.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "a565006df049d0b9dce25d3c71f0bd7faf6ee52d85d7db42d8800f47415f3904" "357bb25350e9def4a24816342f5e368e1a201f38d7d72761638cee4fc2f58206" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.core.inj "user constant" .inherited (.inherited [`LeCnstrProof.core.noConfusion])
    "2c7268bafc8740b30cb27dd700a234eda1a60bf37b3b5b19ea23df674321f52f" "17541b34dbd9786303e6718567166a985cdcc5d9a21b6a422166c10c2930dbe0" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.core.injEq "user constant" .inherited (.inherited [`LeCnstrProof.core.inj])
    "3ea6354c9fc6ad183d6f8742fae4d63f8ddde7a2013b97f7e672289f672db1a0" "2a6c1d9f0b55e5380ef8b49c3093afed8abf4990146dca2b92853330fd112f9d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.core.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "7d6887d77c4ee827a6f4f4a7f5d5381f18351e61776d379191c5448632c3582d" "2cb69a445749c298641fcf03c3a4943836a17a15abae85518b61662d1d094d2a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.coreNeg.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "438e4ed5b0611f31729143f41cd42d1003e535c69567601aef159cd43eef7429" "f1e3a3b74eed2bf0b052ffc81bcbea4552d0a03ec408af4c747348d98218ebc1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.coreNeg.inj "user constant" .inherited (.inherited [`LeCnstrProof.coreNeg.noConfusion])
    "96b817dfa3becba3911c8eb1a1c379d8533b381ece1711adf9516ad492c44bb1" "c1a5691ca500e4ff8331a1b4367726908d66068d6a8c8d8a4d44b6ee13a76fe8" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.coreNeg.injEq "user constant" .inherited (.inherited [`LeCnstrProof.coreNeg.inj])
    "05e7725d700cb7d4cf41d676cbba8c035b1a2eeef2f39fa278076bdf028bb557" "e279cee17e5f88a34537930950aade55038173f17f4271348aedde27c99ce214" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.coreNeg.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "c596e00db32e141ae64b08131bd566d80c7aa7edd2295bcb08dacd1649c7b654" "133ba5ca1a4843ff3498d78e4816916adfc8cf5ed4344883a97c881099df8dc7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.coreToInt.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "d0daa5cc7f033d18bea90e066e1581bae73eed33bb4ee72c9e2f7e9669c7c9fa" "153eef8324a92eddd486305d14283afd8d7ed3f6e8a21bec02c768f94c9b34ff" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.coreToInt.inj "user constant" .inherited (.inherited [`LeCnstrProof.coreToInt.noConfusion])
    "67a0a9c55b85af1314f8e26b74f4368410b0e45596aa38b270365b21cf635fa4" "9e5b4e0d3713e178912df0a2b9267793a5a357f949cce705385694adb1497a56" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.coreToInt.injEq "user constant" .inherited (.inherited [`LeCnstrProof.coreToInt.inj])
    "b88f2ee83e68be2bd37931546f645f032cde8dad4938c2c93a677d87cf729db0" "1ee6230c82ab8bcca501783ff87169d82b7aef46736837cceec19072f96b82b9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.coreToInt.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "957d0d39234d1175ef81c4145be40a76c17c3330bbc84a17f4c308ebff459fb2" "7e296fadb5641c91a74ce0e4379ad6c2813c712e35e99c8b58120961a49c55e7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ctorElim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx])
    "f02fa1b3c835f958ebacb6d1c5dfadd4bd19898894dcf0983c25035267bc82be" "a1922d21e86259459225d1a431af1a31a7c43e7e0fddf143a573f9d4dd243bf5" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "b4dad66f992035289db01c68563d751c08c228acdaf9e856cd66b473db702379" "e02ea5c2950148d6d912d8c8fbfc228420074cbc266cc76de0e0e5678034704a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.dec.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "5634e24e2af439138f3d7fc18a4de79490ca043864f2afc0938bb3a2acc4cc90" "5a62dd4cdede82f2d5541a0fbd49b032efb5787050613fb09ed173f1154e5e38" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.dec.inj "user constant" .inherited (.inherited [`LeCnstrProof.dec.noConfusion])
    "fb8e2d9d5f4e21638981d04a48604416fbb7fba0c963fcaee73f7f6f7eefc4c6" "b51e777b47490a4bef2d6b6e1f7816d167d983930f22bf25aec857e636527d9a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.dec.injEq "user constant" .inherited (.inherited [`LeCnstrProof.dec.inj])
    "60bc24c20c342eebe0bc701c61aff9f2ecde72851fba17caba7c0ceff2c8f6a2" "346c8025c1065ede25b0c780aff4d7f2cc2a51fcd1a00e0fe4507b8796972f4e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.dec.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "5075c249ed62fba5f8de54830fdb8114b8c5017be4e58a3b1348613887412e6d" "5bee6b290098484889a6e9f95802bd95e5660c37eb1f4d4c5e736a5141722338" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.divCoeffs.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "bc99d13356b95bf1481518998aca7e2dbcc017c5519d68cb661272187f9d3c4e" "1091c91b111dc36ee571378e3ef43e536dca344baf0e7c1d0fc5ef4bd2774d31" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.divCoeffs.inj "user constant" .inherited (.inherited [`LeCnstrProof.divCoeffs.noConfusion])
    "209ca22d86d43b895a677dd73a9f3cf7910b4002a465f55b14f6930c798f6771" "e4e30e6aab738004023acdf9d1a11d69d749ba18c4f3af3b2c89150d5b55fc38" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.divCoeffs.injEq "user constant" .inherited (.inherited [`LeCnstrProof.divCoeffs.inj])
    "38f15e7ed5d7822e296e8d88f86f77e46903bcf04fac8be00abfcd1a38e5d128" "b12c434bf122979f5b0ceebf4f3eab950cf4b089a122a4346fe3cf2b5874544c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.divCoeffs.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "06ceaa14356da8a17a5764cc16c6088f31da2be0ed19ff878db0f037f2e7ad59" "30a785a6e302bff39e33ec05b72627489fe110cc075174d8d0af104d52a16c29" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.dvdTight.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "749651f2e208fb78c0eb46ddd4518d4f0a3590e97eba2c9632a0c6ca349b65a8" "424be60c8d9347765bba22ae22c177e7fac40f0581d635418c74ed76ec50abff" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.dvdTight.inj "user constant" .inherited (.inherited [`LeCnstrProof.dvdTight.noConfusion])
    "559c25b9e4002ea11d8ed2b23ab43d72dd0ca76cd155a52fa2ef4cd4125d9c6a" "dade45afe9f90c13fdaa7afb2c7a5633785aefa58727fc8bb3a1767ddb1fd604" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.dvdTight.injEq "user constant" .inherited (.inherited [`LeCnstrProof.dvdTight.inj])
    "39ce8f21353c3b912b2ab97188dd4b7a9dce66a0899dc3e58d5d4753c060c521" "f8f145e4cf631b17ab59fa64513c7cd96cf0062548deb6fa86ef0db16934d7d1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.dvdTight.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "36b7c27c0f685c85437d9f6b193d377a31886eb51546c542c16f27e11f8cc8a6" "675be4640484b697cf7e9f222ebc739abfe072e739d111afb4c271e3c0a8ec18" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.negDvdTight.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "fd7734b97f77dbd0826068a0151246c861cb57256c70720c0d7371b6c530cc77" "0cd4025876cbe0d77d57a46d0ade1c9a6421927367277b91a4459916b5ba982e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.negDvdTight.inj "user constant" .inherited (.inherited [`LeCnstrProof.negDvdTight.noConfusion])
    "9d3b3a0a208aafd3d99dc4a9778dc689b2d6298c3e03ae43821df3a89b6d8129" "b5dd5ac6951ce4451dde1743564cad6ce4aa5e396a4e6fdedecec92404b94761" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.negDvdTight.injEq "user constant" .inherited (.inherited [`LeCnstrProof.negDvdTight.inj])
    "e8d24105ede566a7d512c509085f8ca0184ba15c464e6c236ce562ac4a096a07" "0a528f5c276db8ffdf80023c330e9446fd2a5c1b5d74a2b3b66046ca5191f2f9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.negDvdTight.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "812f6c1b1bf7d306020a0e5011d8b9a5bceeac08fa3c8d35172967cad3129572" "128787928fa3f7f341608b1582fb06121d578ac11c7c666c2f825f6bfa171287" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusionType])
    "294733cc6dc3cf5f4c06ee21ad8cdcbd80561572265dd3bab52c1cb41b2531f4" "176c7dd1bfc906b96fa3826db15a0eeab078b296ba35a92f5865c1e8a7d48c88" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.noConfusionType "user constant" .inherited (.inherited [`LeCnstrProof.commRingNorm.elim, `LeCnstrProof.dec.elim, `LeCnstrProof.dvdTight.elim, `LeCnstrProof.norm.elim, `LeCnstrProof.ctorIdx, `LeCnstrProof.cooper.elim, `LeCnstrProof.reorder.elim, `LeCnstrProof.subst.elim, `LeCnstrProof.bound.elim, `LeCnstrProof.combine.elim, `LeCnstrProof.coreToInt.elim, `LeCnstrProof.ofLeDiseq.elim, `LeCnstrProof.ofNatNonneg.elim, `LeCnstrProof.coreNeg.elim, `LeCnstrProof.combineDivCoeffs.elim, `LeCnstrProof.divCoeffs.elim, `LeCnstrProof.ofDiseqSplit.elim, `LeCnstrProof.core.elim, `LeCnstrProof.negDvdTight.elim])
    "7500bbd01dd486759ce7d514a2aff3cf0a6bcd899ef06ca022d46d6dda5041cb" "5af34d59fa58ee77b443297cc7a209b47e11bb06f1b1a35d42dfc10f97d75893" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.norm.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "f375055ead1ec639d54f614d75daa36bbd0084a7b0f7e6a9ccc03a436ac3ece5" "2e1803e14ecb6ec84c797130f6f5d2744f5e1a44970915bb806eb60ab247abcc" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.norm.inj "user constant" .inherited (.inherited [`LeCnstrProof.norm.noConfusion])
    "d7e2de4cb2a9b86fae373f994739e5418ebaef0814143201b1a524a75c5d5661" "31ad09ad4f1582a19915d4dee32660ab8b4e200edf558f6d649c2e0386597cac" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.norm.injEq "user constant" .inherited (.inherited [`LeCnstrProof.norm.inj])
    "a1738ebb7c24b46d7c8475515f58babf52196e1f51615281d5ce55edabe0d7ab" "6f561296e15eea6a0908b6627962ac6c576a6c470c493b1f7c27968aa76ec1ad" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.norm.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "0963371d0f14716a219e0d35193ee35d068b40960955bad9493175483e2dc70c" "f4d2aeaffb8eba721be7cb0b03fd302b2f20dcbdc3e9cbcb163d0bd7b7efe5eb" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ofDiseqSplit.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "d6836d8aff26cf181ea352e0bbc07a1d50ae023579c86e642dc3cbdeea841859" "f60e4a544b5a2a481daa5092230f3c6ed61deb365190476e5805a6806e54b4b5" ""
]

/-- Entries 1600 to 1799. -/
def part8 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ofDiseqSplit.inj "user constant" .inherited (.inherited [`LeCnstrProof.ofDiseqSplit.noConfusion])
    "512dc2493727dcb59f6228941c8b9ece9f040b58c3c438da7610d4631313b6d2" "92856e814485a91d7b6a7366ef8294b3328c47cdfdde3b8ed04c9d74712b635d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ofDiseqSplit.injEq "user constant" .inherited (.inherited [`LeCnstrProof.ofDiseqSplit.inj])
    "24dca174d8b55ebcbaad6fa4357584fb12b3a443cad215472d6c6b6d27076716" "62de045a46ae9f3a4e4b3c5d3a55b57840d9ae02aa38a2c6990ddc3fa9672f87" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ofDiseqSplit.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "308ac48c5e3be5fa7b2901d91fe0b69f1774e406460e69e980034749134365c3" "a11f002fbf0b6d559dcba5f7d230792a344f254c956815b565b6e29983c5ed37" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ofLeDiseq.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "9760b1dc5cc5c5d1f8be8a95b951077e0bfa8a4cdd56d0d79866e311ac36b8e1" "8987d90ad304145932a7e4d46ddc248122fde46f6f3cb1d0da1b9c43cb468edc" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ofLeDiseq.inj "user constant" .inherited (.inherited [`LeCnstrProof.ofLeDiseq.noConfusion])
    "ecc5dd5217a91b37c847c8a2c71096a33acebb9aaca963a749e3501e120cc259" "5d9c3cd5d271b6a57cf2670828f2bab56d3c41fe111b66e8e205b66385f9fc35" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ofLeDiseq.injEq "user constant" .inherited (.inherited [`LeCnstrProof.ofLeDiseq.inj])
    "d4798868f89f3568ec22b388df39fa1f3168487c5b1607226d46508af68ba7b5" "3562687570a979e37395c41598119bfbc6ee349f77f428f89f3db0f7ff21338b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ofLeDiseq.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "178b777db77add50cef5d2b693b35221827ad67207708ddc8f4ef2fa54b4ac55" "fa38607c2e9669618c853fab368686646ad17bebb5c35740ff3dbf5666090b0e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ofNatNonneg.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "e27f94b00b6ce83e852ef39374cda785d8112af41242ff073db9658e3b865700" "7ac94edb5ea78fd1e4b48e313b3d56fd9ad3f3eae75853f2e357b860765173ad" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ofNatNonneg.inj "user constant" .inherited (.inherited [`LeCnstrProof.ofNatNonneg.noConfusion])
    "d0fd60e4c70744ac72b6b2782e4d6f25f0164f34e0fe260f17cedf0c7e001970" "4bea9a88b91d3e4a7a6eef3bfbefc63450c12089b2d13eb2436e28014f289b45" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ofNatNonneg.injEq "user constant" .inherited (.inherited [`LeCnstrProof.ofNatNonneg.inj])
    "6031ac2223a89b30307d81447cee97143327842776eb3416eef54f5563f201ed" "f4a01fb384aed133798a22156489445edb69c2fc01267154f1ad5a1cf8fac89b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.ofNatNonneg.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "2003d87729aea26ed080e980bac589350a011ea004578a6dd21179190b118396" "34db86e9dbc98dd9fc8dbff177028bcf125e26bd17e454bc6ab7cc11bdbefddd" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "abf652066c9c21a5210f25b0e809e46ae54a8e0f5c1596b3e1ff2a2bd43b84a3" "343e61c7e9f3a1dcef42c55cb01e11dd62d98fc67e8c2e4497deeda8ba846965" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "255ca996c2364a0e8803608738617692020138dea759e00a2a712a9029c26ed1" "5227e4589297bcab8f9111ae638214c24d7f2d59f027d7e82b3852bb062dca08" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.reorder.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "dbca484370bb165bad683001e7204be16510154b3e3f75055dd3f61a6942bf50" "f80283ddb6ad3b8fa085b73fcffe13bf13eb75d0c3ef9e301c1a3eec65b70c98" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.reorder.inj "user constant" .inherited (.inherited [`LeCnstrProof.reorder.noConfusion])
    "06a7dd20dd7292b5bfa6401239e7dd92493c71bb07f4c744aadb7b1a7d436ae5" "6c1ab701347b4b558d9064e10fc563d7ea762e59b2767658afb4db0bbde9b320" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.reorder.injEq "user constant" .inherited (.inherited [`LeCnstrProof.reorder.inj])
    "325e3c7ffc03f85821a716e6752388118b640bc992f08ee80f0f5129ad070360" "9c220240fda9342943f90b54d11330a4e84814ea748051592dd49fec791efdc2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.reorder.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "054148552fcf13b8a2cefa5e4dbcfa7d3b78ede79d16aba756545ba446709e14" "14bd1b1e4156a7f6e8035ed0485e46a50532b49b7644861ce4d5aff06c3689ff" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.subst.elim "user constant" .inherited (.inherited [`LeCnstrProof.ctorIdx, `LeCnstrProof.ctorElim])
    "fffca43055219749eb094efead6c81df4c2ae86fac01377801f06af56201e605" "19cb57f9b1d5679c21c855cd8e0c16c36ceab9f5128d8eb8e5c15cfd55991088" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.subst.inj "user constant" .inherited (.inherited [`LeCnstrProof.subst.noConfusion])
    "982e58a5549f11961d7b3332108025585c5c3a71766081a2a8451765d725143e" "edc9bc9f92c69d651d17871604e4b0f43555d0aa8a667d7d002dc27e6268bf11" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.subst.injEq "user constant" .inherited (.inherited [`LeCnstrProof.subst.inj])
    "001b59d0a00390aabebdf9d6fb0a388476c8897e070ef6bbd7633c02eeb0bfb0" "e80071d49ed85df7566332825b77d0c28f7841a83e66256109583ea81b67c0f5" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.subst.noConfusion "user constant" .inherited (.inherited [`LeCnstrProof.noConfusion])
    "dcb751d1110c0ef5037c64b001354302b777184fe5eb92858ba08f9c52f19321" "217710d95afd58012162e983e43ad87eaacebde6872735bbe9b29411c4f095fb" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e35a37ebb6a0329d24019dc5812df34d604d58caa296ae02f2ecf866f172cc5e" "e420dc3c298ea3454f1fc065e750217ed05680cfac4583241f18a76f841598fd" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ff52ea3466eac42a8a6a66b6cb7c835a4fba5b65e97f9cb786434d3d8935b7e2" "c9f9bf650e157b3d6b6fe5a89de6cfd30c06b6942e9e284c044898624c59a6c6" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0e95f06b9ba7c91830c16da14db0ada6a156fbf377e30b38c342673094a5464f" "9fa7ab20301e55ba12280548c460edbc43fb418affe0d96eb5efae008f5e1aaf" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e91f8a6b8084c8fe09bb15c106a5f0cbf82fa573826c75875fafe97ee68c886f" "d4de424b5a15b597802b77a2576a6f8d978e1d53017b895d84a59265ce7fb3a8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.cooper.elim "user constant" .inherited (.inherited [`UnsatProof.ctorIdx, `UnsatProof.ctorElim])
    "224657a8206b681983e611023399297fe5a53052550b5c74fec0a9bcc179d974" "8d137eebe55c168bee50936500d4372dc94677b316fc5ef110f5880a9a64b3ed" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.cooper.inj "user constant" .inherited (.inherited [`UnsatProof.cooper.noConfusion])
    "ed96fb30fc29e2c43fe489556d986190fb0696aae15fad55b60b503cf82a9d07" "3a982675109a88a8b581dc2f17df019b9e1083097803d13f374021dbd6ab9af2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.cooper.injEq "user constant" .inherited (.inherited [`UnsatProof.cooper.inj])
    "f9cc7aa1faed096d925edf612b840278904b92dcbddcaea762ab1b425beaaab8" "e0601dc5b65f20966aaaa166624b367e4658af307bf160f84b0a3edfec1202bc" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.cooper.noConfusion "user constant" .inherited (.inherited [`UnsatProof.noConfusion])
    "1cf39d9ac83c38bcada017b02fb4c60932a2e440dc1eea765c0e6ce604eeba06" "fb194596cc5c2bfe7f465c303fccc36348c99674056ad65747fd1150bf5b6383" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.ctorElim "user constant" .inherited (.inherited [`UnsatProof.ctorIdx])
    "30b0f94df54b9d4dd694f455d68339b8663bde2ce52f7642b2a2410d5eed11fc" "75d2cbec2bb65c5a949c3af2a94a8c1e9323321d63f084ea90f645a649cf2ccd" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "091c818f590c1103b0855c9e66551eec11a816f04c72dd199987d29e99f4abe0" "deaac144df3c5e9d01ab9bfe9024882ca2fcea5f182616badb53e4d1a1d5aacb" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.diseq.elim "user constant" .inherited (.inherited [`UnsatProof.ctorIdx, `UnsatProof.ctorElim])
    "203ec39abfbea54d588301b749d8cb5a2da6624b7ffecaf44869c87bb614e3b4" "7ccc4f84394a91bd6691b0de13ca517fb802f59c5afb3694618cdeba8b9a70ec" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.diseq.inj "user constant" .inherited (.inherited [`UnsatProof.diseq.noConfusion])
    "6e82d7d3802cc4dca9c14d11296c18ea96f34b0f41871966872174ea530a5dc6" "bdfc3b6b8feb43d7d9d5fdb12766f269ef5b2babcc72f52e156db2a5eb3f6d72" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.diseq.injEq "user constant" .inherited (.inherited [`UnsatProof.diseq.inj])
    "daa4292b61186d01766ba5c737e8a79e594f951214941fbb737560e6353e861f" "7a87290970736a925692fb3de0e1b2996e5d86bfbf9f851723895018be891b58" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.diseq.noConfusion "user constant" .inherited (.inherited [`UnsatProof.noConfusion])
    "c659eb3c99bbbcdcddb42c365b4e4cc610085e68689d2c59e1eb38f5da07137c" "ef37f90ab84f8c3a8dffd7f32da0b44991a381d3e16421a4799a4cd04f3b838c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.dvd.elim "user constant" .inherited (.inherited [`UnsatProof.ctorIdx, `UnsatProof.ctorElim])
    "b40cb794e2298a5a5efcde6c603b32d52c6acc43563ce3d92ed1999e1bc49bdd" "a69d80220ad928a65db5f39d26d2793a805a866a33abd132b50e2b9c405f78ef" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.dvd.inj "user constant" .inherited (.inherited [`UnsatProof.dvd.noConfusion])
    "4ecbbf3d22ed2cb5404095b3c56179132bcec8a6c7fa07258c2090a56906a25c" "1ff231d98a3e040ee69704180899dd6137043cdaac91aa01b09eb8ae6c220513" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.dvd.injEq "user constant" .inherited (.inherited [`UnsatProof.dvd.inj])
    "8d524cc62676a672b7ef96c226398eaf394e0d3296dde70e660a4b20c870d16e" "a00d297b6d0f2b1f032a7e889adff006c905cde40dd3cd1aefbb8840612cebdf" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.dvd.noConfusion "user constant" .inherited (.inherited [`UnsatProof.noConfusion])
    "ca840271ad02f19883bc01dde9bd8c68641de391203b3212099fe0c104f612c6" "60219bba9abf73cce906ec97c0d59f5db11ddfbb9beb4f7574dd23c47f044934" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.eq.elim "user constant" .inherited (.inherited [`UnsatProof.ctorIdx, `UnsatProof.ctorElim])
    "a3256e404c22600694f5011bf451385dfc170e20a4299605708f209e23a0fe93" "d17f3114023c03052cb5cfd8fb4694dff3ead6a99da8c349846d79925b6fec73" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.eq.inj "user constant" .inherited (.inherited [`UnsatProof.eq.noConfusion])
    "536ee59ecdeb5e3ac4602d5f58e84dcb05a94214847d2bc0db13ec957462a0a5" "97116d2e2bf09ccb7a3d5ba3701bcbf30e075dfff198754f0b0ebe253c167c21" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.eq.injEq "user constant" .inherited (.inherited [`UnsatProof.eq.inj])
    "e3488203dc1aea825a0202d2ff5a62e9def3652e3262a0babaa0192d08a65cc0" "1be9dd95e4925d3a14364d4bcbf5d11bf8b0a472b15b843dc663d9e156655a96" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.eq.noConfusion "user constant" .inherited (.inherited [`UnsatProof.noConfusion])
    "8886be17e33369157d61c5220a8448f455c7aabf61a7a8edd0352ea33d2bef8e" "cf3440088e92b888583325969a8cd4e54e30de6dee8caad3cb0ad84178449caf" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.le.elim "user constant" .inherited (.inherited [`UnsatProof.ctorIdx, `UnsatProof.ctorElim])
    "741e28e800151be56440ab79e2ef0c1b70b75d9ead4757fbd5ff9fb47707bd7f" "5a77f2341fb345d8c9d4b4d889f35f3d21e08c50df7fdf5bbb75232b13047c34" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.le.inj "user constant" .inherited (.inherited [`UnsatProof.le.noConfusion])
    "60a5280f37d19a554d3bf1257d6f33e1acc25b7f51079965c3b839319a8c7f52" "819b0890e2a80879f587a9f090211fef629d88fd31fd32e5b0d5f276f313e615" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.le.injEq "user constant" .inherited (.inherited [`UnsatProof.le.inj])
    "f5832b0705ed92e998cd861faa14f1e55c4d73afb39f2af8a44dc8124fbfc107" "f71f79a361ad81d6106b77aa162ad903cfc901e04ec8dfb79d52b68d6212891d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.le.noConfusion "user constant" .inherited (.inherited [`UnsatProof.noConfusion])
    "5f7cd6e855fa14eb76904e1dbc7e18092142e8bd8d195ba987d27f308d12b262" "0ad33a6a46f03a503a60350358782f15be003a95dfe494a5fb0fb705583d4385" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.noConfusion "user constant" .inherited (.inherited [`UnsatProof.noConfusionType])
    "185474832af3c82ecf952566e402110c190af1d3b50f6b11d64bba6a5f6cfa39" "10994e1709e84b3166bc187875ba8497c7eb55e812bdfbf71009c0c0103684f0" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.noConfusionType "user constant" .inherited (.inherited [`UnsatProof.cooper.elim, `UnsatProof.dvd.elim, `UnsatProof.le.elim, `UnsatProof.eq.elim, `UnsatProof.diseq.elim, `UnsatProof.ctorIdx])
    "a6fbfac4230aa49485320ef6e2ef94b963e52032e8a704c9869888ee956a715e" "3d231ec4d2b6e8f0751f3183eddb72b9b719254fcda0b970de3e9f94d9075e4e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e1b49f51e12a215d5416dbc1d48b45425080b97430bf36e1ec07c3e783f9ae34" "2030131c7a438172ecc23809936f22ab26545083e51b34a3b645a58c5a7dee3e" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d69e6440907a54695f07b081350a18d53ed8ba143ed58df17cedcb838cbec2a0" "0cdb34f88087601f72ef14e4d01f52b37ac899a74a2142151a45cd80d6ef42ea" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "85a24f55398a917aee85d4a010268491ccdd46c1c6c910b170a42b4b498ca41e" "fc84045f6f2c20cfcf074e0fecfc547439810c181e1c79f364bf55b7b31c33e4" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr._sizeOf_2 "sizeOf family" .o11aPending (.root false true false)
    "e2a92f924f397ee61827e23616fd2e88e68658d4b276dc9934eefbc27bab7535" "ef3e62ae2cb6743dd4356e095b85c98650195291f8c021f892bb11412594661a" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr._sizeOf_inst "sizeOf family" .o11aPending (.root false true false)
    "a68dfd8ad37a0d7353c831effb9c40edcb120a99e3ed2832e29aedda3c2d11c1" "938e11308f9983cfd6b6f26b3ad3be5c16c08958cac568465667563c26306ea2" "value.@1.λ.body.fn" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "767a78bfd0d31e8f4dca91a442d33430ad8c9dd4b96e0856aa348d41c75082db" "3dd9a4d1621440c44ace4ba0efc1f1b4ba42bf1d69bea4281b7427a227a1ea8a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dfbf34e3a21897de93415ce74d53b1048a9f6cfc8081eaa5392aeae6490e93e6" "6df63b5569052b511a3fbacb9a1ce705162e93bc1381a82d0d389f13a48e02e0" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d702ca348ec82c3cd8a702bb8e402de358ea76f34581912d20bbe1e2d217ffbc" "a4764bc7ee1ef3442a6b98a43d74f6b9c06e15e802a6cb35a75556340fd64c7b" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "f2460b7d68d84b2ff64c503aae835bbcbf3c4fd1664e57747bdbffc3b35d1d27" "7dfbea026720a178d97edd529d1cf2e1cca832e76097645eec163b7af66ef204" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.mk.inj "user constant" .inherited (.inherited [`DiseqCnstr.mk.noConfusion])
    "a099bab77113041afea271ceca84fc73d5a7a87a2db2c04c9dcad57067986dd8" "8375aca9fe13cc3f6e83bf8fa18aa660591811f0d20125c8848cfc2761ab1dfc" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.mk.injEq "user constant" .inherited (.inherited [`DiseqCnstr.mk.inj])
    "4d6e880fe59cf688a6782b42a5e4fbf9237e67eebcb6b93c10c712f2e68748d6" "0a0e247325099dc76532cce7813794e725c5558a435a98b61f50dc03e06ce04a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.mk.noConfusion "user constant" .inherited (.inherited [`DiseqCnstr.noConfusion])
    "524a8bab72a9e82ec078a4af6df93835c150444e3ff4c2e50da3337151ee166f" "d0dd1415cba9dd897a57687804fed35542511f8e69ac49d012f8a8f09b2d3856" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.mk.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstr._sizeOf_inst, `DiseqCnstrProof._sizeOf_inst])
    "078ebac4ce215824bf4d84f657ee911a63ce9f4d48b014c1e9892dea048d93d9" "ca0d366d5993086983fa21afb0ab149e197d8629fd1929470b1447816135d511" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.noConfusion "user constant" .inherited (.inherited [`DiseqCnstr.noConfusionType])
    "8fa0d777eebf2eef3a2d398e4c401bd2d4ee77e3e82ebe3c20a1c291caa837cc" "2e57275be50b81641b903efdead2f0f6bebdc02b064d753408f54f381f463498" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "c7274d0b433bbc3f48e3f0be58f93ff769726fc5aa873cd95bb96a8438210472" "640d13f956c2afaef84d6db92cb9a0490b3f87f320f080aca4e0b11eed7fd692" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "de41580be1bcfbcba9dad929960fa2597a0137ebfd9069f5d90bf6384675c56e" "9ce9d1e69fb16cc61a4c404d5606c4502c571afda532ee17163278688dc2931e" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "9deea21239de4357d1b95f9fd6c7b57fc6e24206749e71a956455bf4c4028ab9" "5ed957a8bc64702a8694661487bde2ff9390c6019ac202df6d748fc9a7fad1d6" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof._sizeOf_inst "sizeOf family" .o11aPending (.root false true false)
    "6e544b31bccfa51cc310fc586f38ed01db34a47fa05118d1cc9341ffc1f8728b" "ed1253eb46eee6440440daecab5082df52332f25da65893a3c6adaf3f0d7c5da" "value.@1.λ.body.fn" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a6c3871f4aeccd4f83f273d6865cfcb8347f8eea07303c600595949d1426b555" "2efa60b590d236572b0073a9f6360c4d77e18fd807b19824eac7dc5fd789c7dd" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5c544d1d3e938e54cfde5b23954ca81f0f3c5d9bfd3f4087a8a53af903d2c2f9" "e27cb9c35da6b83777a2270569ee3583fa56919b3283c832337c04107d4adf5a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "87767078c157f3869cae4cda776e6a3005ea9328a981af59d218cfbc7e1685b4" "8608c061ae2f1b02b311f574a2a8a33dd3a4377c7672a77a2d2794cce11e61d5" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "191ab7f135b63d6e256e86b7d1add71a1174809e22a97687c34dea4535f046c3" "6526eed039f32a244c037afccf215b7a3da38e28211a356470d9a0a9847ddc2c" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.core.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorElim, `DiseqCnstrProof.ctorIdx])
    "ec01b12bc7f49edc59913658844431e8faa6370728393090b8231f1f565ee340" "7f5ac0a1f2f8fac657ffa2f2691bda502df0013c3426443041778eb4a846489a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.core.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.core.noConfusion])
    "c88d5858ff6c213c350d1de5390de3db8a3f85daae82e35de860ae67e7bee7ea" "dc31bf3caf36d70f8874cce0da5f1f39732650870ce8530c305759ddd78f9a0f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.core.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.core.inj])
    "ec5fbed1fab45d33f9c581357c9c89c013ea840309c20c81664cdfc7be0ea0c9" "f99625e91c0dd77c59c437ccb58a98308c0da55db9db7481f48615e878bd0444" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.core.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "ace50c2b9b5c23853814e69fdc66af7373b91e79b167b92f5fcef3b2b3c29023" "3d9f29b58401bbc00793020ae5502b5e70aaa56c1648d20fc5c2256b0d2631a0" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.core.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstrProof._sizeOf_inst])
    "b85f2224ce8fdb1e90db7de74051355afe8a230ad0fe74dd3e509058b7d59265" "78abeb13d12c4c38b19107239d52310aa8216f6dc7131dbf67442f3c4985e32e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.coreOfNat.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorElim, `DiseqCnstrProof.ctorIdx])
    "572e060f8401c9c2f48a0c1995a544c48eb919278dafdfe481b198c7a8bebc56" "08d3b4cef849180eaf8ac579eb9b855f7754c1556ce3325ce0fb820a5fb115bb" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.coreOfNat.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.coreOfNat.noConfusion])
    "cd6feaa330da870daa2ded6fffa429af520169e9e5957c088b37727201271984" "99d667a7458a317b64b1683749b9d3d6d30aca130b751a624f900febba503bb6" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.coreOfNat.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.coreOfNat.inj])
    "5d8d0073acdc55d55e15110f9d68bc3704b6d7769890b16ded2afcb8d098a8fb" "4fc7c2730d0ab9e95c02e4214cc79430131c037a8f3176522ed34cd7848ff88a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.coreOfNat.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "0b76b760e57053992ea3e9b77b378208f9c7a0fec5e0f96b9845dcdf34183b50" "6973241e93078a80697fda007f889c12124ec3841979d475e9bed298033370c9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.coreOfNat.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstrProof._sizeOf_inst])
    "90deab7b8ec8624dddd1df088de74ed6753d9fbecd48ad87b6e9e1648b8a5e89" "460602d8e7c4c34e6dc832e6931c369f0bf139397814b2cadae78e3c565a4e69" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.ctorElim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorIdx])
    "666c38d1a5cba9de0598f839d43e78c2c13b78868281168f42173ab950570391" "9879894e7c5a68d812a383ee7d53ee2d7a643f4e8e8e308006bc9478e73f566d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "d709f3cce2f55ee1afd98395d0f525ea60fb72f2f923f0196125ef6c90a14deb" "516096b625153ac88bf988131846c960c4e4d1215c8f3f3d3f16c8875842ca02" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.neg.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorElim, `DiseqCnstrProof.ctorIdx])
    "ac587d67af137cc26f5e2958ed800bc0a4d7190758abddb5cd81055bd1b6d88f" "2a8cd5344f582146320ffe2628b886092d6a9435ce719e8013a263a6c0f46cfb" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.neg.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.neg.noConfusion])
    "41a0f8b251664c8f64994cceb93ed6871242fbd3c325a5e2e7a75e3c515fe933" "e1476bf39e3c10387ce8208902719bb6b052840cc66570b6757fe6d768ae4904" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.neg.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.neg.inj])
    "e161d0f19674a1eab135827ca63fc5428bdc3131466a71dd97413198e51db5fe" "58fc408ea813601cb27400c7c30a66792b50eb7d7b3c46dd8d87bccef4eeb5ff" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.neg.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "c18bf0d6de7eb8b8a8cd969d87207143390edc744cf6e79deaa0bb5e4c478787" "a090ee377d63bdb0cca3833191684b29cbc145a2c4661735b38f5146526f5c7b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.neg.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstr._sizeOf_inst, `DiseqCnstrProof._sizeOf_inst])
    "7d1085991126f6feed29521796230238703df6434cb4dbe5b55f366298221e53" "9c8b52355f9f99b0811a2d5cae8a3db1b5bb1028507b3423c1d88d42bc6c610f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusionType])
    "4ac985bdc3b40bbac08916fc6b6bb7e25b0f09b9af6df1df4129de7647cc7e6e" "eacf6c744a5340414c0df4d8995b3480a1a8826074fe8ffcb0795d4fadb23bdd" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.noConfusionType "user constant" .inherited (.inherited [`DiseqCnstrProof.oneNeZero.elim, `DiseqCnstrProof.subst.elim, `DiseqCnstrProof.neg.elim, `DiseqCnstrProof.subst1.elim, `DiseqCnstrProof.core.elim, `DiseqCnstrProof.coreOfNat.elim, `DiseqCnstrProof.ctorIdx, `DiseqCnstrProof.ring.elim])
    "28eaf28547b30661c12bea1cf30e2eea27a5673a87e3e053c4eab19e358d1b23" "68f020771709bba6ce7cd0f8734bf4f97d315a4440f212195b733909e8c5543f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.oneNeZero.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorElim, `DiseqCnstrProof.ctorIdx])
    "c2262753aa2c7fc134276dfcd54a2f1b0a45d29369802b50984b28931adfc2f7" "e73ee231c00f3d7ac80b3c1efb995f58ec89557bc07b5204746bbf486c12b09d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.oneNeZero.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstrProof._sizeOf_inst])
    "c1b7f56c7036d87c4688486af4d27ccdf403beacbf4e836aa9b7ea881c12591d" "9951d7880c0fd865c35b0c0443cd6beddc6c7711560d6fa8f0fdd0d08d399723" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8fcd86d734867a58a6f5ba3485949ef43ce420b807a489ef957678bb7f767045" "69b4ab708e01e0bb41581133956c97469ef444f0232fd55bae9b2f1693d42151" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3790a45d2c5493ef6300397d842682a2c1bb5539dcf4e191bc639d34a454d4be" "ae56f9710b03f3b0ceab6c55e8eb68f323a52935dbd2c29c536728870b8ab3ed" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.ring.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorElim, `DiseqCnstrProof.ctorIdx])
    "a8c7ea6ecb634b74dcb55578e5e43f47b56df53e9fd46604949da68ca5a458fe" "e4042c772bca784a1b105341a207a39fd2427c66abf8a6fbdf030ca9ebddb1c7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.ring.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.ring.noConfusion])
    "cda507472a2edc882871e71c6f4394270d09ce329f7d8c80496fd23b2065e3bb" "9477bf775e22291c4f4656cdd9d79715c56b9b5bb7ef034d212023ae5d0a7dc2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.ring.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.ring.inj])
    "d9ba191419c36b017bde05f1782f0aa85dbcac3637d6ac0f7211d432ca8fc279" "09dfbcd9c6452609fc3172215f4eb4ee43be8c7847b0545931a8386fa8e44946" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.ring.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "7070fc769ee401337d301daa8c865d94f05d01ab56d5a2573fa8249f58824c6c" "9b9a79731070e7884c8a090bc25dc967422aa82321904146eddb05def9e641d7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.ring.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstrProof._sizeOf_inst])
    "9f4deadfded52ac4e0eabcc5245b97b9552d3f6710121438e52a4221b12a387a" "1260e1c405d9efe32d2378268c2b7378715e0a8038522abfc8a7d2ab7c1b6942" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorElim, `DiseqCnstrProof.ctorIdx])
    "ec4b7511698794bd5f6013224f1669add2b4396df4b77e585f092402fd4dc67a" "83d0e6b4788b356f745e673d2e3824c21b220fc142cb362bfcbdd0f35d05d9bd" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.subst.noConfusion])
    "9c6e1cb7c7865aa6b34ad6ceb1cfe7dac71b052d7e69fa73f185be979159ca31" "ed83c79f2c545d94d8608a1ea1f4efeb10ab3835068ed0f0ab91963ec8a33304" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.subst.inj])
    "1b3338988d0e3a9bfe3bfc0a211ea97bd289cdd12cfc49b5bb2497bf056c16df" "4581088d3f7cee8432e2762d065dbebdde5e699401ab6981165763153b5b9b9c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "0c6276ce5ec27d08c77f9b34eea2cc32f4125ac63102e81f4f1e86c914813b2c" "3b330b73406e6e370c59d5bd99b1215ae29741f82af6cf371a8e06c44a026989" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstr._sizeOf_inst, `DiseqCnstrProof._sizeOf_inst])
    "011aaf3cb0725ee66afc6d5b53e7782008e8ea675fd94feef58ae2d685d3cee0" "20c28b50ac338547beaab9de4702dedfb0474c8d7bfc005eeff9a59419971190" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst1.elim "user constant" .inherited (.inherited [`DiseqCnstrProof.ctorElim, `DiseqCnstrProof.ctorIdx])
    "f122a89956b51dd9f664d5083afc71ccf940dca914acb1a156345af4c76fa972" "36d99862ae98c9ba2cfb41a4af99f6e5d4906e620923bcaf7ea44003c59aa094" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst1.inj "user constant" .inherited (.inherited [`DiseqCnstrProof.subst1.noConfusion])
    "f4d49c67b5e65a23f1263074b2434a133d4418a47360e27da48d4524ef7532fc" "1a4013c62e1bf7281f5ace561fdbbd52ae65845d9ba2de26163e16dca27f625a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst1.injEq "user constant" .inherited (.inherited [`DiseqCnstrProof.subst1.inj])
    "25ca5ce7708beca0a2825402f1936a4b7239685d233619bd2474401b39d731cf" "775d2d57277fd8d5eae1e1551d33a54e4a61b244658f75854c29bdb8c7595482" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst1.noConfusion "user constant" .inherited (.inherited [`DiseqCnstrProof.noConfusion])
    "5c59eef8b64a6240ac6d10e7df17f39aeb6fbb1ebdb8dcfbeac8c9ca534eaecf" "5489dcdc71ca4074994a38b9cbfafda1ddd670226549679828287a9b12490f27" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst1.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstr._sizeOf_inst, `DiseqCnstrProof._sizeOf_inst])
    "c328caba9b28bc991619d28898951e676cc9bfc2d86dd1218af90c8003d99d42" "91cbd0bf4f4a107133abf231028c1e893b3dce7afe5be99ebae49df82dbb69b1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8d0514132628bc48ee7ecfb3336cecd8f76398d475ace232520fc482a25cde0b" "eae37b6b1534d392e90b8e5026a68a2fed91350a91b918dce737ca2e87ac4291" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3b5e0950ec8ac612426551a7f9ca5adbaaf406c1c4186e850436bdbb69407fa7" "a332515bf1d63c7187f7c1d4cb61c9e80dbc34307242325919ebade97f365c98" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "52610ea68f84e3c3e36df3a3344021ad40d7ea93831bb7971e07b566f58381eb" "72ec487b37519501ddd6aa2e1c74b9ef11784a047eb6d13235e285790e89179a" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fc985528b9f65c1c737c5dec3c3cefdb75f3e7a1dcdace2e56165d55ebf80bbd" "c415808bbacb3bbd4a9cc02abe4d0fcab8e67c2beec8bafe0df1c8e7ad432c08" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.mk.inj "user constant" .inherited (.inherited [`EqCnstr.mk.noConfusion])
    "3a5d66b5fdc7b3e71d4685b46e4b33fb8bc00cabcbea6ba90cf43d98ff7c7656" "19e9b7d7ac106c0cd2aff4596711e37ee042b389303c8cc4f4ca5c8b0f8ebdf1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.mk.injEq "user constant" .inherited (.inherited [`EqCnstr.mk.inj])
    "e922d9e6fe4811da11383b23f923349644f66769166103e534ab359fb2658db9" "6f03ec6682b100ee7f4595b27a7bb5f415db12ebfdfc356f73c619eb9c343ca4" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.mk.noConfusion "user constant" .inherited (.inherited [`EqCnstr.noConfusion])
    "8bbc4136d8e39b4c99b59d674e91da3a1abf8a07a13e98c6d2fea75ff3f972a2" "7c83101132079df44aefb0bf60602412bcdfb5bfed1d671358430ea8943f0ac2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.noConfusion "user constant" .inherited (.inherited [`EqCnstr.noConfusionType])
    "faf8e78f57e466d7096804d14bea605c7622f435348bfb7980d2054ae5e411f6" "003ae89e0c6e03a6c1b5a2c8151cf205413d8183f2b78229d246aab91fb36005" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "8a937b3f4ba89e79d6332073c77e423ba3bfa96ab005aa140b4a711b63ccbfea" "5ec11715ddc7a5cfcc401a8f383fe048c9926300b7db7d36ccfe03bd1d64c43e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1fea870cd4a02cac75671cc92957359402eeca8f2ccc7a9f9141d87139fbfd70" "f4a563f960a7a5a32aac40b9b14916f856e146242248ae00b6d27a305c3c4174" "type.∀.body.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ca1ed84374d1290fd42791d499aac3f7df3b71a82a50fc4b84ec42479741d2a1" "f6e4a9635a0328ecda6ed8a489e2364021d225e9aea82ef7af33c5b5da0d4126" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d1fba7d2ff2150cfc0da5d0f53ab162454c8d1016d07ad516d54fd31801d78f3" "13ff19013121eb1ed7b6961afc142c2e68faae0db13627183672356958090465" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "838058d7326e2a2c264b9762979293649dcaf5bfa9bd2512399ab1379bfbb9c9" "c72c0ff7dded3abca27b2729c723aadde78e218a169ca15b52af5b913252aff0" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d2d514b55daf6d6eec4184a48f5cc832135a23356d8274e3d8d10d81c245d874" "a325af3372733f3505e45223a36d38f994eb48ca36cf1aed722b8c9161778ed5" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1da25c54fda5a938d967adaac5a7149ebc6f0c554cf49dd27bb9d181e6562041" "3bd4c3ccf08ac764809ce169d40c6680f722e38f9814496c579d044502dc51cf" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coeff.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorIdx, `EqCnstrProof.ctorElim])
    "b33036a4af6d12cc8a772b53916bdcb7f45bc80be2a388cd55a33db8f2eaac51" "c2f025891c3ef236290ca42d17d8a4fc0114003297c0b4222c691b70814a36c8" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coeff.inj "user constant" .inherited (.inherited [`EqCnstrProof.coeff.noConfusion])
    "c16ef1fe839793184e80f75c3b3b7e4e17f49572f24147f505f6087b12db3be8" "30dea37137bbbb2b43b4b02512b4ed0dfb55161bb1bed84922d8bb12818e0cd4" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coeff.injEq "user constant" .inherited (.inherited [`EqCnstrProof.coeff.inj])
    "d5b35d06d53f4b5bc3fc5b85c26b0db7ccc59844b8aa986e7bba6427152a0c2c" "79f4b18a13fde3e9c3ae698869dc3507b99ca5195241d1cd240396409ef60b89" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coeff.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "b2a37218553b860dff1b23afaffe95c33b5f7e9397672dd1925d4afaed62bee3" "9d9396224284f9081a95e8d56e726c8540ad3f53e98f5b6d6f9500a032ca619f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.core.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorIdx, `EqCnstrProof.ctorElim])
    "295dfabf2454fc8300465bfe80f8e974b32f6b5d1542f748ef50ec08e95db29d" "c2767351b38723ffbcb4f85fb0cf5256d957cd85b212b431fca3aa50911c64d1" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.core.inj "user constant" .inherited (.inherited [`EqCnstrProof.core.noConfusion])
    "87790c8a33fa4eeffd8bdf5a35048346a1bc529c639898845af6fbc9c610446e" "784210687320ffedb49ba443e51887890967ed5d03de86c40e6f72bb04cc643a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.core.injEq "user constant" .inherited (.inherited [`EqCnstrProof.core.inj])
    "4493fc43046143d34c53805b6e30250ae0a888c31255435d40ec4f6a6f7254b3" "d42b6c753c626cb660e2e3bee5580296a7ff200774e2dc7d3b3b577a1b4fd7d2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.core.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "58dc8e2df82a8d9d10d9a10f80c95133b175ee91b57faec2192a98ac16a9bda5" "5bcbd034b544399991a8b6cb0d402cda3e9a72b83204e6b652030f86a451f951" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coreCommRing.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorIdx, `EqCnstrProof.ctorElim])
    "e788416e4ccdd2d9df1ee196292e22c10dd14acd70c0b1506bdce11f8a142550" "7f1639665bf60fe42798e60e042d33ae9ed12573a672fb295ba11582059e00ac" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coreCommRing.inj "user constant" .inherited (.inherited [`EqCnstrProof.coreCommRing.noConfusion])
    "72e3abd339b66210ca27f45ccdbbd065a0d5848a6f28d6bdde976bb1ecd82c26" "75ad60b7ac9718f604510a7e61705a2f892eee25bc32e82b9ca920db754b22aa" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coreCommRing.injEq "user constant" .inherited (.inherited [`EqCnstrProof.coreCommRing.inj])
    "d78fcb769ea123a28adc80f4cf1ceea7411e2c98e8ca6ef7acc3962d1162c75a" "b3293d81f4ade6517176d21966eccf0be14e6debcb944453867d17dca5c5a612" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coreCommRing.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "360e6bc1693eee7b9c3515381d7deb5c0ba40ce3a880575f2707d6eba11f3fc6" "bafc830d0b03642c385c1293ff49f3bc7697362daee640aaaab6eff5f60cc823" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coreOfNat.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorIdx, `EqCnstrProof.ctorElim])
    "de7c6276aa0ecb283d18ef2e62186ff352ec5c1c0e945dbf938fe8b1c7b7ced3" "cd215c3e6825cf83986bd60a60380d037e1774b8ee0062ec4972164baf2e9a0f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coreOfNat.inj "user constant" .inherited (.inherited [`EqCnstrProof.coreOfNat.noConfusion])
    "e0fc0157eda483187f0a0154db06f8337a4d532085d4b02904c0238f47171cfa" "f8f6fb37dd56495f3edb50f58404b984efcfde8e526c1ed1f6686f3249589cea" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coreOfNat.injEq "user constant" .inherited (.inherited [`EqCnstrProof.coreOfNat.inj])
    "4701359928cd7c5e48ffa8cefaa693f11f10b5d8fde1cfd382e59d6f71df8fb4" "970f651865ed2cb9daacd286bddfb1d4206b18d53ce8190f42d10bd82dbf0053" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coreOfNat.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "f422ffeb3281aa5ebee8813f27a2abf4a93a1da8e3ee02213a4bdbd3b0f9ce70" "3806694bf799ba54a263b72082e8eec796c81a50f167ed767adcbf11d89c4b2c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.ctorElim "user constant" .inherited (.inherited [`EqCnstrProof.ctorIdx])
    "a80a7d2f6a5f6c8ddfc872f7128be676158f10695ad77674c1995e23d08ef5c7" "05365bb55d5386fcfc5e7fb10a39bb7ad0d5ccf07ecb7a5cc8c78005dbe8768c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "f131a7e8c801e40104b2f23273275b0a42cc2630497c690b359c11095624560d" "b8924afeeb83df837d9a202137d350e605e976669379fcc86137604f825cfd61" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.neg.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorIdx, `EqCnstrProof.ctorElim])
    "d4af4149ebfea5934c7eb2e3629d14d6c5070152732fe0f9c6c4a1189b0b7f40" "87347e122156b4a794169c1114a374c681980e0dfabce73ff69a399ef85834f4" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.neg.inj "user constant" .inherited (.inherited [`EqCnstrProof.neg.noConfusion])
    "7b314acbb86f5f49655bb0bc468bd57dc6711faa1e067f26f0f778388217b497" "6edbb588f7da2f38fc6af7b21474fbd34ec78e43b4d3459c5d859a2bfbbe6092" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.neg.injEq "user constant" .inherited (.inherited [`EqCnstrProof.neg.inj])
    "af2fa9bdd6dbc05d7e701f3e56008804805aab9749eb58b9dac26accf39055b1" "abce6fd473f18c40c4d182dbed56f45a4fd68d47b367e8b0a69a58cc41e9307c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.neg.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "28a875bd2b9d0d618b543cbedb9d20cfe53e88e8a8bc4698ede5a988fb9ff1ff" "885baec1efc114bc09ec9428317897ceddfad7aada4f93a67ad538dc41e74458" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusionType])
    "3fd16647ca6e7e21ee608050a513673efdc1814735080e9d15ae5912357e9b21" "2fc522cca3c33a0dcdafbd79b82ab3c9cef88a020fd1be6d8f27123ad395dac3" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.noConfusionType "user constant" .inherited (.inherited [`EqCnstrProof.core.elim, `EqCnstrProof.subst.elim, `EqCnstrProof.ctorIdx, `EqCnstrProof.coeff.elim, `EqCnstrProof.neg.elim, `EqCnstrProof.coreCommRing.elim, `EqCnstrProof.coreOfNat.elim])
    "b7a0b15c2e1f361b46316df1e992cf5c743189be22f8d55e3e862e846770eb83" "1ad0bfbfb6e52148427c7c156864a820f90da6de7eaf64003426a487dc4e6aad" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8f3449025976a0959d6409e896e8cfa124a26af5c5cfa8e0e9da20b08439bcec" "fa459d0fd2fc854e252642675239669ea5f9ff1c46c4be5c743d43ff6b366599" "type.∀.body.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8916cd2e47de8152ba1c5006f521f0d5c6e018e996b3a12b029fcd8e3e1509cb" "95f4e1bc9852bb779edede8da30dbfa07911cf32773cc641698268ca6580402a" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.subst.elim "user constant" .inherited (.inherited [`EqCnstrProof.ctorIdx, `EqCnstrProof.ctorElim])
    "c31d1d2fa4d729465b4448ac1c89820857a88318307be2bfa676f29af909b6da" "748209ae1b59d33af4f67d68fab832b53802b271ade1b22ad069f8e3fa2e880c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.subst.inj "user constant" .inherited (.inherited [`EqCnstrProof.subst.noConfusion])
    "c5a941a9763ce7704406a5943656794c8a8ad900a87b36e77076bead1a415db9" "bd81c72b6aa594a5072bde287b45cfcebfbc5e5b24cd7dc73ea89acde7ff5ff5" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.subst.injEq "user constant" .inherited (.inherited [`EqCnstrProof.subst.inj])
    "454b1b45398f097c82efa55152a5ba340f058a02e1ab618255e0b2bfc1ead8a8" "2642904611295d1c1e58d667434594877dd745c8df468277e2e018a81b50163a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.subst.noConfusion "user constant" .inherited (.inherited [`EqCnstrProof.noConfusion])
    "7041dfd363a8f1ce97f2050e4c490900a4f2a98e353d7a617bf492cc367d665a" "a485f49be1ca1de5fb437ce29a8d9aafd948440d86f5f37ef59028e50e89bea7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "4b6555393b8582bec0208dd4d4b426976f7c1b76e4b849da5969ced982d1f170" "7c6c3d3468ff7762743b43926ff902fe7352c82facc94e07b6aaf96932a2700a" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr._sizeOf_2 "sizeOf family" .o11aPending (.root false true false)
    "6d3da884671a32df7f6d48437ca32ea99ef2ade30c031f2e32a88ce03865ae8a" "fa1be5b06d9ec5e53231b472b3ef5e1a63e1cf8b98abe5bf7d48aa332d2fc473" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr._sizeOf_3 "sizeOf family" .o11aPending (.root false true false)
    "1e09f92eaa14c13b438d30e2f0b19f39086586cb9fc76cb511fe797f3c9d58ce" "2a5fd14e1f8b281472cc76300811bb72e113df16e02e599fd9c5135a0f962796" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr._sizeOf_inst "sizeOf family" .o11aPending (.root false true false)
    "21a3c8f414efd691ca6bb6d32535a5dee694108fd5b93ec2ae0f398e136e34dc" "79cab55d8425b76715e56e0f80363eba8145097e076268cd879d88a428cbb723" "value.@1.λ.body.fn" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "9695dec5fc6c3035432db8179f17845195a29805df318ffd4bec5951bafc9e77" "efe1aabeb0d11c3405ae229d2d9e4bb8e1fe963ec9e45c40cd818c4d9bc64316" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e052e42c2dc97a91fe0aead8dc13c53622cf56f0f2cf8f66ed5eab8c8fdba388" "c1d4737b30f5a102fa29c5204405bd7eab57c96b753d04788b3f12b9b091bdf5" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2e35539b3419ff56e6433032f6121c9676ecdb7bd7877b1e3936062c8ef759e4" "34d4de9483a3f7d21627eee4675e329269a6f0bf7bfc161dce9360719dbe52c4" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "12b60daae001ce3d044d05aa3913b87210b0b1945162bb3b38926a9408f6a012" "ca0e37231a9d22339130c64cdbbb7eb99fdbabd7faaf05b6367d2d9cfb8d6d51" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.mk.inj "user constant" .inherited (.inherited [`IneqCnstr.mk.noConfusion])
    "70b05bfdd3a11c2e8ed02f81aa25e8a6b89b08264272699dd3f578217d1a524e" "e37507ab17e5493bef422750aae212c29b6939fd1a2266b7a70780684a0353c2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.mk.injEq "user constant" .inherited (.inherited [`IneqCnstr.mk.inj])
    "aba79942e12f0cb8f58cf49f847b0cc83b339ee6be4aa2d54faadb2797d5dc28" "076e8f11da6b926d1a9c356a39b7c919edc90e2f6ad30b62ad13648a7f02ad47" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.mk.noConfusion "user constant" .inherited (.inherited [`IneqCnstr.noConfusion])
    "3d6aaf6f2d2dd7fb3b3d64f5d5c59d93202b9f4ad073b320c87c2a05361eaf46" "f08a3928e1c74fd1336409bcf25d7a01b2dc41cf12fcc54661edaa8e98b90afb" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.mk.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst, `IneqCnstr._sizeOf_inst])
    "4fe3cccb6ddeaa49f11cc39b7ae31d30432fb38329907e56e21ed29907b72627" "b5f0e3cc68e2f0292227a58583283d77893bd33e974aef92f4c4b3075ec9a103" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.noConfusion "user constant" .inherited (.inherited [`IneqCnstr.noConfusionType])
    "9a037a91e8bc22e330aed86f5cfc320fb2c488bf3a9f2f721ee41a2516422bb9" "0780511fa574a46d6b0538d9944341d3d5da2f2311b8c1a815e496ed1048eaff" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "b6af9dcbc2bb37071bef93ed15794e0359e78b0e46fe272a246baf70e363424b" "86b83bce76c2115a8838c2e20c2954c218882522d882bff7d7aacf88a0e82297" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2e8da0e2e6fda579baca7f7b18b2831e02617cab499c9b6b4027f54b5cd96b9b" "9b7ff36311afa5663ff0b7c142c0e57e5d2dae6fc5e20a2ba4313a737d5a3ce3" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a3ac43469c10d7d49b43fcbc191c9d02d1215a7508ed310251cfaaf181da50c1" "cf23116c1bb648d794cb58afcce7ec80a292df87355f5935963ebd055e1f7ddc" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof._sizeOf_inst "sizeOf family" .o11aPending (.root false true false)
    "4816bc5331a9808ef1352b97872725ebba359cdcb55544bf4cd105dd94541ca3" "73956bc4092968f1676d67ad5bf684aaf746444a7ea646465ae68fb6db92ce62" "value.@1.λ.body.fn" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "080015f9b5b0281c4942200f57865b7c2c2f02b767f064caf40b59e69aa91838" "e9b155f950b3edd405fe595a993b374ed38af322a71d2a332327a4241cfd66bf" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fa9086f0d477ab880b3dd0aeec9d72822bfb80ad19403f8a6358546edc351167" "5fa59a4536ae963c3fbc2f8e5910989beb39628abf91753f33f9f7eecda7f0b8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "aca34ba7665a7e007afe5dcded061b5479f9daba72942f4cd8b9ecbaaf57e42a" "e75fdfea551fa47b42cc36ecff8c5e6421929c26debf71529ad40c19f9c4326e" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7fd866a9bfc2745f7ab0faf3e9b14bddda0fc2cbfadeb7e8a30310956f27dd2a" "247ffa92a3370c3610731318ab947d80e857051360463e14ed04be58fa2e3e7f" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.combine.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "f886a2845acd64da4ddc023242f6459a91645227cfd2027f00f9de93454886d9" "ddb0c49f05d8799032c77eb80bb9efb013878763585afe7c4f1ff4af7bd7a496" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.combine.inj "user constant" .inherited (.inherited [`IneqCnstrProof.combine.noConfusion])
    "3accbab6e0d5c4d0b29a8492546c1e9161d46125c5ed9995c807e832c7e21aff" "4070b4744bede09a35d6c1117d5205b0d50bc804c00c58f3a3763e3bb4283e9e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.combine.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.combine.inj])
    "d403e6b2fc61af4371e42134b5d79c7978a1503c016b0735f9b7d6a46124a10e" "da1eca79ff64c7d3e1c6c90d43136d3afe31a942b7af91c705e5b87608a45a85" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.combine.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "1331648884f39ad2afed57b7d778bc065db2ab20b12f6d54e459d506dd3f2a70" "3de7da52caf1f932462189b7d8b1685757599b736f011986fe575b0b580086ac" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.combine.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst, `IneqCnstr._sizeOf_inst])
    "b5cbbe20fa4f4467aa7c6759cf65222e4d4be472f4f678f3da4c2176d979daca" "9645a0aa2f1322611ca54e73895741ff1443d978a7b5bc00e87c336b229c8760" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.core.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "f5859b19b8688d009586276262ee2f626b461607765463a1f32cce0c49c2a453" "2ff30d86cdf58e6b685330150dc8aa0dee9861020bd02644de3767f989ce6300" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.core.inj "user constant" .inherited (.inherited [`IneqCnstrProof.core.noConfusion])
    "c79c049f6c87df83825cb085361a3d8c557b367460fe498a4590ff2946028307" "1db2032452279b1e7497530dcc5fc1f795c35e2c1ef5a42aa52b02b51624cf72" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.core.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.core.inj])
    "26dadd3bc7800caa9cf0a32fe623db50866bd9194841c5dc7312e8fe2825dc68" "f8b8d2ab784dec2a6da24fed173549d0ceef6fd27ee6cde3eba45cc001b24127" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.core.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "d09f41622bc9c67db65bb8f8077d9af9518917db9340ca7095d8569d35f58d41" "0641c1cbbb9cd9a77865f64f6fddf65dc380d0740338b0b19531f218b8dea94e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.core.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "a74a60920f98ef433c60fbba9817f6fa0cc32d585a599961ceb2fdac0ce9e0d1" "d3046ef142abea885e697b71ee8b2fea67fa7114a895310b69b95d7ed2c2b8f2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.coreOfNat.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "ee5d90c9926d00472f35350939c28c64288c9f6754d83ba8a0be7e52ebac2072" "5b9f1d04ab3217c6594cc26c9650058091355e9531b68f5d95b01a988ff84414" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.coreOfNat.inj "user constant" .inherited (.inherited [`IneqCnstrProof.coreOfNat.noConfusion])
    "908a0594ab53d9c7188f930a1c4ad4dc85e3a5c9f810b9970eae35678a7fda80" "6842abf65af9a1c44dabd5f95cf77bf63d8ef6c59aff30ece0ed1b0bded6c60b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.coreOfNat.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.coreOfNat.inj])
    "53f1bc4b39da21f81f6a1f540940c9e6b600952b2c77ef5e68afe0ae028b445b" "529a7a43f812bea1231cd934d21c77e509b8a9ce3d18400ce5c058a13194562a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.coreOfNat.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "42852ea44696a84563a02bfde10dbd8fa037ddf9b727193817f56ed2ed0bf41a" "69c9d239f5eda1ddbf276efc5d821edcbfc60a17c09a7987fe43a6af76d74ea6" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.coreOfNat.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "35373a974552d40d5c66ff036d2c1f0b8b27d8e9dcf80a641654c50b2a2cb631" "23d1dea558573704469fb0ef67585e56907d5ff4b09a87629049de3ca45dcbf0" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ctorElim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorIdx])
    "de61b9670b570432cd66368e14e779f6527b5020459a8003ac9822b1b488ee18" "c576545294ac44656a1b7133b60e33d2d7f944c7754e18655ccbda723bb4687b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "65eadcd63fed49b569a8bd8bfcaef5ec6f03f1055f05b967299a4a777116dce5" "87a75f53c03cabca7651dd3c4dc965f8346eb39db631747af329cb09e22e296c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.dec.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "893f0fa6cecc2dabe7c8389252266ae90485b890a828e566da7bf3bb48e1d53d" "c2ce2e2f032ab62cc144549007750f951d49173904e0e13875ab5cb82ba5851a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.dec.inj "user constant" .inherited (.inherited [`IneqCnstrProof.dec.noConfusion])
    "da240101cb2e3cfc14cc39e2d9f96a84b6c5d93defdf281dd6766df52f6abb45" "49a8d9e134417589ba8302e8c3c075428b7b73a5841ed615e019aaf716d97602" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.dec.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.dec.inj])
    "eca19a4b87f9e726ce501d1d3547bb1dbb2179b3b27bea9e5a2e90b79681de46" "fed0f6dcea7a28587b99e29cc5d7692076b03770ed64c9ce3611d17bf1c8684e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.dec.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "0c5c9efb71d1540d03c1cf471ec3532d5c47a7cff3032dc903198e3501d535dd" "30b5cfa0921c7eff6a7031753a7dfdb1b44e9126c331c5c3574d1bec7c069839" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.dec.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "9f757738ff82e1c612a0d153fa9909275918cce4163d15ae8e213ba858d6c7d9" "2e44a59375b47c0b63f56f08a05d1fb2f324583f3a71cd12d4cb867e2602b743" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusionType])
    "8c9bcc3f8961bb07aa68e61037748bc2975960549a8bb35eb9edd73e1aaea6f7" "18d06e796c337320715cd1c4603b9a33e324d1c1df93bfccc5d6b61314208e5b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.noConfusionType "user constant" .inherited (.inherited [`IneqCnstrProof.notCoreOfNat.elim, `IneqCnstrProof.ofEq.elim, `IneqCnstrProof.coreOfNat.elim, `IneqCnstrProof.ring.elim, `IneqCnstrProof.subst.elim, `IneqCnstrProof.ofEqOfNat.elim, `IneqCnstrProof.norm.elim, `IneqCnstrProof.ofDiseqSplit.elim, `IneqCnstrProof.dec.elim, `IneqCnstrProof.ringEq.elim, `IneqCnstrProof.oneGtZero.elim, `IneqCnstrProof.combine.elim, `IneqCnstrProof.core.elim, `IneqCnstrProof.notCore.elim, `IneqCnstrProof.ctorIdx])
    "ae3842a81981dd98e320e4ca1bae17823e9d25df52af21fe18061301e55ff410" "462a996581f34428ccf5218c42552b050219b0a48d87d7f9264893cf970f1b81" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.norm.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "80596ea9022106c51d8c59a8e8de62187fc8d8155e0905f9760ef3571ff17cf1" "cdcd6b565b084f4300850e50902064037119349804ae9129391505b95121ca92" ""
]

/-- Entries 1800 to 1882. -/
def part9 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.norm.inj "user constant" .inherited (.inherited [`IneqCnstrProof.norm.noConfusion])
    "1464b6b29fa7d828d265bc97df0a0e637fdd34ac99eab57cc46a0ccb0666e784" "fcfcd240208d3ee2bb922becccd7b434680dfecd6a0c4de1d7a658aa1894698d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.norm.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.norm.inj])
    "95969d8a74cbc2c992c5a7903dccbd9fbe2c8f9044bff95d4f4d1facb83985cd" "15607f8f9fca99eb86979d39c6e7223739df1308c5741e5c3c37d439e4c5d72b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.norm.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "fb15acb3e42646a2e65c6db44f7ab9f3c0e30cd3b91f9eb619c194116fda1f71" "276ee85a4f9edb6a20ec086fb3754cb5a8b841fd0d30a02f65c90fe2ac27448b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.norm.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst, `IneqCnstr._sizeOf_inst])
    "bea3ae8c8d027116b019c310417d5afd4853b2030515633d67079dcee0457dc7" "c860dce9597f77999b28ed48e0ac98fd3b16b8040f2560dbf2254cc2852747ac" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCore.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "29fefc50e752a9d4c9fb099666b468da330bc308fb383b0a192faed17bcc6b10" "d9d112bae46f6a2790afaed28eb68b03b9a0e491bbc1c19e113de413dc11d23d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCore.inj "user constant" .inherited (.inherited [`IneqCnstrProof.notCore.noConfusion])
    "2875b422b06ee356098f3ac8ce6cde01cd84b618d063182587b8779cbde09cd2" "144d3deb956c28914d9496be2de9a392579058c8701b78379103eeab39f4ec45" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCore.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.notCore.inj])
    "777ec58957da1dd973cf1a945a93ed452e75ff091e84f61a937b4cfd352f1e32" "3289c6b0cb4f3d84623efb066340d8eba711d6aee1ad9d92fc90544c8394711b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCore.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "5ad81d895ee54736bc266db31ae66c17ca8b2edec452f5dece23bc0617362f84" "2584de64f4919abc770c50726e886730e7de942562618c1906222756ef76f6cb" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCore.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "01a6e3b2e1158517ca0fb75bf042ca356c58bea423b5e38840bb4dbff6151c33" "a8673db404d1d868ec65a55e2f6eaa129eb6e45cb4c3c6518ff3f6c6822b8ea9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCoreOfNat.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "6c48d2eb7af8f0c331d820a8a420d652da9eadd455eb4998f1189d5ac0f405d3" "e15d0c6a701ee7180705688807f78603b81d729fc2f92b018f468c0167899fd8" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCoreOfNat.inj "user constant" .inherited (.inherited [`IneqCnstrProof.notCoreOfNat.noConfusion])
    "063f8f454717bd16c840de925045669877a1adbe0bcebf84e30aea66a3fba37a" "acaea78f03c3f6451aa9476cec9267dc4f3fc036f401c885953216830703ecdd" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCoreOfNat.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.notCoreOfNat.inj])
    "55bd91b81e3286fd76ef728f3b2f2d98ccbb26f152a5f6f9958ad1727fb747f3" "8e7a2b128727d80a6e21ce56fc168016ab86773b10016c9e2d380932160da845" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCoreOfNat.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "54d9c8ee5123275a7d6ae76ded94027974e644d38e5666ea23ddb364b20432bb" "3a0db49c3f71f17fbbcb535ea231f09ecafdf1c93d47b5001391ba45d456f9df" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCoreOfNat.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "c812f8fec228bc3d0143516bf67ad5adf8a653b086ba6d4b715d07dd3c9bac7c" "e938a79fb9e303575db64bf5642da8a13a2f01840f607e6353bb8b3a009d7a72" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofDiseqSplit.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "1644513b16fc035285693c324c043867eb04178005d94adb0206c50e5afeb024" "c42eef30f655b07d8abc4a93f7cc870caf3f627b6c57c295287bc43fc87052ef" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofDiseqSplit.inj "user constant" .inherited (.inherited [`IneqCnstrProof.ofDiseqSplit.noConfusion])
    "b7f777d5db82a149031c1c70e0e1c852d9624740158c5bac58df1935a6909809" "386ea2e7b7f23d201c28725afbccc46249b55408f45fe843f3f3db7873d32836" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofDiseqSplit.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.ofDiseqSplit.inj])
    "67be5810dcc8c0677c5d83062fe717d1c3fd80588f602ac34b4bd2bcf4fdd42d" "c83819bf07d2b3309cdc06d981ce91a971a8207f3c8ebc6785447151c0e177bc" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofDiseqSplit.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "e1ffc027178f29edf9dd771c402fcbc8f17e3c8bc3216efd193da1ec70205c69" "c748c36c665613ae1e301ebaca24ea494106575f323f7c3982de940d02650f68" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofDiseqSplit.sizeOf_spec "user constant" .inherited (.inherited [`UnsatProof._sizeOf_inst, `DiseqCnstr._sizeOf_inst, `IneqCnstrProof._sizeOf_inst])
    "cfc29c7dfba8091979426e2637e589c43cbf670583d9287e67ee2d43dcf31cea" "d7e15f1873bfbc006fbfcfd403503b50b8cb129f0657e2d9255f6fbbaf1615b9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEq.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "73ca9f08dceec7207d01d0a47e42af129c8d7ef6f2dcefcfae118af6f147689e" "9a0ba4946db8d7c0c67cb61e83c99aabdbcf8e26b908814618f8553385cb7702" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEq.inj "user constant" .inherited (.inherited [`IneqCnstrProof.ofEq.noConfusion])
    "77edccb5d332c88db0e79663e5cde203368cb5fa6ff6e495c5c3c4e8127b6a08" "af030c3c70b3033b4f9c4589737bc5e8afae4a2de5d98457f9619db79960568e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEq.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.ofEq.inj])
    "2f817430103bffb08befe70f7ced57717fd3f90cb226dd631a64e56161dc8068" "ac6be3178b4f90fd20b637d1cda247690025c542a34a5e8f354f2f8ac2526a47" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEq.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "492be7743dacc70a8c7c17edbad84b0a2a3b77f2f67589f44238aadba70b8459" "e416c578ccac4a220a333378049cf823cb5386466beaa7ca8940162fc8b91367" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEq.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "4603107e6a354c19517fa39721aa1ea28c43e97de795b2f9f2ef93fdd1600664" "2ebd9e0e8cd14d9eb5f7416060f07527e0c59abf97e91fac4a3ef2d63071c74c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEqOfNat.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "e3d990d8f263c78c513ffa087c87fe2bf46d826e3401e923caa6d69543d794bf" "64ed6688f744a2ca88cbb478f5a47f10c1925e96a2ae0da388a79a7bb8d99d41" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEqOfNat.inj "user constant" .inherited (.inherited [`IneqCnstrProof.ofEqOfNat.noConfusion])
    "7c5a0300199ffeed96eedb5f9b2b0b9cce3ebab403660d78021de617ec9d5270" "cb9dea05dbb6d2407e8f8868ce6c3c7e17cb87185e93e842a5be2c5781768e08" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEqOfNat.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.ofEqOfNat.inj])
    "65171e14b6a1f8ae526e7ea82212fb93c5449559db455a1e0698d89282f765cb" "5709edbaba25151d8144ad611dabe7d2657fdaf43d22f2587cafbe7549d9606e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEqOfNat.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "f1be6f75d5ddae6d81eefc96ca33667fba0fec8025b69a9c3c108b0d66a59b44" "fa5b18ccf70316683258387e711f908b4c70477f02b1883266e62c9670e2ef05" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEqOfNat.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "d06162abe66e36f46f4c3080c35613a3be5ec59a36ebc26c16f459f2d004a874" "6340c0177170a045b41b01c26ce74fdbdfddece30921fb61bd6eec1b51107c44" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.oneGtZero.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "c543f5eeba6bcde94c2cba474c04d9ec93a8a8294f6c27a8f40a40c06b9a4678" "693c45ee28dc223d1d53235d6adab097ae1931f76f2b37aa1c8e2974c0e82530" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.oneGtZero.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "7167f92dc8816fc4ec17978ab468441c41161719340123e4035fdf6319e5cb9d" "84d24b400f3c47e78100e6173c2ac227ad225e6f0f4592d5e463ad037c8b61ae" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2bb3e55f987b275b8b1cc2ed3dd459567635ff969f72471e914a1396b13a4056" "06b592545e16c174884278209525dcacee29811e2c9718fce2a516789788ead1" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7396d2991fdb06838fc9d6f924b3322115c56115a72c9d5e8934e2b223498457" "08d029718ca33d416533ba123d507247868e05a1e21598b6618474336b2540d8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ring.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "f765c9cce3737e62107112a0afae65a39fd52ecaf45f31c4243ced91c6e5eabd" "a0bf93bdcae3fc088e30ea231633fcd98ba8fb9214963a32c9149aae48eefeb7" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ring.inj "user constant" .inherited (.inherited [`IneqCnstrProof.ring.noConfusion])
    "accbd6341d08c02e6fb849475ce6925abc5f7846945976d20fcd6919bcb2b0d6" "6e250d5a969ca0957f5562c2ab2689705023f24d6d8030ae657ed797ccc41b2b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ring.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.ring.inj])
    "6c5c1a53a7e7b58a59bd4bb20116cb283f9c7d5ea20c2551df7ce2b44e37da1e" "71538a32eed443c9f172f5a87626a6dee398bbab3015dcdcacb8d98b1b7df587" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ring.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "45e8c4905500e871d248cf1adee81641256e7e7487552960861c942571388974" "a83abfb21423b91ff43a45bbd4c6bc7ca2358e829d4000602dd8396bb70dcd03" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ring.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "20d8f15b9079591b8cd8601a2f7152ca8364c933efd20e6fd75b21e0d2b1d02a" "6be6302c2afe490023ce7cd091969ce1d5ec84b845973135fa3c0aec1d5ba90e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ringEq.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "e11f6a1fdde353104900e8ca99d8b3f09bf63ace571df69e3de44f3f467fe03c" "96747d1e5ee65b06ffe1637fe79cee7d2e75cd7771c74eab77f8f2fcd362ed43" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ringEq.inj "user constant" .inherited (.inherited [`IneqCnstrProof.ringEq.noConfusion])
    "031354d68c518982d45d79a0a7a3d4ceb01c3d9779d55d31f7d36cd2db689460" "517e208797114b57b8e80b4862fcb1702fdf5f9f887bb5b0f88dd26fcca27c5d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ringEq.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.ringEq.inj])
    "408a0bfdf692fc9c029c0fd32565ea915985f583814223b7a82fc49b01d89574" "f7c574983fb7f1464297815380249e71776c8a05f1199dce302dd69c3b24ac69" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ringEq.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "117434550ba1f6c339b75c7b65fc27e3168e3ebea67b0a1e413b7bd5385f134c" "b97ac331f77d1f50baa9d13de81c418163f23c096de9fb3c1f5e9f28c91c994b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ringEq.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "3dacb1e7bed424eb8c096588d97449dfcee0876c69ee8db92e5205312b415d18" "2023896d79f60925b3c3d1839af5e0373044c4a3d4c7bb2c5d7a64b492e8aa4f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.subst.elim "user constant" .inherited (.inherited [`IneqCnstrProof.ctorElim, `IneqCnstrProof.ctorIdx])
    "f3f6eb3e3079fab8f44879e5853111924262ccbcac76701004611c22efa865cc" "60d164262a6eb1ffa788cefe38b5e09dd20b236a7bea415182dc59653694bbc9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.subst.inj "user constant" .inherited (.inherited [`IneqCnstrProof.subst.noConfusion])
    "675c931571df3a95d2ccd9b5c74b3541b41e5fbd1c649769160fe9b32e1736e4" "8408f90ed147f28c4f63ddb9b0a3ae6708c43ccccd11d8e7d61dfe425fb86229" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.subst.injEq "user constant" .inherited (.inherited [`IneqCnstrProof.subst.inj])
    "4db69bb1c8b169ce0c8fdeb95558682d733b65da4ee42d08a377b62125436980" "1c3e61089a210d41a28114e869a62e23d27e5cc8c045e5fe7bfd3a9234a69a72" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.subst.noConfusion "user constant" .inherited (.inherited [`IneqCnstrProof.noConfusion])
    "22cb70585e8c9d52346f5589bda57a691c1176d6b1f1b5968adc7a3a4e02c26d" "677d3aeae653e2cc9603e882d63dc12d556df2537fb04b3f795155639c921caf" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.subst.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst, `IneqCnstr._sizeOf_inst])
    "b5083cb595f0e1ca587616cea952d75c24e55d150f6c8682b75cd133c9da67aa" "57f94ff5fea8599f78bdb015590328dc931d3233e4d579a1012ea750a9ff4197" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof._sizeOf_inst "sizeOf family" .o11aPending (.root false true false)
    "b56f470d7c99d75df77302315a9c774c6c697474d6008af73ed60c50f851ff8e" "02ed207daac694fc23c392c31a6b1cd6eb6cec457b9755f3b1a9373d8e0fb43d" "value.@1.λ.body.fn" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fb226f44ab7b006474ce6925f33a25cdf94de536110892eea3689e7a7114ae3b" "999e6430c31222308c7cb01c2892962ff79f8f36c8996a702879ad04c3b1cd0e" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "435f0c9ad6b59fe721c5062523281f0e81d9213a5e03c17453c9fa2f2ac79b47" "73c4ab1502297a0df8bc67c23be308eaa99fa39486ada05815c456d3a4d2381b" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b2948c710f1b91bc78407e8e9581661140e7e4fb16aca2bd081cd730936cc31f" "84155b04fe96bdfc21b836543f1346828c1c5fcac040b96d854cfd00fafa3e4b" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1900a41bb7538e61b1d503b70185b3477da7ea67d6445d8100b56638181484b9" "a1035a40b074edb78499af69098da75619b4cb60c9f95711ad0f6d739ec6708f" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.ctorElim "user constant" .inherited (.inherited [`UnsatProof.ctorIdx])
    "214bee4b812a622f06d7fcfebc4f66143fd3305def6dce32592ec6e24d2bd8d7" "72c692b34ea9f8a8cc76a87664ccc76e7283e19ac5ba9ed15d286d72080b9ef4" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.ctorIdx "caller of a changed block" .pendingPasses .unexplained
    "8df0afbc425236eafba9f44794b38fb64f8c040db5e520264489d324bc7b4bb9" "250dafb6986225fe1508a61d144cd23090160d80741d3b9be989af293468c46f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.diseq.elim "user constant" .inherited (.inherited [`UnsatProof.ctorElim, `UnsatProof.ctorIdx])
    "514a0514534dd7c24315ce7782b0924c1346c760d2394b2d61c3243014178d83" "fee98ea1c164c79afb37db9d4e04ddeb55511ab6e892aa885192818ca07a218d" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.diseq.inj "user constant" .inherited (.inherited [`UnsatProof.diseq.noConfusion])
    "f2f3af5144f72327fcd6b61f4a5991c2c982266531d6aed13d4a56b071208a83" "d0b1c944a1045feadd04b50d31f8264c7723943a9bf83e719d83d6d2cc56f357" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.diseq.injEq "user constant" .inherited (.inherited [`UnsatProof.diseq.inj])
    "14f67ea21e02cec332bc619491b032d4fc666c9f20f3a7db6e5fc9e13764ec3f" "7e0fd0b257b4be2354fe8475c2f6c496681b79a9d8a098974216dd7e88861e80" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.diseq.noConfusion "user constant" .inherited (.inherited [`UnsatProof.noConfusion])
    "819145f1094eb04d27e6aa6d5a8757f1c380be738a5abdb44f1428f086cc682d" "392149fd1ece8143bf93035e6a2500f372c9f9a3f664b347f60d307bbcfbbc41" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.diseq.sizeOf_spec "user constant" .inherited (.inherited [`UnsatProof._sizeOf_inst, `DiseqCnstr._sizeOf_inst])
    "950bd0ebc5c2b761d97af1eb27b38bbff010c3c62f16f2d7f3203f802f547988" "f13d41d3861537eedb3eb46cacbcdee5b63955c0311a5032dc5babaa159ed9b9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.lt.elim "user constant" .inherited (.inherited [`UnsatProof.ctorElim, `UnsatProof.ctorIdx])
    "db2ed9ac3a8db09433f8674c4e275853f76b405c7e90ec65f841f73582018e5b" "d27aec358814b8a4a3f21c4700538d980777b38b248a0fbde492b800f41f90f9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.lt.inj "user constant" .inherited (.inherited [`UnsatProof.lt.noConfusion])
    "3142a65f516c06785e3b0839a1cc8e818b652324350f8c23dbb11e66c2c61f48" "3b773f3aa6a4df631cb68cbc3c55d4c4463e557dd555ffbb48eef0eac536d215" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.lt.injEq "user constant" .inherited (.inherited [`UnsatProof.lt.inj])
    "ccb6c44afa7575427b7ce7f6916d8ffcefc0b2e6bf3c1be9ffe0baa0d20ff6f9" "92e0e6515d5397dcb79abf3ca2e93b8ed2be79d19c2caa3636d61527236e231e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.lt.noConfusion "user constant" .inherited (.inherited [`UnsatProof.noConfusion])
    "4e78f46934919f36ab4b5cc5cdd7f09a6370f9df2491b36255173a57b949ab30" "530a6d844e0c805b69636e2830461f1e45bd0b2fc57ce858423a9b80dbcfc695" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.lt.sizeOf_spec "user constant" .inherited (.inherited [`UnsatProof._sizeOf_inst, `IneqCnstr._sizeOf_inst])
    "7db1620eb349e5e89775e44bb0d7bb373a4bcf8a39373cd6a5bf33ce5e643fa2" "eaa99e2323826c15b387e25c396202bfbf5341f2c54b50946690ce84a0ea5cd5" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.noConfusion "user constant" .inherited (.inherited [`UnsatProof.noConfusionType])
    "7d2a53f6ec9551e754d48aae62ea6f88bd3d67a2225baccaf2a04e087e865efb" "f11a31554b74fb0068333c6d727bd118f30e7e8b209ba38fde38dc5862e3d1d9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.noConfusionType "caller of a changed block" .pendingPasses .unexplained
    "62da1039e027cbd12eb1547c4f4ff838730a5271f1cc89edb7fd102563904218" "f42505520ceae78b75235e873bbce354b548f4e7a8c2108239f9fa5f9c62a42c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c6d6643b2efec099db31c557dc67b897d530a6f38dbd58e06748abfdfef61850" "27984d633fdb66cda209145f9ece2f14868bed7893a3e5b7092bcb90c3bdcf38" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7aee83b161cebc0b18d9911863c32286c732535bca251ebd8637cbe13297ba3f" "92c73f4b174ac70bfba383029c880fdccd80af60233cad541642d572cefa5920" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Fixtures.LetNonDep.Split "A" "B" `Left.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2160eea920c18ef2361d6c2a8859f332bed9d4c3ebde702fb07e762d926300cb" "9ecaab2697b9e2b459cf50333469faa03db1c68f04e74078cbba4ab7ac872b6f" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Fixtures.LetNonDep.Split "A" "B" `Right.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0a332fefb2139bc295cb2394cf49ba1da5d77a84565b3222f10bc2b4f5332ff8" "47a7a7d529c14fc353bbc4ab0546173c806399dd01c50431b778bf15d283b89a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Fixtures.LetNonDep.Equal "A" "B" `Left.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a731530733ed61c5855a00b8604dd40dcc8cc47ad9b2fe47e60f13d78bb90f1e" "24bf667f7ec512fde8b5f64806a8ab1ada647672ead7dec5c81301e665599a83" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Fixtures.LetNonDep.Equal "A" "B" `Right.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "24bf667f7ec512fde8b5f64806a8ab1ada647672ead7dec5c81301e665599a83" "a731530733ed61c5855a00b8604dd40dcc8cc47ad9b2fe47e60f13d78bb90f1e" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Fixtures.NestedLevels.Mixed "A" "B" `Left.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7491f38aa5180ce1a17bb67df6eebbe706c971d5d00e1e7b2e64f60cba1d11de" "90612f29a1874723dd245e736729413432cd46c6abd2a4ea4fd8073af984d58e" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Fixtures.NestedLevels.Mixed "A" "B" `Left.rec_1 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyA
    "ac796825d9bcbe0eb9e1c3fed8dd34072750a23ce7201733c7d925f202088499" "-" "",
  e `Tests.Ix.Compile.Fixtures.NestedLevels.Mixed "A" "B" `Left.rec_2 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyA
    "8df84916972d20e405d2f55ccc353b82ead5213ef22b13712a074f9d7eb086a9" "-" "",
  e `Tests.Ix.Compile.Fixtures.NestedLevels.Mixed "A" "B" `Left.rec_3 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyA
    "e281747466cc8f2bcdfdae5c3587e28d1c72de21adf6e603a932312668e4aa90" "-" "",
  e `Tests.Ix.Compile.Fixtures.NestedLevels.Mixed "A" "B" `Right.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "f1154ee85d4ad1b9827e1194378e4eaeacebc57f488284d4f0dcc6803a819559" "8a0bfa35be7da4d484fcfee7b02cb04f3ca041d7d3e2938ee45b7e7c90149af0" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Fixtures.NestedLevels.Mixed "A" "B" `Right.rec_1 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "c1f246847a385808070b3ada8a50a018d7bab24550fa4c22d9dc3110590b0484" "",
  e `Tests.Ix.Compile.Fixtures.NestedLevels.Mixed "A" "B" `Right.rec_2 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "f1dd890edb39a99adc73fc82181c181c918e8216d0a53608ccbcaba427bddd30" "",
  e `Tests.Ix.Compile.Fixtures.NestedLevels.Mixed "A" "B" `Right.rec_3 "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "9c9f7774e8370fdc9a92bcb932c8f97ab0d32d62a388e42d3f0e9e72eb3f6611" "",
  e `Tests.Ix.Compile.Fixtures.NestedLevels.Neighbour "A" "B" `Left.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d1c2ca9393f1c17bab9742888ecf096bf675563815b99de0e9fdf2bc695a72d3" "0c21353e8cd1dc848d115d8aad8f896bd4a4fdffc028f0c97a26ea880f3b1436" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Fixtures.NestedLevels.Neighbour "A" "B" `Right.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0c21353e8cd1dc848d115d8aad8f896bd4a4fdffc028f0c97a26ea880f3b1436" "d1c2ca9393f1c17bab9742888ecf096bf675563815b99de0e9fdf2bc695a72d3" "type.∀.dom.∀.dom"
]

/-- The measured non-canonical set. -/
def nonCanonical : List NonCanonicalEntry :=
  part0 ++ part1 ++ part2 ++ part3 ++ part4 ++ part5 ++ part6 ++ part7 ++ part8 ++ part9

end Tests.Ix.Compile.NonCanonicalDefault
