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
    "e55bb46e42de613f3f698f1f256bb0c43d4d2ab4126d267ea8b2a195b5979f67" "7ecc1fcb2d7f097e778c164e9665d57efa098d9c1ebcee0d529130903d4c9630" "value.λ.body" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo._f "structural functional" .pendingTransport (.root false true false)
    "946a04b42cf1cf5ca1420cc450facc5d4c25876b7017f5252801b58133e62e59" "670c4e32a9d88760ada44a3976269be77726d24b4da8c9de453922e1b87e0822" "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@5" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo._sunfold "user constant" .inherited (.inherited [`cTr, `cFo])
    "f7082d0443c1b38239ee1cfdff4e567d258b3d696b64d7fbbe3f92de7b225e16" "239af410afc555c9c55293077a79ded46fd2e8874c6695be43156e2e18a40838" "",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr "clique member" .pendingTransport (.root false true true)
    "9aa5f057ed6e7e54bad1f0149269970892b4c883a73f90ab6ca89c7301788317" "8970fd3c2912f2e862b3ee0c5c82df3eff51905ff2f40e0719b63c2176ee8516" "value.λ.body.@4.λ.body.λ.body.@2.fn" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr._f "structural functional" .pendingTransport (.root false true false)
    "4cdb47b0efb189248c0332e19a478d3aab0fcbaa323105310b68494152f6a7df" "237e78baff718f272ad46fe08fcaa9038834e3764fbc472e7c26bb96430c7d00" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr._sunfold "user constant" .inherited (.inherited [`lFo, `cFo])
    "fb34937e88e5d7e41ee2513fd96a275d23ec6806f3d1289cd1a6749a3ffaf220" "d1af06d85247648a324db39dab8892b112e59ef91c4900e51f834cd489109a4a" "",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo "clique member" .pendingTransport (.root false true false)
    "925800c959defb61ab59e9ca4f1d03a8569d17c91230fcb5b683510ee78ae582" "671bf000e880c2b96203922ab5521785be73b705ad390454002e10e31bce0bcd" "value.λ.body" "projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo._f "structural functional" .pendingTransport (.root false true false)
    "15d43c0ba995e823fbbd1c7227fa5a3b5182b11eff33a35da82a4b21704b3f59" "a3b54b4648b2c97d9f1a17f4b95e1bcca4222acdae4d929574ac47cf28b500d5" "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@4.@4" "path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo._sunfold "user constant" .inherited (.inherited [`lFo, `cTr])
    "d27e527b120e8e2aebd09a605de7966c237b488a6220c5a6fee5eb1e110d4298" "a4769f9dc5df3bc2011170a55507983f70af0b6bfd0bbb7cc9aaa7783bca257a" "",
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
    "85bf0b29cbd0ae51eb6fcccec7c9fee8586402949922062961c9ae3531ab612a" "6dcbc436be70e74e5439e656b44114c10b02e09ebcb2fe1441108d2b5f3a9831" "value.λ.body.λ.body.let.ty.∀.body.∀.dom.fn" "`let funType_i` bound in clique order (`withFunTypes`); zeta-equivalent",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `evM.match_2 "transformed matcher" .pendingTransport (.root true true false)
    "1e1f7200e87028eca387c1d44c2e215254ade0a761a157a3e6b628a177185cb5" "8efb3c6d1d1af97d41c976418b640ec8605d679fa71ff5c4cc5ff1479daebbe8" "type.∀.dom.∀.body.∀.dom.fn" "IndPred `below` matcher: `funType_i` binders in clique order; regenerated by transport (R)+(A)",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `odM "clique member" .pendingTransport (.root false true false)
    "5af09c32f715506203cbeac80e27bc502eae94b01b2bdf563df48f41cdbd8322" "797a7574b276e948ceb2835036b98f0035a98b53882fa3d04a4c190e1f114de2" "value.λ.body.λ.body.let.ty.∀.body.∀.dom.fn" "`let funType_i` bound in clique order (`withFunTypes`); zeta-equivalent",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `odM.match_2 "transformed matcher" .pendingTransport (.root true true false)
    "66e611953d044882c13c3c4ff2d30aedc04e9b0923a5377368a8ede7b6adbf37" "01e46e132d415b1d954324c5401b4ac974a1965282e4d1b9314c664c4fa1ec43" "type.∀.dom.∀.body.∀.dom.fn" "IndPred `below` matcher: `funType_i` binders in clique order; regenerated by transport (R)+(A)",
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
    "cd37d419d255515656933e6d23afe32bffc3622104ad299967bf429b71328188" "3149caf1f58e19e0832f94972715f19a8fb484385a3ed50e37ef683a5e12fd5e" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "9f571cee8cd34435aae331146255374c3c30bd41d22263eb4d83e9487a9971d1" "ecb5aa3e7f9be159472b15d3af82ab2d24f88b45a0502ffcc86c00d1320e9973" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.a.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "6d49117afba347441fd9d5c801883965a81a59d32b23b89e2f613cce8ede1432" "5ba8df4f5c5b687425a8c97a35a5a33c0d9617049892ca7563726f89bd459959" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6825ad81f198d5b2c2383e8f41765aa9173509839d83eca74daf8ed4250cf7f6" "edb22d889d302d4fc637bd44e88dcadb1f8a38bf305e62670e018b630cfcb4fa" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c87e3173622cbced80a8ba699a7da4f6dedba809cbef16bd6e968dc15278c30c" "377aeaba992e9d9c13d4aa246284169c574fb6350f892c0c02d0e5a69b133506" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "61409cf8593535276483244e4931eddbcfe3c128ec76ebb73f98e09c5235aa04" "162916defdace1c6bef8b2e24099f7dcd356717119fd8de74c9f49e3d71199f9" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "231dc18951ea73da5c170f4d74f2cc36c744823c7a2e5bc63d2833f57237bc90" "607b55c6ab4127543778e692744db18f9f4d0403b2f323cdde273214930d053e" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.nil.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "1306c44721989e0badcb92934c7b477015f0d751772f8b67a115b6124d735d07" "9c6e07355e685e9c65caeb6e041a6155e814bc3fb7618a18042c173a21a53570" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3ccc83899f75d3c94a6f6edac10f5a968ab26ea933205cbc7ac420376c39080d" "c25c953a464d477303c1228a5d162fb91be4191770fda51ed39d0a34c7ca1524" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d80456773bd6b4b102754a79e2c45bd6feaee3685cb0646a3b41716daddd1e02" "81a68179231d6907cae95db052b597990c7a2b1f31f5e1b6a79ff245082fe9d1" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.size "caller of a changed block" .pendingPasses (.root false true false)
    "a079964bc4740aa5f8db3225b1cede4039647cdd6ab1f0a8b3c24454bfa9bf10" "9a7b9edc257295cf6bcc6702620bd771333f97c635fe50ad2793b611998324c3" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.size._f "caller of a changed block" .pendingPasses (.root true true false)
    "52f668901e95777428555c59f3cfd2c3a90221269c7a3ef2c67fd4342a007d5a" "2e6a7a55c47616efd970fc5db3eef79241777a5230e2e4413014c7d02491e38d" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.size._sunfold "user constant" .inherited (.inherited [`A.size])
    "73bf83c71709837e792456ee256596e7dc4254ffca8cded759b3072af5512be0" "cf579bb3bd210d950de95b61dd25608099935de910afe091c68830264b1df69b" "",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a17da90a847d92e8024d980f152101a3ee8f2096baa675ddc6cb69732b2d1ebc" "f6abd9ed9fa5e1d41083e3fd94b9497f3929b8c3b57bb15bd3ecd84afea5c021" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fd85ad262719d83a12fc1d950e9cbab5a15eddf153ec38dbcd5fc507216927a7" "27ae2ec72b9d470cb04e1fec2db3bf84a0db4376e54bc964cfcb5188b8fba868" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ab8acb574825a6d2c00a02642757cc90d37a478525eab15ffd76f53041572b70" "f51addddeb2bda9e8d058e0b18aea15c86380b78e043b35d6ad475e6954ed292" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "597541cb7d1515de8618e8ab7f7f7e0f4f5693cfb3ea6be3dd1cb1fd8891e662" "6fee31554733eb6825e76545eec5a750f07ca2367e17928095e4e31dd46915f0" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c8322e03d558f85a8edc7fe68524013880ad0bbcb7dc890136d247154b230992" "488ee843bd3a5db6dcaea357ec8fb7edfe5e5b79537f9417cc7b85f7ae348707" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "32038f41f6815ac7654830d5262dd2880649a594097cc8af729505ce45c84ef9" "9ac4ffee9f38aecd8787eaacb1f4c9ad3748ec11379ffd85e516843877f35f52" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `size2 "user constant" .inherited (.inherited [`A.size])
    "81c2c0294c78f9ec0a8639ef01410a81fe0b57486d2db8631d4d22742cb1c8d6" "fd18761c8cf346a9d5720ee4a2533b0cd6a7a8bd878d9d20acff7ed9d8652bd0" "",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7f763b22ab7d2313414b0863abcfd8be6d6248a894cafa3985de4aa1ee87dc76" "ebc3c6e344916a094060c73b9dbffccf4be05a447422a622d604072e21f82db9" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0d06ac6e1421355535a9373b31b4c6c694d6a90e27e88ebbc5df987ac06e167e" "de13524f04eb0a83af891ea98d10e5e75f7ecb56d8980251a58f64be8b610094" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7ae45a0991d805839663d60aaa3c1a21e95d2d82884cb29bd25e4dfbce5a0609" "36db7a4a9d8402bfa9bac3644c5222f85f12c1538671e96918d01c0d5752e4a2" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "162f42113d4810a627b1428cba24770478ac759a69c93f1f6308c7046e52e791" "1cb86054c4b59b486a1ac476d135afe8752728f43713d1061c908f1b6ecd6731" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6bb942cd82f258244933f967c95096c6f2224be3e42000044f6c48bea7494a5c" "828c49458b8195d317602ed1e50d073f750366fdd0fb2d8805ea2fb12c57e372" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Even.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ceae26812d0993921e96c02861e907a6ebb35bf8ba2a569b93520c1b49a243b3" "dcea23ce9f3d4d3171865b8ddece321fa8b7016725e8821b11f5b4d6c464508a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6c1946534e24d67671f05c36dae164a239acbf49a727475b6836e00b11869cdb" "635e2c9b6b9b2b3919e4d03d5465a968917f2a818cc061f5cf71634ddd86eb17" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "df0c39076c064a2919c5dfb2f1b73c9e9c20d6425039e0f17133c7356490d71b" "f709e453f6ff968b5a08f4cced87c6563ccbb2399ce07726fd6ab0c7cd616eb8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fee09fb5867ff9dbae55ae9aedbf8c3119464b44caae329e490a0286172b57d7" "7d6f949ba4fb394bafe9abbff8d1b55a99903326c2ff5c06f0442d5b71878985" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "166df2c4e8e3fe7a8b6ed7d65b3c5f2c17fc342de8c3d22bb46f54f70e4689ce" "27d3ce37d2427158d4c7b9d458ae803c555d55f579f44848054bbea895e194de" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c9cce8cecf22064511a309ecf5cd00f6c87b031ed8e058eb09fd699217fa8c71" "16322604a39ee2bc2c59b6433315f3b40ddb32f55011712161bc88252942c5bf" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQReord "twin" "orig" `Odd.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1527c316d83a38d43628ce583eb0dba56fdbb7a296b8a0e2e0f64f0e845a3ac4" "c3c6e9068e2b7d3a4ecb6fdc5243e5a0c8288a344a7bb8240e67e9bd8e382cb8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "19e46c2c75aba8115ea388c0f2c1cbc22f450d7fcd18cf31fd375cde30828552" "8213397c2ef94e997c72f414215b607d6a596692f727b2b7e92ad5c1e66271f6" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "cb38961a123f89cadfc53462a78ff4dbfea68b5aabccb0706ec0e7a5853ad4b7" "dfa3b4b8edc8219901c2f579d769c771b0b1b2a025b5efee3ed2807f303fa791" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.a.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "028b918c12d718298eb45d488de35571619507e7cd476a66da582e007caf017d" "f57838f5f203e4afcf753dad2e4838d6997dcb9d63acff9466417b8f1c8d1098" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5415f5f54a992d17fec6b65e0382c4577c3c7dfeb1d4f1e16b36448e23f299cb" "17f5ea7d767f19b280e22f1194210bc852a2d9697596daa4818a050fb08d2272" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1ebbb6b48539de5701c56e706a923d1db699775392773af34933912d17dc61da" "1d83bc6710567484d746c04b269c933d0fc03437e0b2348e9fd65b1b77b965e9" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ae750f0205d850cbda2dc93d13b6a498c0750ccf4b91d2bb68ddc3c414937faf" "4d96be5956fca8ab6be3115d25c1fe60a2a278d7386d5854a0554ea08f562f9d" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "bdd6c50576fd96d51f72aed7ffa79736ef61ca32aa8158e3a6b51d92c1750f53" "4b75385c7045e7852c776f7feb439b030baa2eeed7fcb618c66bb16e3bd36ccd" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.len "caller of a changed block" .pendingPasses (.root false true false)
    "a547241d523add64489dbe6d9bcffdaa0e11cee9fd2d77c1f8340fb5c5899246" "695f5dae0bcc913038d0207d1a25720b8c04b503998d8fff8532f99ff3b575b0" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.len._f "caller of a changed block" .pendingPasses (.root true true false)
    "4cf893733c374cb1e3d3193e6849687b35b597e8339b7a494c69912565a5b934" "50a97cdfcaf35fef5816074e6551f227029fc2ec898d320cd5252cc6bc41631b" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.len._sunfold "user constant" .inherited (.inherited [`A.len])
    "4d723026dd9e109918901fa7dad29203102a220255ced0743a93ddfe9d957c37" "37aca8f02a0d00b79593a83338b231b9e5d09242f9c63d1bb87fb61f457b6f34" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.nil.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "9a2ccaeac841163498ff30c729158232c2fde2948c593b0434359c016a391fcf" "2a2cdf86d8e40f14fc7ada709238857154b02786b47b3401409a8599de92e7ff" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "507879810bce736d4eaf20aa5fe5e0ff6a59641422f54f61cb7c7dee3614eb55" "bc4d5e04e34bebe33ec6ad6138a67ad9f50db6f517d43e758c0ee5217b23f322" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2ac559561fdbc297ca67c47f791c18079f104f9c745c0ab4b340dfe4fdd42b76" "7fb0e68c45047dbe22e7ab84978f97973a15c93b9c602ba55093eb18cde6f369" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.sum "caller of a changed block" .pendingPasses (.root false true false)
    "c7129e39f7bfd2043f3378c09e6f9d5edf719f73180cd4ae03f319cc262f60fd" "47bc3f1e51710dca412bb6623e1a0ba191a2365592adf1fc380b153ee76e1997" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.sum._f "caller of a changed block" .pendingPasses (.root true true false)
    "de86570efb9b22e8cf776caf80d968a5ad6fab401dadf8c32bd55dcc70c4fffa" "be6f2dc389f0b29fd4fdd7b810f119dde345541207ac51736c9d47a5572ebd0b" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.sum._sunfold "user constant" .inherited (.inherited [`A.sum])
    "94b9d8b062531a4a3943a576e713f7a9dd7512501e1c51f224b970bf400aa145" "c935f273e7c8fcf35c367a2c8d3e8bd32d7a87a67a83c3ef9d56437679008285" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.below "block auxiliary" .image .onlyB
    "-" "11a02ff01639cb2e18097f2819d5aeffa7863652a43edd53dbcb6a8a0ccc5424" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.brecOn "block auxiliary" .image .onlyB
    "-" "4352a61a2f59ac64ef865cd4c6fab60c7787fd23be1381a339f82f9ca28b162e" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.brecOn.eq "block auxiliary" .image .onlyB
    "-" "2ff628a276a05b418b962c3b16ad80d0d5893649c9d6e754a0c1a9cfd18de6a6" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.brecOn.go "block auxiliary" .image .onlyB
    "-" "a16b21c967e7357925412409876fd0316caeb5ccf96819e5726384bb6193cf4f" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.noConfusion "noConfusion" .pendingNoConfusion (.root false true false)
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "62097ef059b0e99d2abee440f8691386cb2afd54beb68a2cf3a336a726852a0b" "f9cc97e627e1497c57d63be38890d913085305c7273ede067538078438900f73" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dfa05d5f71d78161d48645eae61fe74366ed0196a36d361827c4b360c8af6812" "8db08eb4c7eb99558e309570ed6f1ebab46facccc9c9f247986ee5314891839a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `len2 "user constant" .inherited (.inherited [`A.len])
    "c7de97e5d77bc5368dd7623036851ed5296ee3ad2b92c5b103e44f3ac577d806" "bdf0926212f05a88afc426a31502759e60e89b57328df753113b6b0b04297588" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `len_succ "user constant" .inherited (.inherited [`A.len])
    "989a21960afdfd4c3e43ac3e8a38c11d77ce64f365deeeb593253f1358a8a82c" "73a88720f99e6d3aeb21fd4739119feb24dedc3907953b58eb2f56b9c23fd6e9" "",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `sum1 "user constant" .inherited (.inherited [`A.sum])
    "cb50a2624f5ad023677ab12de80a33455ead17b955e22e4d1d61e8efc413b113" "24533728ec0d092c42e24cb48c08bf5492a36ca75b4b6df239169dd405e80c4b" "",
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
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.mk.sizeOf_spec "sizeOf family" .o11aPending (.root false true false)
    "62da2845006a89ddbf242ec098db179137bec49fd23f804e990969d2cc35c5d3" "c47e4738b2c89a7c1a32c0466f3694cfa40cda5127f84d5b82ea64e19fd5eb5f" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
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
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
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
    "6592d6b48818dbd9faa38a6d7a6d6605e1d1b570be9bdcfec1ecaddef860dd5f" "a0e4f22c6582e6e416d45942fc12c02fce1f00e7769072e0e22d797a30cd5857" "type.∀.body.∀.dom.∀.dom",
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
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.mk.sizeOf_spec "sizeOf family" .o11aPending (.root false true false)
    "62da2845006a89ddbf242ec098db179137bec49fd23f804e990969d2cc35c5d3" "c47e4738b2c89a7c1a32c0466f3694cfa40cda5127f84d5b82ea64e19fd5eb5f" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
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
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
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
    "2cac384d7ac546c6d236663e5c81f0bfadbd463e1311d26cab8e0ee51b726791" "570ba64ccffa3d5767ccb526a4b75ab9075909142348fec3b0be643c830354f3" ""
]

/-- Entries 400 to 599. -/
def part2 : List NonCanonicalEntry := [
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
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
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
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c09085185737921cb32d9f4ae87bf398174cf7c6ff37b1f84018fa1232b60565" "982b163bacf09f5d93e21edf31f66e438929df26c44e7fd4d774a104633bc674" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1ef1eab0f0ea73af40b15337444a8317d7359eeab39e3123d36624c6a3612825" "6416e95e5dbc8465b4094be3510d9b9b262131e0e367fa41a838ce7b001546e4" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "19e46c2c75aba8115ea388c0f2c1cbc22f450d7fcd18cf31fd375cde30828552" "8213397c2ef94e997c72f414215b607d6a596692f727b2b7e92ad5c1e66271f6" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "cb38961a123f89cadfc53462a78ff4dbfea68b5aabccb0706ec0e7a5853ad4b7" "dfa3b4b8edc8219901c2f579d769c771b0b1b2a025b5efee3ed2807f303fa791" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.a.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "028b918c12d718298eb45d488de35571619507e7cd476a66da582e007caf017d" "f57838f5f203e4afcf753dad2e4838d6997dcb9d63acff9466417b8f1c8d1098" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5415f5f54a992d17fec6b65e0382c4577c3c7dfeb1d4f1e16b36448e23f299cb" "17f5ea7d767f19b280e22f1194210bc852a2d9697596daa4818a050fb08d2272" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1ebbb6b48539de5701c56e706a923d1db699775392773af34933912d17dc61da" "1d83bc6710567484d746c04b269c933d0fc03437e0b2348e9fd65b1b77b965e9" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ae750f0205d850cbda2dc93d13b6a498c0750ccf4b91d2bb68ddc3c414937faf" "4d96be5956fca8ab6be3115d25c1fe60a2a278d7386d5854a0554ea08f562f9d" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "bdd6c50576fd96d51f72aed7ffa79736ef61ca32aa8158e3a6b51d92c1750f53" "4b75385c7045e7852c776f7feb439b030baa2eeed7fcb618c66bb16e3bd36ccd" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.len "caller of a changed block" .pendingPasses (.root false true false)
    "a547241d523add64489dbe6d9bcffdaa0e11cee9fd2d77c1f8340fb5c5899246" "695f5dae0bcc913038d0207d1a25720b8c04b503998d8fff8532f99ff3b575b0" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (WB SurgSplit)",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.len._f "caller of a changed block" .pendingPasses (.root true true false)
    "4cf893733c374cb1e3d3193e6849687b35b597e8339b7a494c69912565a5b934" "50a97cdfcaf35fef5816074e6551f227029fc2ec898d320cd5252cc6bc41631b" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (WB SurgSplit)",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.len._sunfold "user constant" .inherited (.inherited [`A.len])
    "4d723026dd9e109918901fa7dad29203102a220255ced0743a93ddfe9d957c37" "37aca8f02a0d00b79593a83338b231b9e5d09242f9c63d1bb87fb61f457b6f34" "",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.nil.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "9a2ccaeac841163498ff30c729158232c2fde2948c593b0434359c016a391fcf" "2a2cdf86d8e40f14fc7ada709238857154b02786b47b3401409a8599de92e7ff" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
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
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "62097ef059b0e99d2abee440f8691386cb2afd54beb68a2cf3a336a726852a0b" "f9cc97e627e1497c57d63be38890d913085305c7273ede067538078438900f73" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dfa05d5f71d78161d48645eae61fe74366ed0196a36d361827c4b360c8af6812" "8db08eb4c7eb99558e309570ed6f1ebab46facccc9c9f247986ee5314891839a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `len2 "user constant" .inherited (.inherited [`A.len])
    "c7de97e5d77bc5368dd7623036851ed5296ee3ad2b92c5b103e44f3ac577d806" "bdf0926212f05a88afc426a31502759e60e89b57328df753113b6b0b04297588" "",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7f763b22ab7d2313414b0863abcfd8be6d6248a894cafa3985de4aa1ee87dc76" "ebc3c6e344916a094060c73b9dbffccf4be05a447422a622d604072e21f82db9" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0d06ac6e1421355535a9373b31b4c6c694d6a90e27e88ebbc5df987ac06e167e" "de13524f04eb0a83af891ea98d10e5e75f7ecb56d8980251a58f64be8b610094" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7ae45a0991d805839663d60aaa3c1a21e95d2d82884cb29bd25e4dfbce5a0609" "36db7a4a9d8402bfa9bac3644c5222f85f12c1538671e96918d01c0d5752e4a2" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "162f42113d4810a627b1428cba24770478ac759a69c93f1f6308c7046e52e791" "1cb86054c4b59b486a1ac476d135afe8752728f43713d1061c908f1b6ecd6731" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6bb942cd82f258244933f967c95096c6f2224be3e42000044f6c48bea7494a5c" "828c49458b8195d317602ed1e50d073f750366fdd0fb2d8805ea2fb12c57e372" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ceae26812d0993921e96c02861e907a6ebb35bf8ba2a569b93520c1b49a243b3" "dcea23ce9f3d4d3171865b8ddece321fa8b7016725e8821b11f5b4d6c464508a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Even.viaRec "caller of a changed block" .bare (.root false true false)
    "5b91b50d4c4fe9b970fc85af1f8a09eb7b0012c72d86d62f07185f6b9f63bd99" "00cc400d69c397b1984d30f194f57844d20749e702925c9363727765bd20d09f" "value.@0.λ.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6c1946534e24d67671f05c36dae164a239acbf49a727475b6836e00b11869cdb" "635e2c9b6b9b2b3919e4d03d5465a968917f2a818cc061f5cf71634ddd86eb17" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "df0c39076c064a2919c5dfb2f1b73c9e9c20d6425039e0f17133c7356490d71b" "f709e453f6ff968b5a08f4cced87c6563ccbb2399ce07726fd6ab0c7cd616eb8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fee09fb5867ff9dbae55ae9aedbf8c3119464b44caae329e490a0286172b57d7" "7d6f949ba4fb394bafe9abbff8d1b55a99903326c2ff5c06f0442d5b71878985" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "166df2c4e8e3fe7a8b6ed7d65b3c5f2c17fc342de8c3d22bb46f54f70e4689ce" "27d3ce37d2427158d4c7b9d458ae803c555d55f579f44848054bbea895e194de" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c9cce8cecf22064511a309ecf5cd00f6c87b031ed8e058eb09fd699217fa8c71" "16322604a39ee2bc2c59b6433315f3b40ddb32f55011712161bc88252942c5bf" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C1 "can" "src" `Odd.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1527c316d83a38d43628ce583eb0dba56fdbb7a296b8a0e2e0f64f0e845a3ac4" "c3c6e9068e2b7d3a4ecb6fdc5243e5a0c8288a344a7bb8240e67e9bd8e382cb8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "19e46c2c75aba8115ea388c0f2c1cbc22f450d7fcd18cf31fd375cde30828552" "8213397c2ef94e997c72f414215b607d6a596692f727b2b7e92ad5c1e66271f6" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "cb38961a123f89cadfc53462a78ff4dbfea68b5aabccb0706ec0e7a5853ad4b7" "dfa3b4b8edc8219901c2f579d769c771b0b1b2a025b5efee3ed2807f303fa791" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.a.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "028b918c12d718298eb45d488de35571619507e7cd476a66da582e007caf017d" "f57838f5f203e4afcf753dad2e4838d6997dcb9d63acff9466417b8f1c8d1098" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5415f5f54a992d17fec6b65e0382c4577c3c7dfeb1d4f1e16b36448e23f299cb" "17f5ea7d767f19b280e22f1194210bc852a2d9697596daa4818a050fb08d2272" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1ebbb6b48539de5701c56e706a923d1db699775392773af34933912d17dc61da" "1d83bc6710567484d746c04b269c933d0fc03437e0b2348e9fd65b1b77b965e9" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ae750f0205d850cbda2dc93d13b6a498c0750ccf4b91d2bb68ddc3c414937faf" "4d96be5956fca8ab6be3115d25c1fe60a2a278d7386d5854a0554ea08f562f9d" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "bdd6c50576fd96d51f72aed7ffa79736ef61ca32aa8158e3a6b51d92c1750f53" "4b75385c7045e7852c776f7feb439b030baa2eeed7fcb618c66bb16e3bd36ccd" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.cnt "caller of a changed block" .pendingPasses (.root false true false)
    "9d8bdb0bfbdc878f109d4e9acc712eb7e09b04a0fffcde3fd31b9495e9117212" "59050a7372bde4f04b20180aeb6079363bddb6426d7072d707aaa198d04e3a56" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.cnt._f "caller of a changed block" .pendingPasses (.root true true false)
    "737d9847f6255247ce5ac946c55c9a631b41f125be5e7933ab807eaeb40c54d4" "131ddf13c0a7382cfbb24e6f91629ec18d77ce32f956ae01b7ece26c2536cfbc" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.cnt._sunfold "user constant" .inherited (.inherited [`A.cnt])
    "c7b4b2af419c9bc6cf2285fd0b048dfaf8e422835c91f0e96ac44b85891a449a" "d9fe21c411239138bb00b39e905cc037afb0fcf3767936bc8946d3b0bce4c75d" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.len "caller of a changed block" .pendingPasses (.root false true false)
    "a547241d523add64489dbe6d9bcffdaa0e11cee9fd2d77c1f8340fb5c5899246" "695f5dae0bcc913038d0207d1a25720b8c04b503998d8fff8532f99ff3b575b0" "value.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.len._f "caller of a changed block" .pendingPasses (.root true true false)
    "4cf893733c374cb1e3d3193e6849687b35b597e8339b7a494c69912565a5b934" "50a97cdfcaf35fef5816074e6551f227029fc2ec898d320cd5252cc6bc41631b" "type.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.len._sunfold "user constant" .inherited (.inherited [`A.len])
    "4d723026dd9e109918901fa7dad29203102a220255ced0743a93ddfe9d957c37" "37aca8f02a0d00b79593a83338b231b9e5d09242f9c63d1bb87fb61f457b6f34" "",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.nil.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "9a2ccaeac841163498ff30c729158232c2fde2948c593b0434359c016a391fcf" "2a2cdf86d8e40f14fc7ada709238857154b02786b47b3401409a8599de92e7ff" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
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
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.noConfusion "noConfusion" .pendingNoConfusion (.root false true false)
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
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
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8506418545e3a8f96e273e6ec1054ce2a27cb455e5cf544a96d3ba1d8c4c2449" "36954ffccccd1451205a7cf2f8d4a2145398685ff143420f3f529a32ac5b9ac7" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "cc008ce1e8d15a1fc4ebf96569c3367f1236054d8fbc115679f75c1f4f329293" "ccd3ec3dcc20fc1964201f45b7bb48e92ecf3d3fcafbe655715d44a57fa59ea2" "type.∀.dom.∀.dom",
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
  e `Tests.Ix.Compile.Twins.Proto.C3b "can" "src" `X.casesOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2efa4bbd958d459004f3a93a7400ab7ba98da1688554df3e17a1fcbd2439a636" "757541206477da5f1aed7a4f6069168ddc96ad6897815cb4215d140048bd3c09" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C3b "can" "src" `X.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d2d89c26f75ac727358474a7f94e4f3243cda39617619200efcd322e701c98d3" "8c91a944c6505733a4f525d2b3dd0dae7c5adad9af49ced202f90c5b8ba73866" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C3b "can" "src" `X.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b39239fea24258438423f0a464b8cb32cacc283668fb10d77328c32e0ecd90f3" "33f4863c8256713a69dfa6a0a8444028a3702f46e37f9eee0cd6dd8398b1a1e4" "kind",
  e `Tests.Ix.Compile.Twins.Proto.C3b "can" "src" `q "user constant over the block" .pendingCollapse (.root false true false)
    "fe79fec6d1b0c2a7a6511dd85a3ae5407ce9f77705e235b76cbdab970db69667" "51c3ddba2dbb2ef3af1d9d7fde23619f8e39166150e8336714a58842e571262a" "value.λ.body" "theorem over a collapsed Prop pair",
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
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.mk.sizeOf_spec "sizeOf family" .o11aPending (.root false true false)
    "62da2845006a89ddbf242ec098db179137bec49fd23f804e990969d2cc35c5d3" "c47e4738b2c89a7c1a32c0466f3694cfa40cda5127f84d5b82ea64e19fd5eb5f" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "001293f7f7890c8941d95ddff31e3d9e6a4bba42204d00a8a9da983677fec23d" "c6f4c9ef77bf9bb5326f5f668dae16b86df01b495c9565c39c55678c2966f57d" "type.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1ed4553a14482ddca6bdd6edad60854958ec2a5487f219b7ea2746affb1e8b0d" "f5d32e768429ef56dcfd352f7c03888b2524947c48be691507328bf134e6bd55" "type.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.rec_1 "block auxiliary" .image .onlyB
    "-" "c7f59215d14ef2b35ca5bbfd749f16dee94336156e2fcdfcca2525ddcca640c4" "" "§4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.below "block auxiliary" .image .onlyB
    "-" "b0782747033c62bdd93ce0f6e1e54493b17cb7634107527fe80f240ae973e2fd" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.brecOn "block auxiliary" .image .onlyB
    "-" "922bbf33b177831e0ecbe06d0fccbd2b40428e64db7e38b38a64fa633bb10e59" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.brecOn.eq "block auxiliary" .image .onlyB
    "-" "877826a718d6a20dd2f42c33cc100acfd2c9e36232b8656f864a043c75463cff" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.brecOn.go "block auxiliary" .image .onlyB
    "-" "f280f4cd05ec7ca01893c2aceecfe2a89b1f0a1cf31c8c06e73102cfa9d1bc1d" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.noConfusion "noConfusion" .pendingNoConfusion (.root false true false)
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8" "value.λ.body.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block"
]

/-- Entries 600 to 799. -/
def part3 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.noConfusionType "noConfusion" .pendingNoConfusion (.root false true false)
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4" "value.λ.body.λ.body.λ.body" "§4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "62097ef059b0e99d2abee440f8691386cb2afd54beb68a2cf3a336a726852a0b" "38a0af07b0206343309225612792bd3d2c1d87b1b9b1e9c54c9dc98ee08115e1" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dfa05d5f71d78161d48645eae61fe74366ed0196a36d361827c4b360c8af6812" "239c0dde0c354de1bb9ac55d18211c95299ec5562eb98e636350c6c2a02a7730" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `useRec "caller of a changed block" .pendingPasses (.root false true false)
    "8f6c02851a5204712eb85557310e53ceaf31f54c90254c741312c0e780fe327d" "7aeedf4f57b16518b3a1bd77269d310bfd4a003388820b7140099f3bf0a6b60d" "value" "raw `rec` user over a block whose nested auxiliary evaporates (O2)",
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
    "3bb054b90e0582df85c92e346ffd1d629209328e85a6d36616531ab5fcb306f2" "57f0a168d63b1d32b79e42d5555990e19705308b46a8b55bcd0cf851bf72feb4" "value.λ.body.λ.body.let.body.let.body" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.toR.match_2 "user constant over the block" .indPredBelow (.root true true false)
    "d4fd427576f9b54f7c46c99776b0c0432d74ee8979de5a39e01c7908f4003eff" "e58d497a225b925ad0463e367f3ccc3aa8cf54942cb1d65a4c0a333b871ac065" "type.∀.body.∀.body.∀.dom.∀.body.∀.body.∀.dom" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
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
    "be619db32fe0d4ea5d256ddc9db477cc9769a6c29e9c372778aeb990a0b9bce0" "de3bfe5ec6e826c1294a8bc7e4b1f1d922d694dd06e948ed511b101368974fd0" "value.λ.body.λ.body.let.body.let.body" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.toR.match_2 "user constant over the block" .indPredBelow (.root true true false)
    "4e63421fe9885ad5f4197226213dda9164e3c1c9f129abe4abdffc5f35607998" "83e7e57cf112328253227ec833f8d34b9bb765d6226c0a09b93eddad1ab4928b" "type.∀.body.∀.body.∀.dom.∀.body.∀.body.∀.dom" "Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
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
    "3fd79d6295e2750e0d18de5b6cd9d75489830c72a379ee3ef66ee712b6079cbc" "84f78aba9e58fc4f7ef534f4d16a3a28a83c245dc7fc5af26d49996a14aae2ca" "value.λ.body.λ.body.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A._sizeOf_inst "user constant" .inherited (.inherited [`A._sizeOf_1])
    "a1d896f3080d0d531fd0d0a1f3dff7f06e256f89f2a75b440d1cf5f0a4b58ac3" "2462eb84718d1b3ef26608abf899e63715c7bfac5952bffc13bee8cfcde4ebec" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.a.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "204d851c73e29e97ed79ec34676ab30109f86d80d438d3249f722938d7f5d09f" "5e5494874f76ac7bc736b95584603e0175f2a761bfc4ca57fd9be1490b17bae5" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3635caecef138b7c291e8f63192d852092f9cac21a5d58a4f8576017fa6aa6ed" "48a7790bbb69f0e5f94e8d85d74044e6d50a941716e683f167ba63c6b6d81c82" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3a24af0ef3aebf3693c541e110d8abc41d05a3e556b6f43afd7cf6b126cc74ad" "3cbc2c01dafd05389c25dba48d9578c266b074b5525ea1b3f5c01892149316c5" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c45597871edcdf0f86bee0605379bf84d5d1cc2efcfbb16a0454d45951406eac" "d3eaa8132eb775787fb424b4a84772671a1a2469e54406d226549142a4052d4d" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "445126f1411307c03771a7219bf1400511821f4513fe3ebfb52df5d16cd0fec3" "5ba59c80129a46b3a4561edf5662fad5a6af6715b3da5704c0abcad98599cdc8" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.depth "caller of a changed block" .pendingPasses (.root false true false)
    "6b89d0d2e6de373c3c955e16a54e64d2a36d38bc13bbc28810893aa3515c811f" "d84c4a25e60038f053c7df40bc4661484185042e1ed1df5baa018c59c6c8c861" "value.λ.body.λ.body" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.depth._f "caller of a changed block" .pendingPasses (.root true true false)
    "8fcb310ec4de65102343f86a9581d01f163665862a4716bd49277468697d434d" "140a043f9fb29044818639d1621138d4e6ca9abd3e7c7c7cfe08c3375479048d" "type.∀.body.∀.body.∀.dom" "structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.depth._sunfold "user constant" .inherited (.inherited [`A.depth])
    "e28d8f1382b9a037a12a52ff4416a54433b84e70baf9923a0f6fe8db63965460" "2981633121c3b553f16b5d2e13ec763c8dbfb2f049c4de6170eb7f284c2c718d" "",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.nil.sizeOf_spec "user constant" .inherited (.inherited [`A._sizeOf_inst])
    "63d898cf8525d6be264fd0d7010e8997f947bfabdc9e9e9f2fe2baf88f9105f7" "4aa7bce1a4238a4f2406f8e960987c9f8f17c09ec2bc9ca24a485a6c5b3948d6" "" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a01edc74ebc4071abdd7ec7f35cfc38da692245a9764e5d98f59204dd902aa86" "95cfb2f4803902b089395617c9b16ee347c8079b759aa28d9e4348baa1f27433" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6b0e9178d2044078f7ef5ed01f0c0deacd961e2aa43ae44fc31ca2eec9026e98" "561e81efbc0c1ce6c990b30966ec94db6ae98c476a0f6110fb1f0063b0184f95" "type.∀.body.∀.body.∀.dom"
]

/-- Entries 800 to 999. -/
def part4 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.below "block auxiliary" .image .onlyB
    "-" "cb6f32f746d2315981cd805fe676f0eb97ed44a21fa27ae8eddc4e00948128dc" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.brecOn "block auxiliary" .image .onlyB
    "-" "7b6b5bb433c778b54f1c01e9d9a86314d23bcc306b6396eaf86926b544e9174d" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.brecOn.eq "block auxiliary" .image .onlyB
    "-" "8848be1857f85e351b18ea9190b9cc81d88fba40571252e6605a80f7c495be10" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.brecOn.go "block auxiliary" .image .onlyB
    "-" "978d0334cc26b28bc30387abccb3e498a0d21e0f60a906b896c5a1c66cb8c4e6" "" "§4.7 (b): exists for the Lean block, not for the Ix component",
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
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "41442b55e8e872dbd9d0faf5ef6f1b0b28534ce26cb6f063e838411cb6bab1ae" "ffca40a88ea9cb00a089e9a2dcd0aec1e5d73f16395937a5ce850577b0b2b7e5" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `Code.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e3094f26ecc5f43b146eb29ff7ba98bdb47931686ddb192e5671167a203309fc" "8702fee56f282365a1d7646cea1e7b603e20a0f41a76d9924c98014bf0a214da" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0f0e51c988f02681178841819e29317a0e09cd7d6318abd7af8224e7a5200630" "a5c030b39f7f70cafa0cd58ab1ae2d98493a5d59f118b738df2dec63de1537e9" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a73b1be089af845be9889d556ee8a427a68750a899ab8f922238e48ed0453a02" "5a3680a51b333f9760f5c219cdb2ed05c4f4a15d410a5b22877a79d198dbf1c7" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "6fea987cdf441af8b64477a6b6b65bb0189643aac9fcd87f9eeafb0259f4cee6" "8cc2a715911397bbd6f33d8d0f0bd8472c8c70a28a62c388b608200f576535e8" "type.∀.body.∀.dom.∀.dom.fn",
  e `Tests.Ix.Compile.Oracle.Lib.LCNF "twin" "orig" `FunDecl.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d236bddbad7f98e5b583eebac82263d2ff20bd3fe44c1f827853816ca1b94d10" "3fefa4efc285ed214c7e688d76ff323a92c8b55be91808fbd176bc406829e714" "type.∀.body.∀.dom.∀.dom.fn",
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
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ba4f9388a1c3ba73825cdd16800b3ce735981737db877028c987605b1e4489f0" "4a2c972cfc23dccf1b281e3bf8af965727b7a7645ec57968bbc818eb902788d2" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitPred.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "354694e14c1bcb2919e3616d6cf78482872b39bf60d560446edd9d9c1cfd4f19" "3b948c4698a62e8457471580bcfcf12143eb256f6d3bb9e4552f7861c4fa7883" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "9a8f3ed5e18e48afb2f670c84372442b702aeaf556641a6b41e90991e5469692" "1202d54db7c52f629fcc2ce8af044284520d1ac36e6b5ee29be3597c5277d9a1" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "37269622b61335e50bdbab807dd1137214510e067ba5c76cd2bf4da2b43b6668" "2d3792c9d83505a0c6c93bdaccb2a577184b9d6eef77e72c05c2e5bdb9b76d0b" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "056dd4cf529e7316f54ceb273de18a8d8a386ab581cc1bd307a0f34669091f25" "0a7c4be7e7c912bced588302603eba647ef251deeec83ee4160ce623be44fe29" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `CooperSplitProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1dd50a3e97f1e4eeae1956d5937d50008d26be118b14aeb456cea5df665a1b6e" "391b0cd1d90be887211ab066e4eb7ae66912bd16180c771d1816f2e53f7cd166" "type.∀.dom.∀.dom",
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
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "17280c4739ca677cd53ecc779a6da7d2c6384b77a0b3218caadf331936c7c10b" "45e3af2aa3b4a596e04d62f7c97840029ce990af81d81bd8b3440431d7801c2f" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DiseqCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "90f5648f27df98e6bc543e9136d94a135c2ceb210998a949057f577cab2b58b5" "313bc771426d8a2e24acedb9cd2d8e762febd15202a425cbc246460d7c8e0bcf" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ff6b72199ba6e9e31cc9ec9e87090f79d3cc16279183a215efc2b5ff43b3bb5d" "5eedebffbfb23e0440416d8d4d120a5a3dd5baa7400a628a15a3e1eb782bc68d" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7b5caaadd0b2d803f938f6c26fb9194f2fd988d01b891c1a644494d72d38de4c" "08fc264aa2283baac6b709d09e65c7ab81d43d1f93500a9cb9fe813472cea92d" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "9da85c267d18ba51b659fb43d13cda1a3821673593da2d1c091c0b9eb243935d" "30b9476f2d5bcecadd4b116fe56dab43355f3640c629c9bc9a853727dc7d0b50" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstr.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "26c82ff8cd5eb8bb29ea7c85301fe75462c018b9c96758a30cdffcaaa5a9d1e2" "403ddfffa5c5cf4bf0cc545da86388e5ab64d362488a025ac2414158f3eace9c" "type.∀.dom.∀.dom",
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
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fb05aa5c3213d21a2767a0bd6db6a0034e5c3b8cef6ad1d08bc8b1ee9e1acd45" "27eb7b3aa2eb3db72ea55adcce2f8b0bbd54867acc9550abad2b6bebc756d57a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `DvdCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "50e08503d21b7353534e822727373ba426a0e2647681dac834d03000c5c23a18" "75a6d2eef31356153cf9e368931ea699bfcf421989e157239765bd40f69aede0" "type.∀.dom.∀.dom",
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
    "-" "acdcc1782c380ca9d976a38f7accda7d8936710596dc68cdeb1c4bde2039e79e" "",
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
    "-" "1d27623537ca8c5da789cb376414f0f12d6c6b72c6f18dad512789a31df1e0a7" ""
]

/-- Entries 1000 to 1126. -/
def part5 : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstr.brecOn_9.go "image-kind head of a changed block (its Lean name holds the image)" .image .onlyB
    "-" "f6c3ae6304151d152ff091b118a39bb287e3c5fa22a5eb8f080f66b07aa5451c" "",
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
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "c3f107e62f266d0f9aa63bdceae8b7a2848b58238a77aaabf3a864ff51d1b07f" "dc5dc643273b3b954f0b23dc05318e4c12d8b35dba2f116d007d56637a096566" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `EqCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "bd9bd0068f1207728c6dbf58446dbbe4d929e124b9550a990a511dc6c5094ab9" "a67c441b3a685bdccab3525a054334d3f89fd59e8c24cc3bf5f6123992425cd8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ae5bf300edeabe290782f596e980ab4951052c4e212e79e3bb4b8b804ebcdf06" "f6a9babe231dc096dff36b009b226d8da8de9e612922558804a2bdeee9f42818" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "79fe2f58e6ac07c0c2b58f90913402ea5643ec5cdad7addc1851108f1a47f3c9" "07c8b327857c52247e04ed6a2370a3bc192e667f2673ac321ff52c0b3cb2cd40" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dc8c9ff4e0d365971ecec6cfa489b1da5edbd6a71c84a4a873863bbd3fa8db93" "65c853d1bcdfcf0f52481d9adb1c5fc916886788f273408d11fdf3e7bf4c1567" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "936a859cd6fdbfc9a968997a504affd74c22f61f804976b08b94bb0a87d7643f" "9d7f05afdf96adf04d0568c57e344312af8a5fc4929433225b4d8c9d3bc027b3" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3c71f38c5595978e6023e392572780a65ba7d9b34bdcd657fcc8b82165d5f8c3" "3aa42b6a281c009fff8fea546c3588bae76abee0051cedce961b2a6fcfb040d8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstr.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e6ae57b9c8d89dc93a1fab841963905f3691e6a10adbb087cebb24ecf4e63f79" "c64466bfbb951ff69b0b2486d80661198ff01fcdb460455267c696cb371dc025" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "62a88a221a3f970bbb948c4f9c4da334f4b94cb8ef8e0692fd2fd11d0f537e0f" "ad44d38a9bdbbf886be503a74cfe501389dc8d2b25f828486da0dd67f8e4b362" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5f07e30d3ca221ed4cfa6567c20646ce348ea0677b5e6e044f9a16b68defbbd6" "2cf5bf5126a578762dcae80ac0da12e514e0d99c811105f598f7cc7a31a88e50" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "eef819e5b3a1f23419de8344465c75450546960adc656a1d38ab2e97b87ee488" "48e5937f9e9948c2ad7a9016f4b1127eada0f49355eedf5c7958ba339116bcb0" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "91404fbe5acdba843e4ea2006e4c902e8404d9188988b7488a1750ccff0ef42e" "6eedf7ce146d045c89554d2449ed79155f99d7bdf07f54b04088d2ca3d195219" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "abf652066c9c21a5210f25b0e809e46ae54a8e0f5c1596b3e1ff2a2bd43b84a3" "343e61c7e9f3a1dcef42c55cb01e11dd62d98fc67e8c2e4497deeda8ba846965" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `LeCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "255ca996c2364a0e8803608738617692020138dea759e00a2a712a9029c26ed1" "5227e4589297bcab8f9111ae638214c24d7f2d59f027d7e82b3852bb062dca08" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e35a37ebb6a0329d24019dc5812df34d604d58caa296ae02f2ecf866f172cc5e" "e420dc3c298ea3454f1fc065e750217ed05680cfac4583241f18a76f841598fd" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "ff52ea3466eac42a8a6a66b6cb7c835a4fba5b65e97f9cb786434d3d8935b7e2" "c9f9bf650e157b3d6b6fe5a89de6cfd30c06b6942e9e284c044898624c59a6c6" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "0e95f06b9ba7c91830c16da14db0ada6a156fbf377e30b38c342673094a5464f" "9fa7ab20301e55ba12280548c460edbc43fb418affe0d96eb5efae008f5e1aaf" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e91f8a6b8084c8fe09bb15c106a5f0cbf82fa573826c75875fafe97ee68c886f" "d4de424b5a15b597802b77a2576a6f8d978e1d53017b895d84a59265ce7fb3a8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e1b49f51e12a215d5416dbc1d48b45425080b97430bf36e1ec07c3e783f9ae34" "2030131c7a438172ecc23809936f22ab26545083e51b34a3b645a58c5a7dee3e" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Cutsat "twin" "orig" `UnsatProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d69e6440907a54695f07b081350a18d53ed8ba143ed58df17cedcb838cbec2a0" "0cdb34f88087601f72ef14e4d01f52b37ac899a74a2142151a45cd80d6ef42ea" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "85a24f55398a917aee85d4a010268491ccdd46c1c6c910b170a42b4b498ca41e" "2c09df2384c14d3e81a80104c783dabbb4d8f78671581c3c5eea8fd387a97e55" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr._sizeOf_2 "sizeOf family" .o11aPending (.root false true false)
    "e2a92f924f397ee61827e23616fd2e88e68658d4b276dc9934eefbc27bab7535" "18a13d99f62f9cc40cca165aa59fdc9c0e530ec8c516dbe7d0d07b0e65e58353" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr._sizeOf_inst "sizeOf family" .o11aPending (.root false true false)
    "a68dfd8ad37a0d7353c831effb9c40edcb120a99e3ed2832e29aedda3c2d11c1" "b9b7d186c4be9795e57c3fc597a3a224a3ef7de3c0c22a98bc8002497822e858" "value.@1.λ.body.fn" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "767a78bfd0d31e8f4dca91a442d33430ad8c9dd4b96e0856aa348d41c75082db" "3dd9a4d1621440c44ace4ba0efc1f1b4ba42bf1d69bea4281b7427a227a1ea8a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "dfbf34e3a21897de93415ce74d53b1048a9f6cfc8081eaa5392aeae6490e93e6" "6df63b5569052b511a3fbacb9a1ce705162e93bc1381a82d0d389f13a48e02e0" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "d702ca348ec82c3cd8a702bb8e402de358ea76f34581912d20bbe1e2d217ffbc" "a4764bc7ee1ef3442a6b98a43d74f6b9c06e15e802a6cb35a75556340fd64c7b" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "f2460b7d68d84b2ff64c503aae835bbcbf3c4fd1664e57747bdbffc3b35d1d27" "7dfbea026720a178d97edd529d1cf2e1cca832e76097645eec163b7af66ef204" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.mk.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstr._sizeOf_inst, `DiseqCnstrProof._sizeOf_inst])
    "078ebac4ce215824bf4d84f657ee911a63ce9f4d48b014c1e9892dea048d93d9" "030ade7b4ce8013572eb45899592a618edb900ff9a83a5273f72b95ac1206874" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "de41580be1bcfbcba9dad929960fa2597a0137ebfd9069f5d90bf6384675c56e" "9ce9d1e69fb16cc61a4c404d5606c4502c571afda532ee17163278688dc2931e" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "9deea21239de4357d1b95f9fd6c7b57fc6e24206749e71a956455bf4c4028ab9" "5ed957a8bc64702a8694661487bde2ff9390c6019ac202df6d748fc9a7fad1d6" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof._sizeOf_inst "sizeOf family" .o11aPending (.root false true false)
    "6e544b31bccfa51cc310fc586f38ed01db34a47fa05118d1cc9341ffc1f8728b" "8ccbbef4f9e8665b6b1579682c69247b860dee77a16e841690aae6f26414f218" "value.@1.λ.body.fn" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a6c3871f4aeccd4f83f273d6865cfcb8347f8eea07303c600595949d1426b555" "2efa60b590d236572b0073a9f6360c4d77e18fd807b19824eac7dc5fd789c7dd" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "5c544d1d3e938e54cfde5b23954ca81f0f3c5d9bfd3f4087a8a53af903d2c2f9" "e27cb9c35da6b83777a2270569ee3583fa56919b3283c832337c04107d4adf5a" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "87767078c157f3869cae4cda776e6a3005ea9328a981af59d218cfbc7e1685b4" "8608c061ae2f1b02b311f574a2a8a33dd3a4377c7672a77a2d2794cce11e61d5" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "191ab7f135b63d6e256e86b7d1add71a1174809e22a97687c34dea4535f046c3" "6526eed039f32a244c037afccf215b7a3da38e28211a356470d9a0a9847ddc2c" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.core.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstrProof._sizeOf_inst])
    "b85f2224ce8fdb1e90db7de74051355afe8a230ad0fe74dd3e509058b7d59265" "56196a0b30bfe618f11d318afb57468f6526eb5eba04dc8cf12c758fbaeea80f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.coreOfNat.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstrProof._sizeOf_inst])
    "90deab7b8ec8624dddd1df088de74ed6753d9fbecd48ad87b6e9e1648b8a5e89" "0166ac60aa5e80656774a62fd2ab843c40bf847974f83272514a71ca79e877f6" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.neg.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstr._sizeOf_inst, `DiseqCnstrProof._sizeOf_inst])
    "7d1085991126f6feed29521796230238703df6434cb4dbe5b55f366298221e53" "b4c894e1932e914f5b700f60b8fd8c6a10bb466e8dc68781efab7987adcec0dd" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.oneNeZero.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstrProof._sizeOf_inst])
    "c1b7f56c7036d87c4688486af4d27ccdf403beacbf4e836aa9b7ea881c12591d" "152e62a2a546b0aad9ad44bc9faa63d00fffde52428c3db97d80cacac0c0525a" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8fcd86d734867a58a6f5ba3485949ef43ce420b807a489ef957678bb7f767045" "69b4ab708e01e0bb41581133956c97469ef444f0232fd55bae9b2f1693d42151" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3790a45d2c5493ef6300397d842682a2c1bb5539dcf4e191bc639d34a454d4be" "ae56f9710b03f3b0ceab6c55e8eb68f323a52935dbd2c29c536728870b8ab3ed" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.ring.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstrProof._sizeOf_inst])
    "9f4deadfded52ac4e0eabcc5245b97b9552d3f6710121438e52a4221b12a387a" "7f1d70fd294871f0fd020356184a712f97718c59a3af31f6f4271a1098bf9eb2" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstr._sizeOf_inst, `DiseqCnstrProof._sizeOf_inst])
    "011aaf3cb0725ee66afc6d5b53e7782008e8ea675fd94feef58ae2d685d3cee0" "41f01138973442dfccb87196627440681666c9ef8cab96a798d2649f076b718c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst1.sizeOf_spec "user constant" .inherited (.inherited [`DiseqCnstr._sizeOf_inst, `DiseqCnstrProof._sizeOf_inst])
    "c328caba9b28bc991619d28898951e676cc9bfc2d86dd1218af90c8003d99d42" "d652625999dac12f91dec772cfe880f0cc34862dc92543577064c7f414fdbb77" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8d0514132628bc48ee7ecfb3336cecd8f76398d475ace232520fc482a25cde0b" "eae37b6b1534d392e90b8e5026a68a2fed91350a91b918dce737ca2e87ac4291" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "3b5e0950ec8ac612426551a7f9ca5adbaaf406c1c4186e850436bdbb69407fa7" "a332515bf1d63c7187f7c1d4cb61c9e80dbc34307242325919ebade97f365c98" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "52610ea68f84e3c3e36df3a3344021ad40d7ea93831bb7971e07b566f58381eb" "72ec487b37519501ddd6aa2e1c74b9ef11784a047eb6d13235e285790e89179a" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fc985528b9f65c1c737c5dec3c3cefdb75f3e7a1dcdace2e56165d55ebf80bbd" "c415808bbacb3bbd4a9cc02abe4d0fcab8e67c2beec8bafe0df1c8e7ad432c08" "type.∀.body.∀.body.∀.dom",
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
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8f3449025976a0959d6409e896e8cfa124a26af5c5cfa8e0e9da20b08439bcec" "fa459d0fd2fc854e252642675239669ea5f9ff1c46c4be5c743d43ff6b366599" "type.∀.body.∀.body.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "8916cd2e47de8152ba1c5006f521f0d5c6e018e996b3a12b029fcd8e3e1509cb" "95f4e1bc9852bb779edede8da30dbfa07911cf32773cc641698268ca6580402a" "type.∀.body.∀.body.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr._sizeOf_1 "sizeOf family" .o11aPending (.root false true false)
    "4b6555393b8582bec0208dd4d4b426976f7c1b76e4b849da5969ced982d1f170" "b9d2c07c6731bf9cc87846259ec9066aa92e262386831c2c3aed10a32680e826" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr._sizeOf_2 "sizeOf family" .o11aPending (.root false true false)
    "6d3da884671a32df7f6d48437ca32ea99ef2ade30c031f2e32a88ce03865ae8a" "91ee268e9a4f9567a40946537b3da35a1aa7bf7d51e3717092a90e231eeb9e48" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr._sizeOf_3 "sizeOf family" .o11aPending (.root false true false)
    "1e09f92eaa14c13b438d30e2f0b19f39086586cb9fc76cb511fe797f3c9d58ce" "a1bf4ef62ae7de9cf0707b58a29f40e0c03b3eb4c6a7b41573d28c1c9da92e6e" "value.λ.body" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr._sizeOf_inst "sizeOf family" .o11aPending (.root false true false)
    "21a3c8f414efd691ca6bb6d32535a5dee694108fd5b93ec2ae0f398e136e34dc" "36604e31da0f0832b159815e160e328ce311412848e5f0176dc4175ee05f8606" "value.@1.λ.body.fn" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "9695dec5fc6c3035432db8179f17845195a29805df318ffd4bec5951bafc9e77" "efe1aabeb0d11c3405ae229d2d9e4bb8e1fe963ec9e45c40cd818c4d9bc64316" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "e052e42c2dc97a91fe0aead8dc13c53622cf56f0f2cf8f66ed5eab8c8fdba388" "c1d4737b30f5a102fa29c5204405bd7eab57c96b753d04788b3f12b9b091bdf5" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2e35539b3419ff56e6433032f6121c9676ecdb7bd7877b1e3936062c8ef759e4" "34d4de9483a3f7d21627eee4675e329269a6f0bf7bfc161dce9360719dbe52c4" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "12b60daae001ce3d044d05aa3913b87210b0b1945162bb3b38926a9408f6a012" "ca0e37231a9d22339130c64cdbbb7eb99fdbabd7faaf05b6367d2d9cfb8d6d51" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.mk.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst, `IneqCnstr._sizeOf_inst])
    "4fe3cccb6ddeaa49f11cc39b7ae31d30432fb38329907e56e21ed29907b72627" "200052737c6856f2b2572e9438140525cfa877042e649c9a51eecce4d4656e9f" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2e8da0e2e6fda579baca7f7b18b2831e02617cab499c9b6b4027f54b5cd96b9b" "9b7ff36311afa5663ff0b7c142c0e57e5d2dae6fc5e20a2ba4313a737d5a3ce3" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "a3ac43469c10d7d49b43fcbc191c9d02d1215a7508ed310251cfaaf181da50c1" "cf23116c1bb648d794cb58afcce7ec80a292df87355f5935963ebd055e1f7ddc" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof._sizeOf_inst "sizeOf family" .o11aPending (.root false true false)
    "4816bc5331a9808ef1352b97872725ebba359cdcb55544bf4cd105dd94541ca3" "18e9e4887de2c0d7b1a297c4578e05008cb80ee0172b8b733fe4d3144bc2fd88" "value.@1.λ.body.fn" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "080015f9b5b0281c4942200f57865b7c2c2f02b767f064caf40b59e69aa91838" "e9b155f950b3edd405fe595a993b374ed38af322a71d2a332327a4241cfd66bf" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fa9086f0d477ab880b3dd0aeec9d72822bfb80ad19403f8a6358546edc351167" "5fa59a4536ae963c3fbc2f8e5910989beb39628abf91753f33f9f7eecda7f0b8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "aca34ba7665a7e007afe5dcded061b5479f9daba72942f4cd8b9ecbaaf57e42a" "e75fdfea551fa47b42cc36ecff8c5e6421929c26debf71529ad40c19f9c4326e" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7fd866a9bfc2745f7ab0faf3e9b14bddda0fc2cbfadeb7e8a30310956f27dd2a" "247ffa92a3370c3610731318ab947d80e857051360463e14ed04be58fa2e3e7f" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.combine.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst, `IneqCnstr._sizeOf_inst])
    "b5cbbe20fa4f4467aa7c6759cf65222e4d4be472f4f678f3da4c2176d979daca" "f7585b20c4077ca99d9d845e1609b38593aa6fe1195cc5da1360e67b99411aae" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.core.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "a74a60920f98ef433c60fbba9817f6fa0cc32d585a599961ceb2fdac0ce9e0d1" "d3c9cdd4eb55fc217267aebaff5caadf3202899273a059fbed9d62e577766da9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.coreOfNat.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "35373a974552d40d5c66ff036d2c1f0b8b27d8e9dcf80a641654c50b2a2cb631" "84608a0d69e605f65eeb96a57d3850debc77096eeb163a22c0836c00fb53abb8" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.dec.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "9f757738ff82e1c612a0d153fa9909275918cce4163d15ae8e213ba858d6c7d9" "7eda72879d70646dcc6a8d868a0ac5cf57fd184fee3edb419c5e4ae0020e60dc" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.norm.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst, `IneqCnstr._sizeOf_inst])
    "bea3ae8c8d027116b019c310417d5afd4853b2030515633d67079dcee0457dc7" "9552be21f36daaf95edf68bd440cb98fa76ecbda23a5986bf137dae88ab19d26" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCore.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "01a6e3b2e1158517ca0fb75bf042ca356c58bea423b5e38840bb4dbff6151c33" "7f9af11aa91a7bbba72561d828ea650f04aff607303bf10fa61fc0a82b0aa227" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCoreOfNat.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "c812f8fec228bc3d0143516bf67ad5adf8a653b086ba6d4b715d07dd3c9bac7c" "ace80c95d6c7c6c9f325f14c6ffc5c861e2c95c03618d7e4bc5fa3d55279dd74" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofDiseqSplit.sizeOf_spec "user constant" .inherited (.inherited [`UnsatProof._sizeOf_inst, `DiseqCnstr._sizeOf_inst, `IneqCnstrProof._sizeOf_inst])
    "cfc29c7dfba8091979426e2637e589c43cbf670583d9287e67ee2d43dcf31cea" "659c00c5984224026bccb9df7bb45f01f8a7f9458b17d0e836db2915f3108be9" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEq.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "4603107e6a354c19517fa39721aa1ea28c43e97de795b2f9f2ef93fdd1600664" "f06a5606098279c9075cacfc969e744fdd37f22951da37ec66aefc69d6b3569b" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEqOfNat.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "d06162abe66e36f46f4c3080c35613a3be5ec59a36ebc26c16f459f2d004a874" "87d0a2b30689c76ee93bb81d53423d36260cfdc9731d47cb3b97a7c6b500902c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.oneGtZero.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "7167f92dc8816fc4ec17978ab468441c41161719340123e4035fdf6319e5cb9d" "9487fc46795b525b293403ac9b6043dc35500f59a3a5dab1e24aadb96f568b0c" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.rec "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "2bb3e55f987b275b8b1cc2ed3dd459567635ff969f72471e914a1396b13a4056" "06b592545e16c174884278209525dcacee29811e2c9718fce2a516789788ead1" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.recOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "7396d2991fdb06838fc9d6f924b3322115c56115a72c9d5e8934e2b223498457" "08d029718ca33d416533ba123d507247868e05a1e21598b6618474336b2540d8" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ring.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "20d8f15b9079591b8cd8601a2f7152ca8364c933efd20e6fd75b21e0d2b1d02a" "9fb419fa2d4b2ebf71d0ac21d32f75c9b16a8ea3a20944478968183e67c5427e" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ringEq.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst])
    "3dacb1e7bed424eb8c096588d97449dfcee0876c69ee8db92e5205312b415d18" "ceea112676ee95fa15b420842a2f9201b350e7fb5c967ae04c481b77aa983ead" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.subst.sizeOf_spec "user constant" .inherited (.inherited [`IneqCnstrProof._sizeOf_inst, `IneqCnstr._sizeOf_inst])
    "b5083cb595f0e1ca587616cea952d75c24e55d150f6c8682b75cd133c9da67aa" "80c4de67e3d77b2b043098aa0d3d59dc0c9db282951e050e049274473e7eaa39" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof._sizeOf_inst "sizeOf family" .o11aPending (.root false true false)
    "b56f470d7c99d75df77302315a9c774c6c697474d6008af73ed60c50f851ff8e" "d7dd0d384ddcca4f8e3d7749d23dea2ba2dda218bae280ac7cdbdce84eae85ec" "value.@1.λ.body.fn" "§4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.below "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "fb226f44ab7b006474ce6925f33a25cdf94de536110892eea3689e7a7114ae3b" "999e6430c31222308c7cb01c2892962ff79f8f36c8996a702879ad04c3b1cd0e" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.brecOn "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "435f0c9ad6b59fe721c5062523281f0e81d9213a5e03c17453c9fa2f2ac79b47" "73c4ab1502297a0df8bc67c23be308eaa99fa39486ada05815c456d3a4d2381b" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.brecOn.eq "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "b2948c710f1b91bc78407e8e9581661140e7e4fb16aca2bd081cd730936cc31f" "84155b04fe96bdfc21b836543f1346828c1c5fcac040b96d854cfd00fafa3e4b" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.brecOn.go "image-kind head of a changed block (its Lean name holds the image)" .image (.root true true false)
    "1900a41bb7538e61b1d503b70185b3477da7ea67d6445d8100b56638181484b9" "a1035a40b074edb78499af69098da75619b4cb60c9f95711ad0f6d739ec6708f" "type.∀.dom.∀.dom",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.diseq.sizeOf_spec "user constant" .inherited (.inherited [`UnsatProof._sizeOf_inst, `DiseqCnstr._sizeOf_inst])
    "950bd0ebc5c2b761d97af1eb27b38bbff010c3c62f16f2d7f3203f802f547988" "c0eecfe044481543199d35a3fd41d1209b18ebb8d3f2cee55c48ad2e394797ad" "",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.lt.sizeOf_spec "user constant" .inherited (.inherited [`UnsatProof._sizeOf_inst, `IneqCnstr._sizeOf_inst])
    "7db1620eb349e5e89775e44bb0d7bb373a4bcf8a39373cd6a5bf33ce5e643fa2" "ab7c3ee7a25016741a85ba51fdd9164c81428df33acf9b62d15ed6dbaf623e01" "",
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
  part0 ++ part1 ++ part2 ++ part3 ++ part4 ++ part5

end Tests.Ix.Compile.NonCanonicalDefault
