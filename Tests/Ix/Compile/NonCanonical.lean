/-
  The non-canonical set (design document `docs/compiler-passes.md` §7.2).

  Every byte difference between two presentations of a twin family
  (`Tests.Ix.Compile.Twins`) that the compiler at this head produces is
  listed here, with its cause and the evidence it was classified from.
  The twins gate (`lake test -- --ignored twins`) reads this list and is
  exact in both directions: every difference must match an entry by
  `(fixture, presA, presB, constant)`, and every entry must still match a
  difference (a stale entry fails the gate). Entries change only in a
  commit that states the cause.

  The causes of §5.5/§7.1 are the permanent ones (what stays faithful but
  not canonical once Phase A is complete). The compiler at this head does
  not yet run the Phase A passes, so the measured set also holds
  differences that a later package removes; those carry one of the
  `pending*` causes, each naming the pass that removes it, and `inherited`
  for a constant whose own term is identical under the name map and that
  differs only because it references a differing constant.

  The evidence was measured at `f829b760` (Lean 4.34.1): the addresses are
  the Lean compiler's; the kernel verdicts are those of `ix check-lean
  --anon` (Ix.Tc), `ix check-rs --anon` (Rust) and `kernel-check-ixe` (the
  certified checker) on the twins closure as the Lean compiler compiled it,
  where a certified decline or a blocked row counts as not accepted. Most
  rejections are open audit defects of the presentations themselves
  (PropSplit, FieldBelow, F4, collapse; report `plans/wave1/a1g.md`).
-/
import Lean

namespace Tests.Ix.Compile.NonCanonical

inductive NonCanonicalCause where
  /-- Lean's tactic output depends on the presentation beyond the packing. -/
  | tacticAsym
  /-- The transport grammar fails; the fallback carries Lean's packing. -/
  | shape
  /-- GuessLex chose a different measure for a different function order. -/
  | guessLex
  /-- Structural recursion chose a different recursive argument. -/
  | recArg
  /-- A statement that follows the order (`mutual_induct`, `induct`,
      `_mutual.eq_unfold`, bare `@f._mutual`). -/
  | orderStmt
  /-- A bare or partial occurrence of a grouping-dependent auxiliary. -/
  | bare
  /-- The Lean names over a collapsed pair with different arms. -/
  | collapseArms
  /-- Lean's `IndPredBelow` family of a changed Prop block. -/
  | indPredBelow
  /-- A theorem clique whose order cannot be determined. -/
  | noSpec
  /-- A lazily realised equation lemma. -/
  | lazy
  /-- Lean's mutual `_sizeOf_N` over a split block (§4.7 (d), O11a). -/
  | o11aPending
  /-- Today only: the clique encoding's packing order (`PSum` summands,
      `PProd` factors, the packed `below` motives and functionals, the
      projection paths into them, and the fixed-parameter telescope).
      Transport (A5: O13–O16) removes it. -/
  | pendingTransport
  /-- Today only: §4.7 (b), `below`/`brecOn` generated (or not) by the
      member's Lean block rather than its Ix block (Pass 2, A2/A3). -/
  | pendingSplitAux
  /-- Today only: §4.7 (c), Lean's `noConfusion` in enumeration form
      (O11b, A6). -/
  | pendingNoConfusion
  /-- Today only: §4.7 (e)/(f), call-site surgery: leftover reference and
      sharing entries, wrong IH projection or universe (images, A3). -/
  | pendingSurgery
  /-- Today only: collapse passes O7–O12 and O17 are not implemented (A6). -/
  | pendingCollapse
  /-- The constant's own term is identical under the name map; it differs
      only because it references a differing constant (named in `note`). -/
  | inherited
  deriving Repr, BEq, Inhabited

def NonCanonicalCause.tag : NonCanonicalCause → String
  | .tacticAsym => "TACTIC-ASYM" | .shape => "SHAPE" | .guessLex => "GUESSLEX"
  | .recArg => "RECARG" | .orderStmt => "ORDER-STMT" | .bare => "BARE"
  | .collapseArms => "COLLAPSE-ARMS" | .indPredBelow => "INDPRED-BELOW"
  | .noSpec => "NOSPEC" | .lazy => "LAZY" | .o11aPending => "O11A-PENDING"
  | .pendingTransport => "PENDING-TRANSPORT" | .pendingSplitAux => "PENDING-SPLIT-AUX"
  | .pendingNoConfusion => "PENDING-NOCONFUSION" | .pendingSurgery => "PENDING-SURGERY"
  | .pendingCollapse => "PENDING-COLLAPSE" | .inherited => "INHERITED"

structure NonCanonicalEvidence where
  /-- hex address under presentation A (Lean compiler, at measurement) -/
  addrA : String
  /-- hex address under presentation B -/
  addrB : String
  /-- path to the first differing node of the two Lean terms under the
      name map (`Tests.Ix.Compile.Twins.firstDiff`), e.g. `value.λ.body.@3` -/
  firstDiff : String
  /-- accepted by Ix.Tc, the Rust kernel, the certified checker (A; B) -/
  kernelsA : Bool × Bool × Bool := (true, true, true)
  kernelsB : Bool × Bool × Bool := (true, true, true)
  /-- one line; for TACTIC-ASYM the tactic or lemma responsible -/
  note : String
  deriving Repr, Inhabited

structure NonCanonicalEntry where
  /-- the twin family, e.g. `Tests.Ix.Compile.Twins.Cliques.WFPair` -/
  fixture : Lean.Name
  presA : String
  presB : String
  /-- the constant's name in presentation A, relative to A's namespace -/
  constant : Lean.Name
  /-- its canonical position (clique, role) -/
  canonical : String
  cause : NonCanonicalCause
  evidence : NonCanonicalEvidence
  deriving Repr, Inhabited

end Tests.Ix.Compile.NonCanonical

namespace Tests.Ix.Compile.NonCanonical

/-- An entry; the kernel verdicts default to "accepted by all three" and
    are overridden where a checker rejects or declines (report §kernels). -/
def e (fixture : Lean.Name) (presA presB : String) (constant : Lean.Name)
    (canonical : String) (cause : NonCanonicalCause)
    (addrA addrB firstDiff note : String)
    (kernelsA kernelsB : Bool × Bool × Bool := (true, true, true)) : NonCanonicalEntry :=
  { fixture, presA, presB, constant, canonical, cause,
    evidence := { addrA, addrB, firstDiff, kernelsA, kernelsB, note } }

/-- The measured non-canonical set. -/
def nonCanonical : List NonCanonicalEntry := [
  -- Cliques.SA P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev4 "user constant" .inherited
    "b945850c13f8e15f4cfbf8b69962546a45ef1408548f478b3f62a327d4b5005d"
    "61176222ba2bb2c44e2c01cdc7d74dfabe86842cf164708538bcf8a77f7ca088"
    "" "via [ev]",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `od._f "structural functional" .pendingTransport
    "43281966e05730c23b3a58e91c7d538d88266e8eb7f3b7c4fe9ee28bb30f003e"
    "65e783795028f8e0de56fed91c7f0e72c756296832635fd169f985d3b9193187"
    "value.λ.body.λ.body.@3.λ.body.λ.body" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `od._sunfold "user constant" .inherited
    "9315038a844c113e85a7946065c46b6f2607eed124e9e88d752150f766ccb75e"
    "f86c3755548414c515942455c73d44cff29d8132308f4b27fb3eb7f53ba4dd2d"
    "" "via [ev]",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev._f "structural functional" .pendingTransport
    "32ac0d0b7ab46893597f46158112832e456669f74427196c7392b187d6da2f1c"
    "bb08c2c77fa597768efd23f70721372b6a62c794e689d33030e180afec296cc3"
    "value.λ.body.λ.body.@3.λ.body.λ.body" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev._sunfold "user constant" .inherited
    "50bf80ce5ec29abe144366e7fc94cae42c60fc4c660b1c3875012c6ba7e2de09"
    "8d7903ac63b702ac9927c35f0b7834b0eba1ea564f8a860eaeb1759ca449dd2d"
    "" "via [od]",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `od "clique member" .pendingTransport
    "d0fbb9dc3009c45b10d6614048dd0c8f7fa62bed1b833946403b7730466d8bfc"
    "d9174bb759379e687c6af1f2f334f056d0307a6f6d25e7b314875540b35af96a"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev "clique member" .pendingTransport
    "6a95c0e321c602cf788b502681a2d273157a5a0653c26af77691ea83721dcb5d"
    "c8550d91c030b61f2772d502e35b62c37b006d9fa2b6e080bdfe80ad44f0ea5c"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  -- Cliques.SA P0 P3
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `od "clique member" .pendingTransport
    "d0fbb9dc3009c45b10d6614048dd0c8f7fa62bed1b833946403b7730466d8bfc"
    "d9174bb759379e687c6af1f2f334f056d0307a6f6d25e7b314875540b35af96a"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev4 "user constant" .inherited
    "b945850c13f8e15f4cfbf8b69962546a45ef1408548f478b3f62a327d4b5005d"
    "61176222ba2bb2c44e2c01cdc7d74dfabe86842cf164708538bcf8a77f7ca088"
    "" "via [ev]",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev._f "structural functional" .pendingTransport
    "32ac0d0b7ab46893597f46158112832e456669f74427196c7392b187d6da2f1c"
    "bb08c2c77fa597768efd23f70721372b6a62c794e689d33030e180afec296cc3"
    "value.λ.body.λ.body.@3.λ.body.λ.body" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `od._sunfold "user constant" .inherited
    "9315038a844c113e85a7946065c46b6f2607eed124e9e88d752150f766ccb75e"
    "f86c3755548414c515942455c73d44cff29d8132308f4b27fb3eb7f53ba4dd2d"
    "" "via [ev]",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev "clique member" .pendingTransport
    "6a95c0e321c602cf788b502681a2d273157a5a0653c26af77691ea83721dcb5d"
    "c8550d91c030b61f2772d502e35b62c37b006d9fa2b6e080bdfe80ad44f0ea5c"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev._sunfold "user constant" .inherited
    "50bf80ce5ec29abe144366e7fc94cae42c60fc4c660b1c3875012c6ba7e2de09"
    "8d7903ac63b702ac9927c35f0b7834b0eba1ea564f8a860eaeb1759ca449dd2d"
    "" "via [od]",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `od._f "structural functional" .pendingTransport
    "43281966e05730c23b3a58e91c7d538d88266e8eb7f3b7c4fe9ee28bb30f003e"
    "65e783795028f8e0de56fed91c7f0e72c756296832635fd169f985d3b9193187"
    "value.λ.body.λ.body.@3.λ.body.λ.body" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  -- Cliques.S3 P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m1 "clique member" .pendingTransport
    "767f4225ec1f4ac399f138df7adbce32a7aa5d11c750b3e30d8011b07761c756"
    "ee47bbcec22de52e177783fd93a2bc91960b8b9352178c29ce5ddffd039e8a8c"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m1._f "structural functional" .pendingTransport
    "b473b69e52a37dafd09fb533128843a07dbcc58d58777409ffab856ef6d29407"
    "d2e57d36c50cd5775f4c95be7157e608df904c29760f0632f8715f3d8d31477a"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m2._sunfold "user constant" .inherited
    "a431a53139e1e5459d676fa6912c189fafecdbd8ec6bc0d6647cc342fb5a45ad"
    "225e87d17b4f82795b381cdf4914aff5a47a6643aadc6c29111029389cb29557"
    "" "via [m0]",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m0 "clique member" .pendingTransport
    "03122a79297aa4094f1c6e51bcf9608a7aaca756e8375472ea2be1ae426c9e58"
    "7648a473b4a506ce6c12dea7e565108a75b886ddc2555c59185bb584f1e96af7"
    "value.λ.body.proj0" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m0._f "structural functional" .pendingTransport
    "fedaafc7f9367356e16f3202220f6bd36dfebc7c0fd73d316b979b0de7f938c4"
    "2ca8a8b47168b5ab5934c3da7114471d5bfb37bfadd265f5cf61d457209a9a1b"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m0._sunfold "user constant" .inherited
    "a5ee14fd7150d178b2ee2cbfeb6ad4c7e02347e9f0d88e4a5a9f9275a77918c1"
    "ebb965050e6e77227ea8255964a2bf4e86f964499b143ed839afe5c153718ace"
    "" "via [m1]",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m2._f "structural functional" .pendingTransport
    "9bcdd88d009edbd1f0d37bf051063ad4c1f0530790133cb6a8fadabc96584fcb"
    "6d92f0bfe7815b036aa2e8aa94555be69ceca2b9ea03b336e21155446a12035a"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4.proj0" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m1._sunfold "user constant" .inherited
    "05f990b4deabf4cd06b15b91dd8ded3cb149e645ca0cd164109736ba511f3c09"
    "ccfd7b978c8732ff65d05b7278e15c23d6df69be023fe3f7dfaacb59c2a91fbe"
    "" "via [m2]",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m2 "clique member" .pendingTransport
    "14d5577906f40f9b12639e2d5bbde2f977f42adf269a72dd8eacd1d3a9abf002"
    "c4c36f2b9fe75fcd51f1a11b0610a30666fe1b4fec0d1349ef05d57bb009921d"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  -- Cliques.S3 P0 P2
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m2._f "structural functional" .pendingTransport
    "9bcdd88d009edbd1f0d37bf051063ad4c1f0530790133cb6a8fadabc96584fcb"
    "95694ad293b38d37c4a3ce5685b2515611e91594ee8be66d080c374c078df146"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m1 "clique member" .pendingTransport
    "767f4225ec1f4ac399f138df7adbce32a7aa5d11c750b3e30d8011b07761c756"
    "e13bd9b19b38e598d925fd1750c3a93551a4b9d685d6145284c00628a9dd4921"
    "value.λ.body.proj0" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m1._f "structural functional" .pendingTransport
    "b473b69e52a37dafd09fb533128843a07dbcc58d58777409ffab856ef6d29407"
    "9b5514479236441cb7b31271e82f528edd1374ef82f3bb7966587f98c1faa76d"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m1._sunfold "user constant" .inherited
    "05f990b4deabf4cd06b15b91dd8ded3cb149e645ca0cd164109736ba511f3c09"
    "ad27c742e38e5d14f0f32ac3f749bc123c90e0c69d7f8e3ef1e6051ad062d212"
    "" "via [m2]",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m0._f "structural functional" .pendingTransport
    "fedaafc7f9367356e16f3202220f6bd36dfebc7c0fd73d316b979b0de7f938c4"
    "d06c6d35cc3c901f92352c900abf036ce204f29228dec3299fc7791f4efb0a9a"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4.proj0" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m0._sunfold "user constant" .inherited
    "a5ee14fd7150d178b2ee2cbfeb6ad4c7e02347e9f0d88e4a5a9f9275a77918c1"
    "816cae03790bcf05055200ca9ab956e8562975ad79a9fecfb535a343f8475be2"
    "" "via [m1]",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m2 "clique member" .pendingTransport
    "14d5577906f40f9b12639e2d5bbde2f977f42adf269a72dd8eacd1d3a9abf002"
    "b0b46bf9703cebbe8cdf02c8a1830218e2640d02e6e7a65ace6924b1e5cf71f8"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m2._sunfold "user constant" .inherited
    "a431a53139e1e5459d676fa6912c189fafecdbd8ec6bc0d6647cc342fb5a45ad"
    "21d4163d0aa268861745cfdc3b865fe1058e47174afe808a127d337d028aaba3"
    "" "via [m0]",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m0 "clique member" .pendingTransport
    "03122a79297aa4094f1c6e51bcf9608a7aaca756e8375472ea2be1ae426c9e58"
    "9202cdb86d48b9c93c1ba3c318455ef847898b72785c55a82a0ace73e31e156e"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  -- Cliques.SX P0 P2
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo._f "structural functional" .pendingTransport
    "27fd98201750b729e0e181320130e171d176b22a73f90de9719a411eb6fc49f8"
    "63b05e67d2da4ce10f6a63465b537af309d90244ef875fd775e1847498ae564a"
    "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@5" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo "clique member" .pendingTransport
    "cb2ceccb026b6cc729980d52ee1206ff9530828ca7f1b45b89e860733f79783a"
    "0b07971836a898b514ec7a4c899a1a43479a8a2755e0c591cacda0046bfce804"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo._f "structural functional" .pendingTransport
    "026749257a9769d0dafdd5bd27121805d9845fbceecdf53dde000265bcb5be05"
    "cb19c9d8bd5eb1ea673aff7a84c7935df7d49482f36c5a436f72c920264834fa"
    "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@4.@4" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr._sunfold "user constant" .inherited
    "c10eb23935078e5705e028d73b00f119fb90ecaa9cc66e0702302f4bfdd3bbe8"
    "4425558d75f72897b2b3a973ea2ce839a907fe29b65fca637e2199c5c54a3f3b"
    "" "via [lFo, cFo]",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo "clique member" .pendingTransport
    "7c83f22adaec27b49d53b79127eee72becf67ab69d066c52455b51976d023d9f"
    "87c66ac135f6cb8062849a6eb4851d79cbaf136064d45d529e98ef02ca7832d1"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr "clique member" .pendingTransport
    "55dfac14426048a54fccc82a14cea850dad11dd36e93c500dd54de76d1e1b514"
    "8d9876206da19efa6cfa54581e2b59f0bb194445fcf339c6aef8093bc0e7a38f"
    "value.λ.body.@4.λ.body.λ.body.@2.fn" "ROOT[V|K]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo._sunfold "user constant" .inherited
    "7ca92bdd62426d1db06c262f8f7b95f939efcf18d9addf6d95e67c192d9a3400"
    "df7ebbc14e8bded8891c032a4a42bd92961e739828648108c9f764896a53a56e"
    "" "via [cTr, cFo]",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr._f "structural functional" .pendingTransport
    "e840b545c5d514be53b5ab03a879262a0991fd1caea1548134ad9b76291cb48a"
    "0dc499524b6c8a644acd026036dcccfcc2d563f01362836dc87c3bb49c85a7f2"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo._sunfold "user constant" .inherited
    "75e43fe381ad00962db1fca94375d29f1e8c1b89557cf61a6d7c318a0cf4ccdd"
    "3346125e3773800380c8151370b05a31c143dc878dba13ba3a3cb7a057c5c250"
    "" "via [lFo, cTr]",
  -- Cliques.WD P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual._proof_2 "encoding obligation" .pendingTransport
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307"
    "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual._proof_1 "encoding obligation" .pendingTransport
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6"
    "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa.eq_def "equation lemma" .lazy
    "3f7017a98ae057bd3f51728c1078b8151be63f88e3e40dead4719de56ac6e964"
    "311ecc3184b86b232a250a4ca678b70b6e40b57a267e1cdc54ea5c32a98fb21f"
    "value.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wb.eq_def "equation lemma" .lazy
    "e59e349deb22c46e57c0e71786433574411b8dd1522d2e8e69249cc61321ac8c"
    "327144d5b893ee7f5d24097c8fa728d6c7eb81225d9bf0c8fd1f3f3503bbf103"
    "value.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wb "clique member" .pendingTransport
    "c485a2c9367144d0f6cef0490348f437998387316f56f259b2524484428b862e"
    "fae38748a4ee68cdd161650cc02b0ab89db1a0b4bc97c2f9f6a4f25fbbed84de"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa "clique member" .pendingTransport
    "4759d7fe47f0d21c2b99cf95bfc7d5cb7b9ca281166e4f3f92d37c8c308a06b2"
    "641529fc41f1f6b72045cde3fb9c20357b95df6d1e659d54b53617f145b99f36"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual "clique encoding" .pendingTransport
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447"
    "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e"
    "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "ROOT[V|K]; `PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual.eq_def "encoding equation" .orderStmt
    "2b874d7adcde67692447fa1de16691fb35bd9efae63943a64358f346f5832fee"
    "cc2a2148e21ce32e46eff6a75dfd00a1b67f9a0dadbf91639b57c0d4948cf459"
    "type.∀.body.@2.@4.λ.body.@1" "ROOT[TV]; statement over the packed `_mutual`",
  -- Cliques.WD P0 P2
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual._proof_1 "encoding obligation" .pendingTransport
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6"
    "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual._proof_2 "encoding obligation" .pendingTransport
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307"
    "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wb "clique member" .pendingTransport
    "c485a2c9367144d0f6cef0490348f437998387316f56f259b2524484428b862e"
    "fae38748a4ee68cdd161650cc02b0ab89db1a0b4bc97c2f9f6a4f25fbbed84de"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual "clique encoding" .pendingTransport
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447"
    "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e"
    "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "ROOT[V|K]; `PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa.eq_def "equation lemma" .lazy
    "3f7017a98ae057bd3f51728c1078b8151be63f88e3e40dead4719de56ac6e964"
    "311ecc3184b86b232a250a4ca678b70b6e40b57a267e1cdc54ea5c32a98fb21f"
    "value.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa "clique member" .pendingTransport
    "4759d7fe47f0d21c2b99cf95bfc7d5cb7b9ca281166e4f3f92d37c8c308a06b2"
    "641529fc41f1f6b72045cde3fb9c20357b95df6d1e659d54b53617f145b99f36"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual.eq_def "encoding equation" .orderStmt
    "2b874d7adcde67692447fa1de16691fb35bd9efae63943a64358f346f5832fee"
    "cc2a2148e21ce32e46eff6a75dfd00a1b67f9a0dadbf91639b57c0d4948cf459"
    "type.∀.body.@2.@4.λ.body.@1" "ROOT[TV]; statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wb.eq_def "equation lemma" .lazy
    "e59e349deb22c46e57c0e71786433574411b8dd1522d2e8e69249cc61321ac8c"
    "327144d5b893ee7f5d24097c8fa728d6c7eb81225d9bf0c8fd1f3f3503bbf103"
    "value.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  -- Cliques.W3 P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual._proof_2 "encoding obligation" .pendingTransport
    "6d43105b925565d18ef4797b4cd28ef0ecf7d80f7d1c95ca138f121a5f4cf40d"
    "bceac634d415df450def06d4a22b21a761b5ed1656541840965438fa4762b8a9"
    "type.∀.body.∀.body.∀.body.@0.@2.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual._proof_4 "encoding obligation" .pendingTransport
    "ce71876d8dc1a733cf4a015111ba6be5780a8e830183d26f90e2182f961f21cc"
    "2bd27fb76859701c03ad9a256da78686e99bf9bdf55c62591ec604b81592ac37"
    "type.∀.body.∀.body.∀.body.@0.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual._proof_3 "encoding obligation" .pendingTransport
    "1a6d56af84d790f0f5f694bd7eb082c0a1beafe6aacd11323972d60dd5fb64b8"
    "b3b9365f8cbdd96920326a32b76e706633c74d36ce659bd9ac7e8371a71c5b3e"
    "type.∀.body.∀.body.∀.body.@0.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual.eq_def "encoding equation" .orderStmt
    "205423647ec0cfd85f0923b6927f8ea21ec2aeb2caecd718dd3ee0ef039b3991"
    "d0f98e93be3e30d814cb45b26997053706c312d701e191eedcdfa0a5b6cf2ff5"
    "type.∀.body.@2.@4.λ.body.@4.λ.body.λ.body.@3.λ.body" "ROOT[TV]; statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gc.eq_def "equation lemma" .lazy
    "3bba15edc4fcd75ef0851890fa2fb1fdab78f716f53725e64a2feb572e97cb77"
    "9246d7d2b9b39b3a602201240eb94a7f71f84d46ff77138221fd398073a3405b"
    "value.λ.body.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga.eq_def "equation lemma" .lazy
    "f8c18f7082d58145f2a39a644c001fb69d3a99ad05e83f00add2273c7fe17e59"
    "f710ebdcf62e60f8399a516774451ac201a75910363716906bc87bfd428e2bd7"
    "value.λ.body.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gc "clique member" .pendingTransport
    "b6c20f5e441e355d2c4c0af88c436faa414c952532edf32cec404f23e1442de1"
    "2e11e2833c410ba92b2b10f39e2a9aeac6101a2c43c10d352ab60925fea5fe9e"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gb "clique member" .pendingTransport
    "f7787b8d0cd56368b87bb53196fe36fc0b9c2839a10ff3b0fd5e8092369be486"
    "c5e76ac756f4686274196cd37fcc1b8cceeb217a4adf50296aabb36d04303c48"
    "value.λ.body.λ.body.@0.@2.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gb.eq_def "equation lemma" .lazy
    "80a975c58a9c3458b4cc9fd6107a93d37c686fab90119ba3332ae55995c99cc6"
    "eda78c77eafd830877efe20d1b014da7d7f284b706a579c2de8f5b6c15126dc7"
    "value.λ.body.λ.body.@1.@0.@2.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga "clique member" .pendingTransport
    "f565ce3d9ce8ac675ba4e535eddbb0fa48b4e91e7b507e1385056a070b2f971e"
    "8a34e4cd993fb7d9b189ce7b0b75f2670b21b46a029b433f76a82ed106a27bb8"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual "clique encoding" .pendingTransport
    "0e27ba25c79dc7793a8ba162691f785ee152ec1f68d31f4f597d4b09db0a5ef5"
    "9cc2b3854a5c3cc7cdb261fadd317f19800a7d2a2f1eb5c1bed9d698f9f2cc70"
    "value.@4.λ.body.λ.body.@4.λ.body.λ.body.@4.λ.body.λ.body.λ.body.@3.λ.body" "ROOT[V|K]; `PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  -- Cliques.W3 P0 P2
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual._proof_3 "encoding obligation" .pendingTransport
    "1a6d56af84d790f0f5f694bd7eb082c0a1beafe6aacd11323972d60dd5fb64b8"
    "fe16646b2b3f46f4d57a175b5b47d4d644c49dc4d12145774993cb86d21f145d"
    "type.∀.body.∀.body.∀.body.@0.@2.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual._proof_4 "encoding obligation" .pendingTransport
    "ce71876d8dc1a733cf4a015111ba6be5780a8e830183d26f90e2182f961f21cc"
    "757d86daa0a585e4986d23619f3b86f704e970c806116b70cd7932d948b6940b"
    "type.∀.body.∀.body.∀.body.@0.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual._proof_2 "encoding obligation" .pendingTransport
    "6d43105b925565d18ef4797b4cd28ef0ecf7d80f7d1c95ca138f121a5f4cf40d"
    "776dbac01f0a7c74dd91c8d188c9e34fe6a7cf75c293f611385a8223789eaca2"
    "type.∀.body.∀.body.∀.body.@0.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual "clique encoding" .pendingTransport
    "0e27ba25c79dc7793a8ba162691f785ee152ec1f68d31f4f597d4b09db0a5ef5"
    "43efb240d50538091e93d4cdf2ffa2140037e6df0cda820c120ab0c46dc3b447"
    "value.@4.λ.body.λ.body.@4.λ.body.λ.body.@4.λ.body.λ.body.λ.body.@1.@1" "ROOT[V|K]; `PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gb "clique member" .pendingTransport
    "f7787b8d0cd56368b87bb53196fe36fc0b9c2839a10ff3b0fd5e8092369be486"
    "05ba5aaf6cc1a11fe2b70b8a352d383eac701c8c8664fd79f55dcc56fed95b28"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gb.eq_def "equation lemma" .lazy
    "80a975c58a9c3458b4cc9fd6107a93d37c686fab90119ba3332ae55995c99cc6"
    "b33c695be2db8daff75040287be55e02c3af085aad7a3c578c0a91af7ee46f79"
    "value.λ.body.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gc "clique member" .pendingTransport
    "b6c20f5e441e355d2c4c0af88c436faa414c952532edf32cec404f23e1442de1"
    "1645a1d44ec15056218e26836cee53bb5734275d598fede262d1bfa0a0aa6124"
    "value.λ.body.λ.body.@0.@2.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gc.eq_def "equation lemma" .lazy
    "3bba15edc4fcd75ef0851890fa2fb1fdab78f716f53725e64a2feb572e97cb77"
    "2019c99986595cfc25a562b82c729700a516e8df62dcb1cf92bee249feddf9cc"
    "value.λ.body.λ.body.@1.@0.@2.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga "clique member" .pendingTransport
    "f565ce3d9ce8ac675ba4e535eddbb0fa48b4e91e7b507e1385056a070b2f971e"
    "2c41be0e21fc26c4193b3acf79ff54ebe9db6c51435930697eb2dc2662ede79f"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual.eq_def "encoding equation" .orderStmt
    "205423647ec0cfd85f0923b6927f8ea21ec2aeb2caecd718dd3ee0ef039b3991"
    "554d9601db74da49f2f7e6e581f9e461b0cfacf16cb79a7fbb58cf49060aebc3"
    "type.∀.body.@2.@4.λ.body.@4.λ.body.λ.body.@1.@1" "ROOT[TV]; statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga.eq_def "equation lemma" .lazy
    "f8c18f7082d58145f2a39a644c001fb69d3a99ad05e83f00add2273c7fe17e59"
    "4801b23753ad6cf3a56f04dee9d12fe507df470f09436510af9c550f57aa10a8"
    "value.λ.body.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  -- Cliques.WG P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `gb.eq_def "equation lemma" .lazy
    "8c620db260db49063de075bc9839f00b2d732c0468bb8b87f896facb9385a128"
    "40f2789bf7efed9f6c15d43fedf77c2d9d497674c59a312cecac7bd3f8082943"
    "value.λ.body.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `gb "clique member" .guessLex
    "978a66e918dbcc26dee988dbbd25fd28f5f613c3482a5c14e1e32951b0bbccd9"
    "b0865eadcc8365b3b3d27419f53a0779d72ca275dd90978551c382b52fcf3f49"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection, over the GUESSLEX-differing `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga._mutual.eq_def "encoding equation" .orderStmt
    "04e8346072b66c68dde386ff5a5a1ce9144a185d226fc9099d8865ad22cc3c9f"
    "1dffc78b59df95be2ef948f52dd2c2138e3c7c9fe8f05aa4c808f72a2d0c359f"
    "type.∀.body.@2.@4.λ.body.@4.λ.body.λ.body.@3.λ.body.@1" "ROOT[TV]; statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga.eq_def "equation lemma" .lazy
    "725de1dc9e6a16cbe621aefb2d4196d823e049f91cb1bb290f8d48051de49a7e"
    "338a400d2f57837f41c97d82d4cab4732b0b4490a5304a9d3143bd5be77cf6e5"
    "value.λ.body.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga._mutual "clique encoding" .guessLex
    "9505e594f820630cddb3e20b6708419abb613c308ad91953d41372120ec19313"
    "f1b52679b1aa1207b01b494315252882f78493caaab7a40793cd0837c62a17aa"
    "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@4.λ.body.λ.body.λ.body.@3.λ.body.@1" "ROOT[V|K]; GuessLex measure: (ga.x, gb.y) under P0, (gb.x, ga.y) under P1 (non-uniform combinations enumerated in function order, first that works); the canonical functional differs",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga "clique member" .guessLex
    "242e5c784fb1c56336cfb8bd9be95aae375a3e029bb6787da7e3802667cd64df"
    "a54529c0d974aef16d4b2a61a038a49491a2f2640bb4451ae4d13b0d18d273d5"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection, over the GUESSLEX-differing `_mutual`",
  -- Cliques.WT P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual._proof_1 "encoding obligation" .pendingTransport
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6"
    "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual._proof_2 "encoding obligation" .pendingTransport
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307"
    "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual "clique encoding" .pendingTransport
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447"
    "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e"
    "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "ROOT[V|K]; `PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta.eq_def "equation lemma" .lazy
    "3f7017a98ae057bd3f51728c1078b8151be63f88e3e40dead4719de56ac6e964"
    "311ecc3184b86b232a250a4ca678b70b6e40b57a267e1cdc54ea5c32a98fb21f"
    "value.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `tb "clique member" .pendingTransport
    "c485a2c9367144d0f6cef0490348f437998387316f56f259b2524484428b862e"
    "fae38748a4ee68cdd161650cc02b0ab89db1a0b4bc97c2f9f6a4f25fbbed84de"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `tb.eq_def "equation lemma" .lazy
    "e59e349deb22c46e57c0e71786433574411b8dd1522d2e8e69249cc61321ac8c"
    "327144d5b893ee7f5d24097c8fa728d6c7eb81225d9bf0c8fd1f3f3503bbf103"
    "value.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta "clique member" .pendingTransport
    "4759d7fe47f0d21c2b99cf95bfc7d5cb7b9ca281166e4f3f92d37c8c308a06b2"
    "641529fc41f1f6b72045cde3fb9c20357b95df6d1e659d54b53617f145b99f36"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual.eq_def "encoding equation" .orderStmt
    "2b874d7adcde67692447fa1de16691fb35bd9efae63943a64358f346f5832fee"
    "cc2a2148e21ce32e46eff6a75dfd00a1b67f9a0dadbf91639b57c0d4948cf459"
    "type.∀.body.@2.@4.λ.body.@1" "ROOT[TV]; statement over the packed `_mutual`",
  -- Cliques.WB P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual._proof_2 "encoding obligation" .pendingTransport
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307"
    "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual._proof_1 "encoding obligation" .pendingTransport
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6"
    "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `bb.eq_def "equation lemma" .lazy
    "e59e349deb22c46e57c0e71786433574411b8dd1522d2e8e69249cc61321ac8c"
    "327144d5b893ee7f5d24097c8fa728d6c7eb81225d9bf0c8fd1f3f3503bbf103"
    "value.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual.eq_def "encoding equation" .orderStmt
    "2b874d7adcde67692447fa1de16691fb35bd9efae63943a64358f346f5832fee"
    "cc2a2148e21ce32e46eff6a75dfd00a1b67f9a0dadbf91639b57c0d4948cf459"
    "type.∀.body.@2.@4.λ.body.@1" "ROOT[TV]; statement over the packed `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba "clique member" .pendingTransport
    "4759d7fe47f0d21c2b99cf95bfc7d5cb7b9ca281166e4f3f92d37c8c308a06b2"
    "641529fc41f1f6b72045cde3fb9c20357b95df6d1e659d54b53617f145b99f36"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual "clique encoding" .pendingTransport
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447"
    "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e"
    "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "ROOT[V|K]; `PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba.eq_def "equation lemma" .lazy
    "3f7017a98ae057bd3f51728c1078b8151be63f88e3e40dead4719de56ac6e964"
    "311ecc3184b86b232a250a4ca678b70b6e40b57a267e1cdc54ea5c32a98fb21f"
    "value.λ.body.@1.@0.fn" "ROOT[V|K]; lazily realised equation lemma; its proof unfolds the clique encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `bb "clique member" .pendingTransport
    "c485a2c9367144d0f6cef0490348f437998387316f56f259b2524484428b862e"
    "fae38748a4ee68cdd161650cc02b0ab89db1a0b4bc97c2f9f6a4f25fbbed84de"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  -- Cliques.PF P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pa.mutual._proof_1 "encoding obligation" .pendingTransport
    "0ddea573a18b7aac2d20a006f8cda1fcef605fc2f31cd9e8782c5e4d1816b923"
    "17dad592622f8c1da82e3fab3f43a962e034ddd7f804ff221d35fbd6846c8469"
    "type.@4.λ.body.@2.λ.body.@1" "ROOT[TV]; monotonicity proof: `PProd.monotone_mk` tree in factor order; `monotone_fst`/`monotone_snd` projection paths per call (A)+(G); statement over the packed type (S)",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pc "clique member" .pendingTransport
    "0c0ebc4460fee8cd928f746e7f2582faa54239b60a439fdff41096a5285ed27a"
    "968c560933816d33fa072b641daa169659e5a3e15f37fea0459f3427a827ca80"
    "value" "ROOT[V]; `PProdN.proj` at the factor position",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pb "clique member" .pendingTransport
    "fc4304ee5143837aac1bbe637884c0babff4d7acc1eaf5bd92d3f92185d32bda"
    "e9177ca30906fde9a52fd1ea6038f4fcde04f2ad313c17bcf0a38e9b89d10567"
    "value" "ROOT[V]; `PProdN.proj` at the factor position",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pa "clique member" .pendingTransport
    "dade135fc1eaa15b37cbf0b182a8b0c752f54bf12eb02840b88f106f4e7fe67a"
    "9911ee6af0f00d2ed01c598fd0263f8aa08491b8d21f22986127f92488458dd3"
    "value.proj0" "ROOT[V]; `PProdN.proj` at the factor position",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pa.mutual "clique encoding" .pendingTransport
    "aae0295814cc6f61f77a936266e0a0bdedf33c89f9e37ea54b90ed658af55105"
    "35e34d7f00e53729f8c161ece500c8b896c38e2fbfadd9a2269617327da253c0"
    "value.@2.λ.body.@2.λ.body.@1" "ROOT[V|K]; `PProd` factor order of the packed functional and instance",
  -- Cliques.PF P0 P2
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pa.mutual._proof_1 "encoding obligation" .pendingTransport
    "0ddea573a18b7aac2d20a006f8cda1fcef605fc2f31cd9e8782c5e4d1816b923"
    "8043e9fdebd60d01ee161bee0427b12e1ed4b505ac63c2534a24c2ea6c2bea04"
    "type.@4.λ.body.@2.λ.body.@3.@1.@1" "ROOT[TV]; monotonicity proof: `PProd.monotone_mk` tree in factor order; `monotone_fst`/`monotone_snd` projection paths per call (A)+(G); statement over the packed type (S)",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pc "clique member" .pendingTransport
    "0c0ebc4460fee8cd928f746e7f2582faa54239b60a439fdff41096a5285ed27a"
    "78ddb333047b376621b3023a40c92677d0a73f7fb9525e3cf8b5ae94cfba9955"
    "value" "ROOT[V]; `PProdN.proj` at the factor position",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pb "clique member" .pendingTransport
    "fc4304ee5143837aac1bbe637884c0babff4d7acc1eaf5bd92d3f92185d32bda"
    "4fbec683f761044ed4c47df9efa8b70e609f9da8ae9ea45976bc75181dfa8735"
    "value.proj0" "ROOT[V]; `PProdN.proj` at the factor position",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pa.mutual "clique encoding" .pendingTransport
    "aae0295814cc6f61f77a936266e0a0bdedf33c89f9e37ea54b90ed658af55105"
    "026e16e83c5526336e4c936926791e6e0d9159f175139d64eb2654deffe595ae"
    "value.@2.λ.body.@2.λ.body.@3.@1.@1" "ROOT[V|K]; `PProd` factor order of the packed functional and instance",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pa "clique member" .pendingTransport
    "dade135fc1eaa15b37cbf0b182a8b0c752f54bf12eb02840b88f106f4e7fe67a"
    "e6b782605202d40bd549614ec9dde18bc3924ace440f0ae00ba59fa6854f68b8"
    "value" "ROOT[V]; `PProdN.proj` at the factor position",
  -- Cliques.TS P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.TS "P0" "P1" `evT._mutual "clique encoding" .pendingTransport
    "78a3577514987bc92d9a2729706e613221b268472784a8d1d7e53287ba4814fa"
    "38b13258377b659e92f44c3b92385ec4029f9fa33836e6f6fb498d9441e0818e"
    "type.∀.body.@4.λ.body.@1.@0.fn" "ROOT[TV|K]; theorem clique by well-founded recursion (not structural: odT (n+1) calls evT (n+1)); GuessLex `(n, funIdx)` literals travel with each function; `PSum` order; inline decreasing proofs equal up to the packing",
  e `Tests.Ix.Compile.Twins.Cliques.TS "P0" "P1" `odT "clique member" .pendingTransport
    "6795d98ab1593083c24882a9ef2d0fd34e1ca351fa107ea677c78781d5c25666"
    "79c0ad141956a442d22eba6ea4f4f0045595168ae83fd0cad44774a3599088b9"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.TS "P0" "P1" `evT "clique member" .pendingTransport
    "bb7f9eb5c1eee2076d608222ae2e59b3bec450945e57240aec1971bc7f4b8402"
    "e968d779096bf66ed8060322ad076feb752b84c1de9c494355ebbe36d7e3e4b8"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  -- Cliques.TW P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.TW "P0" "P1" `wb "clique member" .pendingTransport
    "5883e50b907830935e717e5aa88faf8733fa45e2442687db5aa916e51bad0cb7"
    "993b8c17a4ddf9cec241eef2cfb7fa4913d8bba3683caac3388dc9b7b5a88f50"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.TW "P0" "P1" `wa._mutual "clique encoding" .pendingTransport
    "f4215cec1c7e681c3804e51a25357202c2d500c4acc04ffa3f8ddc9c58a9c012"
    "09a6c8908407175fda86ab1e581780f564eb41fc1fd79ae3ea11581474cfe582"
    "type.∀.dom.@0.@1.λ.body.@2.@1" "ROOT[TV|K]; theorem clique by well-founded recursion; `PSum` order of the `PSigma` domains (hypothesis carried)",
  e `Tests.Ix.Compile.Twins.Cliques.TW "P0" "P1" `wa "clique member" .pendingTransport
    "5ddf195d3f8e7cbe8820d6db12a14b2472f47e6aa4952f1975ca3f02aa0ec075"
    "44e227a443b047e91bbd536284c16c6bc79fa1f3c2ebb8101a96bcae0b0a8025"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  -- Cliques.IP P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `odM.match_2 "transformed matcher" .pendingTransport
    "68626a4237f13c422940ed7f762097a776ebe19ee83c9de8d1beddff43dd5865"
    "9e603fee7874e8da8d3238dcb65741b2ac0c03d0d7c538eab60b0498eaaf7136"
    "type.∀.dom.∀.body.∀.dom.fn" "ROOT[TV]; IndPred `below` matcher: `funType_i` binders in clique order; regenerated by transport (R)+(A)",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `evM.match_2 "transformed matcher" .pendingTransport
    "3582fae2a150da5c36b53947dc78d1d0c89b6291302d5d19c864194c521ab6b4"
    "de267bfb295f3e16b87badb849271d2b1643423f074bc2300a68c5331dcd918e"
    "type.∀.dom.∀.body.∀.dom.fn" "ROOT[TV]; IndPred `below` matcher: `funType_i` binders in clique order; regenerated by transport (R)+(A)",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `odM "clique member" .pendingTransport
    "45f11f1e99ae48aadc8527b6bece926845e99a1ba0ef3eed86ade2d6ebc84d8f"
    "e7e127abf6a278f86163f1ed60923a3e6a6c138403e79dffceb127cec0c94174"
    "value.λ.body.λ.body.let.ty.∀.body.∀.dom.fn" "ROOT[V]; `let funType_i` bound in clique order (`withFunTypes`); zeta-equivalent",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `evM "clique member" .pendingTransport
    "9efd0f3c75547dbf5b4164813e94dc5a96d7f09099cafab984b6c8567455b349"
    "4126319694718f46e7c6afa06c63e08fb26098d2ec2ecc258d816262851b4bbc"
    "value.λ.body.λ.body.let.ty.∀.body.∀.dom.fn" "ROOT[V]; `let funType_i` bound in clique order (`withFunTypes`); zeta-equivalent",
  -- Repro.DQMut twin orig
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B._sizeOf_1 "sizeOf family" .o11aPending
    "f3f9cc6a6602b8596c5bfbbc20987f4be2892697fb83368bcf1e2283b3f68a7b"
    "3f891c0e5fcd4d9c9cd5a5e6884eeefccef52abdcc397baf041bb34b378cd149"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending
    "cd37d419d255515656933e6d23afe32bffc3622104ad299967bf429b71328188"
    "fe6870744ef87bdf9b6bd655fee7a86d1a54fab7454c79e3e9931c318e9fe770"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.a.sizeOf_spec "user constant" .inherited
    "6d49117afba347441fd9d5c801883965a81a59d32b23b89e2f613cce8ede1432"
    "2dda00c024a1b897e199d0c9fc5cc2b39eb4b40a0b2f74407526465c66d1f20e"
    "" "via [A._sizeOf_inst, B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.size._sunfold "user constant" .inherited
    "73bf83c71709837e792456ee256596e7dc4254ffca8cded759b3072af5512be0"
    "dba66c94f50f631709d4e918f6b24af8987755824b34d296b01fcecbfebf56c1"
    "" "via [B.size, A.size]" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.size "user constant over the block" .pendingSurgery
    "a079964bc4740aa5f8db3225b1cede4039647cdd6ab1f0a8b3c24454bfa9bf10"
    "14564d53f6471a9964080a9f3ab0eab34e364af9acd7482a1c2849060ce54f71"
    "value.λ.body" "ROOT[V]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `size2 "user constant" .inherited
    "81c2c0294c78f9ec0a8639ef01410a81fe0b57486d2db8631d4d22742cb1c8d6"
    "dc9615560416aaa7b96672fc6d1d4eec42f701a815636352f41264b66c08ed01"
    "" "via [A.size]" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.nil.sizeOf_spec "user constant" .inherited
    "a572550a6184263f6d3999ca82aa84c41b6e33ef8fa4c1ab4a4b72e95496e4be"
    "fb77b89ce666a1a7780e1dfb256523d63cdb5df143fe49cd3d7c82e338af67c8"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.size "user constant over the block" .pendingSurgery
    "7ab66120eb546a328d7a77dc24057c2590921b439880bd534377f46929624447"
    "9b48eaf2534981eb8cbd9508d141f359828d4a31f54770d78d470fdc99efa95b"
    "value.λ.body" "ROOT[V]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B._sizeOf_inst "user constant" .inherited
    "0bb01d3cc9090441a4b6e2ebc8038a1ff31e3e06e850342abf7a5be8e27837a3"
    "7d49c665ecde9a165ae8d9a0dd52d3f7a2bc943baa4820bc098b43b6bc22bbd6"
    "" "via [B._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A._sizeOf_inst "user constant" .inherited
    "9f571cee8cd34435aae331146255374c3c30bd41d22263eb4d83e9487a9971d1"
    "54973d3d9bb18049964be678045a1e40cecfa0e5bf1d2ad1a317c2f92e30dbc6"
    "" "via [A._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.size._f "user constant over the block" .pendingSurgery
    "c0ed98ee378360d330b40f22a2fd2b9a06153d051825644cec6ae0333f7250b2"
    "cba795713763a988a2e39d99cdd9df454109dca88c2dabc952ac3809b94c65aa"
    "type.∀.body.∀.dom" "ROOT[TV]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.nil.sizeOf_spec "user constant" .inherited
    "1306c44721989e0badcb92934c7b477015f0d751772f8b67a115b6124d735d07"
    "b5fa3cb8b1525a19d0062f237547098e2c255984eb7f7f8053627f5d99155dd2"
    "" "via [A._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.size._unsafe_rec "user constant" .inherited
    "ad920014303db3248d907b1a8ab3ce2f10cca2dd45f2bc80f257b5edc2c291c0"
    "8971a737bb74f2e3401fca6c7f886d3baff6501671656520892d6a8bb0cc4382"
    "" "via [B.size, A.size._unsafe_rec]" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.size._sunfold "user constant" .inherited
    "ca27ead5b84f96c21500cca4e0522c912e2547f9f9045e34b242979270809eed"
    "874d9d7f8e96db471d83cca59f6ea7e75cc584b74fa77f38fc21a8ac60000219"
    "" "via [B.size]",
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `A.size._f "user constant over the block" .pendingSurgery
    "52f668901e95777428555c59f3cfd2c3a90221269c7a3ef2c67fd4342a007d5a"
    "ca91e86fe4ecb4e6c66f38344de75ec64f9e7622c3c281d7f2d0387e6febcb5a"
    "type.∀.body.∀.dom" "ROOT[TV]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQMut "twin" "orig" `B.s.sizeOf_spec "user constant" .inherited
    "853a2628d1ceb69d1a65b68133be82b294e6575e9d0458cddaf8f2b5f57dc8fb"
    "66741a12c494398677fea024de17cd0555bbeb4a4e37b8327757eb27e1555a0c"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  -- Repro.DQSplit twin orig
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending
    "19e46c2c75aba8115ea388c0f2c1cbc22f450d7fcd18cf31fd375cde30828552"
    "e4d11263f453968ce5706ff7a95cb3f070de605ac33f27c0837943d281cfdb99"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B._sizeOf_1 "sizeOf family" .o11aPending
    "2eb155e210e144924c8fd6fcd34064b3de93e368d1c4e0db0084d6e6757ad662"
    "8d5765e26230649e231043a713b9dd9ed080dcdc8e6911dca537abcc3d8a4949"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.nil.sizeOf_spec "user constant" .inherited
    "9a2ccaeac841163498ff30c729158232c2fde2948c593b0434359c016a391fcf"
    "f9e83c2c4d51ad4ae4028b013e568253616972ccbbea2849722deb8262f15469"
    "" "via [A._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `sum1 "user constant" .inherited
    "cb50a2624f5ad023677ab12de80a33455ead17b955e22e4d1d61e8efc413b113"
    "1df133cb0febd51a9557f5811914ff7f64f8b3664b1a70636332131573a86fe0"
    "" "via [A.sum]" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A._sizeOf_inst "user constant" .inherited
    "cb38961a123f89cadfc53462a78ff4dbfea68b5aabccb0706ec0e7a5853ad4b7"
    "48e358be8011bfb098eea1dea62bee4bf4658cd0560e27a1da3d41e46289f203"
    "" "via [A._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.len "user constant over the block" .pendingSurgery
    "a547241d523add64489dbe6d9bcffdaa0e11cee9fd2d77c1f8340fb5c5899246"
    "dc79effd63963fa7a79a675fcd34a5391398b70bb1786a50a92ae2329ea93216"
    "value.λ.body" "ROOT[V]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.len._sunfold "user constant" .inherited
    "4d723026dd9e109918901fa7dad29203102a220255ced0743a93ddfe9d957c37"
    "fdffe33c9b7baaab094d09e182f69eaf6188b201d227226946656f468259bb9e"
    "" "via [A.len]" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.sum._sunfold "user constant" .inherited
    "94b9d8b062531a4a3943a576e713f7a9dd7512501e1c51f224b970bf400aa145"
    "a522c7a8a7f3fc2609ae7c85da5185973a868e59daa42698013f55b2283f3f66"
    "" "via [A.sum]" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B._sizeOf_inst "user constant" .inherited
    "1d662c74343e801295e61ed520909bebbadea0abcf4dba8cbb364da8879b8a4e"
    "77dc1ccd27dce6b852349c7a81df41777528d9720a65930ef14434b1f87f7724"
    "" "via [B._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `len_succ "user constant" .inherited
    "989a21960afdfd4c3e43ac3e8a38c11d77ce64f365deeeb593253f1358a8a82c"
    "ed38e241ea2ccbaedb2e9862b4eea5c3f1a09cbde400da088eebf8ae37658c09"
    "" "via [A.len]" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.a.sizeOf_spec "user constant" .inherited
    "028b918c12d718298eb45d488de35571619507e7cd476a66da582e007caf017d"
    "bf392fbb8a10cd64814ad40fdb6dfec6cbe2f49b966493429a3709a3b95d41a3"
    "" "via [A._sizeOf_inst, B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.noConfusionType "noConfusion" .pendingNoConfusion
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0"
    "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.sum "user constant over the block" .pendingSurgery
    "c7129e39f7bfd2043f3378c09e6f9d5edf719f73180cd4ae03f319cc262f60fd"
    "bc7d14c681d385e667a42be6911963d0b89491be2fe04ff2b50277356b9af923"
    "value.λ.body" "ROOT[V]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `len2 "user constant" .inherited
    "c7de97e5d77bc5368dd7623036851ed5296ee3ad2b92c5b103e44f3ac577d806"
    "30febaeac5efaf6083d3751e44b26a3a61b6af50c073304123b2924a5ac8f8b3"
    "" "via [A.len]" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.len._f "user constant over the block" .pendingSurgery
    "4cf893733c374cb1e3d3193e6849687b35b597e8339b7a494c69912565a5b934"
    "b851cd1ee780cdfae816daf5790d55279735fd46c8dd0bb9ace18e575cec7ade"
    "type.∀.body.∀.dom" "ROOT[TV]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.noConfusion "noConfusion" .pendingNoConfusion
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6"
    "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8"
    "value.λ.body.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `A.sum._f "user constant over the block" .pendingSurgery
    "de86570efb9b22e8cf776caf80d968a5ad6fab401dadf8c32bd55dcc70c4fffa"
    "07c98cc82ab4c4687d1063fddd5ae1228d11ff2eda28b4ffdf07b49bdfd1be7a"
    "type.∀.body.∀.dom" "ROOT[TV]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.nil.sizeOf_spec "user constant" .inherited
    "164baa947a79432ca63998f83c59be1d1ee4b7c778fff0935066dd4c99630ec6"
    "807fd428e3686f34df2b15b45000a0a4f5695b00ddb988b010c6b1b0adc471b9"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.below "block auxiliary" .pendingSplitAux
    "-"
    "3c4e5e0325b928dbbcdc4473eb4bb5f0d6a1c3d2eff6dd285b714a8b7b321ad4"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.brecOn.go "block auxiliary" .pendingSplitAux
    "-"
    "371323c3fee0586738316d6e9a5bdfa221500547aa7e82c865778a5b2df89984"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.brecOn.eq "block auxiliary" .pendingSplitAux
    "-"
    "97987e8dbbaad054e89691e2052e6bf10a98d54403579a067423db9774cbdf5b"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.DQSplit "twin" "orig" `B.brecOn "block auxiliary" .pendingSplitAux
    "-"
    "435319816b6206ccd7eeab703e1c2bc0bf35de933c9cb66a9e3fe1f973256b86"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  -- Repro.EvapClosure twin orig
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B._sizeOf_1 "sizeOf family" .o11aPending
    "2eb155e210e144924c8fd6fcd34064b3de93e368d1c4e0db0084d6e6757ad662"
    "abc8ab2a5a0598560993554b00908c3b6588c58d4b02fb2f8a04d5c17eb15c27"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending
    "b7026d7e4027e86fbe090ab636abd8a416c3c971b1d812279d35834decbb2206"
    "d051a3b11fda5e1fd6283976780f51a3b8dbc4b0472e84a037f00082e2a28f2a"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A._sizeOf_inst "user constant" .inherited
    "c9d5273c0cd7358fdd658363e800e780d218f2dbb4a459e54809caa2b5771f70"
    "9eb842c96c0a0f14caa0c59739fdc56a182024eb93ac8bdd79746bf215b6d13d"
    "" "via [A._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.leaf.sizeOf_spec "user constant" .inherited
    "164baa947a79432ca63998f83c59be1d1ee4b7c778fff0935066dd4c99630ec6"
    "35c95a788b72f77c7f3e0871f243dfc8915e1f2d190297161b9c453553997c37"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B._sizeOf_inst "sizeOf family" .o11aPending
    "1d662c74343e801295e61ed520909bebbadea0abcf4dba8cbb364da8879b8a4e"
    "34fa066f60a574e48422f31768ab6646ba8bdaa3d455cc5fcf99caa1d6cbf34c"
    "value.@1.λ.body.fn" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.noConfusionType "noConfusion" .pendingNoConfusion
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0"
    "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.mk.sizeOf_spec "sizeOf family" .o11aPending
    "62da2845006a89ddbf242ec098db179137bec49fd23f804e990969d2cc35c5d3"
    "76a38bea70c25e9cfe33209f9fc3c2c0e490f9d9017947dbfa17808d1aca23ca"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.noConfusion "noConfusion" .pendingNoConfusion
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6"
    "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8"
    "value.λ.body.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.brecOn.eq "block auxiliary" .pendingSplitAux
    "-"
    "97987e8dbbaad054e89691e2052e6bf10a98d54403579a067423db9774cbdf5b"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.rec_1 "block auxiliary" .pendingSplitAux
    "-"
    "c97d72825e7174357a69f7d7104f4ea61941d6df5c1884fc57c1b6ad13fea4c6"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.brecOn_1.go "block auxiliary" .pendingSplitAux
    "-"
    "ae669f7803b9fd9525e2e762a465b2f52be9707973288888c628c45a57e45a46"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A._sizeOf_3 "sizeOf family" .o11aPending
    "-"
    "9cd8836e897cc4b9aa8d12acb7bcd2bba641d62d7b01cf5d4e52ccac65485448"
    "" "ONLY-B; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A._sizeOf_3_eq "sizeOf family" .o11aPending
    "-"
    "fe5c81d50dbf669d74fa36e909fe89f15eda287dcf7eff0de5b0e1f5379d17c8"
    "" "ONLY-B; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.brecOn_1.eq "block auxiliary" .pendingSplitAux
    "-"
    "04c951c6f916a50e05dc95c5d3a1698fdf5bee142e7cbce18e7ad27bf0646010"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.brecOn "block auxiliary" .pendingSplitAux
    "-"
    "435319816b6206ccd7eeab703e1c2bc0bf35de933c9cb66a9e3fe1f973256b86"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.brecOn.eq "block auxiliary" .pendingSplitAux
    "-"
    "d31b22b3842163fa887d4c1097c43436480fb4b133ae92bd444c676b3e3a4fde"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.brecOn.go "block auxiliary" .pendingSplitAux
    "-"
    "371323c3fee0586738316d6e9a5bdfa221500547aa7e82c865778a5b2df89984"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.below_1 "block auxiliary" .pendingSplitAux
    "-"
    "fcc44c8bda9050a304725204976d1ec9eeff1d48982400fb584280f65755b576"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.brecOn_1 "block auxiliary" .pendingSplitAux
    "-"
    "86afbd52f820a54a67734a8a07c82aee4bb33a7b0413769cda8a3f66fcefc7d5"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.brecOn.go "block auxiliary" .pendingSplitAux
    "-"
    "89ba4c8ab7495fe2f3fc0ab2b6e2086f0606d3e91cd2d7340ae5f6130b15df44"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `B.below "block auxiliary" .pendingSplitAux
    "-"
    "3c4e5e0325b928dbbcdc4473eb4bb5f0d6a1c3d2eff6dd285b714a8b7b321ad4"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.brecOn "block auxiliary" .pendingSplitAux
    "-"
    "0b05ef12de295ac32445f6803f764628639514c38e5d65caab6a8d7253cf8105"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.EvapClosure "twin" "orig" `A.below "block auxiliary" .pendingSplitAux
    "-"
    "a2c329bc27cc8d91ec9f035befc8fa7210de33b894f4c1205a2678dc4ea226d3"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  -- Repro.F2_SplitNestedClosure twin orig
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending
    "b7026d7e4027e86fbe090ab636abd8a416c3c971b1d812279d35834decbb2206"
    "d051a3b11fda5e1fd6283976780f51a3b8dbc4b0472e84a037f00082e2a28f2a"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B._sizeOf_1 "sizeOf family" .o11aPending
    "2eb155e210e144924c8fd6fcd34064b3de93e368d1c4e0db0084d6e6757ad662"
    "abc8ab2a5a0598560993554b00908c3b6588c58d4b02fb2f8a04d5c17eb15c27"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B._sizeOf_inst "sizeOf family" .o11aPending
    "1d662c74343e801295e61ed520909bebbadea0abcf4dba8cbb364da8879b8a4e"
    "34fa066f60a574e48422f31768ab6646ba8bdaa3d455cc5fcf99caa1d6cbf34c"
    "value.@1.λ.body.fn" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.mk.sizeOf_spec "sizeOf family" .o11aPending
    "62da2845006a89ddbf242ec098db179137bec49fd23f804e990969d2cc35c5d3"
    "76a38bea70c25e9cfe33209f9fc3c2c0e490f9d9017947dbfa17808d1aca23ca"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.noConfusion "noConfusion" .pendingNoConfusion
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6"
    "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8"
    "value.λ.body.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A._sizeOf_inst "user constant" .inherited
    "c9d5273c0cd7358fdd658363e800e780d218f2dbb4a459e54809caa2b5771f70"
    "9eb842c96c0a0f14caa0c59739fdc56a182024eb93ac8bdd79746bf215b6d13d"
    "" "via [A._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.noConfusionType "noConfusion" .pendingNoConfusion
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0"
    "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.leaf.sizeOf_spec "user constant" .inherited
    "164baa947a79432ca63998f83c59be1d1ee4b7c778fff0935066dd4c99630ec6"
    "35c95a788b72f77c7f3e0871f243dfc8915e1f2d190297161b9c453553997c37"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.below "block auxiliary" .pendingSplitAux
    "-"
    "3c4e5e0325b928dbbcdc4473eb4bb5f0d6a1c3d2eff6dd285b714a8b7b321ad4"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.brecOn.go "block auxiliary" .pendingSplitAux
    "-"
    "89ba4c8ab7495fe2f3fc0ab2b6e2086f0606d3e91cd2d7340ae5f6130b15df44"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.brecOn.eq "block auxiliary" .pendingSplitAux
    "-"
    "d31b22b3842163fa887d4c1097c43436480fb4b133ae92bd444c676b3e3a4fde"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.brecOn "block auxiliary" .pendingSplitAux
    "-"
    "0b05ef12de295ac32445f6803f764628639514c38e5d65caab6a8d7253cf8105"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.brecOn_1 "block auxiliary" .pendingSplitAux
    "-"
    "86afbd52f820a54a67734a8a07c82aee4bb33a7b0413769cda8a3f66fcefc7d5"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.brecOn_1.go "block auxiliary" .pendingSplitAux
    "-"
    "ae669f7803b9fd9525e2e762a465b2f52be9707973288888c628c45a57e45a46"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.brecOn.go "block auxiliary" .pendingSplitAux
    "-"
    "371323c3fee0586738316d6e9a5bdfa221500547aa7e82c865778a5b2df89984"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.below "block auxiliary" .pendingSplitAux
    "-"
    "a2c329bc27cc8d91ec9f035befc8fa7210de33b894f4c1205a2678dc4ea226d3"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.below_1 "block auxiliary" .pendingSplitAux
    "-"
    "fcc44c8bda9050a304725204976d1ec9eeff1d48982400fb584280f65755b576"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.brecOn.eq "block auxiliary" .pendingSplitAux
    "-"
    "97987e8dbbaad054e89691e2052e6bf10a98d54403579a067423db9774cbdf5b"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.brecOn_1.eq "block auxiliary" .pendingSplitAux
    "-"
    "04c951c6f916a50e05dc95c5d3a1698fdf5bee142e7cbce18e7ad27bf0646010"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A.rec_1 "block auxiliary" .pendingSplitAux
    "-"
    "c97d72825e7174357a69f7d7104f4ea61941d6df5c1884fc57c1b6ad13fea4c6"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A._sizeOf_3 "sizeOf family" .o11aPending
    "-"
    "9cd8836e897cc4b9aa8d12acb7bcd2bba641d62d7b01cf5d4e52ccac65485448"
    "" "ONLY-B; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `A._sizeOf_3_eq "sizeOf family" .o11aPending
    "-"
    "fe5c81d50dbf669d74fa36e909fe89f15eda287dcf7eff0de5b0e1f5379d17c8"
    "" "ONLY-B; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F2_SplitNestedClosure "twin" "orig" `B.brecOn "block auxiliary" .pendingSplitAux
    "-"
    "435319816b6206ccd7eeab703e1c2bc0bf35de933c9cb66a9e3fe1f973256b86"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  -- Repro.F4_NestedAlphaUsers twin orig
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `r "user constant over the block" .bare
    "86299fa8f0c366ae2631be68e91d8b14c1b3e342e11670eaeba6dcc994681448"
    "e1c4d3722d61b64a8b62b83d776b589abe9e8b0e127c860a8cb7e804cf55c228"
    "type.∀.body.∀.dom.∀.dom" "ROOT[T]; bare `@A.rec`: its type follows the grouping" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A._sizeOf_2 "sizeOf family" .o11aPending
    "c0d565ce645018032c7aae2532bd445df402682958293efbd1c1d5ed84832a01"
    "3b894264fb2b61fa899db79e1b64ace46e4c3391452a5711668292b060f6fffa"
    "type.∀.dom" "ROOT[TV]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A._sizeOf_3_eq "sizeOf family" .o11aPending
    "-"
    "203831d813d2dd11fdb6657a41dbb43dc270341bb11c039dae14f3c436c1dd12"
    "" "ONLY-B; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.brecOn_2.eq "block auxiliary" .pendingCollapse
    "-"
    "f9f356444c9e8ea3741bc7ffa246785a017f778edf0f8436c9c69e7de8a55ec8"
    "" "ONLY-B; nested auxiliary of the collapsed member (`List B`, merged into `List A` by collapse)" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.brecOn_2 "block auxiliary" .pendingCollapse
    "-"
    "b477fc4695d6a2d6e91e08c6939fabe67e1e948f3e10fadeb5e8510537750659"
    "" "ONLY-B; nested auxiliary of the collapsed member (`List B`, merged into `List A` by collapse)" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A._sizeOf_3 "sizeOf family" .o11aPending
    "-"
    "c0d565ce645018032c7aae2532bd445df402682958293efbd1c1d5ed84832a01"
    "" "ONLY-B; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.below_2 "block auxiliary" .pendingCollapse
    "-"
    "694093dbce13e3f60731f046c62ef385f2e4e1c27b330e0f3a392ff9ce973fc3"
    "" "ONLY-B; nested auxiliary of the collapsed member (`List B`, merged into `List A` by collapse)" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.F4_NestedAlphaUsers "twin" "orig" `A.brecOn_2.go "block auxiliary" .pendingCollapse
    "-"
    "df56c854d9a96c311facb49986499e1a1c270ba4be3f052fc9c46d6cc0ff99de"
    "" "ONLY-B; nested auxiliary of the collapsed member (`List B`, merged into `List A` by collapse)" (kernelsB := (true, true, false)),
  -- Repro.PropCollapse twin orig
  e `Tests.Ix.Compile.Twins.Repro.PropCollapse "twin" "orig" `p_cases "user constant over the block" .pendingCollapse
    "6a99811d2992052ed277106b72cc898e60dcd6a850b6bdcbd9bd9c8945cac093"
    "9c52c63fb2c6c1e3385fcafdef09ed564af1b69901d57fefff915c2c3edda9e7"
    "value.λ.body.fn" "ROOT[V]; `cases` on a collapsed Prop pair (O8)" (kernelsB := (false, false, false)),
  -- Repro.PropSplit twin orig
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `p2 "user constant over the block" .pendingSurgery
    "1bd7cb9e53fe8f73cc204973b247ad505caba1a00ab1427ff725104f7fe8cfda"
    "35a1be57bc0a9e78e9c74f555f3ef4920aabad217080510b47dfc94cfa1a173f"
    "value.λ.body" "ROOT[V]; user of a split Prop member recursor (WB PropSplit: universe count; images, A3)" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `q1 "user constant over the block" .pendingSurgery
    "fe79fec6d1b0c2a7a6511dd85a3ae5407ce9f77705e235b76cbdab970db69667"
    "a9fb37f6a8cfdc06fcf74e99043dd33855f3df1827bc99b3db2847894c436ce3"
    "value.λ.body.fn" "ROOT[V]; user of a split Prop member recursor (WB PropSplit: universe count; images, A3)" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `p1 "user constant over the block" .pendingSurgery
    "fe79fec6d1b0c2a7a6511dd85a3ae5407ce9f77705e235b76cbdab970db69667"
    "a9fb37f6a8cfdc06fcf74e99043dd33855f3df1827bc99b3db2847894c436ce3"
    "value.λ.body.fn" "ROOT[V]; user of a split Prop member recursor (WB PropSplit: universe count; images, A3)" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.PropSplit "twin" "orig" `q2 "user constant over the block" .pendingSurgery
    "51c3ddba2dbb2ef3af1d9d7fde23619f8e39166150e8336714a58842e571262a"
    "1058623f06ffd2ca2dd967d8d7272a87bab174fd233bfdc3e3d09cd04f6276a8"
    "value.λ.body" "ROOT[V]; user of a split Prop member recursor (WB PropSplit: universe count; images, A3)" (kernelsB := (false, false, false)),
  -- Repro.SurgCollapse twin orig
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.f._sunfold "user constant" .inherited
    "20c99d4437f9bab6f7f011cdc25dd9ee8fa9bb6e423ca29ac2b0c0ccae5b2d0b"
    "7636e396e02c68d40b90aa64d57cd383adc9ff6e178331a50918d13367015cbd"
    "" "via [B.g]",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `f "user constant over the block" .collapseArms
    "3c9135f1e3f63dfd29969a8d01c25a8645a4a945598f61c6a26732dd711d6ab6"
    "499400ea4502ecbb33aca48161db72f399d875d84e7605b0bdc94a5b632013ac"
    "value" "ROOT[V]; collapsed pair with different arms (WB-B4; refused after A0)",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `B.g._f "user constant over the block" .collapseArms
    "613f59a1c61670d3010245031560fec838787e2cd97f1de4c5c4481c24310a3a"
    "5fda7ac48a527b0b71e330df93c67f2ab158fefb0c9fbfff37a7670a351af848"
    "type.∀.body.∀.dom" "ROOT[TV]; collapsed pair with different arms (WB-B4; refused after A0)",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `fg_ab "user constant" .inherited
    "41ff23acda237cb9bb054d197a1b5637f5383f5b00f0c81efc3b8147143e8c26"
    "d134337f3e0c00a608debbb55f2429863f4cee68454b2e157a8d37a6da59823d"
    "" "via [A.f]" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `B.g "user constant over the block" .collapseArms
    "134a7a9f34fc485fac30cec655ec00100c540956a105cdcd37d7e86c98ffe269"
    "c157092a95fb45e35eecf49dcf02951be735193bf3bbd02a10cc8c1970953121"
    "value.λ.body" "ROOT[V]; collapsed pair with different arms (WB-B4; refused after A0)",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.f._f "user constant over the block" .collapseArms
    "e800823c91a33fa63d7fde3629e0a00848f7316f8d091c7541922145298bb764"
    "c0ed98ee378360d330b40f22a2fd2b9a06153d051825644cec6ae0333f7250b2"
    "type.∀.body.∀.dom" "ROOT[TV]; collapsed pair with different arms (WB-B4; refused after A0)",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `A.f "user constant over the block" .collapseArms
    "eb51753163b5c03ca62651f58f5819aee628d81d70bb82576db800be3617ac21"
    "1976b151603e58bd9808bf74d8c80155e0f44c94d7b2f1041493c9c6d639cddb"
    "value.λ.body" "ROOT[V]; collapsed pair with different arms (WB-B4; refused after A0)",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `B.g._sunfold "user constant over the block" .collapseArms
    "5e43692a9ebf82c357e0fcf3aae38885984ad14a9e9470afebc0f241434c57bc"
    "cc691d4e7f2bcc3dd87ae4f456135e1cd6c4cc44f750f6631b9d87c764613a4a"
    "value.λ.body.fn" "ROOT[V]; collapsed pair with different arms (WB-B4; refused after A0)",
  e `Tests.Ix.Compile.Twins.Repro.SurgCollapse "twin" "orig" `f_ab "user constant over the block" .collapseArms
    "-"
    "698fd5c11c25e89b1d6d63a0fc6f60f0fdfd0c31deaf53c8760356282ff4c69b"
    "" "ONLY-B; collapsed pair with different arms (WB-B4; refused after A0)" (kernelsB := (false, false, false)),
  -- Repro.SurgIdx twin orig
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending
    "9355113f809718723b3a8de22294befb19bb17826d40108439ed9ebd2c43dedd"
    "95f13d12169f410396c318de22a800eb5242995000e39f2b60b20395396f228c"
    "value.λ.body.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B._sizeOf_1 "sizeOf family" .o11aPending
    "f3f9cc6a6602b8596c5bfbbc20987f4be2892697fb83368bcf1e2283b3f68a7b"
    "13157d2102543f3e0ba8636859a9c9c170ee987060813fbca01c636d4bb45a19"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.leaf.sizeOf_spec "user constant" .inherited
    "a572550a6184263f6d3999ca82aa84c41b6e33ef8fa4c1ab4a4b72e95496e4be"
    "1c9edd583856aafcdb7735de5bc5eb19ca6f10e62e681709d5b5b426b6e5c4b7"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B.node.sizeOf_spec "user constant" .inherited
    "853a2628d1ceb69d1a65b68133be82b294e6575e9d0458cddaf8f2b5f57dc8fb"
    "62c21e83df6d6ba6493e1c1808276dc99861a75c477c6b2487f2f36180843dbe"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.mk.sizeOf_spec "user constant" .inherited
    "9665285930461804b77abb5a641360b34b5c8bec9552c673f7ac0cdd74f50855"
    "6fda9f4c65e4f033d0cea4cb7496e75c7013b08da288c39e0d4f2bfa867b0a98"
    "" "via [A._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `B._sizeOf_inst "user constant" .inherited
    "0bb01d3cc9090441a4b6e2ebc8038a1ff31e3e06e850342abf7a5be8e27837a3"
    "67599e3dc9e47094959cf60500e86a836e4d1f1bc3af366d7aba3ec49b1648af"
    "" "via [B._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A._sizeOf_inst "user constant" .inherited
    "f945b5596af1982bf2e8a32944f0dfd0a1ba4437dfa85eb299b336af1de560f0"
    "eaea4ac10bcc700b55b3bb1a3fdddd38e56c7df106e873e3a251221d9d062ef3"
    "" "via [A._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.brecOn "block auxiliary" .pendingSplitAux
    "-"
    "1e71a4056094c78fe34b45becb276af95dd9009371a57c9535abb42cb114fd5c"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.brecOn.go "block auxiliary" .pendingSplitAux
    "-"
    "06c9bce40823e60cdbfe111a910d1091c5f632aff9e7c64b46d30accea0549f8"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.below "block auxiliary" .pendingSplitAux
    "-"
    "dc8e5fbbda99f5f3511e8afbb534be0299b879c801a0e33fa8c3a14c58626bec"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx "twin" "orig" `A.brecOn.eq "block auxiliary" .pendingSplitAux
    "-"
    "206f9e285b9b0d5bce33cbbcf91dd0a6d41b7399fac053188d88b2a1383513fa"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  -- Repro.SurgIdx2 twin orig
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending
    "2eb155e210e144924c8fd6fcd34064b3de93e368d1c4e0db0084d6e6757ad662"
    "364fed2c26363125c9d0d9b5d19c9063f752dcd5fd8657b334b4ea60ea43a550"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B._sizeOf_1 "sizeOf family" .o11aPending
    "edf5bfacfc4993cbbeba2ace3c050a918e9b50a1e37d3e14fcb4a892c6e93a01"
    "356b34118bb6527712037f65a0e4f270cdb5759f25b1eecc4ea00ead483d183a"
    "value.λ.body.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.size._f "user constant over the block" .pendingSurgery
    "31412935835a3fb0d46666e16bdb86dea8b23a49d0850f235f0ac7282d87c385"
    "ce32b87716c8e8b9cb0886ddf87de2180b6ec306859f2ed2a76ee6298ecd2dff"
    "type.∀.body.∀.body.∀.dom" "ROOT[TV]; brecOn call site of a member with another index count (WB SurgIdx; images, A3)",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B._sizeOf_inst "user constant" .inherited
    "3cd85a68a7cf7c3bc0922b28ac5c059b40782d86f32b1f0357ad1d923278a66d"
    "8ab00abc724e3b49cd34d88d65b0f0d77df7d52763593e66387e3c22871eb1e4"
    "" "via [B._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.node.sizeOf_spec "user constant" .inherited
    "e68760dc05f9074f9bd84f469844c0bb02c641153d9f799e6099e38b40526a41"
    "63e3cdce5c5dfe34020342b288d4dbaef55137e72a83542e16e95e69eceb7272"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A._sizeOf_inst "user constant" .inherited
    "1d662c74343e801295e61ed520909bebbadea0abcf4dba8cbb364da8879b8a4e"
    "0c9a1942757f4538c2254de810bef57156c156271b725c8ff50842fd209d7f80"
    "" "via [A._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.noConfusion "noConfusion" .pendingNoConfusion
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6"
    "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8"
    "value.λ.body.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.noConfusionType "noConfusion" .pendingNoConfusion
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0"
    "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.mk.sizeOf_spec "user constant" .inherited
    "164baa947a79432ca63998f83c59be1d1ee4b7c778fff0935066dd4c99630ec6"
    "20325ae3c26d282e5df9a952db6a82c41c9736f05c22423ec0adfba2b021dce9"
    "" "via [A._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.size "user constant over the block" .pendingSurgery
    "6080eafe62eb306a3fd21ce255d6bb2e851ebd04f14bf55105e5ffb01f208bb8"
    "b968379be08a372c97bf7e9a0eeab04ae749d5f46ca00ac7753ffa63c872d610"
    "value.λ.body.λ.body" "ROOT[V]; brecOn call site of a member with another index count (WB SurgIdx; images, A3)" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `bsize "user constant" .inherited
    "79607be1835bfd6e897fb762fcb38297ab2e0e1897c873fe478ece6235635206"
    "5a96f8be8b2baf5139255c6a1671266ca0e0e5d21998f5a9a97b14a2731c2792"
    "" "via [B.size]" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.leaf.sizeOf_spec "user constant" .inherited
    "d516e3ce8b6b6f7b0c5dcfb55cac3b9b933cd693d7801f8fb429f2bed08e3b68"
    "fa5363da0a5e128a62e66034cfe39b5d51733b3248735151ab2eedb67ec85312"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `B.size._sunfold "user constant" .inherited
    "4939f2f2890510c9c6c6b3c2e71ec76cccd617d865eec7695fa65cb5cdd17455"
    "3d21cfe7f9cb43244e72f96f6f4eec70cf81f18c813fed0fee2f8fe085fadd50"
    "" "via [B.size]" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.below "block auxiliary" .pendingSplitAux
    "-"
    "3c4e5e0325b928dbbcdc4473eb4bb5f0d6a1c3d2eff6dd285b714a8b7b321ad4"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.brecOn "block auxiliary" .pendingSplitAux
    "-"
    "435319816b6206ccd7eeab703e1c2bc0bf35de933c9cb66a9e3fe1f973256b86"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.brecOn.go "block auxiliary" .pendingSplitAux
    "-"
    "371323c3fee0586738316d6e9a5bdfa221500547aa7e82c865778a5b2df89984"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgIdx2 "twin" "orig" `A.brecOn.eq "block auxiliary" .pendingSplitAux
    "-"
    "97987e8dbbaad054e89691e2052e6bf10a98d54403579a067423db9774cbdf5b"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  -- Repro.SurgSplit twin orig
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B._sizeOf_1 "sizeOf family" .o11aPending
    "2eb155e210e144924c8fd6fcd34064b3de93e368d1c4e0db0084d6e6757ad662"
    "8d5765e26230649e231043a713b9dd9ed080dcdc8e6911dca537abcc3d8a4949"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A._sizeOf_1 "sizeOf family" .o11aPending
    "19e46c2c75aba8115ea388c0f2c1cbc22f450d7fcd18cf31fd375cde30828552"
    "e4d11263f453968ce5706ff7a95cb3f070de605ac33f27c0837943d281cfdb99"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.len._sunfold "user constant" .inherited
    "4d723026dd9e109918901fa7dad29203102a220255ced0743a93ddfe9d957c37"
    "fdffe33c9b7baaab094d09e182f69eaf6188b201d227226946656f468259bb9e"
    "" "via [A.len]" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.noConfusion "noConfusion" .pendingNoConfusion
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6"
    "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8"
    "value.λ.body.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.noConfusionType "noConfusion" .pendingNoConfusion
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0"
    "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.a.sizeOf_spec "user constant" .inherited
    "028b918c12d718298eb45d488de35571619507e7cd476a66da582e007caf017d"
    "bf392fbb8a10cd64814ad40fdb6dfec6cbe2f49b966493429a3709a3b95d41a3"
    "" "via [B._sizeOf_inst, A._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.len._f "user constant over the block" .pendingSurgery
    "4cf893733c374cb1e3d3193e6849687b35b597e8339b7a494c69912565a5b934"
    "b851cd1ee780cdfae816daf5790d55279735fd46c8dd0bb9ace18e575cec7ade"
    "type.∀.body.∀.dom" "ROOT[TV]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (WB SurgSplit)" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.nil.sizeOf_spec "user constant" .inherited
    "164baa947a79432ca63998f83c59be1d1ee4b7c778fff0935066dd4c99630ec6"
    "807fd428e3686f34df2b15b45000a0a4f5695b00ddb988b010c6b1b0adc471b9"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `len2 "user constant" .inherited
    "c7de97e5d77bc5368dd7623036851ed5296ee3ad2b92c5b103e44f3ac577d806"
    "30febaeac5efaf6083d3751e44b26a3a61b6af50c073304123b2924a5ac8f8b3"
    "" "via [A.len]" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.nil.sizeOf_spec "user constant" .inherited
    "9a2ccaeac841163498ff30c729158232c2fde2948c593b0434359c016a391fcf"
    "f9e83c2c4d51ad4ae4028b013e568253616972ccbbea2849722deb8262f15469"
    "" "via [A._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A._sizeOf_inst "user constant" .inherited
    "cb38961a123f89cadfc53462a78ff4dbfea68b5aabccb0706ec0e7a5853ad4b7"
    "48e358be8011bfb098eea1dea62bee4bf4658cd0560e27a1da3d41e46289f203"
    "" "via [A._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B._sizeOf_inst "user constant" .inherited
    "1d662c74343e801295e61ed520909bebbadea0abcf4dba8cbb364da8879b8a4e"
    "77dc1ccd27dce6b852349c7a81df41777528d9720a65930ef14434b1f87f7724"
    "" "via [B._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `A.len "user constant over the block" .pendingSurgery
    "a547241d523add64489dbe6d9bcffdaa0e11cee9fd2d77c1f8340fb5c5899246"
    "dc79effd63963fa7a79a675fcd34a5391398b70bb1786a50a92ae2329ea93216"
    "value.λ.body" "ROOT[V]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (WB SurgSplit)" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.brecOn "block auxiliary" .pendingSplitAux
    "-"
    "435319816b6206ccd7eeab703e1c2bc0bf35de933c9cb66a9e3fe1f973256b86"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.brecOn.eq "block auxiliary" .pendingSplitAux
    "-"
    "97987e8dbbaad054e89691e2052e6bf10a98d54403579a067423db9774cbdf5b"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.brecOn.go "block auxiliary" .pendingSplitAux
    "-"
    "371323c3fee0586738316d6e9a5bdfa221500547aa7e82c865778a5b2df89984"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Repro.SurgSplit "twin" "orig" `B.below "block auxiliary" .pendingSplitAux
    "-"
    "3c4e5e0325b928dbbcdc4473eb4bb5f0d6a1c3d2eff6dd285b714a8b7b321ad4"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  -- Proto.C2 can src
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B._sizeOf_1 "sizeOf family" .o11aPending
    "2eb155e210e144924c8fd6fcd34064b3de93e368d1c4e0db0084d6e6757ad662"
    "8d5765e26230649e231043a713b9dd9ed080dcdc8e6911dca537abcc3d8a4949"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A._sizeOf_1 "sizeOf family" .o11aPending
    "19e46c2c75aba8115ea388c0f2c1cbc22f450d7fcd18cf31fd375cde30828552"
    "e4d11263f453968ce5706ff7a95cb3f070de605ac33f27c0837943d281cfdb99"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.a.sizeOf_spec "user constant" .inherited
    "028b918c12d718298eb45d488de35571619507e7cd476a66da582e007caf017d"
    "bf392fbb8a10cd64814ad40fdb6dfec6cbe2f49b966493429a3709a3b95d41a3"
    "" "via [A._sizeOf_inst, B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.cnt._sunfold "user constant" .inherited
    "c7b4b2af419c9bc6cf2285fd0b048dfaf8e422835c91f0e96ac44b85891a449a"
    "422ec3d6a3855cd5b3cb3098021eb844ce54228ab2cc72547b17f55e8903794f"
    "" "via [A.cnt]" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.cnt "user constant over the block" .pendingSurgery
    "9d8bdb0bfbdc878f109d4e9acc712eb7e09b04a0fffcde3fd31b9495e9117212"
    "6452e6bdda977d0319fcce196663eca5f6b1f133d4661c51d4a96571378e0b63"
    "value.λ.body" "ROOT[V]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.cnt._f "user constant over the block" .pendingSurgery
    "737d9847f6255247ce5ac946c55c9a631b41f125be5e7933ab807eaeb40c54d4"
    "e6bd484ba0cba23ee05933796be1982606745f6bdbab2cb917b8babf98eef62f"
    "type.∀.body.∀.dom" "ROOT[TV]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.len._sunfold "user constant" .inherited
    "4d723026dd9e109918901fa7dad29203102a220255ced0743a93ddfe9d957c37"
    "fdffe33c9b7baaab094d09e182f69eaf6188b201d227226946656f468259bb9e"
    "" "via [A.len]" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.viaRec "user constant over the block" .pendingSurgery
    "b3070b38cc2e3180e858b80263b21baf221e1a1cfbb4a835309c88695deb77f3"
    "34f461b855818b4255cc410913060938d692c56b669d3a148b67b185b03b77cd"
    "value" "ROOT[V]; raw `rec` user over a split block: relocated calls (O2)",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.noConfusionType "noConfusion" .pendingNoConfusion
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0"
    "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.nil.sizeOf_spec "user constant" .inherited
    "9a2ccaeac841163498ff30c729158232c2fde2948c593b0434359c016a391fcf"
    "f9e83c2c4d51ad4ae4028b013e568253616972ccbbea2849722deb8262f15469"
    "" "via [A._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A._sizeOf_inst "user constant" .inherited
    "cb38961a123f89cadfc53462a78ff4dbfea68b5aabccb0706ec0e7a5853ad4b7"
    "48e358be8011bfb098eea1dea62bee4bf4658cd0560e27a1da3d41e46289f203"
    "" "via [A._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B._sizeOf_inst "sizeOf family" .o11aPending
    "1d662c74343e801295e61ed520909bebbadea0abcf4dba8cbb364da8879b8a4e"
    "77dc1ccd27dce6b852349c7a81df41777528d9720a65930ef14434b1f87f7724"
    "value.@1.λ.body.fn" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.nil.sizeOf_spec "user constant" .inherited
    "164baa947a79432ca63998f83c59be1d1ee4b7c778fff0935066dd4c99630ec6"
    "807fd428e3686f34df2b15b45000a0a4f5695b00ddb988b010c6b1b0adc471b9"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.len._f "user constant over the block" .pendingSurgery
    "4cf893733c374cb1e3d3193e6849687b35b597e8339b7a494c69912565a5b934"
    "b851cd1ee780cdfae816daf5790d55279735fd46c8dd0bb9ace18e575cec7ade"
    "type.∀.body.∀.dom" "ROOT[TV]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `A.len "user constant over the block" .pendingSurgery
    "a547241d523add64489dbe6d9bcffdaa0e11cee9fd2d77c1f8340fb5c5899246"
    "dc79effd63963fa7a79a675fcd34a5391398b70bb1786a50a92ae2329ea93216"
    "value.λ.body" "ROOT[V]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.noConfusion "noConfusion" .pendingNoConfusion
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6"
    "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8"
    "value.λ.body.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.brecOn.eq "block auxiliary" .pendingSplitAux
    "-"
    "97987e8dbbaad054e89691e2052e6bf10a98d54403579a067423db9774cbdf5b"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.brecOn "block auxiliary" .pendingSplitAux
    "-"
    "435319816b6206ccd7eeab703e1c2bc0bf35de933c9cb66a9e3fe1f973256b86"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.brecOn.go "block auxiliary" .pendingSplitAux
    "-"
    "371323c3fee0586738316d6e9a5bdfa221500547aa7e82c865778a5b2df89984"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C2 "can" "src" `B.below "block auxiliary" .pendingSplitAux
    "-"
    "3c4e5e0325b928dbbcdc4473eb4bb5f0d6a1c3d2eff6dd285b714a8b7b321ad4"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  -- Proto.C2b can src
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A._sizeOf_1 "sizeOf family" .o11aPending
    "f3f9cc6a6602b8596c5bfbbc20987f4be2892697fb83368bcf1e2283b3f68a7b"
    "967266171d808ac10b7dfbd4c9cd05393c707ba3b3256d2d06ef3dd4fd250f4c"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.nil.sizeOf_spec "user constant" .inherited
    "a572550a6184263f6d3999ca82aa84c41b6e33ef8fa4c1ab4a4b72e95496e4be"
    "836f92cd1c41c103490e03aab5bbc75e399286711e5644c4e8a439c3b64fcc0c"
    "" "via [A._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.size._sunfold "user constant" .inherited
    "21dbec313e8724b3d0f337a66dd05d90119f32ad96b8f488a828e8babc9fab8b"
    "5cb9fcaa7ef3ff6b06c964f0da3344834d8cb0bacbb6b06242c822774dfad5da"
    "" "via [B.size]",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.size "user constant over the block" .pendingSurgery
    "d1d1b84b12affbd542eb57f26314db23b6c115609bef6ca69b6eb3946907df6a"
    "9ba97824ed6ec7fa7570346e71af6ebc5070693b674f2ae1ded573fedd81216c"
    "value.λ.body" "ROOT[V]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (no cross field)",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.len._f "user constant over the block" .pendingSurgery
    "c0ed98ee378360d330b40f22a2fd2b9a06153d051825644cec6ae0333f7250b2"
    "94d9b46a2f6e002c37cc218219bcc3729b6485a1b477cd05e6a8f3c2a039a73b"
    "type.∀.body.∀.dom" "ROOT[TV]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (no cross field)",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A._sizeOf_inst "user constant" .inherited
    "0bb01d3cc9090441a4b6e2ebc8038a1ff31e3e06e850342abf7a5be8e27837a3"
    "6323f9346acc4976b0d39335776164b5030f67413ba18af08be3489a6e8d96b9"
    "" "via [A._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.cons.sizeOf_spec "user constant" .inherited
    "853a2628d1ceb69d1a65b68133be82b294e6575e9d0458cddaf8f2b5f57dc8fb"
    "fdc304f7cb48d1ba0b6543c1ef7d6fb052c7ad2eac954e37626d41b48fcc8a9f"
    "" "via [A._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.len._sunfold "user constant" .inherited
    "ca27ead5b84f96c21500cca4e0522c912e2547f9f9045e34b242979270809eed"
    "db9a47085b1491cbb7b68fed257cb4870ce040541685dbb04d29752f97e2a109"
    "" "via [A.len]",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `A.len "user constant over the block" .pendingSurgery
    "7ab66120eb546a328d7a77dc24057c2590921b439880bd534377f46929624447"
    "9c13ccaab03593977d3f98699612a65ec4b5e5f5fdfd8ddfe21927a1ecfefb44"
    "value.λ.body" "ROOT[V]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (no cross field)",
  e `Tests.Ix.Compile.Twins.Proto.C2b "can" "src" `B.size._f "user constant over the block" .pendingSurgery
    "184b08ec1c68807cffcdb3404cdb2e19df236ca302ebc5b19a11d8296b3d73ed"
    "92804c9cc5307155d0d4d86ff0f21773a4e50ca79e73fd5f89259054a9efc35a"
    "type.∀.body.∀.dom" "ROOT[TV]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing) (no cross field)",
  -- Proto.C3 can src
  e `Tests.Ix.Compile.Twins.Proto.C3 "can" "src" `p1 "user constant over the block" .pendingSurgery
    "fe79fec6d1b0c2a7a6511dd85a3ae5407ce9f77705e235b76cbdab970db69667"
    "a9fb37f6a8cfdc06fcf74e99043dd33855f3df1827bc99b3db2847894c436ce3"
    "value.λ.body.fn" "ROOT[V]; user of a split Prop member recursor (WB PropSplit: universe count; images, A3)" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Proto.C3 "can" "src" `p2 "user constant over the block" .pendingSurgery
    "1bd7cb9e53fe8f73cc204973b247ad505caba1a00ab1427ff725104f7fe8cfda"
    "35a1be57bc0a9e78e9c74f555f3ef4920aabad217080510b47dfc94cfa1a173f"
    "value.λ.body" "ROOT[V]; user of a split Prop member recursor (WB PropSplit: universe count; images, A3)" (kernelsB := (false, false, false)),
  -- Proto.C3b can src
  e `Tests.Ix.Compile.Twins.Proto.C3b "can" "src" `q "user constant over the block" .pendingCollapse
    "fe79fec6d1b0c2a7a6511dd85a3ae5407ce9f77705e235b76cbdab970db69667"
    "1058623f06ffd2ca2dd967d8d7272a87bab174fd233bfdc3e3d09cd04f6276a8"
    "value.λ.body" "ROOT[V]; theorem over a collapsed Prop pair" (kernelsB := (false, false, false)),
  -- Proto.C4 can src
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B._sizeOf_1 "sizeOf family" .o11aPending
    "2eb155e210e144924c8fd6fcd34064b3de93e368d1c4e0db0084d6e6757ad662"
    "abc8ab2a5a0598560993554b00908c3b6588c58d4b02fb2f8a04d5c17eb15c27"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A._sizeOf_1 "sizeOf family" .o11aPending
    "b7026d7e4027e86fbe090ab636abd8a416c3c971b1d812279d35834decbb2206"
    "d051a3b11fda5e1fd6283976780f51a3b8dbc4b0472e84a037f00082e2a28f2a"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.noConfusionType "noConfusion" .pendingNoConfusion
    "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0"
    "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B._sizeOf_inst "sizeOf family" .o11aPending
    "1d662c74343e801295e61ed520909bebbadea0abcf4dba8cbb364da8879b8a4e"
    "34fa066f60a574e48422f31768ab6646ba8bdaa3d455cc5fcf99caa1d6cbf34c"
    "value.@1.λ.body.fn" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.noConfusion "noConfusion" .pendingNoConfusion
    "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6"
    "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8"
    "value.λ.body.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (c): enumeration form depends on the Lean block",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.leaf.sizeOf_spec "user constant" .inherited
    "164baa947a79432ca63998f83c59be1d1ee4b7c778fff0935066dd4c99630ec6"
    "35c95a788b72f77c7f3e0871f243dfc8915e1f2d190297161b9c453553997c37"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A._sizeOf_inst "user constant" .inherited
    "c9d5273c0cd7358fdd658363e800e780d218f2dbb4a459e54809caa2b5771f70"
    "9eb842c96c0a0f14caa0c59739fdc56a182024eb93ac8bdd79746bf215b6d13d"
    "" "via [A._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.mk.sizeOf_spec "sizeOf family" .o11aPending
    "62da2845006a89ddbf242ec098db179137bec49fd23f804e990969d2cc35c5d3"
    "76a38bea70c25e9cfe33209f9fc3c2c0e490f9d9017947dbfa17808d1aca23ca"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `useRec "user constant over the block" .pendingSurgery
    "8f6c02851a5204712eb85557310e53ceaf31f54c90254c741312c0e780fe327d"
    "b9d79d31a5a346d648538c432d0f90622fc332616e0bae945b3d75389e1570b4"
    "value" "ROOT[V]; raw `rec` user over a block whose nested auxiliary evaporates (O2)",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.brecOn_1.go "block auxiliary" .pendingSplitAux
    "-"
    "ae669f7803b9fd9525e2e762a465b2f52be9707973288888c628c45a57e45a46"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.rec_1 "block auxiliary" .pendingSplitAux
    "-"
    "c97d72825e7174357a69f7d7104f4ea61941d6df5c1884fc57c1b6ad13fea4c6"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.brecOn.go "block auxiliary" .pendingSplitAux
    "-"
    "371323c3fee0586738316d6e9a5bdfa221500547aa7e82c865778a5b2df89984"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A._sizeOf_3 "sizeOf family" .o11aPending
    "-"
    "9cd8836e897cc4b9aa8d12acb7bcd2bba641d62d7b01cf5d4e52ccac65485448"
    "" "ONLY-B; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.brecOn_1.eq "block auxiliary" .pendingSplitAux
    "-"
    "04c951c6f916a50e05dc95c5d3a1698fdf5bee142e7cbce18e7ad27bf0646010"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.brecOn.eq "block auxiliary" .pendingSplitAux
    "-"
    "d31b22b3842163fa887d4c1097c43436480fb4b133ae92bd444c676b3e3a4fde"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A._sizeOf_3_eq "sizeOf family" .o11aPending
    "-"
    "fe5c81d50dbf669d74fa36e909fe89f15eda287dcf7eff0de5b0e1f5379d17c8"
    "" "ONLY-B; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.below_1 "block auxiliary" .pendingSplitAux
    "-"
    "fcc44c8bda9050a304725204976d1ec9eeff1d48982400fb584280f65755b576"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.below "block auxiliary" .pendingSplitAux
    "-"
    "3c4e5e0325b928dbbcdc4473eb4bb5f0d6a1c3d2eff6dd285b714a8b7b321ad4"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.below "block auxiliary" .pendingSplitAux
    "-"
    "a2c329bc27cc8d91ec9f035befc8fa7210de33b894f4c1205a2678dc4ea226d3"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.brecOn.go "block auxiliary" .pendingSplitAux
    "-"
    "89ba4c8ab7495fe2f3fc0ab2b6e2086f0606d3e91cd2d7340ae5f6130b15df44"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.brecOn "block auxiliary" .pendingSplitAux
    "-"
    "435319816b6206ccd7eeab703e1c2bc0bf35de933c9cb66a9e3fe1f973256b86"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `B.brecOn.eq "block auxiliary" .pendingSplitAux
    "-"
    "97987e8dbbaad054e89691e2052e6bf10a98d54403579a067423db9774cbdf5b"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.brecOn "block auxiliary" .pendingSplitAux
    "-"
    "0b05ef12de295ac32445f6803f764628639514c38e5d65caab6a8d7253cf8105"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C4 "can" "src" `A.brecOn_1 "block auxiliary" .pendingSplitAux
    "-"
    "86afbd52f820a54a67734a8a07c82aee4bb33a7b0413769cda8a3f66fcefc7d5"
    "" "ONLY-B; §4.7 (b): nested auxiliary of the Lean block that evaporates in the split",
  -- Proto.C6 can src
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X._sizeOf_4 "sizeOf family" .o11aPending
    "-"
    "c0d565ce645018032c7aae2532bd445df402682958293efbd1c1d5ed84832a01"
    "" "ONLY-B; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C6 "can" "src" `X._sizeOf_4_eq "sizeOf family" .o11aPending
    "-"
    "203831d813d2dd11fdb6657a41dbb43dc270341bb11c039dae14f3c436c1dd12"
    "" "ONLY-B; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  -- Proto.C7 can src
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.self "user constant over the block" .pendingCollapse
    "9286fa32b14a78f4a7c1928f9065999665a8963b7881d11a88626b05b1bc7275"
    "a4a16434e0c27b1c2ab1ec7138ccc2f10c0835c161ad813f42d6caa3c775679f"
    "value.λ.body.λ.body.let.body" "ROOT[V]; structural theorems over a collapsed IndPred pair (O10)" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.self.match_1_7 "user constant over the block" .pendingCollapse
    "81f827493b8098b3c94644163b3a2a0728dc6d134e195b285c866f94be603b51"
    "-"
    "" "ONLY-A; structural theorems over a collapsed IndPred pair (O10)",
  e `Tests.Ix.Compile.Twins.Proto.C7 "can" "src" `X.self.match_2 "user constant over the block" .pendingCollapse
    "-"
    "920cfd422111124ad7f09da844c8e3d13025aa372c557ccc962331789ffcc971"
    "" "ONLY-B; structural theorems over a collapsed IndPred pair (O10)" (kernelsB := (false, false, false)),
  -- Proto.C7b can src
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.toR.match_2 "user constant over the block" .indPredBelow
    "798cdebbd7c748dcfec2c80a49bc29a7d196ab1b0b6629ebe66299db68c83187"
    "885530e94cb47575b8cdeea5d48647339a2fde64b57ebf95b0515883bc502eac"
    "type.∀.body.∀.body.∀.dom.∀.body.∀.body.∀.dom" "ROOT[TV]; Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.toR "user constant over the block" .indPredBelow
    "50fe12a59dc160f4a631b0f53326e0e214ee13c12c261804c7e2587bde392179"
    "60bcaf3e4f5eb2eda63082a5c8ec6541600f0f63b0fea9ff4e3ff7b2f01d87b5"
    "value.λ.body.λ.body.let.body.let.body" "ROOT[V]; Lean IndPredBelow family (and its users) of the changed Prop block, R split off" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `OddP.toR "user constant over the block" .indPredBelow
    "1b89d937bc08c34d761bcf15462418ddfa9a3b98c0edffd1a351a4a208652147"
    "f7537566880bd04f60701e51fc36bab5aeb10e02ca06832e530e4b0957645591"
    "value.λ.body.λ.body.let.body.let.body" "ROOT[V]; Lean IndPredBelow family (and its users) of the changed Prop block, R split off" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `EvenP.toR.match_2 "user constant over the block" .indPredBelow
    "fe1c05ab20b887b350ab84a0425e4e26781c9aa4ca8ef3205308063baa11c51a"
    "7064d688a309679e85646d41e78462c4e62d411b802385c3e25752b3a022e44e"
    "type.∀.body.∀.body.∀.dom.∀.body.∀.body.∀.dom" "ROOT[TV]; Lean IndPredBelow family (and its users) of the changed Prop block, R split off" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.below.casesOn "block auxiliary" .indPredBelow
    "-"
    "95ea6e993be6153c5c6fceaed9267578985aba35421d0b5ed21a3ff3e39a75c1"
    "" "ONLY-B; Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.below.rec "block auxiliary" .indPredBelow
    "-"
    "23d836c85e6bfe6a13b1700592d4fdec4490472c68276a1a3c4bf1121e27db09"
    "" "ONLY-B; Lean IndPredBelow family (and its users) of the changed Prop block, R split off",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.brecOn "block auxiliary" .indPredBelow
    "-"
    "d18a58d48e919bc69032806995ca939e6430d7b10044d640ad58be9629b858b3"
    "" "ONLY-B; Lean IndPredBelow family (and its users) of the changed Prop block, R split off; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.below "block auxiliary" .indPredBelow
    "-"
    "66942408d847ddf39d53a58d374630ed0f63debe7e6d997b8c6891f8cddb41db"
    "" "ONLY-B; Lean IndPredBelow family (and its users) of the changed Prop block, R split off; §4.7 (b): exists for the Lean block, not for the Ix component" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Proto.C7b "can" "src" `R.below.mk "user constant over the block" .indPredBelow
    "-"
    "04f783585b024cbab6e41e5ae8b2f80833de14827b2b95e38c9c96097f67b2af"
    "" "ONLY-B; Lean IndPredBelow family (and its users) of the changed Prop block, R split off" (kernelsB := (true, true, false)),
  -- Proto.C8 can src
  e `Tests.Ix.Compile.Twins.Proto.C8 "can" "src" `X._sizeOf_2 "sizeOf family" .o11aPending
    "8ac1ffd7a325a4cc834a0db80f114b18eb64eecfa0788eddcbb23ccb1dc11022"
    "4df3202436ffbd70a6b1d5c75d7ea85dd0830c7e39e20e3970fa53d5f37b787a"
    "type.∀.dom" "ROOT[TV]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  -- Proto.C9 can src
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A._sizeOf_1 "sizeOf family" .o11aPending
    "3fd79d6295e2750e0d18de5b6cd9d75489830c72a379ee3ef66ee712b6079cbc"
    "1a9e7d0bb87f4de6b16ba3c8d1737e9bc1ec7833a4cc20d64dd7c5b954f7e309"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B._sizeOf_1 "sizeOf family" .o11aPending
    "80507cb26e5140ea89bb0fff714f250b25e368ef5a4e6df03cd6346497d09c15"
    "4f4117df84a2c7c1e87c309ccc072f11d65b9301a3e4d085022e548115a3d8eb"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B._sizeOf_inst "sizeOf family" .o11aPending
    "6d98b1994c7c08ede07696dc4198139298c98a2602e2fade6b3f96c8a8fb519c"
    "c544744da25f4584d043b4a60a6ba118fa2d759d519d60c8df2f5618de1a7467"
    "value.λ.body.λ.body.@1.λ.body.fn" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A._sizeOf_inst "user constant" .inherited
    "a1d896f3080d0d531fd0d0a1f3dff7f06e256f89f2a75b440d1cf5f0a4b58ac3"
    "ff32ae4e2b7369ee709192600deef709aa8a0d9760ddfaa6ac8600cfb9fb0fb6"
    "" "via [A._sizeOf_1]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.leaf.sizeOf_spec "user constant" .inherited
    "d4709f9a9637dbbcb8476dc0ec9b6fd8616dabc41827886c8178e00b5c26be14"
    "f04abb152dc7cae17ff4ef1229555211a9f7cc8fea23aa285e765babe0a7d6ca"
    "" "via [B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.a.sizeOf_spec "user constant" .inherited
    "204d851c73e29e97ed79ec34676ab30109f86d80d438d3249f722938d7f5d09f"
    "90d5549e06683db87b562a802964709fa3ac651bf453f2b1a4bc531b6b8fc1e6"
    "" "via [A._sizeOf_inst, B._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.depth._sunfold "user constant" .inherited
    "e28d8f1382b9a037a12a52ff4416a54433b84e70baf9923a0f6fe8db63965460"
    "0b72e06e1cf815b07783ccecd3175605a9ff9bd8c26d3c716f5428027545493e"
    "" "via [A.depth]" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.depth._f "user constant over the block" .pendingSurgery
    "8fcb310ec4de65102343f86a9581d01f163665862a4716bd49277468697d434d"
    "c4e880910c15ff3b7a898aede63696550d07fd333d99ef1ba0a167428f755a95"
    "type.∀.body.∀.body.∀.dom" "ROOT[TV]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)" (kernelsB := (false, false, false)),
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.nil.sizeOf_spec "user constant" .inherited
    "63d898cf8525d6be264fd0d7010e8997f947bfabdc9e9e9f2fe2baf88f9105f7"
    "1809c16f2eeaf702c2f7529923c50498f01ced7f5ddf567d694c427d1c1e166c"
    "" "via [A._sizeOf_inst]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `A.depth "user constant over the block" .pendingSurgery
    "6b89d0d2e6de373c3c955e16a54e64d2a36d38bc13bbc28810893aa3515c811f"
    "e42d07e6e58e92fa5caccc20288bae57a314e43246fca20e07f6fb9c422c7bad"
    "value.λ.body.λ.body" "ROOT[V]; structural recursion over a split block: `below` path (`x.2.1` vs `x.1`) and the extra motive of the Lean block (O9 re-pathing)" (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.brecOn.eq "block auxiliary" .pendingSplitAux
    "-"
    "1ab20305c8c1d527968d6c03d4257f05b36438af8356ed120c10522487562858"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.brecOn "block auxiliary" .pendingSplitAux
    "-"
    "1f00654859c6a7c5c83b89867392ef9bde5120ea47049e03f5edf413f18806dc"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.brecOn.go "block auxiliary" .pendingSplitAux
    "-"
    "895e8d3f9ac70ef88d3788d8fa11468d402602b497fd2b7ae40f257f967cbf0e"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  e `Tests.Ix.Compile.Twins.Proto.C9 "can" "src" `B.below "block auxiliary" .pendingSplitAux
    "-"
    "c386201cea0b1fc4b153400accab49ae5e466f3e836340cba8e0bd91ac35dd1e"
    "" "ONLY-B; §4.7 (b): exists for the Lean block, not for the Ix component",
  -- Cliques.TP P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sa "clique member" .pendingTransport
    "e9d460ba7b4cd906fd0f660108b189fbfe154953883e20319d7dd6452d4ddaab"
    "3c2d53a05c70b77a5269ac8412b0095ed0dcca53d9ccebb753fbc6368e74d723"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sb._f "structural functional" .pendingTransport
    "2d3cb49f17edbe9962dffe39839decfcef1b848e952b2b0f0eb5a6bcfb0a46e9"
    "bb0d910606ace0c4f4f2ff9c4fe40706a578a62ae074e0184d55ed0b3758cf43"
    "type.∀.body.∀.dom.@0.λ.body.@0.@1.@0.@4" "ROOT[TV]; type of `_f` mentions the packed `below` motive (theorem statements in clique order); path into it" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sa._f "structural functional" .pendingTransport
    "fd47ab03aaa9797d850828664dca8a12002076c9a72c4ac8bac3309ffdaab7fd"
    "dddcbfd408991573a7c2afd6458b448e746deaada99201f81ea52af60cdaf431"
    "type.∀.body.∀.dom.@0.λ.body.@0.@1.@0.@4" "ROOT[TV]; type of `_f` mentions the packed `below` motive (theorem statements in clique order); path into it" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sb "clique member" .pendingTransport
    "22717b47155044f9187d41730a2f8c2a576647cb2d98eb1ad6d8d7cb08ece66c"
    "c4151352703a615979f59fe2a8d00d70f6afc7d99b28b8845845f23e1da01764"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  -- Cliques.SP P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fa._sunfold "user constant" .inherited
    "524593d208bc2e19ec9b7718cde53e602dda7ef836f446de9199a2a7906ec7e1"
    "139fdb2c10ccbe60a2a493900668e67f0788c53f9a57960a20982e1d348b0587"
    "" "via [fb]" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fa "clique member" .pendingTransport
    "527d25952a6ba44c02993e69db17900753c35a642dfbca24394a9d6397c12f23"
    "0a8782a03088cd47ee3cdfc257b03f5e386e8548f945f5427065b0540c437611"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; fixed-parameter telescope in the first function order (O13b), plus the projection into the packed `brecOn` result" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fb._f "structural functional" .pendingTransport
    "4755dc9f98893af601cf942a679f3239403d4ae45ab03eafd0be03414a48816b"
    "9c564d42d27f9d5a1b58a4befaa82a883e5c438577317f2931ecf4e43078305c"
    "type.∀.dom" "ROOT[TV]; fixed-parameter telescope in the first function order (O13b), plus the path into the packed `below` motive" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fb._sunfold "user constant" .inherited
    "5964fafa5cc2ed01ffbd65046721bbd87504094c6adf3baf1c9622221c98f6fe"
    "7c5ce3d71009032d8d428b9402e0fdf231689095fd78f0e053dc33bef2a285a2"
    "" "via [fa]" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fa._f "structural functional" .pendingTransport
    "f1623552388b51d41e965671cfc420cc8024ebffd72bf81675062fee794f180b"
    "df188f2d008db128174d3049a067aea93c06d7dbcf69ef358032120e773aa144"
    "type.∀.dom" "ROOT[TV]; fixed-parameter telescope in the first function order (O13b), plus the path into the packed `below` motive" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fb "clique member" .pendingTransport
    "78f12253d960f64c81c3e72c93ce696a8bb79a6c0b2deb13853e1a161faefabb"
    "b675671ee9607fb8c67697885976f9b1b0ed1ca10352c2163f153c204ea22122"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; fixed-parameter telescope in the first function order (O13b), plus the projection into the packed `brecOn` result" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  -- Cliques.WP P0 P1
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual._proof_1 "encoding obligation" .pendingTransport
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6"
    "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual._proof_2 "encoding obligation" .pendingTransport
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307"
    "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha.eq_def "equation lemma" .lazy
    "57a59c6c6683b306cca70ca5a92e04b85385414bff173296c04667216610c387"
    "7024839b94a5786e1512be86fd721d95f38cbda1035ea692508c8b4206f3c6bf"
    "value.λ.body.λ.body.λ.body.@1.@0" "ROOT[V]; lazily realised equation lemma; its proof unfolds the clique encoding" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `hb.eq_def "equation lemma" .lazy
    "ba50c991443c66700984e2ebd7e783f68e71b5a574b26685aff7feb82265f671"
    "d3e27bed829407376d4cb0c7da14671d63e7994196c558c340f953fa0f4aec1b"
    "value.λ.body.λ.body.λ.body.@1.@0" "ROOT[V]; lazily realised equation lemma; its proof unfolds the clique encoding" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual.eq_def "encoding equation" .orderStmt
    "304abeedf1bd87f73382bcfc024dedb0aac1a01ea5f7ccb92efa730fb2732633"
    "89a8772f25d96b69de96009004693da023d46169108c225c9aab72ecc40a9aa7"
    "type.∀.dom" "ROOT[TV]; statement over the packed `_mutual`" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `hb "clique member" .pendingTransport
    "b71ab54eb93bd5f8e5cac47b1a83061f3fb5e05e1855139378d94d4a29516b4f"
    "a58ab00877da16960b0d732d2fe021fa9f40fbf5e58b3c84e8bbd53e98fbb9bb"
    "value.λ.body.λ.body.λ.body.@0" "ROOT[V]; fixed-parameter telescope in the first function order (O13b), plus the `PSum` injection" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha "clique member" .pendingTransport
    "96439b5e84d57a74ff0dcacd08017d631b47efee00bacc29669b08843b53440e"
    "97dfbfe76350192cf901c5d92e8c6ea1cb22b69d49e90a4cdd7aae657bab95a8"
    "value.λ.body.λ.body.λ.body.@0" "ROOT[V]; fixed-parameter telescope in the first function order (O13b), plus the `PSum` injection" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual "clique encoding" .pendingTransport
    "e5b17bdb3751da6746ae4ef84d225c3586b1d87a412334584fed79217c9c33ba"
    "5a1b5db06609153eba1fec84761e1e7f3a2c91adc473ac9b6322cea011795fd4"
    "type.∀.dom" "ROOT[TV]; fixed-parameter telescope in the first function order (O13b), plus the `PSum` summand order" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  -- Oracle.Lib.Linear twin orig
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr._sizeOf_2 "sizeOf family" .o11aPending
    "e2a92f924f397ee61827e23616fd2e88e68658d4b276dc9934eefbc27bab7535"
    "25c95b1529f249115cd17451f972f4f5963906105cd4c65ff4cec0c77bf07c33"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr._sizeOf_1 "sizeOf family" .o11aPending
    "4b6555393b8582bec0208dd4d4b426976f7c1b76e4b849da5969ced982d1f170"
    "cb18606bdbb2a92f5eaaf270c9014c8d90ba687bd0528f8ea96284388ce6b94e"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr._sizeOf_1 "sizeOf family" .o11aPending
    "85a24f55398a917aee85d4a010268491ccdd46c1c6c910b170a42b4b498ca41e"
    "f4b16ed704e853487af9e5ae3033a97db1608541e05882606e32ccfae10562cb"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr._sizeOf_3 "sizeOf family" .o11aPending
    "1e09f92eaa14c13b438d30e2f0b19f39086586cb9fc76cb511fe797f3c9d58ce"
    "f84f63c6753dbccfadeb3b6b325ef59e9945a35bf6ce0d3fee3bae4c9defe8d9"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr._sizeOf_2 "sizeOf family" .o11aPending
    "e36b321ad9ad145320a8ef45b0419ad6fb9dc9e2a6e763aa396f11c6ea418478"
    "cdf9c8639d70b8bc8bd74bbeb4e841a3a5823188f0f2646f91363aa00a044dfe"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr._sizeOf_2 "sizeOf family" .o11aPending
    "6d3da884671a32df7f6d48437ca32ea99ef2ade30c031f2e32a88ce03865ae8a"
    "6d4d628d928d48a0cf005a5ba6a6b4f712d74d3b2c26c11228abacf1d7b81eb4"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr._sizeOf_1 "sizeOf family" .o11aPending
    "836e15b01373c36efd496f2a9ef23431ca20a3fef2aa9c0208fd1113ca14dfdd"
    "fa43db4b479e66d33f60875e6dbbfab7bb0ee27670cfea2131ca7be5586343d2"
    "value.λ.body" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.core.sizeOf_spec "user constant" .inherited
    "38c747a2886cfa2b696c6ffffdcb25633b6e245bc54c30b0728223f16538a138"
    "bc1889165cf9b5bae9b279ba2ee7e44c59c3fbeabc5d09142695239a05ee973c"
    "" "via [EqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coreOfNat.sizeOf_spec "user constant" .inherited
    "b2851269787d55f1ecc786491e8e69ec4241e6272a3ba85c890f361f35bd6756"
    "57aec33f492cc8bb0bef1c744c8331ff0ff344965aa1b5e743a3140334714d8a"
    "" "via [EqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr._sizeOf_inst "sizeOf family" .o11aPending
    "a68dfd8ad37a0d7353c831effb9c40edcb120a99e3ed2832e29aedda3c2d11c1"
    "0f407db68763ebde63661d236c572de8876c81fe1c097c1032581e9e2f106060"
    "value.@1.λ.body.fn" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEq.sizeOf_spec "user constant" .inherited
    "4603107e6a354c19517fa39721aa1ea28c43e97de795b2f9f2ef93fdd1600664"
    "1cd29a7242433eef509e62f1ee0ff6aff782a36d80dab129b3240828e5f478d0"
    "" "via [IneqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof._sizeOf_inst "sizeOf family" .o11aPending
    "6e544b31bccfa51cc310fc586f38ed01db34a47fa05118d1cc9341ffc1f8728b"
    "fa61eb8600505a167ca0d08d06767cac5911396341049a7d23c30de8a3445c9a"
    "value.@1.λ.body.fn" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof._sizeOf_inst "user constant" .inherited
    "3b45d6efb915ae8821a7618d119a10461e296f9e04efb7b17614b46a08b6f37f"
    "4c971bbd7f6029e630832bf5ad9857aac27b9a09d2869151840fdf3d7ff604d3"
    "" "via [EqCnstr._sizeOf_2]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ring.sizeOf_spec "user constant" .inherited
    "20d8f15b9079591b8cd8601a2f7152ca8364c933efd20e6fd75b21e0d2b1d02a"
    "24b06d3251e12d864e45ae0e008bf877ff323dfd29e980619f46de5aa1a98819"
    "" "via [IneqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.oneNeZero.sizeOf_spec "user constant" .inherited
    "c1b7f56c7036d87c4688486af4d27ccdf403beacbf4e836aa9b7ea881c12591d"
    "82db7ed91a0216a06ef965614e0d67bece179165c80f318ca3f081422e66ecb9"
    "" "via [DiseqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof._sizeOf_inst "sizeOf family" .o11aPending
    "4816bc5331a9808ef1352b97872725ebba359cdcb55544bf4cd105dd94541ca3"
    "7c3721d0ea1074b4123f4b46d99d7674556da60661003912a38a208813da1b75"
    "value.@1.λ.body.fn" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof._sizeOf_inst "sizeOf family" .o11aPending
    "b56f470d7c99d75df77302315a9c774c6c697474d6008af73ed60c50f851ff8e"
    "48770903088d994835c48ded4aa3b18a81e99a512bab850b42d10a14608e20be"
    "value.@1.λ.body.fn" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr.mk.sizeOf_spec "user constant" .inherited
    "4fe3cccb6ddeaa49f11cc39b7ae31d30432fb38329907e56e21ed29907b72627"
    "737a3e7fee9c3cea2d998268b6dc87f86fa3c275c12908a6c034b0ce4f1a2de5"
    "" "via [IneqCnstrProof._sizeOf_inst, IneqCnstr._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstr._sizeOf_inst "sizeOf family" .o11aPending
    "21a3c8f414efd691ca6bb6d32535a5dee694108fd5b93ec2ae0f398e136e34dc"
    "5e48486a54d17e7a8244580959d3fbf06f8b56998b4df8a630e801a885223e6e"
    "value.@1.λ.body.fn" "ROOT[V]; §4.7 (d): Lean mutual `_sizeOf_N` inlines the block recursor",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCoreOfNat.sizeOf_spec "user constant" .inherited
    "c812f8fec228bc3d0143516bf67ad5adf8a653b086ba6d4b715d07dd3c9bac7c"
    "b40a7a97045f79ff08ba74da3825bf8c0bde125e9879e7f0ad36755be3397551"
    "" "via [IneqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coreCommRing.sizeOf_spec "user constant" .inherited
    "cca3ad838c7a5d5ea75f9caf40f616ddb559af64af3ed426e4c0df22e76c9db5"
    "de4b5ad517afb007a3c6dbbf6a8f6a367bb013c3400bf9b3c013e2bccc1ecaed"
    "" "via [EqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst.sizeOf_spec "user constant" .inherited
    "011aaf3cb0725ee66afc6d5b53e7782008e8ea675fd94feef58ae2d685d3cee0"
    "195055ebacf43a0214d0ed0f0b14bb3cd7040b0bcbf1c773193f99998a840d53"
    "" "via [EqCnstr._sizeOf_inst, DiseqCnstr._sizeOf_inst, DiseqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr.mk.sizeOf_spec "user constant" .inherited
    "6088796e466cb3bd86c3a2673908402990ff17d41a41a6ed4d1c86ba77423b16"
    "904e6310f4e906f6c24d45bf4c5668718432d4fe65682b0461b525ddbc138b34"
    "" "via [EqCnstrProof._sizeOf_inst, EqCnstr._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.oneGtZero.sizeOf_spec "user constant" .inherited
    "7167f92dc8816fc4ec17978ab468441c41161719340123e4035fdf6319e5cb9d"
    "058d15a4ac5de4b72da1eb552db666c6fe36d602a2796b6b43d4231166cbb053"
    "" "via [IneqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.coreOfNat.sizeOf_spec "user constant" .inherited
    "35373a974552d40d5c66ff036d2c1f0b8b27d8e9dcf80a641654c50b2a2cb631"
    "76377fb060d9be13013e7830b8fda1b70c5c7138c12a86847d33a7d4477f22c7"
    "" "via [IneqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.neg.sizeOf_spec "user constant" .inherited
    "7d1085991126f6feed29521796230238703df6434cb4dbe5b55f366298221e53"
    "733343592f030ac13ad16f4e157dbc6990b53a29d74233482856ac7e21069e3a"
    "" "via [DiseqCnstr._sizeOf_inst, DiseqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.neg.sizeOf_spec "user constant" .inherited
    "d341e7c1651dad3b71ecfc490dce4831366fbd071e10780bc5d2b2b0b6bf055c"
    "03b2dc7a4683b68bee8334b168b8fd9050ddfb3eb39314234f35c1f34e45e6e3"
    "" "via [EqCnstrProof._sizeOf_inst, EqCnstr._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.subst1.sizeOf_spec "user constant" .inherited
    "c328caba9b28bc991619d28898951e676cc9bfc2d86dd1218af90c8003d99d42"
    "3a18d140e9cf25c478617ce298e01a665933598ba910ee7f68ead1692c1edda0"
    "" "via [EqCnstr._sizeOf_inst, DiseqCnstr._sizeOf_inst, DiseqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstr.mk.sizeOf_spec "user constant" .inherited
    "078ebac4ce215824bf4d84f657ee911a63ce9f4d48b014c1e9892dea048d93d9"
    "ada312b8e0eb414b50282e459d1dc10fe9052a38623aebc0a2696ba6b642bbc1"
    "" "via [DiseqCnstr._sizeOf_inst, DiseqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.core.sizeOf_spec "user constant" .inherited
    "a74a60920f98ef433c60fbba9817f6fa0cc32d585a599961ceb2fdac0ce9e0d1"
    "1943bfa0948a7ee703f598c942a2cfb3d38cb07179cd8c3bbf3c131575b86edb"
    "" "via [IneqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.diseq.sizeOf_spec "user constant" .inherited
    "950bd0ebc5c2b761d97af1eb27b38bbff010c3c62f16f2d7f3203f802f547988"
    "aee51dde98107e66eb8eca83a704fe4830285fb0bbdbcafc8f0ef00947e03db2"
    "" "via [UnsatProof._sizeOf_inst, DiseqCnstr._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.notCore.sizeOf_spec "user constant" .inherited
    "01a6e3b2e1158517ca0fb75bf042ca356c58bea423b5e38840bb4dbff6151c33"
    "cad711bdb1d052095fc8896df6e88daf8dbdb3c99fc7409df481e60ce079220e"
    "" "via [IneqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.combine.sizeOf_spec "user constant" .inherited
    "b5cbbe20fa4f4467aa7c6759cf65222e4d4be472f4f678f3da4c2176d979daca"
    "e309aa562b1043c6f4f6f99882c2b5a7316fe7166facb8a845beb5ff2d8806e9"
    "" "via [IneqCnstrProof._sizeOf_inst, IneqCnstr._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ringEq.sizeOf_spec "user constant" .inherited
    "3dacb1e7bed424eb8c096588d97449dfcee0876c69ee8db92e5205312b415d18"
    "ea36aaa6854cbd334bcf646f22dccd6eb029975d03d4bd99632de2aaf8689d69"
    "" "via [IneqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.norm.sizeOf_spec "user constant" .inherited
    "bea3ae8c8d027116b019c310417d5afd4853b2030515633d67079dcee0457dc7"
    "ad4920cf1d29d205fb63d51f004914474b0e9aa221ce1d043a4e837911898b38"
    "" "via [IneqCnstrProof._sizeOf_inst, IneqCnstr._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstr._sizeOf_inst "user constant" .inherited
    "5bb1a932545ac2f115a43bcecc1330172c3beea63db10736357c029a4d7eb93a"
    "333409b9d5579975170cac9270fa00619e0f6c7e7c028f4b25118657e87e049d"
    "" "via [EqCnstr._sizeOf_1]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.core.sizeOf_spec "user constant" .inherited
    "b85f2224ce8fdb1e90db7de74051355afe8a230ad0fe74dd3e509058b7d59265"
    "35c0291f29dba0c657e65031928daeb6759ca5fbd83e0d8f108e8cd2a57709e5"
    "" "via [DiseqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.subst.sizeOf_spec "user constant" .inherited
    "f5d587fa64b428b015747099633a3ac87c8baa2ed684e1d2a05cae6a238a8b86"
    "65e19e24d86328a80477104d63eb0bac8a1314dcd53fad92eae59894ef24ba42"
    "" "via [EqCnstrProof._sizeOf_inst, EqCnstr._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `UnsatProof.lt.sizeOf_spec "user constant" .inherited
    "7db1620eb349e5e89775e44bb0d7bb373a4bcf8a39373cd6a5bf33ce5e643fa2"
    "e938f7d52cb54aa49030ec12d2a71f7c0bf08d3c69e0ffd646a37073bc057568"
    "" "via [UnsatProof._sizeOf_inst, IneqCnstr._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofDiseqSplit.sizeOf_spec "user constant" .inherited
    "cfc29c7dfba8091979426e2637e589c43cbf670583d9287e67ee2d43dcf31cea"
    "f4855e7b52d204782e618b77fec0756aa54e8fca1044b37df8f38104748ecb83"
    "" "via [UnsatProof._sizeOf_inst, DiseqCnstr._sizeOf_inst, IneqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.ring.sizeOf_spec "user constant" .inherited
    "9f4deadfded52ac4e0eabcc5245b97b9552d3f6710121438e52a4221b12a387a"
    "87808d7b367dd5b69359c76c3964d6b80567ef6cbbb2fc15c8c42e064c7856a3"
    "" "via [DiseqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.dec.sizeOf_spec "user constant" .inherited
    "9f757738ff82e1c612a0d153fa9909275918cce4163d15ae8e213ba858d6c7d9"
    "5fe676244e78612544c5a34eeca4d973bdb7eb170a97a0c10e181dbf32fc16d3"
    "" "via [IneqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `DiseqCnstrProof.coreOfNat.sizeOf_spec "user constant" .inherited
    "90deab7b8ec8624dddd1df088de74ed6753d9fbecd48ad87b6e9e1648b8a5e89"
    "b1639b4bcb35d9c1be9a2b06d722f5d53cae610163fcd67ac6f79ce023ef906e"
    "" "via [DiseqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `EqCnstrProof.coeff.sizeOf_spec "user constant" .inherited
    "33c829aa7dda3aec93e1315ef80365f575e9e5d4e1e44cd71905f57922f48405"
    "39129586f37effc86b35074a42b7adcabd96d082d89881ff9591e4ab857e931c"
    "" "via [EqCnstrProof._sizeOf_inst, EqCnstr._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.ofEqOfNat.sizeOf_spec "user constant" .inherited
    "d06162abe66e36f46f4c3080c35613a3be5ec59a36ebc26c16f459f2d004a874"
    "e31810ba46ab24f7bde322cb940bb41336555ca66f5dbd8757cd18dc81265e65"
    "" "via [IneqCnstrProof._sizeOf_inst]",
  e `Tests.Ix.Compile.Oracle.Lib.Linear "twin" "orig" `IneqCnstrProof.subst.sizeOf_spec "user constant" .inherited
    "b5083cb595f0e1ca587616cea952d75c24e55d150f6c8682b75cd133c9da67aa"
    "806f8abf939ed83b0b7831373f5ef13890970302e81cd7ecf866163f1b4890b3"
    "" "via [EqCnstr._sizeOf_inst, IneqCnstrProof._sizeOf_inst, IneqCnstr._sizeOf_inst]",
  -- Cliques.WA P0 P1 (A5t, the TACTIC-ASYM probe; kernel verdicts not run for these entries)
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual "clique encoding" .pendingTransport
    "77072c5e6560d1be6a9bc9685b5e7c79aa56f2065994f84d86c4c2d6b749b28a"
    "3b0e15526feeeacadb93a1a5eef651ad56ddc066b50212431324a6a92bdb4779"
    "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "ROOT[V|K]; PSum order of the domain, motive, case trees and measure tree; the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_1 "encoding obligation" .pendingTransport
    "2f26cbff694f6a8bb72246aaa44ff036340467b83cba9f59b64b4e12127053e2"
    "7d5de2d4739bfa89706b90112b4e6679596ba69c90bd83b447f17585844dec15"
    "type.∀.body.∀.body.@5.fn" "ROOT[TV|K]; obligation re-stated over the packing; the goal-specific decreasing_by gives the same proof in both orders (no TACTIC-ASYM)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_2 "encoding obligation" .pendingTransport
    "266d5a80810da61f2cdb9a05392dd32e8f1f8e19b8a523dcd9980bf9d4f8b7d1"
    "10331ba20de201615de5919ad83281e9c5fdd020902cf78beff8fdbd62719e6e"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; obligation re-stated over the packing (no TACTIC-ASYM)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_3 "encoding obligation" .pendingTransport
    "9a89308b9978c15485d5e24b90d25e240a0b20aa76ca8f8cad49fdaf7d7298a8"
    "adf61a53598121f7b789c3363512982f6c8f0be8ea7eb2714358053fe36e7a7b"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; obligation re-stated over the packing (no TACTIC-ASYM)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_4 "encoding obligation" .pendingTransport
    "ebafd6516a002329594de44610e5b29caa9a7b1ec0e96c307e0cc61eaf227425"
    "9037a9baf5fd0aa1923085d1063c69088bf90196b57d59073019802980a446ba"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; obligation re-stated over the packing (no TACTIC-ASYM)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta "clique member" .pendingTransport
    "deec05de7b347d76dbf742d9a27ff97653086ffdbf18a8b5de4c7a3580d26992"
    "88be839c49a3224cd64a80ef9852bd686dc4a12851e7a7b0d51832972c1fcb8e"
    "value.λ.body.@0.fn" "ROOT[V|K]; member injection at its clique position",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `tc "clique member" .pendingTransport
    "41bcc27da9f28ffd1eaca4151a3064ca03fce76cfe4e5d7286446563d1038a12"
    "f519ad6711975650e15ca602b08522ed1a9207d7d59977fe3462f06214227260"
    "value.λ.body.@0.fn" "ROOT[V|K]; member injection at its clique position",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `tb "user constant" .inherited
    "060e9defd68316c2b6f13f719ad81b2e08737319aaa3f6745331aaed4d080f78"
    "5b8df7a16a1ca945d6443430cad1d45195909c1cbdb777ee86a9990143597d1a"
    "" "via [ta._mutual] (tb is at the same summand in both clique orders)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta.eq_def "equation lemma" .lazy
    "cf825df0fcdc215d96592a72d56d9a67d42e587d49464fee89ff21aca5cc0271"
    "1b2f24b1a260bd9002ac4e0541802782dd493f452e46cabb20fa6dd5bca61acf"
    "value.λ.body.@1.@0.fn" "ROOT[V|K]; proof unfolds the encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `tc.eq_def "equation lemma" .lazy
    "2cba5fe7547104f0b93943b1c609b25d54c43287149b3e9987d643ab8a2d23d8"
    "cf4fc56bc13c1093ff201d3d1de52a259243c01ede0dceaef0b563abea4bccd5"
    "value.λ.body.@1.@0.fn" "ROOT[V|K]; proof unfolds the encoding",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `tb.eq_def "user constant" .inherited
    "087b311976df8ed12f1184ecba573e5665c896d2dd105c72ccf174b047c297a7"
    "aa747436471a140a76269da1c4ec0f7f2442ee9dd52c899a3b8dc852cf9d0dfa"
    "" "via [ta._mutual.eq_def, tb, ta]",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual.eq_def "encoding equation" .orderStmt
    "1fe0c2bdbc40ee7e7b51cc3ecc79ab82366db41efd0e90e30c51105e045001c3"
    "106e35daeb35e4579cc1bfa0610afaf7705543552ea524d2e4d8c483a1fdb629"
    "type.∀.body.@2.@4.λ.body.@1" "ROOT[TV]; statement over the packed _mutual",
  -- Cliques.TN P0 P1 (A5t, the NOSPEC probe; kernel verdicts not run for these entries)
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `na "clique member" .noSpec
    "6acfa58679ee85cdf1aaccdf61558625f8a41cd5f83c6ff584bf28e956a95b31"
    "95c284613996b282c88299bcd6c4028256be8388656282563cdef3a0ceb2ce27"
    "value.λ.body" "ROOT[V]; identical statements: Q6 cannot order the clique, Lean's form kept (na of P0 is nb of P1 byte for byte)",
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `nb "clique member" .noSpec
    "95c284613996b282c88299bcd6c4028256be8388656282563cdef3a0ceb2ce27"
    "6acfa58679ee85cdf1aaccdf61558625f8a41cd5f83c6ff584bf28e956a95b31"
    "value.λ.body" "ROOT[V]; identical statements: Q6 cannot order the clique, Lean's form kept",
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `na._f "structural functional" .noSpec
    "ad617d6050b9c71451d88c8b0afbbc8593d98af5452ed0dcdef9492090d5e67a"
    "992a551847a56ae1a88b48b4c37ef9b0ab8311e5dc7836421375b8471321bea4"
    "value.λ.body.λ.body.@3.λ.body.λ.body.let.val" "ROOT[V]; path into the packed below motive; identical statements (NOSPEC)",
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `nb._f "structural functional" .noSpec
    "992a551847a56ae1a88b48b4c37ef9b0ab8311e5dc7836421375b8471321bea4"
    "ad617d6050b9c71451d88c8b0afbbc8593d98af5452ed0dcdef9492090d5e67a"
    "value.λ.body.λ.body.@3.λ.body.λ.body.let.val" "ROOT[V]; path into the packed below motive; identical statements (NOSPEC)"
]

end Tests.Ix.Compile.NonCanonical
