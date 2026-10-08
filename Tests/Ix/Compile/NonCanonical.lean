/-
  The non-canonical set (design document `docs/compiler-passes.md` §7.2).

  This module keeps the cause/entry types, the retained transport oracle,
  and the Pass 3 pass/clique fixture records. The default twins record is
  `Tests.Ix.Compile.NonCanonicalDefault.nonCanonical`; `twins` compares
  it in both directions, so unrecorded and stale differences fail. See
  `docs/compiler-gates.md`, "Exact records and re-recording". Entries change
  only in a commit that states the cause.

  The chronology below describes the retired legacy record and its later
  retained subsets. Its `pending*` classifications describe that historical
  compiler, not the absence of Pass 3 in today's compiler. `inherited`
  marks a term equal under the name map whose referenced constant differs.

  The original evidence was measured at `f829b760` (Lean 4.34.1): the addresses are
  the Lean compiler's; the kernel verdicts are those of `ix check-lean
  --anon` (Ix.Tc), `ix check-rs --anon` (Rust) and `kernel-check-ixe` (the
  certified checker) on the twins closure as the Lean compiler compiled it,
  where a certified decline or a blocked row counts as not accepted. Most
  rejections are open audit defects of the presentations themselves
  (PropSplit, FieldBelow, F4, collapse). These are historical observations.

  Re-run on the merged tree `de10a62e` (A0's safety fixes included): every
  remaining entry has the same addresses as at `f829b760`; the entries of
  the constants A0 now refuses were removed and the refusals are listed in
  `expectedRefusals`.

  A5f (2026-10-03) added the clique families
  `RF`, `NS`, `LI`, `LC`, `PU`, `RA`, `WH`, `TR`, `TQ` and `WU` (70 entries,
  measured at `b86e2043`), with the first measured `RECARG` (`RA`),
  `TACTIC-ASYM` (`WH`) and `SHAPE` (`PU`) entries, and moved `TN` from
  `NOSPEC` to `pendingTransport` (Q6's recovered specification orders it).

  A2 (D6, one constant per auxiliary): the set
  is unchanged (same entries, same causes); the evidence addresses of 21
  entries moved. Four are auxiliaries that are now standalone constants
  instead of projections into a per-kind block (F4 `A.below_2`,
  `A.brecOn_2`, `.go`, `.eq`: packaging), and 17 reference such an
  auxiliary (SX `cTr`, `lFo`, `cFo`, their `_f` and `_sunfold`; IP `evM`,
  `odM`, their `match_2`; C7b `EvenP.toR`, `OddP.toR`, their `match_2`:
  cascade).

  A2 migration commit (discovery order for nested auxiliaries, levels after
  `canonUniv`, one constant per auxiliary): re-measured on the merged tree. The set is unchanged
  (427 differences, same entries, same causes), and the evidence addresses
  are exactly those above: the 21 D6 updates are the whole move, because
  discovery order and the level rule move no address of the twins closure
  (no evidence drift on the merged tree).

  M6R slice 6 (2026-10-07) deleted the legacy call-site surgery from both
  compilers, and with it the legacy record described above (`nonCanonicalOff`,
  497 entries, the twins' `IX_PASS3=off` compile) and its A0 refusals
  (`expectedRefusals`, 12 constants). The twins gate reads the default (Pass 3)
  record, `Tests.Ix.Compile.NonCanonicalDefault.nonCanonical`. This file keeps
  the types, the clique transport's oracle (`transportOracle`: the 157 rows of
  the legacy record that `clique-transport` reads), and the Pass 3 records of
  the proof-justified passes' fixtures (`nonCanonicalPasses`) and of the
  clique families (`nonCanonicalOn`).
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
  /-- Decision 5 (D1): the Lean name keeps its faithful, convertible form and
      the proof-justified pass named here (O7–O12) stored the canonical form
      under `c._ix` (`Ix.Compile.Pass.ixFormName`; switch-on fixtures only). -/
  | pjForm (pass : String)
  /-- Pass 3 (the default since M6): the Lean name of an image-kind head of a
      changed block (`rec`, `casesOn`, `recOn`, `below*`, `brecOn*`, `.go`, `.eq`)
      denotes its image, Lean's own form over the canonical constants (Def 3.4,
      decision 3); the canonical constant is its `_ix` display name (D14), which
      the twins compare where both presentations have it. Faithful only, by
      design (design document §7.1). -/
  | image
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
  | .pendingCollapse => "PENDING-COLLAPSE" | .pjForm p => s!"PJ-FORM-{p}" | .image => "IMAGE"
  | .inherited => "INHERITED"

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

/-- The clique transport's oracle (`clique-transport`, `Tests.Ix.Compile.Transport`):
    the differences of the clique families' twin pairs **before the transport**,
    with the causes that suite reads (`pendingTransport`: packing order only, which
    the transport must reproduce exactly; `guessLex`; and the residual causes
    `recArg`, `tacticAsym`, `shape`, which it must not). Measured with the legacy
    call-site surgery, which compiled cliques in Lean's form (`IX_PASS3=off`,
    before the flip, M6). M6R slice 6 (2026-10-07) deleted that mode and its
    record (`nonCanonicalOff`, 497 entries); these 157 entries are the rows of it
    the transport suite reads, kept unchanged as its oracle: they describe the
    fixtures' Lean terms, not a compile mode. -/
def transportOracle : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `od._f "structural functional" .pendingTransport
    "43281966e05730c23b3a58e91c7d538d88266e8eb7f3b7c4fe9ee28bb30f003e"
    "65e783795028f8e0de56fed91c7f0e72c756296832635fd169f985d3b9193187"
    "value.λ.body.λ.body.@3.λ.body.λ.body" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev._f "structural functional" .pendingTransport
    "32ac0d0b7ab46893597f46158112832e456669f74427196c7392b187d6da2f1c"
    "bb08c2c77fa597768efd23f70721372b6a62c794e689d33030e180afec296cc3"
    "value.λ.body.λ.body.@3.λ.body.λ.body" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `od "clique member" .pendingTransport
    "d0fbb9dc3009c45b10d6614048dd0c8f7fa62bed1b833946403b7730466d8bfc"
    "d9174bb759379e687c6af1f2f334f056d0307a6f6d25e7b314875540b35af96a"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev "clique member" .pendingTransport
    "6a95c0e321c602cf788b502681a2d273157a5a0653c26af77691ea83721dcb5d"
    "c8550d91c030b61f2772d502e35b62c37b006d9fa2b6e080bdfe80ad44f0ea5c"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `od "clique member" .pendingTransport
    "d0fbb9dc3009c45b10d6614048dd0c8f7fa62bed1b833946403b7730466d8bfc"
    "d9174bb759379e687c6af1f2f334f056d0307a6f6d25e7b314875540b35af96a"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev._f "structural functional" .pendingTransport
    "32ac0d0b7ab46893597f46158112832e456669f74427196c7392b187d6da2f1c"
    "bb08c2c77fa597768efd23f70721372b6a62c794e689d33030e180afec296cc3"
    "value.λ.body.λ.body.@3.λ.body.λ.body" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev "clique member" .pendingTransport
    "6a95c0e321c602cf788b502681a2d273157a5a0653c26af77691ea83721dcb5d"
    "c8550d91c030b61f2772d502e35b62c37b006d9fa2b6e080bdfe80ad44f0ea5c"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `od._f "structural functional" .pendingTransport
    "43281966e05730c23b3a58e91c7d538d88266e8eb7f3b7c4fe9ee28bb30f003e"
    "65e783795028f8e0de56fed91c7f0e72c756296832635fd169f985d3b9193187"
    "value.λ.body.λ.body.@3.λ.body.λ.body" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m1 "clique member" .pendingTransport
    "767f4225ec1f4ac399f138df7adbce32a7aa5d11c750b3e30d8011b07761c756"
    "ee47bbcec22de52e177783fd93a2bc91960b8b9352178c29ce5ddffd039e8a8c"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m1._f "structural functional" .pendingTransport
    "b473b69e52a37dafd09fb533128843a07dbcc58d58777409ffab856ef6d29407"
    "d2e57d36c50cd5775f4c95be7157e608df904c29760f0632f8715f3d8d31477a"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m0 "clique member" .pendingTransport
    "03122a79297aa4094f1c6e51bcf9608a7aaca756e8375472ea2be1ae426c9e58"
    "7648a473b4a506ce6c12dea7e565108a75b886ddc2555c59185bb584f1e96af7"
    "value.λ.body.proj0" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m0._f "structural functional" .pendingTransport
    "fedaafc7f9367356e16f3202220f6bd36dfebc7c0fd73d316b979b0de7f938c4"
    "2ca8a8b47168b5ab5934c3da7114471d5bfb37bfadd265f5cf61d457209a9a1b"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m2._f "structural functional" .pendingTransport
    "9bcdd88d009edbd1f0d37bf051063ad4c1f0530790133cb6a8fadabc96584fcb"
    "6d92f0bfe7815b036aa2e8aa94555be69ceca2b9ea03b336e21155446a12035a"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4.proj0" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m2 "clique member" .pendingTransport
    "14d5577906f40f9b12639e2d5bbde2f977f42adf269a72dd8eacd1d3a9abf002"
    "c4c36f2b9fe75fcd51f1a11b0610a30666fe1b4fec0d1349ef05d57bb009921d"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
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
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m0._f "structural functional" .pendingTransport
    "fedaafc7f9367356e16f3202220f6bd36dfebc7c0fd73d316b979b0de7f938c4"
    "d06c6d35cc3c901f92352c900abf036ce204f29228dec3299fc7791f4efb0a9a"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4.proj0" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m2 "clique member" .pendingTransport
    "14d5577906f40f9b12639e2d5bbde2f977f42adf269a72dd8eacd1d3a9abf002"
    "b0b46bf9703cebbe8cdf02c8a1830218e2640d02e6e7a65ace6924b1e5cf71f8"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m0 "clique member" .pendingTransport
    "03122a79297aa4094f1c6e51bcf9608a7aaca756e8375472ea2be1ae426c9e58"
    "9202cdb86d48b9c93c1ba3c318455ef847898b72785c55a82a0ace73e31e156e"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo._f "structural functional" .pendingTransport
    "946a04b42cf1cf5ca1420cc450facc5d4c25876b7017f5252801b58133e62e59"
    "670c4e32a9d88760ada44a3976269be77726d24b4da8c9de453922e1b87e0822"
    "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@5" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo "clique member" .pendingTransport
    "e55bb46e42de613f3f698f1f256bb0c43d4d2ab4126d267ea8b2a195b5979f67"
    "7ecc1fcb2d7f097e778c164e9665d57efa098d9c1ebcee0d529130903d4c9630"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo._f "structural functional" .pendingTransport
    "15d43c0ba995e823fbbd1c7227fa5a3b5182b11eff33a35da82a4b21704b3f59"
    "a3b54b4648b2c97d9f1a17f4b95e1bcca4222acdae4d929574ac47cf28b500d5"
    "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@4.@4" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo "clique member" .pendingTransport
    "925800c959defb61ab59e9ca4f1d03a8569d17c91230fcb5b683510ee78ae582"
    "671bf000e880c2b96203922ab5521785be73b705ad390454002e10e31bce0bcd"
    "value.λ.body" "ROOT[V]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr "clique member" .pendingTransport
    "9aa5f057ed6e7e54bad1f0149269970892b4c883a73f90ab6ca89c7301788317"
    "8970fd3c2912f2e862b3ee0c5c82df3eff51905ff2f40e0719b63c2176ee8516"
    "value.λ.body.@4.λ.body.λ.body.@2.fn" "ROOT[V|K]; projection into the packed `brecOn` result at the clique position; packed motive order",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr._f "structural functional" .pendingTransport
    "4cdb47b0efb189248c0332e19a478d3aab0fcbaa323105310b68494152f6a7df"
    "237e78baff718f272ad46fe08fcaa9038834e3764fbc472e7c26bb96430c7d00"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "ROOT[V]; path into the packed `below` motive: position of the function in its type former group (clique order)",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual._proof_2 "encoding obligation" .pendingTransport
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307"
    "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual._proof_1 "encoding obligation" .pendingTransport
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6"
    "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
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
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa "clique member" .pendingTransport
    "4759d7fe47f0d21c2b99cf95bfc7d5cb7b9ca281166e4f3f92d37c8c308a06b2"
    "641529fc41f1f6b72045cde3fb9c20357b95df6d1e659d54b53617f145b99f36"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
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
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gc "clique member" .pendingTransport
    "b6c20f5e441e355d2c4c0af88c436faa414c952532edf32cec404f23e1442de1"
    "2e11e2833c410ba92b2b10f39e2a9aeac6101a2c43c10d352ab60925fea5fe9e"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gb "clique member" .pendingTransport
    "f7787b8d0cd56368b87bb53196fe36fc0b9c2839a10ff3b0fd5e8092369be486"
    "c5e76ac756f4686274196cd37fcc1b8cceeb217a4adf50296aabb36d04303c48"
    "value.λ.body.λ.body.@0.@2.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga "clique member" .pendingTransport
    "f565ce3d9ce8ac675ba4e535eddbb0fa48b4e91e7b507e1385056a070b2f971e"
    "8a34e4cd993fb7d9b189ce7b0b75f2670b21b46a029b433f76a82ed106a27bb8"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual "clique encoding" .pendingTransport
    "0e27ba25c79dc7793a8ba162691f785ee152ec1f68d31f4f597d4b09db0a5ef5"
    "9cc2b3854a5c3cc7cdb261fadd317f19800a7d2a2f1eb5c1bed9d698f9f2cc70"
    "value.@4.λ.body.λ.body.@4.λ.body.λ.body.@4.λ.body.λ.body.λ.body.@3.λ.body" "ROOT[V|K]; `PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
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
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gc "clique member" .pendingTransport
    "b6c20f5e441e355d2c4c0af88c436faa414c952532edf32cec404f23e1442de1"
    "1645a1d44ec15056218e26836cee53bb5734275d598fede262d1bfa0a0aa6124"
    "value.λ.body.λ.body.@0.@2.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga "clique member" .pendingTransport
    "f565ce3d9ce8ac675ba4e535eddbb0fa48b4e91e7b507e1385056a070b2f971e"
    "2c41be0e21fc26c4193b3acf79ff54ebe9db6c51435930697eb2dc2662ede79f"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `gb "clique member" .guessLex
    "978a66e918dbcc26dee988dbbd25fd28f5f613c3482a5c14e1e32951b0bbccd9"
    "b0865eadcc8365b3b3d27419f53a0779d72ca275dd90978551c382b52fcf3f49"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection, over the GUESSLEX-differing `_mutual`",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga._mutual "clique encoding" .guessLex
    "9505e594f820630cddb3e20b6708419abb613c308ad91953d41372120ec19313"
    "f1b52679b1aa1207b01b494315252882f78493caaab7a40793cd0837c62a17aa"
    "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@4.λ.body.λ.body.λ.body.@3.λ.body.@1" "ROOT[V|K]; GuessLex measure: (ga.x, gb.y) under P0, (gb.x, ga.y) under P1 (non-uniform combinations enumerated in function order, first that works); the canonical functional differs",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga "clique member" .guessLex
    "242e5c784fb1c56336cfb8bd9be95aae375a3e029bb6787da7e3802667cd64df"
    "a54529c0d974aef16d4b2a61a038a49491a2f2640bb4451ae4d13b0d18d273d5"
    "value.λ.body.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection, over the GUESSLEX-differing `_mutual`",
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
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `tb "clique member" .pendingTransport
    "c485a2c9367144d0f6cef0490348f437998387316f56f259b2524484428b862e"
    "fae38748a4ee68cdd161650cc02b0ab89db1a0b4bc97c2f9f6a4f25fbbed84de"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta "clique member" .pendingTransport
    "4759d7fe47f0d21c2b99cf95bfc7d5cb7b9ca281166e4f3f92d37c8c308a06b2"
    "641529fc41f1f6b72045cde3fb9c20357b95df6d1e659d54b53617f145b99f36"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual._proof_2 "encoding obligation" .pendingTransport
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307"
    "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual._proof_1 "encoding obligation" .pendingTransport
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6"
    "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); body differs only in goal copies (`id`); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba "clique member" .pendingTransport
    "4759d7fe47f0d21c2b99cf95bfc7d5cb7b9ca281166e4f3f92d37c8c308a06b2"
    "641529fc41f1f6b72045cde3fb9c20357b95df6d1e659d54b53617f145b99f36"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual "clique encoding" .pendingTransport
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447"
    "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e"
    "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "ROOT[V|K]; `PSum` summand order of domain, motive, case trees and measure tree; per-function measures equal; equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `bb "clique member" .pendingTransport
    "c485a2c9367144d0f6cef0490348f437998387316f56f259b2524484428b862e"
    "fae38748a4ee68cdd161650cc02b0ab89db1a0b4bc97c2f9f6a4f25fbbed84de"
    "value.λ.body.@0.fn" "ROOT[V|K]; `PSum` injection at the clique position (A)",
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
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `odM.match_2 "transformed matcher" .pendingTransport
    "4c737e0ec02324907ffb50f846873186dd3cc3d66510eec89a212747be5ba459"
    "faabdf4dfae1b3ca8b74378c129eb73defab49542de62aba22ec2e42331a9d73"
    "type.∀.dom.∀.body.∀.dom.fn" "ROOT[TV]; IndPred `below` matcher: `funType_i` binders in clique order; regenerated by transport (R)+(A)",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `evM.match_2 "transformed matcher" .pendingTransport
    "7a61df282f48e8bfa8c2ca603616f15e278c7c61c315c1fbb47aac40aba0c914"
    "2beb358feb2e7a05ecc2be785dad6b152790d85f23972ace4cad05d7d9c1be5c"
    "type.∀.dom.∀.body.∀.dom.fn" "ROOT[TV]; IndPred `below` matcher: `funType_i` binders in clique order; regenerated by transport (R)+(A)",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `odM "clique member" .pendingTransport
    "3dd63241391b7a881d2a7d21cdc88e01aaee05cf22b55383c4bd7532cce44f88"
    "29d497b90092325ea818f848d4d95dacadb6f2ac187e52315434deb715bd3b27"
    "value.λ.body.λ.body.let.ty.∀.body.∀.dom.fn" "ROOT[V]; `let funType_i` bound in clique order (`withFunTypes`); zeta-equivalent",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `evM "clique member" .pendingTransport
    "55e92b0f4431c3cbb924303a7d04d6ab9bbbba2257b2e8def68994925dacd20e"
    "ec18d622c25d595ae22f520d993ed32c870ed7c6d7e5a37094c67f5f7ab503ed"
    "value.λ.body.λ.body.let.ty.∀.body.∀.dom.fn" "ROOT[V]; `let funType_i` bound in clique order (`withFunTypes`); zeta-equivalent",
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
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fa "clique member" .pendingTransport
    "527d25952a6ba44c02993e69db17900753c35a642dfbca24394a9d6397c12f23"
    "0a8782a03088cd47ee3cdfc257b03f5e386e8548f945f5427065b0540c437611"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; fixed-parameter telescope in the first function order (O13b), plus the projection into the packed `brecOn` result" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fb._f "structural functional" .pendingTransport
    "4755dc9f98893af601cf942a679f3239403d4ae45ab03eafd0be03414a48816b"
    "9c564d42d27f9d5a1b58a4befaa82a883e5c438577317f2931ecf4e43078305c"
    "type.∀.dom" "ROOT[TV]; fixed-parameter telescope in the first function order (O13b), plus the path into the packed `below` motive" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fa._f "structural functional" .pendingTransport
    "f1623552388b51d41e965671cfc420cc8024ebffd72bf81675062fee794f180b"
    "df188f2d008db128174d3049a067aea93c06d7dbcf69ef358032120e773aa144"
    "type.∀.dom" "ROOT[TV]; fixed-parameter telescope in the first function order (O13b), plus the path into the packed `below` motive" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fb "clique member" .pendingTransport
    "78f12253d960f64c81c3e72c93ce696a8bb79a6c0b2deb13853e1a161faefabb"
    "b675671ee9607fb8c67697885976f9b1b0ed1ca10352c2163f153c204ea22122"
    "value.λ.body.λ.body.λ.body" "ROOT[V]; fixed-parameter telescope in the first function order (O13b), plus the projection into the packed `brecOn` result" (kernelsA := (true, true, false)) (kernelsB := (true, true, false)),
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual._proof_1 "encoding obligation" .pendingTransport
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6"
    "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); equal under packKey",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual._proof_2 "encoding obligation" .pendingTransport
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307"
    "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408"
    "type.∀.body.∀.body.@4.fn" "ROOT[TV|K]; decreasing obligation re-stated over the packing (S); equal under packKey",
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
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `na "clique member" .pendingTransport
    "6acfa58679ee85cdf1aaccdf61558625f8a41cd5f83c6ff584bf28e956a95b31"
    "95c284613996b282c88299bcd6c4028256be8388656282563cdef3a0ceb2ce27"
    "value.λ.body" "ROOT[V]; identical statements (na of P0 is nb of P1 byte for byte); the recovered specifications tie in one class, ordered by Pass 1's seed order (Q6, A5f); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `nb "clique member" .pendingTransport
    "95c284613996b282c88299bcd6c4028256be8388656282563cdef3a0ceb2ce27"
    "6acfa58679ee85cdf1aaccdf61558625f8a41cd5f83c6ff584bf28e956a95b31"
    "value.λ.body" "ROOT[V]; identical statements; the recovered specifications tie in one class, ordered by Pass 1's seed order (Q6, A5f); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `na._f "structural functional" .pendingTransport
    "ad617d6050b9c71451d88c8b0afbbc8593d98af5452ed0dcdef9492090d5e67a"
    "992a551847a56ae1a88b48b4c37ef9b0ab8311e5dc7836421375b8471321bea4"
    "value.λ.body.λ.body.@3.λ.body.λ.body.let.val" "ROOT[V]; path into the packed below motive; identical statements; ordered by the recovered specification (Q6, A5f); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `nb._f "structural functional" .pendingTransport
    "992a551847a56ae1a88b48b4c37ef9b0ab8311e5dc7836421375b8471321bea4"
    "ad617d6050b9c71451d88c8b0afbbc8593d98af5452ed0dcdef9492090d5e67a"
    "value.λ.body.λ.body.@3.λ.body.λ.body.let.val" "ROOT[V]; path into the packed below motive; identical statements; ordered by the recovered specification (Q6, A5f); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `rb "clique member" .pendingTransport
    "ac60049a1892d2d7929e6245b9d38cc4e61693debee7b0a9886e2e9acecdf237"
    "81ecddd3fbcf0168139a2e1e1f1a0384d90d3f3c8a8b1d826c654ee64e3b06c1"
    "value.λ.body" "ROOT[V]; packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `rb._f "structural functional" .pendingTransport
    "ce212569e61531f373a9766d9040cab31cf4bedcbd528748232748bc7c78c2d7"
    "4c5dce85fe8586bb8a1ea4fa76cf70bcfec977748c8418dfd47f8c794b2afa8a"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "ROOT[V]; packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `ra._f "structural functional" .pendingTransport
    "adb0877becc21251dba32d6f1ccbe6735a0bba7f7b0a6550890f5bf4d9a80d44"
    "bfc0b1efabc2c32500e3e3fbec6f4d7f7b87e8f00b09522dd2aebc99ffcadeb7"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "ROOT[V]; packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `ra "clique member" .pendingTransport
    "a1f04a02148000c792d8ae0aef37fd6a62cbe17ae0a191882ee888940c9c357d"
    "45cd8d22b3641f5c5f2a66236c0dc3602aa02f13b3558bcb38dc41d4e0d9c456"
    "value.λ.body" "ROOT[V]; packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `rb._f "structural functional" .pendingTransport
    "ce212569e61531f373a9766d9040cab31cf4bedcbd528748232748bc7c78c2d7"
    "4c5dce85fe8586bb8a1ea4fa76cf70bcfec977748c8418dfd47f8c794b2afa8a"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "ROOT[V]; packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `ra._f "structural functional" .pendingTransport
    "adb0877becc21251dba32d6f1ccbe6735a0bba7f7b0a6550890f5bf4d9a80d44"
    "bfc0b1efabc2c32500e3e3fbec6f4d7f7b87e8f00b09522dd2aebc99ffcadeb7"
    "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "ROOT[V]; packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `ra "clique member" .pendingTransport
    "a1f04a02148000c792d8ae0aef37fd6a62cbe17ae0a191882ee888940c9c357d"
    "45cd8d22b3641f5c5f2a66236c0dc3602aa02f13b3558bcb38dc41d4e0d9c456"
    "value.λ.body" "ROOT[V]; packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `rb "clique member" .pendingTransport
    "ac60049a1892d2d7929e6245b9d38cc4e61693debee7b0a9886e2e9acecdf237"
    "81ecddd3fbcf0168139a2e1e1f1a0384d90d3f3c8a8b1d826c654ee64e3b06c1"
    "value.λ.body" "ROOT[V]; packed motive order and the paths into below through the reflexive field ((x 0).1.2 against .1.1); the transport reproduces it (clique-transport)",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `nl._f "structural functional" .pendingTransport
    "44a09cfbb06bd7fd97e101445ac87731923c60dd87a91cd28f309e21f9fe36a3"
    "5ecb15bdc67c7d3b089a9798df36b3aa915edc8b3efa3f1d7d77940c4c1cdd39"
    "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@4.@4" "ROOT[V]; packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `na "clique member" .pendingTransport
    "fe2ce779aacd87f063f930dc49cc5804a922bcd9bfb70910df960690ad004915"
    "b7f3db9d945710991b36ea5e357b516bbae08a1b0fd75b10621bae4bf3edf1d0"
    "value.λ.body" "ROOT[V]; packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `nl "clique member" .pendingTransport
    "ec27435dc7b8f0b619ead0c424d76cd490032a9cc9c9bb660b2a89330ec02660"
    "e8654f8097cc96dc715a2881b47cda1c6295173e4188a0a978bec16a9921af53"
    "value.λ.body.@3.λ.body.λ.body.@2.fn" "ROOT[V|K]; packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `nb "clique member" .pendingTransport
    "06cfcbc9ef246fd43f37997c676d92739e28165751c88b2b265c90f4e2ed150c"
    "ac7329d3d4f6e99a9b05556ddc4edf764bd2240768c434f537ec8fb7cdca9a46"
    "value.λ.body" "ROOT[V]; packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `na "clique member" .pendingTransport
    "fe2ce779aacd87f063f930dc49cc5804a922bcd9bfb70910df960690ad004915"
    "b7f3db9d945710991b36ea5e357b516bbae08a1b0fd75b10621bae4bf3edf1d0"
    "value.λ.body" "ROOT[V]; packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `nl "clique member" .pendingTransport
    "ec27435dc7b8f0b619ead0c424d76cd490032a9cc9c9bb660b2a89330ec02660"
    "e8654f8097cc96dc715a2881b47cda1c6295173e4188a0a978bec16a9921af53"
    "value.λ.body.@3.λ.body.λ.body.@2.fn" "ROOT[V|K]; packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `nb "clique member" .pendingTransport
    "06cfcbc9ef246fd43f37997c676d92739e28165751c88b2b265c90f4e2ed150c"
    "ac7329d3d4f6e99a9b05556ddc4edf764bd2240768c434f537ec8fb7cdca9a46"
    "value.λ.body" "ROOT[V]; packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `nl._f "structural functional" .pendingTransport
    "44a09cfbb06bd7fd97e101445ac87731923c60dd87a91cd28f309e21f9fe36a3"
    "5ecb15bdc67c7d3b089a9798df36b3aa915edc8b3efa3f1d7d77940c4c1cdd39"
    "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@4.@4" "ROOT[V]; packing of the Rose group (na, nb) at the motive and functional positions of brecOn/brecOn_1, and its paths; the nested List Rose group has one function; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `la.mutual._proof_1 "encoding obligation" .pendingTransport
    "23f2fcf243de4f203af437cecae5aa8e456a296211e7f854d84afba79be84183"
    "c6f2eaa1f32e2bef4c81216442e92f4387ed945253669b02d356188afec72db4"
    "type.@4.λ.body.@2.λ.body" "ROOT[TV]; PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `lc "clique member" .pendingTransport
    "c6bf45aa737fa84ea64238f4834cf8da5b7d869963c25796f8e4c0b3d4c58275"
    "5234d7f723dbab4efa505988576ae3f72c905c69da3ae46b572c03bc22876d6c"
    "value" "ROOT[V]; PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `la "clique member" .pendingTransport
    "794636154366ec6dc813c37fc84560f9dd123a2dc5189ec542d18f462b0af64a"
    "343f2868bb45d3b0e5e94c8464a9f23feda4dc03bafe73b3faef36814ef4a1bf"
    "value" "ROOT[V]; PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `la.mutual "clique encoding" .pendingTransport
    "844a3be331e7f7c758450925cb2a90675dcf0b0860acdc05e16d81c61e5df7ed"
    "0df7605cdc6de89fc8c8e5a82f154ca3474e0411a1701835480f6af2bd4a7682"
    "value.@2.λ.body.@2.λ.body" "ROOT[V|K]; PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `la.mutual._proof_1 "encoding obligation" .pendingTransport
    "23f2fcf243de4f203af437cecae5aa8e456a296211e7f854d84afba79be84183"
    "1142aeb7fe76382e4b955041246185112babeb5fed14dc8cc1a4d65cb0c19b46"
    "type.@4.λ.body.@2.λ.body.@3" "ROOT[TV]; PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `la "clique member" .pendingTransport
    "794636154366ec6dc813c37fc84560f9dd123a2dc5189ec542d18f462b0af64a"
    "7a884321a9426c7970621310d2f19b60b63bfe1b8890c24ecc9db23e40050aba"
    "value.proj0" "ROOT[V]; PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `lb "clique member" .pendingTransport
    "365e2b96a786e4251db200a6e5d9085c3eea6086ecd1d6bc80a64804479fc2ca"
    "f6af9ba245fe8ca2d99be2d31078f152f98f50bb75455c30895e1f9eec5c03e8"
    "value.proj0" "ROOT[V]; PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `la.mutual "clique encoding" .pendingTransport
    "844a3be331e7f7c758450925cb2a90675dcf0b0860acdc05e16d81c61e5df7ed"
    "7487e2bca961ef77d3aa8b7eca1691fe462020f9be2b4b99fa6dbab3b52d5e43"
    "value.@2.λ.body.@2.λ.body.@3" "ROOT[V|K]; PProd factor order of the lattice fixpoint (lfp_monotone over ImplicationOrder, instCompleteLatticePProd), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `ca.mutual._proof_1 "encoding obligation" .pendingTransport
    "c0238e623b000ba4cab169e97fa2f5bbe19c1b19257da7c955f568859dcd9e39"
    "d1986090ac5216fe4f2a0d6667c95969888402b565139e4191d8717f5ba63ad9"
    "type.@4.λ.body.@2.λ.body" "ROOT[TV]; PProd factor order of the coinductive fixpoint (ReverseImplicationOrder), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `cb "clique member" .pendingTransport
    "80120e58691cbe338529b87f7617bfe7187d814a86e1f4a0d304efa7564aa2d7"
    "b76d692d77bf7afa6bd6d7c3714a6d56d53126863bbea898272ccdefc17af824"
    "value" "ROOT[V]; PProd factor order of the coinductive fixpoint (ReverseImplicationOrder), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `ca.mutual "clique encoding" .pendingTransport
    "ebf6e6b156580df2615158241987a80dad9d4c32fe0b016dcd3067ef5289eddf"
    "26f0280c765173003d6dbf565073450987c730824676f6bd699c78134addd1c6"
    "value.@2.λ.body.@2.λ.body" "ROOT[V|K]; PProd factor order of the coinductive fixpoint (ReverseImplicationOrder), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `ca "clique member" .pendingTransport
    "e86bf216cc4b16624aacd3e4ab50da5ff52925a9eb8841fecbd0ce263082834f"
    "f0a459489ed8443f6cb1313451a2aab90fa87698e259a8b4e373422772a606b3"
    "value" "ROOT[V]; PProd factor order of the coinductive fixpoint (ReverseImplicationOrder), the paths, the monotone_mk tree and the path proofs; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ua.mutual._proof_1 "encoding obligation" .shape
    "b7bc40a157711d751e43e91fc474e33b76c2fb4c878863a4ac3722312b1a8b0b"
    "326b4257346d42a8eefa6b46b73df65f6862789cadf88ea8baa7fb8435a78296"
    "type.@4.λ.body.@2.λ.body.@3.@1.@1" "ROOT[TV]; the user-written monotonicity proofs (an intro script projecting h : f ⊑ g, and a lemma chain with the instances its own unification found) are outside the grammar: the composition fallback monotone_compose (mono φ) h keeps Lean's proofs (clique-transport (f))",
  e `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ub "clique member" .pendingTransport
    "95b8e93dbb6bf28a4ac287b7b37ddd209f005d9ce94001abb50af0fec2500de1"
    "f382cb3d3db3db3d41ff4548771c3e6a09c409d50346a7c712d880b496b55e83"
    "value" "ROOT[V]; PProd factor order of the fixpoint and the members' paths; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ua.mutual "clique encoding" .pendingTransport
    "98442a03f9dfa6b72b5ac7adb902937dfd834e3071aec027601dc2c8c245a95b"
    "c98c6d8730e61475657d5c36d5642286dc8898eb0cefb389a14982923822f9cf"
    "value.@2.λ.body.@2.λ.body.@3.@1.@1" "ROOT[V|K]; PProd factor order of the fixpoint and the members' paths; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ua "clique member" .pendingTransport
    "c8e4b93e1e28fd1dcf8ef447ff7977c39411c7123d2cfddabbc0da9b7bf601a4"
    "bbbe1e9e94849a0ac25db829e901e10bf54091ea7d597a4f329bc6ee2abfe771"
    "value" "ROOT[V]; PProd factor order of the fixpoint and the members' paths; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `rb "clique member" .recArg
    "d578cc4aed44eacedaa3d6c3b01a3f91a1df96a6619568c2295f3a538b538400"
    "69ec6b468f31adb4416a5337d78d0a3683b962fc779aa41b8554f663f8c99af4"
    "value.λ.body.λ.body.fn" "ROOT[V]; Lean's allCombinations picked (ra.x, rb.y) under P0 and (rb.x, ra.y) under P1: brecOn over different arguments (clique-transport (f))",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `rb._f "structural functional" .recArg
    "17354ef0aeee92d76a8d286b6d7872b467fd3f60fe44a0a2fa5b0ec653ff1921"
    "0b4277b06c6b8bc03ead07e16f0edbc44affdb19387289d0680576f912f10a83"
    "value.λ.body.λ.body.λ.body.@0.λ.body.λ.body.∀.dom.@1" "ROOT[V]; Lean's allCombinations picked (ra.x, rb.y) under P0 and (rb.x, ra.y) under P1: brecOn over different arguments (clique-transport (f))",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra "clique member" .recArg
    "2e382f44b64ef0d59ad37730359abdb14ab33271ebd7b616a348302c555198fc"
    "36c4cfebb52faba910bfe2269aa5c77b87d855eab9e47eb07f8d4982f50ca86c"
    "value.λ.body.λ.body.fn" "ROOT[V]; Lean's allCombinations picked (ra.x, rb.y) under P0 and (rb.x, ra.y) under P1: brecOn over different arguments (clique-transport (f))",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra._f "structural functional" .recArg
    "a4ca7ec36d6d47cba1a964f929947892dcaa354e1cda9c8f43b169ce83a4e220"
    "bcaa8bdad6fddf93d4d61cb14fed4674b79cc401f7f900fd7a556e715b984a50"
    "value.λ.body.λ.body.λ.body.@0.λ.body.λ.body.∀.dom.@1" "ROOT[V]; Lean's allCombinations picked (ra.x, rb.y) under P0 and (rb.x, ra.y) under P1: brecOn over different arguments (clique-transport (f))",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra._sparseCasesOn_1 "clique auxiliary" .recArg
    "3a4d0a9cb60745860c348a96bb097d439c3b156a60085eedbf4febb58fc9821d"
    "-"
    "" "ONLY-A; Lean's sparse casesOn for ra's match on x, which exists only while x is ra's recursive argument; Lean's allCombinations picked (ra.x, rb.y) under P0 and (rb.x, ra.y) under P1: brecOn over different arguments (clique-transport (f))",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `ha "clique member" .pendingTransport
    "81a1116c189347bb57bfeed4fdc7502c5269315582c04aa9815485162ea27be0"
    "15ec7af204f1cc5615f11aa34dc0d3d54c919fabc00fe81d8781292884bbdca3"
    "value.λ.body.λ.body.λ.body.λ.body.@1" "ROOT[V]; PSum order of the encoding and the fixed telescope; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `hb "clique member" .pendingTransport
    "afc03d9f741d843fe9590666f7f260990cc457cc68a552ed117eff1ae1561f7c"
    "5b029055e35a1a6ca14149c622e343b185991dfd6fae99026eb71cae6e73e90e"
    "value.λ.body.λ.body.λ.body.λ.body.@1" "ROOT[V]; PSum order of the encoding and the fixed telescope; the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `ha._mutual "clique encoding" .tacticAsym
    "a7bf3d2955497f278338733e61cc5d3dc811eb0b4f52a132982b9ee267ca1cfa"
    "533939407aa6db690941e7c604843562fb5b16c7ca42c09118038d78f3bef142"
    "value.λ.body.λ.body.λ.body.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body.@1" "ROOT[V]; decreasing_by `assumption` takes the most recent `1 < k` in the packed function's context, whose fixed parameters follow the first function: _proof_k k h₂ under P0, k h₁ under P1 (Lean.Elab.Tactic.assumption, FixedParams.lean); the rest of the encoding transports exactly",
  e `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `rb "clique member" .pendingTransport
    "7085cfdfb166749435e0c1d59f22e1796877dcb83ecfa64a8b3d05bf7362406d"
    "55e412c17212dd415e079e198e94f2d0e5ee81ae9a232371140af0052f959767"
    "value.λ.body" "ROOT[V]; identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `rb._f "structural functional" .pendingTransport
    "98108fcdcffe277bf9fdce4b8af643b1b785867304c24a149d4b775f5160a4ab"
    "cb12be024d8ab4425c89facd16419aa4416f8a35a02dc910c309e29fb3d6a16a"
    "value.λ.body.λ.body.@4.λ.body.λ.body.let.val" "ROOT[V]; identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `ra._f "structural functional" .pendingTransport
    "6b6a82b3efe33c928262df29a6e1e52725b2dd8a78d90979b1b57fd8353cbbc7"
    "68deb3de80fe3694fc0389a033a873e633618467eaa924299bec4b449353613d"
    "value.λ.body.λ.body.@3.λ.body.λ.body.let.val" "ROOT[V]; identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `ra "clique member" .pendingTransport
    "f515069851bec772c86c3429da59017111da4e12fec7a2c50f55a4dc3ba2e7dd"
    "c57bf565c6293ef91fd9162550ed5e87273fc22950125916325790cf69473b83"
    "value.λ.body" "ROOT[V]; identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TQ "P0" "P1" `qa "clique member" .pendingTransport
    "b54f2593059f634aacbc338c3a6a9f1d174e9c878602a973ccb39b94a1da691b"
    "808cbd7f9bf7daab6785c7cf800175ac51255af01e73840ef56b4f111b1da16d"
    "value.λ.body.@0.fn" "ROOT[V|K]; identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TQ "P0" "P1" `qb "clique member" .pendingTransport
    "5ff24256028f491cffba1917f580101010c8cd13ec8c2b5eb46b8a31c85be8a6"
    "77b89a107f331e04c153051103491879bb066e16f5a60ed7614aaad2dd3a8e3c"
    "value.λ.body.@0.fn" "ROOT[V|K]; identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.TQ "P0" "P1" `qa._mutual "clique encoding" .pendingTransport
    "e221ec86aeb3fe776065dda776611fdc22c24a263d0fcf3e070a8d5bd1b4c39c"
    "71fe3265b59618938cb2faf2c8de64ba2c21e021af3bc308451210711fa2af30"
    "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "ROOT[V|K]; identical statements; ordered by the recovered specification (Q6, second source); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wx._mutual "clique encoding" .pendingTransport
    "29ade7866807a108f74e5e7af9dd2d16e97e0bc0ec70d8c0348e2f72461a77e2"
    "ea34c5fded17085a9976c048f5b01246fb7ace26452defea241709934aee40d1"
    "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body" "ROOT[V|K]; PSum order of the encoding; the user values of type PSum Nat Nat stay (the position restriction); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wx "clique member" .pendingTransport
    "d4453beb9378ad0545d57b3921bd3679fc92382e9a8278fef1183e3c8247c289"
    "1ae9cccb49d7220eb4d0e94e465b26444c563356f14ce8d6ba9ee97ca9248b90"
    "value.λ.body.@0.fn" "ROOT[V|K]; PSum order of the encoding; the user values of type PSum Nat Nat stay (the position restriction); the transport reproduces it",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wy "clique member" .pendingTransport
    "92a70374d60266f75c22cc5167b08c23ecd199f5e0fc61dbc36ee39e069dfee2"
    "c65c287d359b894044850482f45c4d64856e31f7561d672d368ff84b6d7120a3"
    "value.λ.body.@0.fn" "ROOT[V|K]; PSum order of the encoding; the user values of type PSum Nat Nat stay (the position restriction); the transport reproduces it"
]

end Tests.Ix.Compile.NonCanonical

namespace Tests.Ix.Compile.NonCanonical

/-- The non-canonical set of the proof-justified passes' fixtures **with the
    switch on** (`IX_PASS3=images`; `Tests/Ix/Compile/Pass/O7Collapse.lean` …,
    A6p): every twin pair of those fixtures that the `pass3` suite lists as
    differing (`Tests.Ix.Compile.Pass3.passTwinsNC`), with its cause; exact in
    both directions there (a pair that differs without an entry, an entry
    whose pair is byte-equal, or evidence addresses that moved, fail the
    suite). `presA` is the fixture's `Src` presentation, `presB` its `Can`
    presentation (`Perm` for O12's permuted pair); the constant is the full
    name in `Src`. Decision 5 (D1, M1-b): the Lean name of every constant a
    proof-justified pass rewrote keeps its faithful form and is recorded
    `PJ-FORM-<pass>` (the canonical form is `<constant>._ix`, compared with
    the twin in `pjPassTwins`); constants over such a name that no pass
    rewrote are `INHERITED`. -/
def nonCanonicalPasses : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Pass.O11bNoConfusion "src" "can" `PassO11b.Src.E.noConfusionType "split-off enumeration, two constructors" .pendingNoConfusion
    "55cdd0e212e6163b0be130360f15b61776d90cbaa59106ab55e511a5a76a13fb" "3904c4a2443198b28b9640aa48ac1f65f15d3ecf838890f0bb6c5e25bbed07b6" "value"
    "O11b declines: the enumeration form needs `E.ctorIdx`, `noConfusionTypeEnum` scheduled first (no edge yet)"
  , e `Tests.Ix.Compile.Pass.O11bNoConfusion "src" "can" `PassO11b.Src.E.noConfusion "split-off enumeration, two constructors" .pendingNoConfusion
    "55b3bf142fb5a8078ad3b7515f90ab239c32ae0443dfe383b67dae6f4ba17fc5" "d22707b38e0abb7f8254c3b1bf1f583807d6990e42b1f5d71ebd6d83b124b60d" "value"
    "O11b declines with `E.noConfusionType` (the pair is rewritten together)"
  , e `Tests.Ix.Compile.Pass.O9Split "src" "can" `PassO9.Src.A.len._f "Lean's structural handler over a split block" .orderStmt
    "a2efeed435e50d00fb1a10f4a2cc798d17d4cbf88d6ebcec215737533dcf2e3b" "e0b305275f4a5cf30747e12ad76a6cb88db3927a3b03ea20c2eeda6191f1378b" "type"
    "Lean's `_f` keeps its Lean type over Lean's `A.below` (faithful); the canonical handler is `A.len._ix_retyped._f` (O9)"
  , e `Tests.Ix.Compile.Pass.O9Split "src" "can" `PassO9.Src.A.sum._f "Lean's structural handler over a split block" .orderStmt
    "4477494fff8d528aaa2184be891e4ecf17183b355b661e712aef8fcb66ada662" "d54ac8229d28df80a1ce6b07ac8c397fa0f2fac34ce4545f3167591ab968eba3" "type"
    "Lean's `_f` keeps its Lean type over Lean's `A.below` (faithful); the canonical handler is `A.sum._ix_retyped._f` (O9)"
  , e `Tests.Ix.Compile.Pass.O7Collapse "src" "can" `PassO7.Src.A.viaRec "collapsed class, rec/recOn user" (.pjForm "O7")
    "bc5317547248abcb639c2d7f9d9cf174342e3548378c0dcfa9cae1b0c734fd55" "f983d1c96ed723925281ee26f10aeddd6c43e69da83834c209989bd399fbee12" "value"
    "O7 wrote the canonical form under `PassO7.Src.A.viaRec._ix` (decision 5, D1); the Lean name keeps the paired image"
  , e `Tests.Ix.Compile.Pass.O7Collapse "src" "can" `PassO7.Src.B.viaRecOn "collapsed class, rec/recOn user" (.pjForm "O7")
    "14b32160449534866ae3d02470e8ee1e6411fee3b2b70013cfa35e9a292e8761" "6bbb5d8c5e7cc62b456a6f86573a8a9025c9fcf32e4368b20e500953d767ce2c" "value"
    "O7 wrote the canonical form under `PassO7.Src.B.viaRecOn._ix` (decision 5, D1); the Lean name keeps the paired image"
  , e `Tests.Ix.Compile.Pass.O7Collapse "src" "can" `PassO7.Src.Z.viaRec "collapsed class, rec/recOn user" (.pjForm "O7")
    "5ea52960a8aaad04fb5390c5fe22263f3f954685da093c32276067eaeffc9327" "885af19cf6aa9f4124b065f1d468171ca2f87f803a47bb1d68c84343bb2c91c3" "value"
    "O7 wrote the canonical form under `PassO7.Src.Z.viaRec._ix` (decision 5, D1); the Lean name keeps the paired image"
  , e `Tests.Ix.Compile.Pass.O8Cases "src" "can" `PassO8.Src.A.isNil "collapsed class, casesOn user" (.pjForm "O8")
    "040ef29f138ee786eb0f82a655ee3fd9b27baec3b85033549f837e8b66e47f2c" "3170b105367d9998bcffb237e7e9e2be3c0dab4f80aad79bb99c63c581b87b4c" "value"
    "O8 wrote the canonical form under `PassO8.Src.A.isNil._ix` (decision 5, D1); the Lean name keeps the packed `casesOn` image"
  , e `Tests.Ix.Compile.Pass.O8Cases "src" "can" `PassO8.Src.B.isNil.match_1 "collapsed class, casesOn user" (.pjForm "O8")
    "c30016faa606a224ce3dd9f0b96efd961e8832739fb43a1f4716835fa9fa5e9a" "8456b93a61151feea7878938feb7e719ffbef279f28f05c3e798f036ff56fa5c" "value"
    "O8 wrote the canonical form under `PassO8.Src.B.isNil.match_1._ix` (decision 5, D1); the Lean name keeps the packed `casesOn` image"
  , e `Tests.Ix.Compile.Pass.O8Cases "src" "can" `PassO8.Src.B.isNil "collapsed class, casesOn user" .inherited
    "3114fdf07ff2fa91fb6b0b374f027bf30f2c937f4aa3d272724c76ac630658cd" "05cf888a8c9082b817f58d65e3cc02030d9a691139c71d7bae8c2b9897527410" "value"
    "refers to its matcher, whose Lean name keeps its form (PJ-FORM-O8); an ordinary caller, not rewritten"
  , e `Tests.Ix.Compile.Pass.O8Cases "src" "can" `PassO8.Src.Z.isE.match_1 "collapsed class, casesOn user" (.pjForm "O8")
    "f3aebd55c3c54527074935415cdaa1fb192248d096e4903ded32e7c3e7ff5d33" "110cb189c805dee312f3ebb2fdc3c3386c4141e6e73a7ae4467221cfd0e7a9f5" "value"
    "O8 wrote the canonical form under `PassO8.Src.Z.isE.match_1._ix` (decision 5, D1); the Lean name keeps the packed `casesOn` image"
  , e `Tests.Ix.Compile.Pass.O8Cases "src" "can" `PassO8.Src.Z.isE "collapsed class, casesOn user" .inherited
    "d0a14bd41fd76cd0f9f99176e08e1376389cbfb4c0a77a97a598a8c7779f58b2" "db7b2a61071fa02d66467b8552979308c5605f22c69f64215a9a2ab335263d9b" "value"
    "refers to its matcher, whose Lean name keeps its form (PJ-FORM-O8); an ordinary caller, not rewritten"
  , e `Tests.Ix.Compile.Pass.O8Cases "src" "can" `PassO8.Src.A.noConfusionType "collapsed class, casesOn user" (.pjForm "O8")
    "5d8cc79549e7987db34159f9e5b36c853b531ad363fa70440bef847652f624e5" "2028e58d86f9a54b9e53c4f4201b53ccac824e2a3733a06ff4c6a43d5d859b51" "value"
    "O8 wrote the canonical form under `PassO8.Src.A.noConfusionType._ix` (decision 5, D1); the Lean name keeps the packed `casesOn` image"
  , e `Tests.Ix.Compile.Pass.O8Cases "src" "can" `PassO8.Src.A.isNil' "collapsed class, casesOn user" (.pjForm "O8")
    "040ef29f138ee786eb0f82a655ee3fd9b27baec3b85033549f837e8b66e47f2c" "3170b105367d9998bcffb237e7e9e2be3c0dab4f80aad79bb99c63c581b87b4c" "value"
    "O8 wrote the canonical form under `PassO8.Src.A.isNil'._ix` (decision 5, D1); the Lean name keeps the packed `casesOn` image"
  , e `Tests.Ix.Compile.Pass.O9Split "src" "can" `PassO9.Src.A.len "split block, structural recursion with a cross field" (.pjForm "O9")
    "393be87e63da9492c3c2c314667cd0671551dfd2781f6046eacc847bc05e7f20" "1aa7daac74258befc2805df37237e18b32c8b8509d589aed29315bcec40d55f3" "value"
    "O9 wrote the canonical form under `PassO9.Src.A.len._ix` over the canonical handler (decision 5, D1); the Lean name keeps the image's `brecOn`"
  , e `Tests.Ix.Compile.Pass.O9Split "src" "can" `PassO9.Src.A.sum "split block, structural recursion with a cross field" (.pjForm "O9")
    "50962dc02b18ee4837a6691ed4dd341c606c7321425ab74a189e7f2b07c390c2" "b47d9a8f07600cda70ede611f0c39135ef2cec92a791d46cacb3ba8dcde8b530" "value"
    "O9 wrote the canonical form under `PassO9.Src.A.sum._ix` over the canonical handler (decision 5, D1); the Lean name keeps the image's `brecOn`"
  , e `Tests.Ix.Compile.Pass.O9Split "src" "can" `PassO9.Src.A.cnt "split block, structural recursion with a cross field" (.pjForm "O9")
    "d584e3dd173b05f57ffdf8f2e3d87becf09afb72cea2ccdb43c470fdffbfd437" "25099c659c347d4f2f80859c95e288c51387342c0a9f927450c2af8feb2a473b" "value"
    "O9 wrote the canonical form under `PassO9.Src.A.cnt._ix` over the canonical handler (decision 5, D1); the Lean name keeps the image's `brecOn`"
  , e `Tests.Ix.Compile.Pass.O9Split "src" "can" `PassO9.Src.len2 "split block, structural recursion with a cross field" .inherited
    "3beb161273d4c7c71c938c8e490bd5774079e75ede7fd1278ebd0e3d67014eb1" "73297a7529e110573fbbcfd2bb04ce0c432f9a836d6465cb6dbd4fd1b9917083" "type"
    "refers to `A.len`, `A.sum` or `A.cnt` by the Lean name (PJ-FORM-O9)"
  , e `Tests.Ix.Compile.Pass.O9Split "src" "can" `PassO9.Src.len3 "split block, structural recursion with a cross field" .inherited
    "7c3b8d3b9be7e51e6e806e073ecea3b02d20f78ea3ca5e73be3030c0c5b858ca" "5f0fdce39667fe3272aa5efe3021896ce9ce36b06dc1b4d406d72bcf4566f749" "type"
    "refers to `A.len`, `A.sum` or `A.cnt` by the Lean name (PJ-FORM-O9)"
  , e `Tests.Ix.Compile.Pass.O9Split "src" "can" `PassO9.Src.sum2 "split block, structural recursion with a cross field" .inherited
    "4c1349cda643321e8c72538b516ac5965fd4303f20989f5f6c35548e53fe4400" "4d81ea2117782916a5267e86a799fea7c7d1f4da624dbddf23a3ee7ae640253a" "type"
    "refers to `A.len`, `A.sum` or `A.cnt` by the Lean name (PJ-FORM-O9)"
  , e `Tests.Ix.Compile.Pass.O9Split "src" "can" `PassO9.Src.len_succ "split block, structural recursion with a cross field" .inherited
    "cc42c984cd18ec7a990aa5d03b52512c6f9c96e4239b3aca15f7ade5ef59c09e" "01ca0eeb5924a077160af363ba31686a01fa5b86e071303118df9fd42be7ce7c" "type"
    "refers to `A.len`, `A.sum` or `A.cnt` by the Lean name (PJ-FORM-O9)"
  , e `Tests.Ix.Compile.Pass.O9Split "src" "can" `PassO9.Src.cnt1 "split block, structural recursion with a cross field" .inherited
    "9b62339a2168b8414d140704cae7d20b75726a8185e774f3c23ff106333a96c6" "ad104b62da324e6ad04dfe28016416d0ddd031758e6ce3c47031b981eb936bd6" "type"
    "refers to `A.len`, `A.sum` or `A.cnt` by the Lean name (PJ-FORM-O9)"
  , e `Tests.Ix.Compile.Pass.O10O12Collapse "src" "can" `PassO10.Src.A.h "collapsed pair, structural recursion" .pendingCollapse
    "49ebbf31bb4bd9aeb4d8c196ef434a29c09f703b71a83e12dea8f24a3dda9cec" "7ab66120eb546a328d7a77dc24057c2590921b439880bd534377f46929624447" "value"
    "the structural clique is transported by the clique hook (A5), so O10/O12 do not fire; the collapsed twin's single function needs the encoding shrink O17 (deferred, D3)"
  , e `Tests.Ix.Compile.Pass.O10O12Collapse "src" "can" `PassO10.Src.B.k "collapsed pair, structural recursion" .pendingCollapse
    "5f8f9915ab817345b7f7525dc996931160260c3694dad3be8f7351b992715355" "7ab66120eb546a328d7a77dc24057c2590921b439880bd534377f46929624447" "value"
    "the structural clique is transported by the clique hook (A5), so O10/O12 do not fire; the collapsed twin's single function needs the encoding shrink O17 (deferred, D3)"
  , e `Tests.Ix.Compile.Pass.O10O12Collapse "src" "can" `PassO10.Src.h_two "collapsed pair, structural recursion" .inherited
    "5fe2de1c5f94270f6bd8b7ffb9890c6a66cd4207c695ac54a17e6f2d04cc796d" "0daa95225c9ab546c3425d0b38c3fe2c8614bd46e0546617e825241715991f3c" "type"
    "refers to a transported clique member of a collapsed block (PENDING-COLLAPSE)"
  , e `Tests.Ix.Compile.Pass.O10O12Collapse "src" "perm" `PassO10.Src.A.f "collapsed pair, structural recursion" .pendingCollapse
    "a858010777fc36ad93c67367919660ea534599d50e50a171afc95e3b1b179dfd" "f1ef79f377ea3f1e1d26b9a6f754a0756841901cae205cf57b164d80568d1067" "value"
    "the structural clique is transported by the clique hook (A5), so O10/O12 do not fire; the collapsed twin's single function needs the encoding shrink O17 (deferred, D3)"
  , e `Tests.Ix.Compile.Pass.O10O12Collapse "src" "perm" `PassO10.Src.B.g "collapsed pair, structural recursion" .pendingCollapse
    "267441cde0a9b0ffa99c9726d6c3e25469b5b5b6cad01642e8db84ad47c4d57f" "82c10943463dd3f9e7eddf4fe9a99202f766682efcf57d60b9837b578f59fc17" "value"
    "the structural clique is transported by the clique hook (A5), so O10/O12 do not fire; the collapsed twin's single function needs the encoding shrink O17 (deferred, D3)"
  , e `Tests.Ix.Compile.Pass.O10O12Collapse "src" "perm" `PassO10.Src.fg_ab "collapsed pair, structural recursion" .inherited
    "492c491c844bebb7aeea604686c91540ab5ada6ad62e68fa95ccb7968295fd79" "2c40997cd6a2807e308345d78072f4e98adaa58c2c0ec818912d6c01d6c1ef3b" "type"
    "refers to a transported clique member of a collapsed block (PENDING-COLLAPSE)"
  , e `Tests.Ix.Compile.Pass.O10O12Collapse "src" "perm" `PassO10.Src.fg_bab "collapsed pair, structural recursion" .inherited
    "3a249dbaf3ef05e1478ec304af56a3d5b549bfb653b347a73b17b4f7917fd609" "eacdd6a9280086294f07b6ff06804204d8ac79f173ae1b88076d2047dee99aac" "type"
    "refers to a transported clique member of a collapsed block (PENDING-COLLAPSE)"
  , e `Tests.Ix.Compile.Pass.O10O12Collapse "src" "can" `PassO10.C8.Src.A.h "collapsed pair, structural recursion" .pendingCollapse
    "eebfe1edb3a39dcf09f2cce5ab68a19a51829df928dc9794cba1a8bf748836c5" "1b61c85dcf983bfcc24851e64f90f5f7462be26d7ec34faa618bc0760a80703c" "value"
    "the structural clique is transported by the clique hook (A5), so O10/O12 do not fire; the collapsed twin's single function needs the encoding shrink O17 (deferred, D3)"
  , e `Tests.Ix.Compile.Pass.O10O12Collapse "src" "can" `PassO10.C8.Src.B.h "collapsed pair, structural recursion" .pendingCollapse
    "1dea93ebdf9d8cf1707a90cbe52a301859bcfec668c796738b944101670c0408" "1b61c85dcf983bfcc24851e64f90f5f7462be26d7ec34faa618bc0760a80703c" "value"
    "the structural clique is transported by the clique hook (A5), so O10/O12 do not fire; the collapsed twin's single function needs the encoding shrink O17 (deferred, D3)"
  , e `Tests.Ix.Compile.Pass.O10O12Collapse "src" "can" `PassO10.C8.Src.C.h "collapsed pair, structural recursion" .pendingCollapse
    "0954f9483357e095ca2c420677b3c94c8973f6c49ea9c0561f36aa750e34cf6c" "ef3f42aa4933f91d1e97c7871161819cd186d33a88eb130ff1f1ce4420658793" "value"
    "the structural clique is transported by the clique hook (A5), so O10/O12 do not fire; the collapsed twin's single function needs the encoding shrink O17 (deferred, D3)"
  , e `Tests.Ix.Compile.Pass.O10O12Collapse "src" "can" `PassO10.C8.Src.h_ex "collapsed pair, structural recursion" .inherited
    "bedb456632b39ee62433bed090384665beb53b7a99defb19effc221aca49e199" "28ff1cd19af89d18fee40c0d22c383c9ef9c315b413bee83da4cb88a750e6f73" "type"
    "refers to a transported clique member of a collapsed block (PENDING-COLLAPSE)"
  , e `Tests.Ix.Compile.Pass.O11bNoConfusion "src" "can" `PassO11b.Src.B.noConfusionType "split-off enumeration, one constructor" (.pjForm "O11b")
    "c9112b5c2daafef397038049d0868a990d355d00ec702d62fe2c23f08c26f9f4" "f94f909903c277574adf722ccb7c246bc717b773cb367fde035da90b4a779ac0" "value"
    "O11b wrote the enumeration form under `PassO11b.Src.B.noConfusionType._ix` (decision 5, D1); the Lean name keeps the general form"
  , e `Tests.Ix.Compile.Pass.O11bNoConfusion "src" "can" `PassO11b.Src.B.noConfusion "split-off enumeration, one constructor" (.pjForm "O11b")
    "6df4cee531b34c717442d6aac4c8322da1ef93049d47389322376dce62db20d8" "dfbfaadea389bff0586dfc8c2c339acf7f1456c3a9272829c78b3197a1cb84d6" "value"
    "O11b wrote the enumeration form under `PassO11b.Src.B.noConfusion._ix` (decision 5, D1); the Lean name keeps the general form"
  , e `Tests.Ix.Compile.Pass.O11bNoConfusion "src" "can" `PassO11b.Src.nc "split-off enumeration, one constructor" .inherited
    "16e6a0d52dd035cb1572f709b59ed78cf653cf5f4fcf590425618669126864b6" "98cc3a136fd1ee9b5d82b6473a0a8107fbeef1fb6a109e67118092a8bf4b66c4" "type"
    "states `B.noConfusion` by its Lean name (PJ-FORM-O11b)"
]

end Tests.Ix.Compile.NonCanonical

namespace Tests.Ix.Compile.NonCanonical

/-- The non-canonical set of the clique families **with the switch on**
(`IX_PASS3=images`: changed cliques through the clique transport,
`Ix.Compile.Pass.Cliques`), read by `pass3-cliques` and exact in both
directions there. The names are Lean names and the `_ix` names of the
canonical constants, relative to the reference presentation. -/
def nonCanonicalOn : List NonCanonicalEntry := [
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `od._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "43281966e05730c23b3a58e91c7d538d88266e8eb7f3b7c4fe9ee28bb30f003e" "65e783795028f8e0de56fed91c7f0e72c756296832635fd169f985d3b9193187" "value.λ.body.λ.body.@3.λ.body.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "32ac0d0b7ab46893597f46158112832e456669f74427196c7392b187d6da2f1c" "bb08c2c77fa597768efd23f70721372b6a62c794e689d33030e180afec296cc3" "value.λ.body.λ.body.@3.λ.body.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "32ac0d0b7ab46893597f46158112832e456669f74427196c7392b187d6da2f1c" "bb08c2c77fa597768efd23f70721372b6a62c794e689d33030e180afec296cc3" "value.λ.body.λ.body.@3.λ.body.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `od._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "43281966e05730c23b3a58e91c7d538d88266e8eb7f3b7c4fe9ee28bb30f003e" "65e783795028f8e0de56fed91c7f0e72c756296832635fd169f985d3b9193187" "value.λ.body.λ.body.@3.λ.body.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m1._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "b473b69e52a37dafd09fb533128843a07dbcc58d58777409ffab856ef6d29407" "d2e57d36c50cd5775f4c95be7157e608df904c29760f0632f8715f3d8d31477a" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m0._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "fedaafc7f9367356e16f3202220f6bd36dfebc7c0fd73d316b979b0de7f938c4" "2ca8a8b47168b5ab5934c3da7114471d5bfb37bfadd265f5cf61d457209a9a1b" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m2._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "9bcdd88d009edbd1f0d37bf051063ad4c1f0530790133cb6a8fadabc96584fcb" "6d92f0bfe7815b036aa2e8aa94555be69ceca2b9ea03b336e21155446a12035a" "value.λ.body.λ.body.@3.λ.body.λ.body.@4.proj0" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m2._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "9bcdd88d009edbd1f0d37bf051063ad4c1f0530790133cb6a8fadabc96584fcb" "95694ad293b38d37c4a3ce5685b2515611e91594ee8be66d080c374c078df146" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m1._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "b473b69e52a37dafd09fb533128843a07dbcc58d58777409ffab856ef6d29407" "9b5514479236441cb7b31271e82f528edd1374ef82f3bb7966587f98c1faa76d" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m0._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "fedaafc7f9367356e16f3202220f6bd36dfebc7c0fd73d316b979b0de7f938c4" "d06c6d35cc3c901f92352c900abf036ce204f29228dec3299fc7791f4efb0a9a" "value.λ.body.λ.body.@3.λ.body.λ.body.@4.proj0" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "52a987639794c1db5e7385fbb563c6a75f665679ea982622300e77922ad501d5" "ae363b9cda9638fa9686d4b381dc9a676f2d52a4ffff51c061021c19a890fb99" "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@5" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "d90b3fb84212449b28689dda72a5b33a2441536c0026aef7d0d52ea4a43f3720" "f5485ab3ad53ac26004d88c0f094a13a6e9b46c004027eb6199621f909fee63c" "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@4.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "14aaa1ec78220ab13ef4eb9134c9260fb940dbabd9fb801f7e39ccd21b6d6be9" "f315630469a6313017fabc85531d5a356ab7e5f810c7b3592d4e66b390a31398" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual._proof_2 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307" "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6" "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa.eq_def "equation lemma" .lazy
    "119ac4c5c40a57c8e73fabb716af66c2fc17d22ec095a8a8b8108dba87cde3a1" "311ecc3184b86b232a250a4ca678b70b6e40b57a267e1cdc54ea5c32a98fb21f" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wb.eq_def "equation lemma" .lazy
    "d30d73b1646265e5d700dbcb6efea8dff8e117a7410bc38f56f1c191d2104f96" "327144d5b893ee7f5d24097c8fa728d6c7eb81225d9bf0c8fd1f3f3503bbf103" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447" "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual.eq_def "encoding equation" .orderStmt
    "2b874d7adcde67692447fa1de16691fb35bd9efae63943a64358f346f5832fee" "cc2a2148e21ce32e46eff6a75dfd00a1b67f9a0dadbf91639b57c0d4948cf459" "type.∀.body.@2.@4.λ.body.@1" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6" "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual._proof_2 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307" "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447" "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa.eq_def "equation lemma" .lazy
    "119ac4c5c40a57c8e73fabb716af66c2fc17d22ec095a8a8b8108dba87cde3a1" "311ecc3184b86b232a250a4ca678b70b6e40b57a267e1cdc54ea5c32a98fb21f" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual.eq_def "encoding equation" .orderStmt
    "2b874d7adcde67692447fa1de16691fb35bd9efae63943a64358f346f5832fee" "cc2a2148e21ce32e46eff6a75dfd00a1b67f9a0dadbf91639b57c0d4948cf459" "type.∀.body.@2.@4.λ.body.@1" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wb.eq_def "equation lemma" .lazy
    "d30d73b1646265e5d700dbcb6efea8dff8e117a7410bc38f56f1c191d2104f96" "327144d5b893ee7f5d24097c8fa728d6c7eb81225d9bf0c8fd1f3f3503bbf103" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual._proof_2 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "6d43105b925565d18ef4797b4cd28ef0ecf7d80f7d1c95ca138f121a5f4cf40d" "bceac634d415df450def06d4a22b21a761b5ed1656541840965438fa4762b8a9" "type.∀.body.∀.body.∀.body.@0.@2.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual._proof_4 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "ce71876d8dc1a733cf4a015111ba6be5780a8e830183d26f90e2182f961f21cc" "2bd27fb76859701c03ad9a256da78686e99bf9bdf55c62591ec604b81592ac37" "type.∀.body.∀.body.∀.body.@0.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual._proof_3 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "1a6d56af84d790f0f5f694bd7eb082c0a1beafe6aacd11323972d60dd5fb64b8" "b3b9365f8cbdd96920326a32b76e706633c74d36ce659bd9ac7e8371a71c5b3e" "type.∀.body.∀.body.∀.body.@0.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual.eq_def "encoding equation" .orderStmt
    "205423647ec0cfd85f0923b6927f8ea21ec2aeb2caecd718dd3ee0ef039b3991" "d0f98e93be3e30d814cb45b26997053706c312d701e191eedcdfa0a5b6cf2ff5" "type.∀.body.@2.@4.λ.body.@4.λ.body.λ.body.@3.λ.body" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "0e27ba25c79dc7793a8ba162691f785ee152ec1f68d31f4f597d4b09db0a5ef5" "9cc2b3854a5c3cc7cdb261fadd317f19800a7d2a2f1eb5c1bed9d698f9f2cc70" "value.@4.λ.body.λ.body.@4.λ.body.λ.body.@4.λ.body.λ.body.λ.body.@3.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual._proof_3 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "1a6d56af84d790f0f5f694bd7eb082c0a1beafe6aacd11323972d60dd5fb64b8" "fe16646b2b3f46f4d57a175b5b47d4d644c49dc4d12145774993cb86d21f145d" "type.∀.body.∀.body.∀.body.@0.@2.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual._proof_4 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "ce71876d8dc1a733cf4a015111ba6be5780a8e830183d26f90e2182f961f21cc" "757d86daa0a585e4986d23619f3b86f704e970c806116b70cd7932d948b6940b" "type.∀.body.∀.body.∀.body.@0.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual._proof_2 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "6d43105b925565d18ef4797b4cd28ef0ecf7d80f7d1c95ca138f121a5f4cf40d" "776dbac01f0a7c74dd91c8d188c9e34fe6a7cf75c293f611385a8223789eaca2" "type.∀.body.∀.body.∀.body.@0.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "0e27ba25c79dc7793a8ba162691f785ee152ec1f68d31f4f597d4b09db0a5ef5" "43efb240d50538091e93d4cdf2ffa2140037e6df0cda820c120ab0c46dc3b447" "value.@4.λ.body.λ.body.@4.λ.body.λ.body.@4.λ.body.λ.body.λ.body.@1.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual.eq_def "encoding equation" .orderStmt
    "205423647ec0cfd85f0923b6927f8ea21ec2aeb2caecd718dd3ee0ef039b3991" "554d9601db74da49f2f7e6e581f9e461b0cfacf16cb79a7fbb58cf49060aebc3" "type.∀.body.@2.@4.λ.body.@4.λ.body.λ.body.@1.@1" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `gb.eq_def "equation lemma" .lazy
    "8c620db260db49063de075bc9839f00b2d732c0468bb8b87f896facb9385a128" "76756617005ee9f40088352a058d4b86f4070b4ba99a73b383868e6ac91ed62d" "value.λ.body.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `gb "clique member" .guessLex
    "978a66e918dbcc26dee988dbbd25fd28f5f613c3482a5c14e1e32951b0bbccd9" "5337df8a3848071b3fa1fe71fb801aa7ea2f63c159b27860d51da14d3ada7232" "value.λ.body.λ.body.@0.fn" "the canonical functional differs: GuessLex picked another measure for the other order (D22 pins Lean's choice)",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga._mutual.eq_def "encoding equation" .orderStmt
    "04e8346072b66c68dde386ff5a5a1ce9144a185d226fc9099d8865ad22cc3c9f" "1dffc78b59df95be2ef948f52dd2c2138e3c7c9fe8f05aa4c808f72a2d0c359f" "type.∀.body.@2.@4.λ.body.@4.λ.body.λ.body.@3.λ.body.@1" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga.eq_def "equation lemma" .lazy
    "725de1dc9e6a16cbe621aefb2d4196d823e049f91cb1bb290f8d48051de49a7e" "1191d1d47fc19100e00b95245b819e129bc79647cab4a7c1c5f40b788087be44" "value.λ.body.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "9505e594f820630cddb3e20b6708419abb613c308ad91953d41372120ec19313" "f1b52679b1aa1207b01b494315252882f78493caaab7a40793cd0837c62a17aa" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@4.λ.body.λ.body.λ.body.@3.λ.body.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga "clique member" .guessLex
    "242e5c784fb1c56336cfb8bd9be95aae375a3e029bb6787da7e3802667cd64df" "40ad1a3600d87fbeb7553899424e3cb97d0dde6d38b7b6f30bf8f152ff5ecd71" "value.λ.body.λ.body.@0.fn" "the canonical functional differs: GuessLex picked another measure for the other order (D22 pins Lean's choice)",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6" "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual._proof_2 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307" "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447" "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta.eq_def "equation lemma" .lazy
    "119ac4c5c40a57c8e73fabb716af66c2fc17d22ec095a8a8b8108dba87cde3a1" "311ecc3184b86b232a250a4ca678b70b6e40b57a267e1cdc54ea5c32a98fb21f" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `tb.eq_def "equation lemma" .lazy
    "d30d73b1646265e5d700dbcb6efea8dff8e117a7410bc38f56f1c191d2104f96" "327144d5b893ee7f5d24097c8fa728d6c7eb81225d9bf0c8fd1f3f3503bbf103" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual.eq_def "encoding equation" .orderStmt
    "2b874d7adcde67692447fa1de16691fb35bd9efae63943a64358f346f5832fee" "cc2a2148e21ce32e46eff6a75dfd00a1b67f9a0dadbf91639b57c0d4948cf459" "type.∀.body.@2.@4.λ.body.@1" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual._proof_2 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307" "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6" "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `bb.eq_def "equation lemma" .lazy
    "d30d73b1646265e5d700dbcb6efea8dff8e117a7410bc38f56f1c191d2104f96" "327144d5b893ee7f5d24097c8fa728d6c7eb81225d9bf0c8fd1f3f3503bbf103" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual.eq_def "encoding equation" .orderStmt
    "2b874d7adcde67692447fa1de16691fb35bd9efae63943a64358f346f5832fee" "cc2a2148e21ce32e46eff6a75dfd00a1b67f9a0dadbf91639b57c0d4948cf459" "type.∀.body.@2.@4.λ.body.@1" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "dbc695fb29a7ce1669949b7525a305fbd4d1f11b5f1fbc352801a21aa7831447" "3427ae546dcec334c124360ff8d7484e7c97bbf7da70a47e61947ad058875f4e" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba.eq_def "equation lemma" .lazy
    "119ac4c5c40a57c8e73fabb716af66c2fc17d22ec095a8a8b8108dba87cde3a1" "311ecc3184b86b232a250a4ca678b70b6e40b57a267e1cdc54ea5c32a98fb21f" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pa.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "0ddea573a18b7aac2d20a006f8cda1fcef605fc2f31cd9e8782c5e4d1816b923" "17dad592622f8c1da82e3fab3f43a962e034ddd7f804ff221d35fbd6846c8469" "type.@4.λ.body.@2.λ.body.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pa.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "aae0295814cc6f61f77a936266e0a0bdedf33c89f9e37ea54b90ed658af55105" "35e34d7f00e53729f8c161ece500c8b896c38e2fbfadd9a2269617327da253c0" "value.@2.λ.body.@2.λ.body.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pa.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "0ddea573a18b7aac2d20a006f8cda1fcef605fc2f31cd9e8782c5e4d1816b923" "8043e9fdebd60d01ee161bee0427b12e1ed4b505ac63c2534a24c2ea6c2bea04" "type.@4.λ.body.@2.λ.body.@3.@1.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pa.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "aae0295814cc6f61f77a936266e0a0bdedf33c89f9e37ea54b90ed658af55105" "026e16e83c5526336e4c936926791e6e0d9159f175139d64eb2654deffe595ae" "value.@2.λ.body.@2.λ.body.@3.@1.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.TS "P0" "P1" `evT._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "78a3577514987bc92d9a2729706e613221b268472784a8d1d7e53287ba4814fa" "38b13258377b659e92f44c3b92385ec4029f9fa33836e6f6fb498d9441e0818e" "type.∀.body.@4.λ.body.@1.@0.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.TW "P0" "P1" `wa._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "f4215cec1c7e681c3804e51a25357202c2d500c4acc04ffa3f8ddc9c58a9c012" "09a6c8908407175fda86ab1e581780f564eb41fc1fd79ae3ea11581474cfe582" "type.∀.dom.@0.@1.λ.body.@2.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `odM.match_2 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "ad2109b70d8bcfdd495136d20ec3129341fc3e8f7cb40ec3c12f0d9c994101f5" "36eb9a22918e8eb22c991c6c46f9b457b79b2b605a04da5d497cac78941b5b4b" "type.∀.dom.∀.body.∀.dom.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `evM.match_2 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "c6811a1fabf7498b43ed04a9215d9bade1a8635f1bf3eff5477ee8e7e905a17e" "bb86122e6c18f5806837f497e2236d93bda8a9d2742582dbac273dbdba1e2fe9" "type.∀.dom.∀.body.∀.dom.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sb._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "2d3cb49f17edbe9962dffe39839decfcef1b848e952b2b0f0eb5a6bcfb0a46e9" "bb0d910606ace0c4f4f2ff9c4fe40706a578a62ae074e0184d55ed0b3758cf43" "type.∀.body.∀.dom.@0.λ.body.@0.@1.@0.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sa._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "fd47ab03aaa9797d850828664dca8a12002076c9a72c4ac8bac3309ffdaab7fd" "dddcbfd408991573a7c2afd6458b448e746deaada99201f81ea52af60cdaf431" "type.∀.body.∀.dom.@0.λ.body.@0.@1.@0.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fb._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "4755dc9f98893af601cf942a679f3239403d4ae45ab03eafd0be03414a48816b" "9c564d42d27f9d5a1b58a4befaa82a883e5c438577317f2931ecf4e43078305c" "type.∀.dom" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fa._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "f1623552388b51d41e965671cfc420cc8024ebffd72bf81675062fee794f180b" "df188f2d008db128174d3049a067aea93c06d7dbcf69ef358032120e773aa144" "type.∀.dom" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "24ce7b01a7f68ecea1e59627248a615f58ccfd435f8c058016f1f95dfd6191b6" "5fdb169ee5639e5367b7ca20abbab138e3c3b127b490901ade94083a6fed1f68" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual._proof_2 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "0c739daac4453efefe97ea2124eddc567c901a609e1a36d0191f7a499dde8307" "848b4d81111d5d993e61fbba20672461261caef265d28eac51ec2bf032089408" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha.eq_def "equation lemma" .lazy
    "57a59c6c6683b306cca70ca5a92e04b85385414bff173296c04667216610c387" "4942a1875a4c59792337ce5ffa338eee866de72408e85ef189772ce5daf2ad0c" "value.λ.body.λ.body.λ.body.@1.@0" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `hb.eq_def "equation lemma" .lazy
    "ba50c991443c66700984e2ebd7e783f68e71b5a574b26685aff7feb82265f671" "f48d91b5497d912fdb93f07f9bb2e49c4fd8cfff97f760aeafadef950ec3a837" "value.λ.body.λ.body.λ.body.@1.@0" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual.eq_def "encoding equation" .orderStmt
    "304abeedf1bd87f73382bcfc024dedb0aac1a01ea5f7ccb92efa730fb2732633" "89a8772f25d96b69de96009004693da023d46169108c225c9aab72ecc40a9aa7" "type.∀.dom" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "e5b17bdb3751da6746ae4ef84d225c3586b1d87a412334584fed79217c9c33ba" "5a1b5db06609153eba1fec84761e1e7f3a2c91adc473ac9b6322cea011795fd4" "type.∀.dom" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_2 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "266d5a80810da61f2cdb9a05392dd32e8f1f8e19b8a523dcd9980bf9d4f8b7d1" "10331ba20de201615de5919ad83281e9c5fdd020902cf78beff8fdbd62719e6e" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_4 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "ebafd6516a002329594de44610e5b29caa9a7b1ec0e96c307e0cc61eaf227425" "9037a9baf5fd0aa1923085d1063c69088bf90196b57d59073019802980a446ba" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_3 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "9a89308b9978c15485d5e24b90d25e240a0b20aa76ca8f8cad49fdaf7d7298a8" "adf61a53598121f7b789c3363512982f6c8f0be8ea7eb2714358053fe36e7a7b" "type.∀.body.∀.body.@4.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "2f26cbff694f6a8bb72246aaa44ff036340467b83cba9f59b64b4e12127053e2" "7d5de2d4739bfa89706b90112b4e6679596ba69c90bd83b447f17585844dec15" "type.∀.body.∀.body.@5.fn" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual.eq_def "encoding equation" .orderStmt
    "1fe0c2bdbc40ee7e7b51cc3ecc79ab82366db41efd0e90e30c51105e045001c3" "106e35daeb35e4579cc1bfa0610afaf7705543552ea524d2e4d8c483a1fdb629" "type.∀.body.@2.@4.λ.body.@1" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "77072c5e6560d1be6a9bc9685b5e7c79aa56f2065994f84d86c4c2d6b749b28a" "3b0e15526feeeacadb93a1a5eef651ad56ddc066b50212431324a6a92bdb4779" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `na._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "ad617d6050b9c71451d88c8b0afbbc8593d98af5452ed0dcdef9492090d5e67a" "992a551847a56ae1a88b48b4c37ef9b0ab8311e5dc7836421375b8471321bea4" "value.λ.body.λ.body.@3.λ.body.λ.body.let.val" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `nb._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "992a551847a56ae1a88b48b4c37ef9b0ab8311e5dc7836421375b8471321bea4" "ad617d6050b9c71451d88c8b0afbbc8593d98af5452ed0dcdef9492090d5e67a" "value.λ.body.λ.body.@3.λ.body.λ.body.let.val" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `rb._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "ce212569e61531f373a9766d9040cab31cf4bedcbd528748232748bc7c78c2d7" "4c5dce85fe8586bb8a1ea4fa76cf70bcfec977748c8418dfd47f8c794b2afa8a" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `ra._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "adb0877becc21251dba32d6f1ccbe6735a0bba7f7b0a6550890f5bf4d9a80d44" "bfc0b1efabc2c32500e3e3fbec6f4d7f7b87e8f00b09522dd2aebc99ffcadeb7" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `rb._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "ce212569e61531f373a9766d9040cab31cf4bedcbd528748232748bc7c78c2d7" "4c5dce85fe8586bb8a1ea4fa76cf70bcfec977748c8418dfd47f8c794b2afa8a" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `ra._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "adb0877becc21251dba32d6f1ccbe6735a0bba7f7b0a6550890f5bf4d9a80d44" "bfc0b1efabc2c32500e3e3fbec6f4d7f7b87e8f00b09522dd2aebc99ffcadeb7" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `nl._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "ed06ae82fa8626f18f62f1bcbbe20cdb0433be69c6df7d582d9805fa5615d49b" "082e23013ad28dd96fbbcdc68320a2d28df5b1ea2385c510f208023421cecfd8" "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@4.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `nl._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "ed06ae82fa8626f18f62f1bcbbe20cdb0433be69c6df7d582d9805fa5615d49b" "082e23013ad28dd96fbbcdc68320a2d28df5b1ea2385c510f208023421cecfd8" "value.λ.body.λ.body.@3.λ.body.λ.body.λ.body.@4.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `la.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "23f2fcf243de4f203af437cecae5aa8e456a296211e7f854d84afba79be84183" "c6f2eaa1f32e2bef4c81216442e92f4387ed945253669b02d356188afec72db4" "type.@4.λ.body.@2.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `la.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "844a3be331e7f7c758450925cb2a90675dcf0b0860acdc05e16d81c61e5df7ed" "0df7605cdc6de89fc8c8e5a82f154ca3474e0411a1701835480f6af2bd4a7682" "value.@2.λ.body.@2.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `la.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "23f2fcf243de4f203af437cecae5aa8e456a296211e7f854d84afba79be84183" "1142aeb7fe76382e4b955041246185112babeb5fed14dc8cc1a4d65cb0c19b46" "type.@4.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `la.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "844a3be331e7f7c758450925cb2a90675dcf0b0860acdc05e16d81c61e5df7ed" "7487e2bca961ef77d3aa8b7eca1691fe462020f9be2b4b99fa6dbab3b52d5e43" "value.@2.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `ca.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "c0238e623b000ba4cab169e97fa2f5bbe19c1b19257da7c955f568859dcd9e39" "d1986090ac5216fe4f2a0d6667c95969888402b565139e4191d8717f5ba63ad9" "type.@4.λ.body.@2.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `ca.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "ebf6e6b156580df2615158241987a80dad9d4c32fe0b016dcd3067ef5289eddf" "26f0280c765173003d6dbf565073450987c730824676f6bd699c78134addd1c6" "value.@2.λ.body.@2.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ua.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "b7bc40a157711d751e43e91fc474e33b76c2fb4c878863a4ac3722312b1a8b0b" "326b4257346d42a8eefa6b46b73df65f6862789cadf88ea8baa7fb8435a78296" "type.@4.λ.body.@2.λ.body.@3.@1.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ub "clique member" .shape
    "95b8e93dbb6bf28a4ac287b7b37ddd209f005d9ce94001abb50af0fec2500de1" "508ee88bd8a929bac5db824e484702dd7bbfbdb9815b598bade6165a6acab3d5" "value" "via ua._ix.mutual: its monotonicity proof took the composition fallback (SHAPE)",
  e `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ua.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "98442a03f9dfa6b72b5ac7adb902937dfd834e3071aec027601dc2c8c245a95b" "c98c6d8730e61475657d5c36d5642286dc8898eb0cefb389a14982923822f9cf" "value.@2.λ.body.@2.λ.body.@3.@1.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ua "clique member" .shape
    "c8e4b93e1e28fd1dcf8ef447ff7977c39411c7123d2cfddabbc0da9b7bf601a4" "5c0156271d4c9113e7ef52f4ec9f911d5d9e45c675c7d247e61669b2d85cccb1" "value" "via ua._ix.mutual: its monotonicity proof took the composition fallback (SHAPE)",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `rb "clique member" .recArg
    "5039de75827b5249a6ccd9fa22db9b94c5684418e8757aa5c8698d4ce8701926" "4d7d61d5cb52ebeeffedf40c55b61a826d4b616de1748d5d518a0c77f36f70c6" "value.λ.body.λ.body.fn" "structural recursion on x under one order and on x_1 under the other: the canonical functionals differ",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `rb._f "structural functional (Lean's)" .recArg
    "17354ef0aeee92d76a8d286b6d7872b467fd3f60fe44a0a2fa5b0ec653ff1921" "0b4277b06c6b8bc03ead07e16f0edbc44affdb19387289d0680576f912f10a83" "value.λ.body.λ.body.λ.body.@0.λ.body.λ.body.∀.dom.@1" "another recursive argument; the canonical x._ix._f differ too",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra "clique member" .recArg
    "4407ba2db279f943dfcca9b6ca6d216e87e23c7691826daf145741ab2be59834" "44869f94620473b65548c748c261686be20c85ee676988ea1c39b7da8cc08467" "value.λ.body.λ.body.fn" "structural recursion on x under one order and on x_1 under the other: the canonical functionals differ",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra._f "structural functional (Lean's)" .recArg
    "a4ca7ec36d6d47cba1a964f929947892dcaa354e1cda9c8f43b169ce83a4e220" "bcaa8bdad6fddf93d4d61cb14fed4674b79cc401f7f900fd7a556e715b984a50" "value.λ.body.λ.body.λ.body.@0.λ.body.λ.body.∀.dom.@1" "another recursive argument; the canonical x._ix._f differ too",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra._sunfold "user constant" .inherited
    "d27657c874dc052379d3e5eefb6faab94a630bc0267475b13367719c6ffdb5c0" "1822e19e6cdaf3c41169a3528f76c3d8383851b5227977b60c15ef5dd1da0f82" "" "via [rb]",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `rb._sunfold "user constant" .inherited
    "2342460fc4d332b83a1dfb99109e12c5cfe497be6a4b383aeda21f43405a2ad1" "6701d39b9914f8650da37d90a02ca3f964d9fda6330a10b6c6664c0bd654121a" "" "via [ra]",
  e `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra._sparseCasesOn_1 "sparse casesOn of the recursive argument" .recArg
    "3a4d0a9cb60745860c348a96bb097d439c3b156a60085eedbf4febb58fc9821d" "-" "" "ONLY-A: the other recursive argument needs no sparse casesOn",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `ha "clique member" .tacticAsym
    "81a1116c189347bb57bfeed4fdc7502c5269315582c04aa9815485162ea27be0" "a3d4bf350e02c3df5c332a74663309c3a562cf9785a743ad1b8492818731900e" "value.λ.body.λ.body.λ.body.λ.body.@1" "via the canonical ha._ix._mutual: the decreasing goals of P0 and P1 take the most recent 1 < k of the fixed context (assumption, omega)",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `ha.eq_def "equation lemma" .lazy
    "c8a926c0b15ac771de190bb1bb38887a9b14e03df3a51e239cb1954d3bf52183" "5fc89b1e74ba9508fb3e4fe0cd1c195d2e920938dc5d178867fa38163e35837d" "value.λ.body.λ.body.λ.body.λ.body.@1.@1" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `hb.eq_def "equation lemma" .lazy
    "895d6edfc2e83439b104aeb6f8a2e044351f4dd4a6dc95f9867ed343ae8edc7d" "efd0b35cd60e3ad25403d9681c613e3b927284635ea579caa43df6453cefbc90" "value.λ.body.λ.body.λ.body.λ.body.@1.@1" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `ha._mutual.eq_def "encoding equation" .orderStmt
    "713e343c7260eec8f36e0df24ebae7be003ad5f43c0913868cc6f35bccc135aa" "c5647bc6499224213d33344f77cdf7498457ba83c22144acbc3b14dc3c4268a4" "type.∀.body.∀.body.∀.body.∀.body.@2.@4.λ.body.@3.λ.body.@1" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `hb "clique member" .tacticAsym
    "afc03d9f741d843fe9590666f7f260990cc457cc68a552ed117eff1ae1561f7c" "1a794d1bcf32e34b8b35d62c10c55913dd2c3b995b1e7c2208a769f0c5f65d67" "value.λ.body.λ.body.λ.body.λ.body.@1" "via the canonical ha._ix._mutual: the decreasing goals of P0 and P1 take the most recent 1 < k of the fixed context (assumption, omega)",
  e `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `ha._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "a7bf3d2955497f278338733e61cc5d3dc811eb0b4f52a132982b9ee267ca1cfa" "533939407aa6db690941e7c604843562fb5b16c7ca42c09118038d78f3bef142" "value.λ.body.λ.body.λ.body.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `rb._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "98108fcdcffe277bf9fdce4b8af643b1b785867304c24a149d4b775f5160a4ab" "cb12be024d8ab4425c89facd16419aa4416f8a35a02dc910c309e29fb3d6a16a" "value.λ.body.λ.body.@4.λ.body.λ.body.let.val" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `ra._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "6b6a82b3efe33c928262df29a6e1e52725b2dd8a78d90979b1b57fd8353cbbc7" "68deb3de80fe3694fc0389a033a873e633618467eaa924299bec4b449353613d" "value.λ.body.λ.body.@3.λ.body.λ.body.let.val" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.TQ "P0" "P1" `qa._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "e221ec86aeb3fe776065dda776611fdc22c24a263d0fcf3e070a8d5bd1b4c39c" "71fe3265b59618938cb2faf2c8de64ba2c21e021af3bc308451210711fa2af30" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wx._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "29ade7866807a108f74e5e7af9dd2d16e97e0bc0ec70d8c0348e2f72461a77e2" "ea34c5fded17085a9976c048f5b01246fb7ace26452defea241709934aee40d1" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wy.eq_def "equation lemma" .lazy
    "b3b3766e869f41d5e016f20fd111a3078865b4e678a9fea2271665c911924696" "f9a53f194d6e42939af76f7dd338862ff4c9081d9b15b7ed9a7137a63edf3e2e" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wx.eq_def "equation lemma" .lazy
    "661646809e41f9088fe58c7623c66b6bb19e137df5a4ec2f242ae06e10c821b6" "1369d30019bbd8c870ac4a620feece8eaaf1963ade3dc8a01d756f4370422d97" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wx._mutual.eq_def "encoding equation" .orderStmt
    "a3574f238552c2f40c8328764184166dd04daa2832607300df5528398e21d223" "d80a2ec1dea3ed3a5569755bacc357727c3092c1b2f37454047f9f1ab969f2c7" "type.∀.body.@2.@4.λ.body.@3.λ.body" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  -- Ownership-based WF transport (FIX-pfwf, 2026-10-05; `WFConjugation`): a member's carried
  -- equation lemma is transported through the dependent source-domain adapter over the packed
  -- `eq_def`, which keeps Lean's injections (its form follows Lean's clique order). Under the
  -- shape-based transport these were transported by the packing re-association and matched.
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gc.eq_def "equation lemma" .lazy
    "8e0fbe1b5a5d406f26ff7cf750803c576da84e9386e8612ade88af5c8adcd6b5" "2382710c48945868893b5c14b79bdc5684139f27f99564acb2c72140d172bd5f" "value.λ.body.λ.body.@1.@0.fn" "a member's equation lemma, carried: proof through the source-domain adapter over the packed eq_def (Lean's injections)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga.eq_def "equation lemma" .lazy
    "f35827b4c84b6f70580a8b6912fd4b3da4501c1225357921aacb8a390e8bcf48" "5c2804a821ded475222bcbd1e8a33804e12ce6020fecc37b81cebfba71147408" "value.λ.body.λ.body.@1.@0.fn" "a member's equation lemma, carried: proof through the source-domain adapter over the packed eq_def (Lean's injections)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gb.eq_def "equation lemma" .lazy
    "663b6353b44257a43edf91bae9c44925f0e4acedf1067f072d5bb02dc3cbf04b" "fc2ee9f81c98e1b6112357b83f5717dee461c1d558e9a440fa4c502f05b01b41" "value.λ.body.λ.body.@1.@0.@2.fn" "a member's equation lemma, carried: proof through the source-domain adapter over the packed eq_def (Lean's injections)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gb.eq_def "equation lemma" .lazy
    "663b6353b44257a43edf91bae9c44925f0e4acedf1067f072d5bb02dc3cbf04b" "fd9070ea53ccdc65142d822ef5a8d6a137254e55661212ce314a6ec546de63b6" "value.λ.body.λ.body.@1.@0.fn" "a member's equation lemma, carried: proof through the source-domain adapter over the packed eq_def (Lean's injections)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gc.eq_def "equation lemma" .lazy
    "8e0fbe1b5a5d406f26ff7cf750803c576da84e9386e8612ade88af5c8adcd6b5" "b5f74e9a149a8afab9eef2365af9473a23ac4c0c7e47bc3d2c521b6366cbcea8" "value.λ.body.λ.body.@1.@0.@2.fn" "a member's equation lemma, carried: proof through the source-domain adapter over the packed eq_def (Lean's injections)",
  e `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga.eq_def "equation lemma" .lazy
    "f35827b4c84b6f70580a8b6912fd4b3da4501c1225357921aacb8a390e8bcf48" "0c4d2f04b89b366281ee0e7e5de8c2ede32a9bfcde6cbba7f38960ea1f4da6b2" "value.λ.body.λ.body.@1.@0.fn" "a member's equation lemma, carried: proof through the source-domain adapter over the packed eq_def (Lean's injections)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `tb.eq_def "user constant" .inherited
    "8045fb2714463d5f507803c8f11719736d5d682267259d79a86a90f935f5e534" "d9f2efb0b94dae865d19bbaf6933db69604de6ae0e89d95276c5f94d1fe5b425" "" "via [ta._mutual.eq_def]",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta.eq_def "equation lemma" .lazy
    "b54c8cd37a0a2fae100d92e29ecc88aa73098d1b6a0831b60a2f084e30c5aaf0" "42d3af4361d9bb629204e234341576b19e79cc86be1aa7c1a55b90d37ec1c80d" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: proof through the source-domain adapter over the packed eq_def (Lean's injections)",
  e `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `tc.eq_def "equation lemma" .lazy
    "883d9d49e5f48fd84bd3ff3ee96b7f736be600a4a919cfb10791b88244ec0c15" "97a7ea7346e26e1e2d9a28da11c782d267ed3a990e5732ad10f18be206cb7091" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: proof through the source-domain adapter over the packed eq_def (Lean's injections)",
  -- The clique-ownership sources (`Tests.Ix.Compile.Twins.ownershipFamilies`; FIX-pfwf O3), measured
  -- with the commit that registered them (M1-a): Lean's encoding constants of the transported cliques
  -- (ORDER-STMT), the carried member equation lemmas (LAZY), and S1, S2, R1, which the transport keeps
  -- in Lean's form (NOSPEC: recovery declines on the ownership grammar and the statements tie).
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF1 "A" "B" `first.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "e671b29fceba8cc20324dec2d0ffabe25226595b9b6e12c367c9ea4e327082c8" "9b4940a87d847f5a332f3881c60cf687ecdab19790460818273fa8291023c814" "type.∀.body.@4.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF1 "A" "B" `first.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "b4c4dc1730ff0e891c8a4989a790640c78c3e6b93ee6e5484ee46c5adcbd9ef4" "0f2333bc92b60d25941985333b773e502cf1d500806702d8b476fc8c8e26800c" "value.λ.body.@2.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF2 "A" "B" `first.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "e39c6fb358f9843a274b6a2aae57f538ad77deb283c721c0ac27711cf1418fc0" "3b9d58377332abc5d2b71b9ee3bbad0bdd59b32f625705750ecd6aafa7582433" "type.∀.body.@4.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF2 "A" "B" `first.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "09b82e9ed2407a220dce1d8b009e729b85af7306409af56af7ab6a6032774227" "cd153781fe02b322fc9e6781948ce00b4a884fac7c8c6168e70ef3d6202e9aee" "value.λ.body.@2.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF3 "A" "B" `first.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "d38724da453f7d3acf869eade643ffe49afff087b41e63c0c4431fae289ec0f8" "42cbdfc0d1f510eb6fb5a7f8142f8ffbac05eb5d85d634a44921e9a678d42b08" "type.∀.body.@4.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF3 "A" "B" `first.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "16631ba556536b881fe84599e887cfbb602b56c532b7f3be077bf34b8e04ccf3" "448c8555ee6d79b6c7cc1733ff8527629020875fad50b0cb9b2ea506084dd422" "value.λ.body.@2.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF4 "A" "B" `first.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "08450c597d30d6ef5c8f2e8eb469906fcde0481b8db8e031b9d5a4db1e666465" "2f2734edf99fed84d662cbc89e1dffab6cf009923679c3eabdd167b26e3c4c3c" "type.∀.body.@4.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF4 "A" "B" `first.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "27b8e5f489f2772a4eb9bb834784e74b35d0cf9e3149e5bd72f9836085fc8bcc" "3f1cb051758b7c67958192e3da3a3e4e3eb0bb31cb047ee0aefb70be2c2312af" "value.λ.body.@2.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF2C "A" "B" `first.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "ef46edef9497401ec61d99bab772c98f980e737b788a22348d89963529c41bb8" "a0f783028f65c70c25b302a937f75f9e470c3bccdc10a53a3fbb2b6d9e54bc6b" "type.∀.body.@4.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF2C "A" "B" `first.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "11c6cd3b1107e0b890b8011e13b2721e0f739918486a8cd643f6b704be4d5560" "c94a45c53b593ee049789b88e0c52e1a6176fc7aaf1ca05a2a580109efcc0861" "value.λ.body.@2.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF3C "A" "B" `first.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "9db57a515196e4662a23c109005b51e3721b7ad41d11c86cb758e2148bae944e" "24098ee09a8d54aa93bf399d557a4169bf12f0cfba5a5a4be06bf8afd0c7e4fd" "type.∀.body.@4.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF3C "A" "B" `first.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "62f450b8d2bedf5910f622fd41d71f165b7daccdb7c40e017dc3df848705f5de" "10de8546fefeb9038051212c2100dd9bc5ea277b6a45d28b91be9d99250d6c9c" "value.λ.body.@2.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF4C "A" "B" `first.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "a1cb59d3bf598bb6cd857e656982198d35994bef432d5962b337fba725f3c7aa" "7cdb9900095cfe74c3609e7f045bf9e0a6f0d5af2aed7acf09b124e72dce9ef0" "type.∀.body.@4.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF4C "A" "B" `first.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "307120536def828bc2de647641cbffcf177af23cfc7b8079992b320ba6c44d58" "3ac6ada4f1e6a15bc4a1095de3a0d87b98815fbf9fb29567716277956343a26c" "value.λ.body.@2.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF5 "A" "B" `first.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "3253871765e4877727992e0859a3a51a7dd4c9bdd828a051ff5441e5027397c4" "b346921348a31ebf07f0f0fe88cb056395837d0cceb3c0ec83d7dea96b1094d9" "type.@4.λ.body.@2.λ.body.@3.@1.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF5 "A" "B" `first.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "4a4c20467572611a6d56b4f2323becc03ab12a4ce675d34398d9bb3e103acfde" "fca68e937aa6c4be5f37a9e72ec8693f6538e90a6195c168b2633c75bd8d0d79" "value.@2.λ.body.@2.λ.body.@3.@1.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF6 "A" "B" `first.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "e3eb8c26937ff0523f27850b11cdf8b967879d4cc7d60d0fa2d2291e4566ac56" "ae69c4542735fe9bf0a47259e7e060cc4e93c193ebff6ebaf6d621c97be1bd4f" "type.∀.body.@4.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF6 "A" "B" `first.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "6f43a29039481794dc43ecd065a8fb149224a1c58c138f3a10b1ff1768cdc5eb" "5ac3bdc340e5d3541d41492f0a2daa0aa8f3cd59442b094c0979f6fd8e4b71c7" "value.λ.body.@2.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF7 "A" "B" `first.mutual._proof_1 "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "55050fd5db36a75b984c7ab3ae7a4e483d14aa52336fdab8b0e33e447fe216fb" "71d152deec492831de2b8d233f5e0aff1992cc5a7a729668e3c6c37cd2cc86e6" "type.@4.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.PF7 "A" "B" `first.mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "3a859aa5eb696cc3ee167f6cb13fbdb4846b295f8abf61a6e3de84ce5ee9800d" "cb5621ef481b944a5895a3d5e7b42e416f45051c407e72bef8b8cd66a2e92837" "value.@2.λ.body.@2.λ.body.@3" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF1 "A" "B" `first.eq_def "equation lemma" .lazy
    "782eaaf6a59f8c331fdf6043660649f3a1f39ad61d4d6fa716f7888312f2e49c" "4d5eb651b0a6ba9ce73c4e80b573ce8a16ac8985c2ce461790d6e95b2417b77f" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF1 "A" "B" `first._mutual.eq_def "encoding equation" .orderStmt
    "fc367f587442cf47bb85f9b385c4f9af05a8701d254e9b6a3db865a59d1abbfd" "8b34e3d81a4a36f1030833efe4e49bf7ed6a1a192da4a51c9f0cacab469d0655" "type.∀.body.@2.@4.λ.body.@3" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF1 "A" "B" `first._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "3ebbfb7f555960bc417736ae0ae9cc5932b4ca372aa49576aff5d39748d0e3ca" "c0ae3aa9ffc60ab30cd84f3d4af935d8c1df03b739f42b590bc7a6e3260efefa" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF1 "A" "B" `second.eq_def "equation lemma" .lazy
    "b2ee49453b93b814669e5fcb9e77d19686c24abf9b42c8e6dcd1fbe64fd84887" "67fa48c970019afdd47e603b3bffd68d8b95a7002bc993ad34fe807a80a5d756" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF2 "A" "B" `first._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "af4a13ba3154a1b5f08afda07a544b258f4c4be17ca36deba9a7f1c13ea0a289" "01e4a1725db27f38f3191395a46d93133bf71bd02521f3fc9a604a2ddb2f924c" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF2 "A" "B" `first._mutual.eq_def "encoding equation" .orderStmt
    "a1a60185e167aaf686629190107eb08ab6a0ec29ad4fef9d997b5150f9024d50" "1514792edb5a01280adcdbc92f0d8edfa5d4d5d3f8df4100037d86565c22533c" "type.∀.body.@2.@4.λ.body.@3" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF2 "A" "B" `first.eq_def "equation lemma" .lazy
    "9ea82fa861a3bc17e4768c268886b9b41a7722419c720f25acf382289cc6595d" "8b82db512eff5b9fa2113e91e84e9de9770c27f2e80287e2af636a7b49427ac1" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF2 "A" "B" `second.eq_def "equation lemma" .lazy
    "4c9da2ccbd2ba71fe9d21ed9cb0eda0845ae5fb3999c03ea92b496f7cbd5649d" "a9313bd4a9a8351276d41384093a1ac9ef1b1ae249d0e0906c5a92fa85dfec9b" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF3 "A" "B" `first._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "0dbd97943d6530493e0eaea1b269eefd9222be1befda7d6d2b4de494eb05c13b" "8db574eda72c661d899b250ef94e11af9b71e1f469cb9d0f8e47a41069781ae6" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF3 "A" "B" `first._mutual.eq_def "encoding equation" .orderStmt
    "ce99918bc79b86bfe6d862e615dcea9a4a33315a214efa561d6ef85757470b4d" "6ff4a5021de5834f2a894f4492e44af6c1e7e0099e37cc96b6ade8c9f913c3f5" "type.∀.body.@2.@4.λ.body.@3" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF3 "A" "B" `first.eq_def "equation lemma" .lazy
    "6e81191a7438e62ed0405a722ae8b1ae1544485777b115cdc6ce842fbe65635e" "c19a361734231b9527c4b20ebb89dbdd8083f5f660ef3dfe05bc2e4a0e367695" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF3 "A" "B" `second.eq_def "equation lemma" .lazy
    "4175c95637070f69c9c4187631133f9fbd5dca9801862aa3f0ffc89b0a8f3f6c" "99d3bbbe75253de1490b8ea7d7bddaef222a57b040f3f66ecc9d2b1426a60c97" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF4 "A" "B" `second.eq_def "equation lemma" .lazy
    "6bc279f8fb8066ea1892db6018a931df3bea267acd2743c80fddc5ed92193e7d" "c364f2475754ba5c11fad54338c008d43692752ffc277f4d46035cefe9a0d3d7" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF4 "A" "B" `first._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "320e943e931429dc411ccda0c5969bd8b82376489f6a25e1903419bb9e462d02" "534c1061521425523e33349615169bb7371d1b9d9325983a92287b59b5db7814" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF4 "A" "B" `first.eq_def "equation lemma" .lazy
    "9dd79db4385aa08aa015451d5f7350d4e861a013963ebf230280f0f8c8027877" "77a8b93bac0e7d64490ea6623060e3bf867c65c909b8c4a70d22564901d34ca6" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF4 "A" "B" `first._mutual.eq_def "encoding equation" .orderStmt
    "603cced502c021147c2598ac9bdd8303e521a4f6ce722e2c2e1db219ecd759b3" "b0961a71bd67c1c40cff7b3be907244304165ef358f4ab71b1fe2fc3219f12ed" "type.∀.body.@2.@4.λ.body.@3" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF5 "A" "B" `second.eq_def "equation lemma" .lazy
    "65d8bff9dfd89da213ebb4ecb91c96bfd78dc4354d14fa79eb3dcb7846acbd1d" "4da3e49e526204a131ee6d864b084617b27839971be9a7b36c1c5245ad4cb230" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF5 "A" "B" `first._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "2832aebe99fd81fb90e227eadd640754efd5142c15869b56c87fdbfdbcee5527" "33b2cb27a872620f6b281b8ad4d2272ff6a4da88a696b7cde148dcb0cee38371" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF5 "A" "B" `first.eq_def "equation lemma" .lazy
    "05e4a6dbb8f68f9bc3818540772357a0efb518a6d2fbe340e0f9038a71f4d81d" "dedb5e84418beacf675272a8cc5cfcad79a21d7b27cf4de66b7648ec9bd2b1f7" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF5 "A" "B" `first._mutual.eq_def "encoding equation" .orderStmt
    "55de8add6a41f1d2cdd29e3737bdef2343b71b0169263bfab3f431e74fac30d3" "7204c66ae68484fe81f0139b6c8e11f373d3377a71fe503196d62f6d959df594" "type.∀.body.@2.@4.λ.body.@3" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF6 "A" "B" `first._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "a0b455f72db0c57c44249b64391d210151366d4f2cd32b41e020f1c7a4d2ad67" "a189892ee0c5a45f8cc8ca609ac338b9764678432d5a0661ff5713b131c276c0" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF6 "A" "B" `first.eq_def "equation lemma" .lazy
    "767f5e5a22e551d854cfaf117cb65a9add1f9372648d654bde19dbde161b3444" "24031d337aa83b455a25cba2f2a318d9c533b7450ac6038b233cec82b6135f53" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF6 "A" "B" `second.eq_def "equation lemma" .lazy
    "cfa432606a7aa9e45651ab662b172a41bca241f5dda7cc9ac41f796cd64703ea" "26d91dfa58a0cf8049c9f1c01c5a7c2a08402bf498a27d2c31de2c5170df8d55" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF6 "A" "B" `first._mutual.eq_def "encoding equation" .orderStmt
    "19e6fde72cf1279bcea5b8499dcf8be66f3b3d1807643459a3a7bdcc526a55ca" "e31dc05739de254e8d0715091d46a7a3e38ecfd89c5d041cc0427bb3cc9766b6" "type.∀.body.@2.@4.λ.body.@3" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF7 "A" "B" `first._mutual.eq_def "encoding equation" .orderStmt
    "c0253fabe5626fe7f4950989cb66b4232558a4fcc347c9db6504714297e8e35b" "8c4a7bc2aea534a5c68f5f0c90f5690fb8a297c108c263bb44c034f500a8a0f9" "type.∀.body.@2.@4.λ.body.@3" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF7 "A" "B" `first._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "918f2716650ff7a5632696c813d118976ae48f8934de411e7290a193874880d5" "7b26950106d94325a26cf8c1671bfa28fdf6d38f8b43ebe688526bab5ace7d68" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF7 "A" "B" `first.eq_def "equation lemma" .lazy
    "d646037d0051f1ae2272c6d618745c05be9e516fe885fcd15ce966978b7ad3c9" "8325cc59c261fbcb0a3995bbef6ec271ca34b387b7c04215e2824b94a437eb98" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF7 "A" "B" `second.eq_def "equation lemma" .lazy
    "388c89ae09d98ed6d05e1e29801c5c445063f5601c404a61cdc0c2e6041add75" "c8adb3f3b97db00a2939d899462291ad0d3002ff0a2f328770efee9efcf6a806" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF8 "A" "B" `second.eq_def "equation lemma" .lazy
    "8afeb5d5379664f601bd8b14bfffac1aa1723427576d204f2dcbff446f03241f" "e5e0dfb08e33f51438dc05c62e9c6751b2c8081591f62dac70360a7ae5b17898" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF8 "A" "B" `first.eq_def "equation lemma" .lazy
    "d32e4cab191d5140523197606c87296be267ddafa763e3a3b7802e617bb097d2" "1b52c4991440156755beb7e9039f5ff212fce7866322aabd6eeca5ec7c74cfc8" "value.λ.body.@1.@0.fn" "a member's equation lemma, carried: transported over the regenerated canonical eq_def on one side, Lean's own proof on the other",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF8 "A" "B" `first._mutual "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "a7eb8630dfe06618bded5365b56c9f347ec0a786c0354a9a6cbd277be8732d9d" "86681f1c3a91226d2e2f4b4785ac807a8a30bd5d983201e124c1b76b6f5578ae" "value.@3.λ.body.λ.body.@4.λ.body.λ.body.@3.λ.body.@1" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.WF8 "A" "B" `first._mutual.eq_def "encoding equation" .orderStmt
    "1060ffaadf5b325c8d4f62b22c64e35ffab588cab303e951929d123380b6bd35" "ba321c176049fdf3f24023141d418c132224133773a8b22ee759cf1cd4991396" "type.∀.body.@2.@4.λ.body.@3.@1" "Lean's packed equation lemma under its Lean name (statement over Lean's packing)",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S1 "A" "B" `second "clique member" .noSpec
    "0396fdbbdca9bcc4ab255b7972c57fa7488e648a570cbf064cac41efb8be5495" "d9524994d6d2fbf610acdb6ad41ae42dab6836620ddaea1e30ae03363090bb4a" "value.λ.body" "the order is undetermined: recovery declines (grammar: a brecOn application of the block outside a member's root (in first._f)) and the statements tie; Lean's form in both orders",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S1 "A" "B" `first "clique member" .noSpec
    "2960d0bd59fe219680c5b19ddbf83e2361ef84dc1f41a3c62ccabd926c6ba299" "54c453ab555eb235ef77da502154c8242d75f39591e3cfbfff83cd3ba64fe050" "value.λ.body" "the order is undetermined: recovery declines (grammar: a brecOn application of the block outside a member's root (in first._f)) and the statements tie; Lean's form in both orders",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S1 "A" "B" `second._f "Lean's encoding constant (the clique stays in Lean's form)" .noSpec
    "22f73ec238ab67bf936f6402bd16bf4e3352d83da65f7f22d06ac4880f02d29d" "d383933dfc0292bb71de31ad0ca30b7863254e94bf19c00a2de98ba81c84aaab" "value.λ.body.λ.body.@3.λ.body.λ.body" "the order is undetermined: recovery declines (grammar: a brecOn application of the block outside a member's root (in first._f)) and the statements tie; Lean's form in both orders",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S1 "A" "B" `first._sunfold "user constant" .inherited
    "a3d7449b24b179ddc1ca7e6fe8f685cb769f54620c6ea496d9a9df16191ff1d8" "b26f8afc70ccc9dec0c9c7c11aa355aa3210d0047ef4cdb9a73e428671074061" "" "via [second]",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S1 "A" "B" `second._sunfold "user constant" .inherited
    "1fed9bc1f141af427a247ecd87754ebed783e5f0f994f76d40cf220cada6931b" "4b4f33437f31935a9ffa3b43777fcac80e2422e488df512df9a19a405202653a" "" "via [first]",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S1 "A" "B" `first._f "Lean's encoding constant (the clique stays in Lean's form)" .noSpec
    "a2ff5e3045525dddb6ac4f60361fd6045e1e015509e8d65da096900da5617e5e" "06fa31c03562f436a4a92807e7408ad290ede0357fe33104521d4c09a056e0c4" "value.λ.body.λ.body.@3.λ.body.λ.body" "the order is undetermined: recovery declines (grammar: a brecOn application of the block outside a member's root (in first._f)) and the statements tie; Lean's form in both orders",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S2 "A" "B" `first._f "Lean's encoding constant (the clique stays in Lean's form)" .noSpec
    "480f6bac42b271a83724ad6024b2540e3e25fed757646b0ab54a3e347ad9cde9" "b4f0f49df0722295fb3d881d96be864bb714c588ee715a582da716279e9985ea" "value.λ.body.λ.body.@3.λ.body.λ.body" "the order is undetermined: recovery declines (grammar: a binder d of a below type that is not the recursion's dictionary) and the statements tie; Lean's form in both orders",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S2 "A" "B" `second._sunfold "user constant" .inherited
    "8f22d8f53b45012d5d1efe4ddecb2a5a04e541f11f6a8a8a8afab4e2d5b9b041" "e4bc9416cfe435a4ed06a27145d95bc86ada11fbb49e302151fa7b5bee560281" "" "via [first]",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S2 "A" "B" `second "clique member" .noSpec
    "03736e098ab70c1a4b6c32e1df0b0e103db563025eb8015e064f05120eef3a00" "70d43ca460eaba80e1a4f0a88664364e7ae625217241a146e27bf5aaf1f30063" "value.λ.body" "the order is undetermined: recovery declines (grammar: a binder d of a below type that is not the recursion's dictionary) and the statements tie; Lean's form in both orders",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S2 "A" "B" `first._sunfold "user constant" .inherited
    "4097ad440c616f057981c5cab9e020fbdfe48e572e7d30f9cb12e872805e1a14" "fb812c421c128303dcc4f109c22ce10da0bff21e58dc673f20c8c7093f724d0b" "" "via [second]",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S2 "A" "B" `first "clique member" .noSpec
    "995a22d91635b7752ac872ecebcabaa3b1fa9290c144f18c1c2caae4db2b3187" "7aabf16fdae1c77f879f9ccd1574c1fed41f62096159ca392f0ddeb71b82ecdb" "value.λ.body" "the order is undetermined: recovery declines (grammar: a binder d of a below type that is not the recursion's dictionary) and the statements tie; Lean's form in both orders",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S2 "A" "B" `second._f "Lean's encoding constant (the clique stays in Lean's form)" .noSpec
    "22f73ec238ab67bf936f6402bd16bf4e3352d83da65f7f22d06ac4880f02d29d" "d383933dfc0292bb71de31ad0ca30b7863254e94bf19c00a2de98ba81c84aaab" "value.λ.body.λ.body.@3.λ.body.λ.body" "the order is undetermined: recovery declines (grammar: a binder d of a below type that is not the recursion's dictionary) and the statements tie; Lean's form in both orders",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S3 "A" "B" `first._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "02a464c61f968b3e65967c9c3ee9743acefb57090600cb1a4449ad2745a07471" "d2943c824c62a991e9ebdc3f6a398fd3ea76b3985b9b996180681c8f3616d625" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S3 "A" "B" `second._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "a487a223c3f013b8fc6e2ec7f4b824a9a68e20cd3ca6d6824eef48cc8baf6b3c" "0ba278158f8fad833af5d7fbee616e1644ecdcf814c37460b21ba73868120815" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S4 "A" "B" `first._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "14a06bd04456aac4390e8f8ff0f4c0aec0d50e836c3c4b896e4c340462f17708" "f4d0946ee64d7ed2344e6caa6a79f6b4ddc281044a55e60202ac5efd06e19fd3" "value.λ.body.λ.body.@3.λ.body.λ.body.@2.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S4 "A" "B" `second._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "621da63bb0b758594f8bcc508238262f0e45c69d3af533db7582c237b3e7b4ca" "2bf7f11b7cdca5749785a34df743eb500c67dff8840da1220218a416125c880d" "value.λ.body.λ.body.@3.λ.body.λ.body.@4" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S5 "A" "B" `first._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "44d0ac81a3ac8c0eb79b8ae0c96d0ce97500d77a31dc10a5153a06be6de509c0" "10d7dee33972b91aa43b893285673d4f675cbdb78eaacab6ee3386953ad37064" "value.λ.body.λ.body.@3.λ.body.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S5 "A" "B" `second._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "22f73ec238ab67bf936f6402bd16bf4e3352d83da65f7f22d06ac4880f02d29d" "d383933dfc0292bb71de31ad0ca30b7863254e94bf19c00a2de98ba81c84aaab" "value.λ.body.λ.body.@3.λ.body.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S6 "A" "B" `second._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "22f73ec238ab67bf936f6402bd16bf4e3352d83da65f7f22d06ac4880f02d29d" "d383933dfc0292bb71de31ad0ca30b7863254e94bf19c00a2de98ba81c84aaab" "value.λ.body.λ.body.@3.λ.body.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.S6 "A" "B" `first._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "171b2c0daf63e4607a3dd89e6d72e492422eb0762a3d70a4393c3484f0b5cb85" "e0090d838ab1f64040bed3753058a0ff129ebcb4c600dcaa7eedce5c6a94c987" "value.λ.body.λ.body.@3.λ.body.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.R1 "A" "B" `second "clique member" .noSpec
    "780248e0a1a13b039e96dfef42e991f67c5770fcc2714de2c4b13c055a76d04c" "2211362afdcc9bd8c32ab8448d2eabfedb6f405f2eb933b5bb1f429605b055aa" "value.λ.body" "the order is undetermined: recovery declines (grammar: a binder d of a below type that is not the recursion's dictionary) and the statements tie; Lean's form in both orders",
  e `Tests.Ix.Compile.CliqueOwnership.Src.R1 "A" "B" `first._f "Lean's encoding constant (the clique stays in Lean's form)" .noSpec
    "e1baa229cf518ac7dc8c83c06bfdf49b022be00b7133882fa19aa5ca1a8cb8c4" "cdb20f5a88523dab3eb91f02da38fb16c4fad7138fb8b4c65ad7b234de9378bf" "value.λ.body.λ.body.@3.λ.body.λ.body.@2.λ.body.@4.@4" "the order is undetermined: recovery declines (grammar: a binder d of a below type that is not the recursion's dictionary) and the statements tie; Lean's form in both orders",
  e `Tests.Ix.Compile.CliqueOwnership.Src.R1 "A" "B" `first._sunfold "user constant" .inherited
    "7cfc208ecff9299d38736a1722e959a39a62b87f309bc209d33f723434717761" "547fefddf971954f21421fcf4290ba174a1c68faa1c1aad4bfabba01d51f3a60" "" "via [second, first]",
  e `Tests.Ix.Compile.CliqueOwnership.Src.R1 "A" "B" `second._f "Lean's encoding constant (the clique stays in Lean's form)" .noSpec
    "30fafe4a29e50fd3af4d9c351132f875234764c696611357bf83e7c6f3d50fad" "0f91d7d47fe5d90a3244f33b91c2a82c6afda54653b3e19a7978053f09a040e7" "value.λ.body.λ.body.@3.λ.body.λ.body.@2.λ.body.@4.@5.@5" "the order is undetermined: recovery declines (grammar: a binder d of a below type that is not the recursion's dictionary) and the statements tie; Lean's form in both orders",
  e `Tests.Ix.Compile.CliqueOwnership.Src.R1 "A" "B" `second._sunfold "user constant" .inherited
    "d01646f7bd1854cdc1c1beec4bb6fd884f784a0a56e85b6e479930d615050923" "7154d0a5a8c0358170e91d380bc4302a4c13bfbec748a0ec4025674821db626a" "" "via [first]",
  e `Tests.Ix.Compile.CliqueOwnership.Src.R1 "A" "B" `first "clique member" .noSpec
    "96a54ef747e1e08967ccc41da0de9ccd600098166dce662a15ab4333fbca1d36" "32fb0e5aabce52baf1155163ccb2969b2ad1b843d612d9a228e75c45ef08dbf2" "value.λ.body" "the order is undetermined: recovery declines (grammar: a binder d of a below type that is not the recursion's dictionary) and the statements tie; Lean's form in both orders",
  e `Tests.Ix.Compile.CliqueOwnership.Src.R2 "A" "B" `first._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "44d0ac81a3ac8c0eb79b8ae0c96d0ce97500d77a31dc10a5153a06be6de509c0" "10d7dee33972b91aa43b893285673d4f675cbdb78eaacab6ee3386953ad37064" "value.λ.body.λ.body.@3.λ.body.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one",
  e `Tests.Ix.Compile.CliqueOwnership.Src.R2 "A" "B" `second._f "Lean's encoding constant (faithful; canonical form under `_ix`)" .orderStmt
    "d979a43078abc370a1d177f678cf40bcf5aecbe3b0dec6bf57dac9ea383d06dc" "5d900a06ea07ddc7cc6914260f72c60076f4fd35464d82c80332fbf27e9dd03a" "value.λ.body.λ.body.@3.λ.body.λ.body" "Lean's own form under its Lean name; the canonical constant is the `_ix` one"
]

end Tests.Ix.Compile.NonCanonical
