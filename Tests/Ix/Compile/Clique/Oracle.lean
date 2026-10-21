/-
  The clique transport's oracle (`clique-transport`): the differences of the
  clique families' twin pairs **before the transport**, with the causes the
  suite reads. `pendingTransport`: the packing order only, which the
  transport must reproduce exactly; `guessLex`: equal up to the measures;
  and the residual causes `recArg`, `tacticAsym`, `shape`, which it must not
  reproduce.

  These are the 157 rows of the donor's `NonCanonical.transportOracle`,
  copied unchanged in the fields the suite reads (family, presentations,
  constant, cause). They were measured with the legacy compile (the call-site
  surgery, which compiled cliques in Lean's form, before Pass 3); that mode
  and its full record are gone. The rows describe the fixtures' Lean terms
  (`Tests/Ix/Compile/Twins/Cliques.lean`, unchanged since), not a compile
  mode, so they remain the transport's oracle. Their evidence fields
  (addresses, first differing node) belonged to that compile and are not
  kept.
-/
import Tests.Ix.Compile.NonCanonical

namespace Tests.Ix.Compile.Clique.Oracle

open Tests.Ix.Compile.NonCanonical (NonCanonicalCause)

/-- One row: the family, the pair (`presA`, the reference, and `presB`), the
constant (relative to `presA`'s namespace) and its cause. -/
structure OracleRow where
  fixture : Lean.Name
  presA : String
  presB : String
  constant : Lean.Name
  cause : NonCanonicalCause
  deriving Repr, Inhabited

def r (fixture : Lean.Name) (presA presB : String) (constant : Lean.Name)
    (cause : NonCanonicalCause) : OracleRow :=
  { fixture, presA, presB, constant, cause }

/-- The oracle, in the donor's order. -/
def transportOracle : List OracleRow := [
  r `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `od._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `od .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P1" `ev .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `od .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `ev .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SA "P0" "P3" `od._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m1._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m0 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m0._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m2._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P1" `m2 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m2._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m1._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m0._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m2 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.S3 "P0" "P2" `m0 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cFo .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `lFo .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SX "P0" "P2" `cTr._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual._proof_2 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual._proof_1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P1" `wa._mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual._proof_1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual._proof_2 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa._mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WD "P0" "P2" `wa .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual._proof_2 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual._proof_4 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual._proof_3 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gc .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `gb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P1" `ga._mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual._proof_3 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual._proof_4 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual._proof_2 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga._mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `gc .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.W3 "P0" "P2" `ga .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `gb .guessLex,
  r `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga._mutual .guessLex,
  r `Tests.Ix.Compile.Twins.Cliques.WG "P0" "P1" `ga .guessLex,
  r `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual._proof_1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual._proof_2 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta._mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `tb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WT "P0" "P1" `ta .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual._proof_2 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual._proof_1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `ba._mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WB "P0" "P1" `bb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pa.mutual._proof_1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pc .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pa .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P1" `pa.mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pa.mutual._proof_1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pc .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pa.mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PF "P0" "P2" `pa .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TS "P0" "P1" `evT._mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TS "P0" "P1" `odT .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TS "P0" "P1" `evT .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TW "P0" "P1" `wb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TW "P0" "P1" `wa._mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TW "P0" "P1" `wa .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `odM.match_2 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `evM.match_2 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `odM .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.IP "P0" "P1" `evM .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sa .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sb._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sa._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TP "P0" "P1" `sb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fa .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fb._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fa._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.SP "P0" "P1" `fb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual._proof_1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual._proof_2 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `hb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WP "P0" "P1" `ha._mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_2 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_3 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta._mutual._proof_4 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `ta .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WA "P0" "P1" `tc .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `na .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `nb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `na._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TN "P0" "P1" `nb._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `rb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `rb._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `ra._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P1" `ra .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `rb._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `ra._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `ra .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.RF "P0" "P2" `rb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `nl._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `na .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `nl .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P1" `nb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `na .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `nl .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `nb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.NS "P0" "P2" `nl._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `la.mutual._proof_1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `lc .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `la .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P1" `la.mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `la.mutual._proof_1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `la .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `lb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.LI "P0" "P2" `la.mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `ca.mutual._proof_1 .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `cb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `ca.mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.LC "P0" "P1" `ca .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ua.mutual._proof_1 .shape,
  r `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ub .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ua.mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.PU "P0" "P1" `ua .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `rb .recArg,
  r `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `rb._f .recArg,
  r `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra .recArg,
  r `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra._f .recArg,
  r `Tests.Ix.Compile.Twins.Cliques.RA "P0" "P1" `ra._sparseCasesOn_1 .recArg,
  r `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `ha .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `hb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WH "P0" "P1" `ha._mutual .tacticAsym,
  r `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `rb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `rb._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `ra._f .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TR "P0" "P1" `ra .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TQ "P0" "P1" `qa .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TQ "P0" "P1" `qb .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.TQ "P0" "P1" `qa._mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wx._mutual .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wx .pendingTransport,
  r `Tests.Ix.Compile.Twins.Cliques.WU "P0" "P1" `wy .pendingTransport
]

end Tests.Ix.Compile.Clique.Oracle
