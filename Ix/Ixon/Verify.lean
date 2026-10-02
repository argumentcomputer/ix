/-
Extracted from Ix/Compile/Verify codec theorem chain at Ix revision
b067697b9d97552c6f52b2f72c892f84e4c7170f.
-/

import Ix.Ixon.Verify.Framing
import Ix.Ixon.Verify.BoundedUniverse
import Ix.Ixon.Verify.BoundedConstant
import Ix.Ixon.Verify.ConstantBounds
import Ix.Ixon.Verify.WorkRecord
import Ix.Ixon.Verify.Canonical
import Ix.Ixon.Verify.TagN

/-! The production codec contracts.
The universe/expression entry points consume the whole buffer. The
legacy `deConstant` remains a prefix decoder; `deConstantExact` checks the
whole buffer. Byte-consumption bounds cover arbitrary successful production
reads; universe expansion uses its separate budget. The accounting interpreter
additionally bounds complete record-parser work on success and failure, with
exact erasure to production. Canonical decoding has its own contract
(`Ixon.Verify.Canonical`). -/
