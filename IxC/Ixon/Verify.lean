/-
Extracted from Ix/Compile/Verify codec theorem chain at Ix revision
b067697b9d97552c6f52b2f72c892f84e4c7170f.
-/

import IxC.Ixon.Verify.Framing
import IxC.Ixon.Verify.BoundedUniverse
import IxC.Ixon.Verify.BoundedConstant
import IxC.Ixon.Verify.ConstantBounds
import IxC.Ixon.Verify.WorkRecord
import IxC.Ixon.Verify.Canonical
import IxC.Ixon.Verify.TagN

/-! The production codec contracts.
The universe/expression entry points consume the whole buffer. The
legacy `deConstant` remains a prefix decoder; `deConstantExact` checks the
whole buffer. Byte-consumption bounds cover arbitrary successful production
reads; universe expansion uses its separate budget. The accounting interpreter
additionally bounds complete record-parser work on success and failure, with
exact erasure to production. Canonical decoding has its own contract
(`Ixon.Verify.Canonical`). -/
