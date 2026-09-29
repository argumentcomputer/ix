/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0

Extracted from Ix/Compile/Verify codec theorem chain at Ix revision
b067697b9d97552c6f52b2f72c892f84e4c7170f.
-/

import Ix.Ixon.Verify.Framing

/-! Preserved production codec contracts, independent of Lean4Lean.
The universe/expression entry points consume the whole buffer. The
legacy `deConstant` remains a prefix decoder; `deConstantExact` checks the
whole buffer. Canonical decoding has a separate K4 contract. -/
