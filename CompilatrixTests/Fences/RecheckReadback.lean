import Compilatrix.Recheck.Readback

/-! Exact fences for structural readback-signature validation. These statements
cover closed indices and source/layout provenance, not source adequacy. -/

/-- info: 'Compilatrix.Recheck.Readback.discover_valid' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Recheck.Readback.discover_valid

/-- info: 'Compilatrix.Recheck.Readback.discover_closed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Recheck.Readback.discover_closed

/-- info: 'Compilatrix.Recheck.Readback.discover_layouts' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Recheck.Readback.discover_layouts
