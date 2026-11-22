import IxCC.Recheck.Readback

/-! Exact fences for structural readback-signature validation. These statements
cover closed indices and source/layout provenance, not source adequacy. -/

/-- info: 'IxCC.Recheck.Readback.discover_valid' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.discover_valid

/-- info: 'IxCC.Recheck.Readback.discover_closed' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.discover_closed

/-- info: 'IxCC.Recheck.Readback.discover_layouts' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.discover_layouts
