import IxCC.Cfg.Rc.Proof.Physical.ScalarTail

/-! Exact axiom fences for Deliverable 4: scalar-tail (`CtorInfo.nscalar ≥ 0`) physical allocation,
publication, constructor-table invariant (`ScalarHeapCtorOk`), release (`Gen.dec`), `@unique`
in-place reuse (`Gen.inPlace_ready`), and `word-w2` readback compatibility. -/

/-- info: 'IxCC.Cfg.Rc.Native.unique_header_reads_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.unique_header_reads_gen

/-- info: 'IxCC.Cfg.Rc.Native.ScalarReservedCell.publish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.ScalarReservedCell.publish

/-- info: 'IxCC.Cfg.Rc.Native.scalar_reserved_from_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.scalar_reserved_from_ready

/-- info: 'IxCC.Cfg.Rc.Native.scalar_publication_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.scalar_publication_ready

/-- info: 'IxCC.Cfg.Rc.Native.scalar_allocator_call_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.scalar_allocator_call_free

/-- info: 'IxCC.Cfg.Rc.Native.scalar_allocator_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.scalar_allocator_caller

/-- info: 'IxCC.Cfg.Rc.Native.scalar_allocation_wrapper_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.scalar_allocation_wrapper_success

/-- info: 'IxCC.Cfg.Rc.Native.scalar_allocation_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.scalar_allocation_total

/-- info: 'IxCC.Cfg.Rc.Native.HeapCtorOk.toScalar' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.HeapCtorOk.toScalar

/-- info: 'IxCC.Cfg.Rc.Native.ScalarHeapCtorOk.alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.ScalarHeapCtorOk.alloc

/-- info: 'IxCC.Cfg.Rc.Native.ScalarHeapCtorOk.dropAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.ScalarHeapCtorOk.dropAll

/-- info: 'IxCC.Cfg.Rc.Native.ScalarHeapCtorOk.reuseCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.ScalarHeapCtorOk.reuseCell

/-- info: 'IxCC.Cfg.Rc.Native.scalar_cell_release_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.scalar_cell_release_ready

/-- info: 'IxCC.Cfg.Rc.Native.scalar_inPlace_reuse_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.scalar_inPlace_reuse_ready

/-- info: 'IxCC.Cfg.Rc.Native.scalar_liveCell_readback_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.scalar_liveCell_readback_words

/-- info: 'IxCC.Cfg.Rc.Native.boxedWord64_liveCell_readback_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.boxedWord64_liveCell_readback_words
