import IxCC.Cfg.Rc.Proof.Physical.PublicationFree

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.freeChain_words' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.freeChain_words

/-- info: 'IxCC.Cfg.Rc.Native.publication_free_chains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.publication_free_chains

/-- info: 'IxCC.Cfg.Rc.Native.publication_free_heads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.publication_free_heads

/-- info: 'IxCC.Cfg.Rc.Native.publication_head_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.publication_head_frame
