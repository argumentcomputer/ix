import Compilatrix.Cfg.Rc.Proof.Physical.PublicationFree

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.freeChain_words' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.freeChain_words

/-- info: 'Compilatrix.Cfg.Rc.Native.publication_free_chains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.publication_free_chains

/-- info: 'Compilatrix.Cfg.Rc.Native.publication_free_heads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.publication_free_heads

/-- info: 'Compilatrix.Cfg.Rc.Native.publication_head_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.publication_head_frame
