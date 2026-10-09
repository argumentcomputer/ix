import Compilatrix.Cfg.Rc.Proof.Physical.PublishFrame

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.fieldAddress_byte' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.fieldAddress_byte

/-- info: 'Compilatrix.Cfg.Rc.Native.publishFields_headerFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.publishFields_headerFrame

/-- info: 'Compilatrix.Cfg.Rc.Native.publishFields_objectFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.publishFields_objectFrame
