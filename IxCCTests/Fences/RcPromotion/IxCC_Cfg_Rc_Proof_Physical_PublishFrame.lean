import IxCC.Cfg.Rc.Proof.Physical.PublishFrame

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.fieldAddress_byte' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.fieldAddress_byte

/-- info: 'IxCC.Cfg.Rc.Native.publishFields_headerFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.publishFields_headerFrame

/-- info: 'IxCC.Cfg.Rc.Native.publishFields_objectFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.publishFields_objectFrame
