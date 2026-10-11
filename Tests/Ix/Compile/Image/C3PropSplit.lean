/- image-gen fixture (`Tests/Ix/Compile/Image.lean`), elaborated at run time and in no Lake library:
   the prototype's `exp-prototype/CertProto/Cases/C3PropSplit.lean` without its commands. -/
/-! Case 3: a Prop block split into singletons that gain large elimination (PropSplit),
and (3b) the alpha-equivalent Prop pair Q1/Q2 (collapse). -/
set_option Elab.async false

namespace C3
namespace Src
mutual
inductive P1 : Prop
  | mk : True → P1
inductive P2 : Prop
  | mk : True → True → P2
end

theorem p1 (h : P1) : True := by
  cases h
  trivial

theorem p2 (h : P2) : True :=
  @P2.rec (fun _ => True) (fun _ => True) (fun _ => trivial) (fun _ _ => trivial) h
end Src

namespace Can
inductive P1 : Prop
  | mk : True → P1
inductive P2 : Prop
  | mk : True → True → P2
theorem p1 (h : P1) : True := by
  cases h
  trivial
theorem p2 (h : P2) : True :=
  @P2.rec (fun _ => True) (fun _ _ => trivial) h
end Can
end C3

namespace C3b
namespace Src
mutual
inductive Q1 : Prop
  | mk : True → Q1
inductive Q2 : Prop
  | mk : True → Q2
end

theorem q1 (h : Q1) : True := by
  cases h
  trivial

theorem q2 (h : Q2) : True :=
  @Q2.rec (fun _ => True) (fun _ => True) (fun _ => trivial) (fun _ => trivial) h
end Src

namespace Can
inductive X : Prop
  | mk : True → X
theorem q (h : X) : True := by
  cases h
  trivial
end Can
end C3b

