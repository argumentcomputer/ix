/-! A Lean mutual block of Prop inductives whose members do not reference
each other. In Lean's (2-type) block the recursors eliminate only into Prop.
aux-gen splits the block into SCC singletons, and a singleton one-constructor
Prop inductive whose fields are proofs gets LARGE elimination, so the
regenerated `.rec`/`.casesOn` gain a universe parameter. -/
namespace PropSplit
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

-- Alpha-equivalent pair (collapse instead of split).
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
end PropSplit
