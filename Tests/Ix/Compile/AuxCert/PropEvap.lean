/-! H8: Prop-only source recursor whose evaporated auxiliary targets a large
external recursor (surgery.rs ~1193-1200 takes the first level as elim level). -/
namespace PropEvap
mutual
inductive A : Prop
  | mk : And B B → A
inductive B : Prop
  | mk : B
end

theorem a_rec1 (h : And B B) : True :=
  @A.rec_1 (fun _ => True) (fun _ => True) (fun _ => True) (fun _ _ => trivial) (fun _ => trivial)
    (fun _ _ _ _ => trivial) h
end PropEvap
