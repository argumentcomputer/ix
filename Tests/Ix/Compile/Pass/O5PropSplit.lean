/- A4 per-pass fixture (`pass3` suite), elaborated at run time and in no Lake library.
O5, the level rule: a Prop block split into two components, each gaining large elimination
(Lean's mutual Prop block eliminates only into Prop). `P.toQ` (`casesOn`, O3) and `Q.elim`
(`Q.rec`, O6) get the Ix auxiliaries at universe `0`; `P.viaRec` (`P.rec` with a relocated
hypothesis) is O2 at universe `0`. -/
set_option Elab.async false

namespace PassO5
mutual
inductive P : Prop
  | p : Q → P
inductive Q : Prop
  | q : True → Q
end

theorem P.toQ (h : P) : Q := @P.casesOn (fun _ => Q) h (fun q => q)
theorem Q.elim (h : Q) : True := @Q.rec (fun _ => True) (fun _ => True) (fun _q _ => trivial) (fun t => t) h
theorem P.viaRec (h : P) : True :=
  @P.rec (fun _ => True) (fun _ => True) (fun _ ih => ih) (fun t => t) h
theorem toQ_pin : P.toQ (.p (.q trivial)) = .q trivial := rfl
end PassO5
